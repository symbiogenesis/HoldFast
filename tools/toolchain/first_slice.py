# SPDX-License-Identifier: Apache-2.0
"""Replay packet-validator proofs, C lowering, and native controls.

The harness checks source-level byte and loan laws in Rocq, lowers the supported
validator to C, and runs separate handwritten assembly controls in Sail.
Optional VerifiedOS CompCert replay exercises the lowered C. See
[first-slice qualification](../../docs/language/first-release.md#first-slice-qualification)
for the evidence and its limits.
"""

import copy
import json
import re
import struct
import subprocess
import sys
import tempfile
import time
from collections.abc import Callable
from contextlib import nullcontext
from dataclasses import dataclass
from pathlib import Path
from typing import Final, cast

from filelock import FileLock

from toolchain import (
    VelaError,
    corpus,
    dialect,
    env,
    gallina_module_name,
    image,
    packet_runtime,
    packet_trace,
    proofenv,
    solver_ledger,
    trace,
)
from toolchain import compiler_diff as cd
from toolchain import (
    elaborate as vela_elaborate,
)
from toolchain import elaboration_check as replay
from toolchain import (
    parser as vela_parser,
)
from toolchain.atomic import publish_report
from toolchain.elaborate_types import (
    _INT_SPECS,
    CheckedElaboration,
    _int_term,
    _parse_numeric_magnitude,
)
from toolchain.hashing import file_sha256
from toolchain.hashing import sha256_bytes as _sha256
from toolchain.jsonutil import unique_object

TIMEOUT: Final = 120
EXAMPLE: Final = "examples/first_slice.vela"
RECEIPT_BYTES: Final = 16 * 1024 * 1024
ARTIFACT_ENTRIES: Final = 4_096
ARTIFACT_BYTES: Final = 256 * 1024 * 1024
PURECAP_CASES: Final = (("pass", "pass", 0), ("bounds-trap", "trap", cd.TRAP_BASE + 28),
                       ("tag-trap", "trap", cd.TRAP_BASE + 28),
                       ("perm-trap", "trap", cd.TRAP_BASE + 28))
# Canonical instruction families for the handwritten capability controls and their
# startup and trap code. The assembler's table also covers the vector configuration.
PURECAP_CONTROL_ROWS: Final = tuple(dialect.TABLE[name] for name in (
    "addi", "addiw", "andi", "auipcc", "beq", "bne", "candperm", "cgetlen", "cgettag",
    "cincoffsetimm", "cjal", "cjalr", "cmove", "csetaddr", "csetbounds", "cspecialrw",
    "csrrs", "lbu", "lc", "lui", "ori", "sb", "sc", "sd", "slli",
))
PERTURBED_CASES: Final = ((7, "perturbed-wrong-payload-byte"), (12, "perturbed-stale-trailing-byte"),
                        (16, "perturbed-checksum-error-code"), (17, "perturbed-unscrubbed-checksum-dst"))

DEFAULT_CCOMP_CANDIDATES: Final[tuple[str, ...]] = (
    "/root/build/lane-scalar-effects-20260926/kernel-protected-final/plain/ccomp",
    "/root/build/compiler-unblock-integration-20260921/compiler/ccomp",
)

EXPECTED_LAWS: Final[tuple[str, ...]] = (
    "LawInhabitedByteCase",
    "LawAllocZeroedRead",
    "LawReadOverWriteSame",
    "LawReadOverWriteOther",
    "LawLoopFramePreservesDisjointSuffix",
    "LawFillAndFrame",
    "LawSymbolicFillFrame",
    "LawSliceMetadataAndRead",
    "LawReadOnlyAndInvalidate",
    "LawDisjointCopyAndFrame",
    "LawCapacityInvarianceSmall",
    "LawCapacityInvarianceLarge",
)

EXPECTED_CONTRACT_OBLIGATIONS: Final[tuple[str, ...]] = (
    "PrepareAndValidatePacket_restores_0_Base",
    "PrepareAndValidatePacket_restores_0_Length",
    "PrepareAndValidatePacket_restores_0_Tag",
    "PrepareAndValidatePacket_restores_0_PermRead",
    "PrepareAndValidatePacket_restores_0_PermWrite",
    *(f"PrepareAndValidatePacket_ensures_{index}" for index in range(10)),
)

EXPECTED_SCENARIO_THEOREMS: Final[tuple[str, ...]] = (
    "ValidateEmptyPacketOk",
    "ValidateFullPacketOk",
    "ValidatePartialPacketScrubsStaleAndTrailingBytes",
    "RejectFramingShort",
    "RejectBadMagic",
    "RejectLengthOutOfBounds",
    "RejectChecksumScrubsDestinationAndRestores",
)


@dataclass(frozen=True)
class NegativeControl:
    name: str
    source: str
    expected_kind: str
    expected_substring: str
    expected_location: tuple[int, int]

    @classmethod
    def marked(cls, name: str, source: str, kind: str, message: str) -> NegativeControl:
        """Strip the single fixture marker and retain its one-based diagnostic location."""
        before, after = source.split("/*error*/")
        prefix = before.replace("\r\n", "\n").replace("\r", "\n")
        location = (prefix.count("\n") + 1, len(prefix.rpartition("\n")[2]) + 1)
        return cls(name, before + after, kind, message, location)

    def check_location(self, line: object, column: object) -> None:
        if type(line) is not int or type(column) is not int or (line, column) != self.expected_location:
            expected_line, expected_column = self.expected_location
            raise ValueError(f"negative control {self.name}: expected diagnostic at "
                             f"{expected_line}:{expected_column}, got {line}:{column}")


NEGATIVE_CONTROLS: Final[tuple[NegativeControl, ...]] = (
    NegativeControl.marked(
        "oob-read",
        """module Vela.FirstSlice.NegOobRead;
public definition u8 BadRead() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    /*error*/Span.Read(s, 8usize);
""",
        "type",
        "cannot prove Span.Read index is within Span.Length bounds",
    ),
    NegativeControl.marked(
        "oob-write",
        """module Vela.FirstSlice.NegOobWrite;
public definition Span<byte> BadWrite() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    /*error*/Span.Write(s, 8usize, 0x01u8);
""",
        "type",
        "cannot prove Span.Write index is within Span.Length bounds",
    ),
    NegativeControl.marked(
        "oob-slice",
        """module Vela.FirstSlice.NegOobSlice;
public definition Span<byte> BadSlice() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    /*error*/Span.Slice(s, 5usize, 4usize);
""",
        "type",
        "cannot prove Span.Slice subrange (offset + count <= Span.Length) is in bounds",
    ),
    NegativeControl.marked(
        "oob-fill",
        """module Vela.FirstSlice.NegOobFill;
public definition Span<byte> BadFill() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    /*error*/Span.Fill(s, 5usize, 4usize, 0x00u8);
""",
        "type",
        "cannot prove Span.Fill subrange (offset + count <= Span.Length) is in bounds",
    ),
    NegativeControl.marked(
        "overflow-slice-extent",
        """module Vela.FirstSlice.NegSliceExtent;
public definition Span<byte> SliceAt(Span<byte> s)
    requires s.CanRead
    => /*error*/Span.Slice(s, usize.Max, 1usize);
""",
        "type",
        "integer addition on 'usize' may overflow",
    ),
    NegativeControl.marked(
        "overflow-fill-extent",
        """module Vela.FirstSlice.NegFillExtent;
public definition Span<byte> FillAt(Span<byte> s)
    requires s.CanWrite
    => /*error*/Span.Fill(s, 1usize, usize.Max, 0u8);
""",
        "type",
        "integer addition on 'usize' may overflow",
    ),
    NegativeControl.marked(
        "mutate-in-borrow",
        """module Vela.FirstSlice.NegMutateInBorrow;
public definition Span<byte> BadBorrowWrite(in Span<byte> pkt)
    requires pkt.CanRead
    requires pkt.CanWrite
    requires pkt.Length >= 4usize
=>
    /*error*/Span.Write(pkt, 0usize, 0xAAu8);
""",
        "type",
        "cannot mutate a read-only 'in Span<byte>' borrow",
    ),
    NegativeControl.marked(
        "mutate-readonly-view",
        """module Vela.FirstSlice.NegMutateReadOnly;
public definition Span<byte> BadViewWrite() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    let ro = Span.ReadOnly(s) in
    /*error*/Span.Write(ro, 0usize, 0xAAu8);
""",
        "type",
        "cannot prove Span has valid tag and write permission (Span.CanWrite)",
    ),
    NegativeControl.marked(
        "mutate-readonly-record-view",
        """module Vela.FirstSlice.NegMutateRecordView;
public record ValidatedPacket<region 'dst>(usize CopiedBytes, in<'dst> Span<byte> PayloadView);
public Span<byte> BadRecordViewWrite<region 'dst>(ValidatedPacket<'dst> pkt)
    requires pkt.PayloadView.CanRead && pkt.PayloadView.Length >= 1usize
{
    var v = pkt.PayloadView;
    /*error*/v[0usize] = 0xAAu8;
    return v;
}
""",
        "type",
        "cannot mutate a read-only 'in' parameter",
    ),
    NegativeControl.marked(
        "read-invalidated-view",
        """module Vela.FirstSlice.NegReadInvalidated;
public definition u8 BadInvalidRead() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    let inv = Span.Invalidate(s) in
    /*error*/Span.Read(inv, 0usize);
""",
        "type",
        "cannot prove Span has valid tag and read permission (Span.CanRead)",
    ),
    NegativeControl.marked(
        "overlapping-copyprefix",
        """module Vela.FirstSlice.NegOverlapCopy;
public definition Span<byte> BadOverlapCopy() =>
    let s = Span.AllocZeroed(64usize, 8usize) in
    let sub = Span.Slice(s, 2usize, 4usize) in
    /*error*/Span.CopyPrefix(s, sub, 4usize);
""",
        "type",
        "cannot prove Span.CopyPrefix source and destination extents are disjoint",
    ),
    NegativeControl.marked(
        "foreign-restore",
        """module Vela.FirstSlice.NegForeignRestore;
public definition Span<byte> BadRestore() =>
    let dst = Span.AllocZeroed(64usize, 8usize) in
    let other = Span.Slice(Span.AllocZeroed(64usize, 4usize), 0usize, 4usize) in
    /*error*/Span.Restore(dst, other);
""",
        "type",
        "Span.Restore requires a slice derived from its parent",
    ),
    NegativeControl.marked(
        "broken-restores-contract",
        """module Vela.FirstSlice.NegBrokenRestores;
public definition Span<byte> BadRestores(/*error*/ref Span<byte> dst)
    requires dst.CanRead
    requires dst.CanWrite
    requires dst.Length >= 8usize
=>
    Span.Slice(dst, 0usize, 4usize);
""",
        "type",
        "assertion could not be established",
    ),
    NegativeControl.marked(
        "restore-then-return-view",
        """module Vela.FirstSlice.NegRestoreThenReturnView;
public Span<byte> BadReturnRestoredView(ref Span<byte> dst)
    effects writes(dst)
    requires dst.CanRead && dst.CanWrite && dst.Length >= 8usize
{
    let roView = Span.ReadOnly(Span.Slice(dst, 0usize, 4usize));
    Span.Restore(ref dst, roView);
    /*error*/return roView;
}
""",
        "type",
        "cannot return a view borrowed from a span that was already restored",
    ),
    NegativeControl.marked(
        "capability-fabrication",
        """module Vela.FirstSlice.NegCapabilityFabrication;
public Span<byte> BadFabricate(usize addr)
{
    return /*error*/Span.AllocZeroed(addr, 8usize);
}
""",
        "type",
        "Span.AllocZeroed(base, length) is a specification constructor",
    ),
    NegativeControl.marked(
        "missing-write-effect",
        """module Vela.FirstSlice.NegMissingWriteEffect;
public Unit BadWriteEffect(ref Span<byte> dst, in Span<byte> pkt)
    /*error*/effects reads(dst), reads(pkt)
    requires dst.CanRead && dst.CanWrite && dst.Length >= 1usize
{
    dst[0usize] = 0x00u8;
}
""",
        "type",
        "callable mutates parameter 'dst' not declared in effects writes(...)",
    ),
    NegativeControl.marked(
        "wrong-expected-byte",
        """module Vela.FirstSlice.NegWrongByte;
theorem BadByte()
    ensures
        let s = Span.Write(Span.AllocZeroed(64usize, 8usize), 0usize, 0x10u8) in
        Span.Read(s, 0usize) == 0x99u8
proof {
    let s = Span.Write(Span.AllocZeroed(64usize, 8usize), 0usize, 0x10u8);
    /*error*/assert Span.Read(s, 0usize) == 0x99u8;
}
""",
        "type",
        "assertion could not be established",
    ),
    NegativeControl.marked(
        "stale-input-leak",
        """module Vela.FirstSlice.NegStaleLeak;
theorem BadStale()
    ensures
        let dirty = Span.Fill(Span.AllocZeroed(64usize, 8usize), 0usize, 8usize, 0xEEu8) in
        let cleaned = Span.Fill(dirty, 0usize, 8usize, 0x00u8) in
        Span.Read(cleaned, 6usize) == 0xEEu8
proof {
    let dirty = Span.Fill(Span.AllocZeroed(64usize, 8usize), 0usize, 8usize, 0xEEu8);
    let cleaned = Span.Fill(dirty, 0usize, 8usize, 0x00u8);
    /*error*/assert Span.Read(cleaned, 6usize) == 0xEEu8;
}
""",
        "type",
        "assertion could not be established",
    ),
    NegativeControl.marked(
        "loop-frame-overlap",
        """module Vela.FirstSlice.NegLoopFrameOverlap;
public theorem BadLoopFrame(ref Span<byte> s, usize bound, usize frameIdx)
    requires s.CanRead && s.CanWrite
    requires bound <= s.Length
    requires frameIdx < bound && frameIdx < s.Length
    ensures s[frameIdx] == old(s[frameIdx])
proof {
    foreach (let i in 0usize..bound)
        invariant i <= bound
        invariant s.CanRead && s.CanWrite && s.Length == old(s.Length)
        /*error*/invariant s[frameIdx] == old(s[frameIdx])
        decreases bound - i
    {
        s[i] = 0xAAu8;
    }
    assert s[frameIdx] == old(s[frameIdx]);
}
""",
        "type",
        "loop invariant could not be established on loop inductive step",
    ),
)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _inputs(root: Path) -> dict[str, str]:
    """Bind the local producer implementation, syntax, locks and encoding data."""
    paths = {EXAMPLE, "tools/run.py", "tools/pyproject.toml", "tools/uv.lock",
             "tools/opam/rocq.lock", "tools/opam/sail.lock",
             "tools/generated/dialect-table.json"}
    paths.update(f"tools/toolchain/parser/{name}" for name in vela_parser.SOURCES)
    paths.update(path.relative_to(root).as_posix()
                 for path in (root / "tools/toolchain").rglob("*.py"))
    return {name: file_sha256(root / name) for name in sorted(paths)}


def _revision(root: Path) -> str:
    revisions = corpus._git(root, "log", "-1", "--format=%H%x00")
    if len(revisions) != 1 or re.fullmatch(r"[0-9a-f]{40,64}", revisions[0]) is None:
        raise ValueError("first-slice producer revision is unavailable")
    return revisions[0]


def _execution_inputs(ccomp_path: Path | None) -> dict[str, object]:
    compiler = _resolve_ccomp(ccomp_path)
    loaded = env.load(toolchain=False)
    files = {"simulator": loaded.simulator, "profile": loaded.profile,
             "python": Path(sys.executable)}
    if compiler is not None:
        files["ccomp"] = compiler
    return {"files": {name: {"path": str(path.resolve()), "sha256": file_sha256(path)}
                      for name, path in files.items()},
            "compcert_available": compiler is not None, "python_version": sys.version}


def _receipt_directory(name: str, parent: Path, prefix: str) -> Path:
    path = Path(name)
    if (not path.is_absolute() or not path.is_dir() or path.is_symlink()
            or path.resolve().parent != parent.resolve()
            or re.fullmatch(re.escape(prefix) + r"[a-z0-9_]+", path.name) is None):
        raise ValueError("first-slice receipt directory is outside its local output scope")
    return path


def _artifacts(directory: Path) -> dict[str, str]:
    """Inventory retained outputs without including the self-referential journal."""
    files: dict[str, str] = {}
    size = 0
    for index, path in enumerate(directory.rglob("*"), 1):
        if index > ARTIFACT_ENTRIES:
            raise ValueError("first-slice output inventory exceeds its entry bound")
        if path.is_symlink():
            raise ValueError("first-slice output contains an alias")
        if path.is_file() and path != directory / "attempt.json":
            with path.open("rb") as stream:
                raw = stream.read(ARTIFACT_BYTES - size + 1)
            size += len(raw)
            if size > ARTIFACT_BYTES:
                raise ValueError("first-slice output inventory exceeds its byte bound")
            files[str(path)] = _sha256(raw)
    if not files:
        raise ValueError("first-slice output inventory is empty")
    return dict(sorted(files.items()))


def _reported_outputs(report: dict[str, object]) -> dict[str, str]:
    """Recheck the producer's explicit source and generated-output identities."""
    outputs: dict[str, str] = {}
    for field in ("source", "gallina", "lowered_c"):
        name, digest = report.get(field), report.get(f"{field}_sha256")
        if not isinstance(name, str) or not isinstance(digest, str):
            raise TypeError(f"first-slice {field} identity is missing or malformed")
        _require(file_sha256(Path(name)) == digest,
                 f"first-slice {field} changed after its producer observation")
        outputs[name] = digest
    return outputs


def _stream_identity(stdout: str, stderr: str) -> dict[str, object]:
    streams = {"stdout": stdout.encode("utf-8"), "stderr": stderr.encode("utf-8")}
    return {key: value for name, raw in streams.items()
            for key, value in ((f"{name}_bytes", len(raw)), (f"{name}_sha256", _sha256(raw)))}


def _retained_stdout(step: dict[str, object]) -> bytes:
    """Recover the explicitly bound stdout prefix without filtering process diagnostics."""
    raw = Path(str(step["log"])).read_bytes()
    stdout_bytes, stderr_bytes = step.get("stdout_bytes"), step.get("stderr_bytes")
    if (type(stdout_bytes) is not int or type(stderr_bytes) is not int
            or stdout_bytes < 0 or stderr_bytes < 0 or stdout_bytes + stderr_bytes != len(raw)):
        raise ValueError("first-slice receipt process stream lengths are malformed")
    stdout, stderr = raw[:stdout_bytes], raw[stdout_bytes:]
    if step.get("stdout_sha256") != _sha256(stdout) or step.get("stderr_sha256") != _sha256(stderr):
        raise ValueError("first-slice receipt process stream hashes changed")
    return stdout


def _simulator_transcript(said: str, returncode: int, *,
                          text: memoryview | None = None) -> tuple[str, int | None, list[str]]:
    """Require one unambiguous terminal verdict and validate each declared trace row."""
    terminals: list[str] = []
    instruction_order = -1
    for raw in said.splitlines():
        line = raw.rstrip()
        if line.lstrip().startswith(("SUCCESS", "FAILURE")):
            terminal = re.fullmatch(r"(?:SUCCESS|FAILURE: ([0-9]+)(?: \(0x([0-9a-fA-F]{8})\))?)", line)
            if terminal is None:
                raise ValueError("first-slice simulator terminal verdict is malformed")
            if terminal[2] is not None and int(terminal[2], 16) != int(terminal[1]):
                raise ValueError("first-slice simulator terminal decimal and hexadecimal codes disagree")
            terminals.append(line)
        parts = line.split()
        if not parts or parts[0] not in {"I", "X", "S", "C", "R", "W", "T"}:
            continue
        if terminals:
            raise ValueError("first-slice simulator commit record follows its terminal verdict")
        if not line.isascii() or trace.COMMIT_RE.fullmatch(line) is None:
            raise ValueError("first-slice simulator commit record is malformed")
        if parts[0] == "I":
            order = int(parts[1])
            if order != instruction_order + 1:
                raise ValueError("first-slice simulator retirement sequence is incomplete or out of order")
            instruction_order = order
            if text is not None:
                pc, word = int(parts[2], 16), int(parts[3], 16)
                at = pc - cd.asm.TEXT_BASE
                if order == 0 and at != 0:
                    raise ValueError(f"first-slice simulator initial PC {pc:#x} differs from image entry"
                                     f" {cd.asm.TEXT_BASE:#x}")
                if at < 0 or at % 4 or at + 4 > len(text) or struct.unpack_from("<I", text, at)[0] != word:
                    raise ValueError(f"first-slice simulator instruction {word:#010x} at PC {pc:#x}"
                                     " disagrees with the linked executable text")
        elif instruction_order < 0:
            raise ValueError("first-slice simulator effect precedes its first instruction")
        elif parts[0] in {"R", "W"}:
            width = int(parts[2])
            if width < 1 or len(parts[4]) != width * 2:
                raise ValueError("first-slice simulator memory record width differs from its value")
    if len(terminals) != 1 or "trap loop" in said or instruction_order < 0:
        raise ValueError("first-slice simulator transcript lacks an unambiguous completed execution")
    verdict, code, _ = cd.htif_verdict("\n".join(terminals), returncode)
    if verdict == "no-verdict":
        raise ValueError("first-slice simulator process contradicts its terminal verdict")
    return verdict, code, trace.normalize_commit(said.splitlines())


def _corrupted_proof(gallina: str) -> str:
    return gallina + (
        "\nDefinition vela_corrupted_check : @Corelib.Init.Logic.eq Corelib.Init.Datatypes.bool "
        "Corelib.Init.Datatypes.true Corelib.Init.Datatypes.false := "
        "@Corelib.Init.Logic.eq_refl Corelib.Init.Datatypes.bool Corelib.Init.Datatypes.true.\n"
    )


def _check_corruption_refusal(gallina: str, code: int, transcript: str) -> None:
    """Require a normal checker refusal at the deliberately false appended definition."""
    sites = re.findall(r'File "([^"\n]+)", line ([0-9]+), characters [0-9]+-[0-9]+:\s*Error:', transcript)
    if (code <= 0 or len(sites) != 1 or Path(sites[0][0]).name != "FirstSliceCorrupted.v"
            or sites[0][1] != str(gallina.count("\n") + 2) or transcript.count("Error:") != 1
            or "has type" not in transcript or "while it is expected to have type" not in transcript):
        raise ValueError("first-slice proof-corruption control did not reach its intended type refusal")


def _retained_steps(report: dict[str, object], directory: Path, artifacts: dict[str, object]) -> str:
    """Bind every declared process observation and the required local proof steps."""
    steps = report.get("steps")
    if not isinstance(steps, list) or not steps or len(steps) > ARTIFACT_ENTRIES:
        raise ValueError("first-slice receipt process coverage is missing or exceeds its bound")
    required = {
        "FirstSlice.compile.log": _opam(["rocq", "c", "-q", "-R", str(directory),
                                          "VelaFirstSlice", "FirstSlice.v"]),
        "FirstSlice.assumptions.log": _opam(["rocq", "c", "-q", "-R", str(directory),
                                              "VelaFirstSlice", "FirstSliceAssumptions.v"]),
        "FirstSlice.kernel.log": _opam(["rocqchk", "-R", str(directory), "VelaFirstSlice",
                                         "VelaFirstSlice.FirstSlice"]),
        "CapSmall.compile.log": _opam(["rocq", "c", "-q", "-R", str(directory),
                                        "VelaFirstSlice", "CapSmall.v"]),
        "CapLarge.compile.log": _opam(["rocq", "c", "-q", "-R", str(directory),
                                        "VelaFirstSlice", "CapLarge.v"]),
        "CapGate.kernel.log": _opam(["rocqchk", "-R", str(directory), "VelaFirstSlice",
                                      "VelaFirstSlice.CapSmall", "VelaFirstSlice.CapLarge"]),
        "FirstSliceCorrupted.compile.log": _opam(["rocq", "c", "-q", "-R", str(directory),
                                                   "VelaFirstSlice", "FirstSliceCorrupted.v"]),
    }
    covered: dict[str, bytes] = {}
    for step in steps:
        if not isinstance(step, dict):
            raise TypeError("first-slice receipt process observation is malformed")
        command, log = step.get("command"), step.get("log")
        native = "cwd" in step or "returncode" in step
        if native:
            working, code = step.get("cwd"), step.get("returncode")
            _require(not any(key in step for key in ("directory", "exit", "status")),
                     "first-slice receipt mixes process producer formats")
        else:
            working, code = step.get("directory"), step.get("exit")
            _require(step.get("status") == "passed" and step.get("expected_refusal", False) is False,
                     "first-slice receipt replay probe did not pass")
        refused = step.get("expected_refusal", False)
        if (not isinstance(command, list) or not command or len(command) > 128
                or any(not isinstance(argument, str) or not argument for argument in command)
                or type(code) is not int or type(refused) is not bool
                or working != str(directory) or not isinstance(log, str)
                or log not in artifacts or step.get("log_sha256") != artifacts[log]
                or Path(log).parent != directory):
            raise ValueError("first-slice receipt process observation is not bound to retained output")
        name = Path(log).name
        if refused != (name == "FirstSliceCorrupted.compile.log") or (code != 0) != refused:
            raise ValueError("first-slice receipt process verdict contradicts its declared coverage")
        if name in required:
            if not native or command != required[name]:
                raise ValueError("first-slice receipt proof command differs from its declared subject")
            if name in covered:
                raise ValueError("first-slice receipt repeats a required proof observation")
            covered[name] = _retained_stdout(step)
            if refused:
                _check_corruption_refusal((directory / "FirstSlice.v").read_text(encoding="utf-8"),
                                          code, Path(log).read_text(encoding="utf-8"))
    if covered.keys() != required.keys() or report.get("proof_corruption_refused") is not True:
        raise ValueError("first-slice receipt omits required local proof or corruption coverage")
    return covered["FirstSlice.assumptions.log"].decode("utf-8")


def _retained_controls(report: dict[str, object], directory: Path,
                       artifacts: dict[str, object]) -> None:
    """Require the declared capacity and semantic-refusal coverage without replay."""
    capacity = report.get("capacity_invariance")
    fields = {"small_capacity", "large_capacity", "obligation_count", "work_steps",
              "reduction_steps", "gallina_bytes", "kernel_checked"}
    if (not isinstance(capacity, dict) or capacity.keys() != fields
            or capacity.get("small_capacity") != "8usize"
            or capacity.get("large_capacity") != "1_000_000_000usize"
            or capacity.get("kernel_checked") is not True):
        raise ValueError("first-slice receipt capacity coverage is missing or malformed")
    for field in ("obligation_count", "work_steps", "reduction_steps", "gallina_bytes"):
        count = capacity.get(field)
        if type(count) is not int or count < (0 if field == "reduction_steps" else 1):
            raise ValueError("first-slice receipt capacity metrics are malformed")
    for stem in ("CapSmall", "CapLarge"):
        for extension in ("vela", "v", "vo"):
            if str(directory / f"{stem}.{extension}") not in artifacts:
                raise ValueError("first-slice receipt omits a required capacity proof artifact")
        literal = capacity["small_capacity" if stem == "CapSmall" else "large_capacity"]
        if (directory / f"{stem}.vela").read_bytes() != _capacity_fixture(str(literal)):
            raise ValueError("first-slice receipt capacity source differs from its declared subject")
        if len((directory / f"{stem}.v").read_bytes()) != capacity["gallina_bytes"]:
            raise ValueError("first-slice receipt capacity size differs from retained Gallina")
    controls = report.get("negative_controls")
    if (not isinstance(controls, list) or len(controls) != len(NEGATIVE_CONTROLS)
            or type(report.get("negative_controls_count")) is not int
            or report["negative_controls_count"] != len(NEGATIVE_CONTROLS)):
        raise ValueError("first-slice receipt semantic-refusal coverage is incomplete")
    expected = {control.name: control for control in NEGATIVE_CONTROLS}
    seen: set[str] = set()
    for row in controls:
        if not isinstance(row, dict) or not isinstance(row.get("name"), str):
            raise TypeError("first-slice receipt semantic-refusal observation is malformed")
        name = row["name"]
        control = expected.get(name)
        if (control is None or name in seen or row.get("parsed_surface") is not True
                or row.get("category") != control.expected_kind
                or not isinstance(row.get("message"), str)
                or control.expected_substring not in row["message"]):
            raise ValueError("first-slice receipt semantic-refusal subject or verdict changed")
        control.check_location(row.get("line"), row.get("column"))
        path = directory / "negative-controls" / f"{name}.vela"
        if str(path) not in artifacts or path.read_bytes() != control.source.encode("utf-8"):
            raise ValueError("first-slice receipt semantic-refusal source differs from its declared subject")
        seen.add(name)


def _retained_execution(report: dict[str, object], directory: Path,
                        artifacts: dict[str, object]) -> None:
    """Reconstruct retained simulator observations and bind optional compiler coverage."""
    execution, runs = report.get("execution_inputs"), report.get("purecap_cheri_runs")
    if not isinstance(execution, dict) or not isinstance(execution.get("files"), dict):
        raise TypeError("first-slice receipt execution identities are malformed")
    files = execution["files"]
    for key in ("simulator", "profile"):
        if not isinstance(files.get(key), dict) or not isinstance(files[key].get("path"), str):
            raise TypeError("first-slice receipt simulator or profile identity is missing")
    if not isinstance(runs, dict) or runs.keys() != {case[0] for case in PURECAP_CASES}:
        raise ValueError("first-slice receipt capability execution coverage is incomplete")
    with tempfile.TemporaryDirectory(prefix="image-bindings-", dir=directory.parent) as temporary:
        for mode, verdict, code in PURECAP_CASES:
            row = runs[mode]
            if not isinstance(row, dict) or not isinstance(row.get("process"), dict):
                raise TypeError("first-slice receipt capability process is missing or malformed")
            process = row["process"]
            elf, log = directory / f"purecap_{mode}.elf", directory / f"purecap_{mode}.sail.log"
            expected_command = [files["simulator"]["path"], "--config", files["profile"]["path"],
                                "--trace-commit", "--inst-limit", str(cd.INST_LIMIT),
                                "--terminal-log", str(directory / f"purecap_{mode}.term"), str(elf)]
            if (process.get("command") != expected_command or type(process.get("returncode")) is not int
                    or process["returncode"] < 0 or process.get("log") != str(log)
                    or str(log) not in artifacts or process.get("log_sha256") != artifacts[str(log)]
                    or str(elf) not in artifacts):
                raise ValueError("first-slice receipt capability process subject changed")
            stdout = _retained_stdout(process).decode("utf-8")
            raw = log.read_bytes()
            said = stdout + raw[len(stdout.encode("utf-8")):].decode("utf-8")
            retained_image = elf.read_bytes()
            control_text = _check_purecap_control_image(retained_image)
            observed_verdict, observed_code, records = _simulator_transcript(said, process["returncode"],
                                                                             text=control_text)
            regenerated = Path(temporary) / elf.name
            refused, image_bytes = cd.assemble(_purecap_cheri_asm_stream(mode), elf.stem, regenerated)
            if (refused or regenerated.read_bytes() != retained_image
                    or (observed_verdict, observed_code) != (verdict, code) or not records
                    or row.get("verdict") != verdict or type(row.get("code")) is not int or row["code"] != code
                    or type(row.get("records")) is not int or row["records"] != len(records)
                    or row.get("trace_digest") != trace.digest(records)
                    or row.get("cap_roundtrip") is not cd.cap_roundtrip(records)
                    or type(row.get("image_bytes")) is not int or row["image_bytes"] != image_bytes):
                raise ValueError("first-slice receipt capability image, trace or verdict changed")
    compiler = report.get("compcert_sail")
    available = execution.get("compcert_available")
    if (type(available) is not bool or not isinstance(compiler, dict)
            or compiler.get("available") is not available
            or ("ccomp" in files) is not available):
        raise ValueError("first-slice receipt CompCert availability contradicts execution identity")
    if not available:
        if compiler != {"available": False}:
            raise ValueError("first-slice receipt unavailable CompCert carries execution claims")
        return
    ccomp = files["ccomp"]
    clight, assembly = directory / "first_slice/first_slice.light.c", directory / "first_slice/first_slice.s"
    if (not isinstance(ccomp, dict) or compiler.get("ccomp_path") != ccomp.get("path")
            or compiler.get("ccomp_sha256") != ccomp.get("sha256")
            or compiler.get("clight_path") != str(clight) or str(clight) not in artifacts
            or compiler.get("clight_sha256") != artifacts[str(clight)] or str(assembly) not in artifacts
            or compiler.get("asm_sha256") != artifacts[str(assembly)]
            or type(compiler.get("asm_lines")) is not int
            or compiler["asm_lines"] != len(assembly.read_text(encoding="utf-8").splitlines())
            or type(compiler.get("interp_exit_code")) is not int or compiler["interp_exit_code"] != 0
            or compiler.get("sail_verdict") != "pass"
            or type(compiler.get("sail_records")) is not int or compiler["sail_records"] <= 0
            or not isinstance(compiler.get("sail_trace_digest"), str)
            or re.fullmatch(r"[0-9a-f]{16}", compiler["sail_trace_digest"]) is None
            or type(compiler.get("sail_cap_roundtrip")) is not bool):
        raise ValueError("first-slice receipt CompCert subjects or execution summary changed")
    controls = compiler.get("perturbed_controls")
    expected = [{"name": label, "check_id": check, "verdict": "fail", "target_code": check,
                 "interp_code": check} for check, label in PERTURBED_CASES]
    if (not isinstance(controls, list) or controls != expected
            or any(type(row.get(key)) is not int for row in controls
                   for key in ("check_id", "target_code", "interp_code"))):
        raise ValueError("first-slice receipt perturbed compiler coverage is incomplete")
    _retained_compiler(compiler, files, directory, artifacts)


def _retained_compiler(compiler: dict[str, object], files: dict[str, object], directory: Path,
                       artifacts: dict[str, object]) -> None:
    """Bind each compiler reading and target verdict to retained process subjects."""
    programs = compiler.get("programs")
    expected = {"first_slice": 0, **{label: check for check, label in PERTURBED_CASES}}
    if not isinstance(programs, list) or len(programs) != len(expected):
        raise ValueError("first-slice receipt compiler process coverage is incomplete")
    ccomp, simulator, profile = (cast("dict[str, object]", files[key])["path"]
                                for key in ("ccomp", "simulator", "profile"))
    command = [ccomp, "-fverifiedos-typed", "-dclight"]
    seen: set[str] = set()
    with tempfile.TemporaryDirectory(prefix="compiler-bindings-", dir=directory.parent) as temporary:
        for program in programs:
            if not isinstance(program, dict) or not isinstance(program.get("name"), str):
                raise TypeError("first-slice receipt compiler program is malformed")
            name = program["name"]
            if (name not in expected or name in seen or type(program.get("expect")) is not int
                    or program["expect"] != expected[name]):
                raise ValueError("first-slice receipt compiler program subject changed")
            seen.add(name)
            fresh, interpreted = directory / name, directory / f"{name}.interp"
            source, unit, interp_unit = directory / f"{name}.c", fresh / f"{name}.i", interpreted / f"{name}.i"
            assembly, elf = fresh / f"{name}.s", directory / f"{name}.elf"
            subjects = ((source, "source_sha256"), (unit, "preprocessed_sha256"),
                        (interp_unit, "preprocessed_sha256"))
            if any(str(path) not in artifacts or artifacts[str(path)] != program.get(field)
                   for path, field in subjects) or str(assembly) not in artifacts or str(elf) not in artifacts:
                raise ValueError("first-slice receipt compiler source or effective input changed")
            required = {
                str(fresh / f"{name}.preprocess.log"):
                    ([*command, "-E", source.name, "-o", str(unit)], str(directory)),
                str(fresh / f"{name}.compile.log"):
                    ([*command, "-S", unit.name, "-o", assembly.name], str(fresh)),
                str(interpreted / f"{name}.preprocess.log"):
                    ([*command, "-E", unit.name, "-o", str(interp_unit)], str(fresh)),
                str(interpreted / f"{name}.interpret.log"):
                    ([*command, "-interp", interp_unit.name], str(interpreted)),
                str(directory / f"{name}.sail.log"):
                    ([simulator, "--config", profile, "--trace-commit", "--inst-limit", str(cd.INST_LIMIT),
                      "--terminal-log", str(directory / f"{name}.term"), str(elf)], None),
            }
            processes = program.get("processes")
            if not isinstance(processes, list) or len(processes) != len(required):
                raise ValueError("first-slice receipt compiler process coverage is incomplete")
            observed: dict[str, str] = {}
            for process in processes:
                if not isinstance(process, dict) or not isinstance(process.get("log"), str):
                    raise TypeError("first-slice receipt compiler process is malformed")
                log = process["log"]
                if (log not in required or log in observed or process.get("command") != required[log][0]
                        or process.get("cwd") != required[log][1] or log not in artifacts
                        or process.get("log_sha256") != artifacts[log]
                        or type(process.get("returncode")) is not int or process["returncode"] < 0
                        or (not log.endswith(".sail.log") and process["returncode"] != 0)):
                    raise ValueError("first-slice receipt compiler process subject or verdict changed")
                stdout = _retained_stdout(process).decode("utf-8")
                observed[log] = stdout
                if log.endswith(".interpret.log"):
                    ended = cd._TERMINATED_RE.findall(stdout)
                    if len(ended) != 1 or int(ended[0]) != expected[name]:
                        raise ValueError("first-slice receipt interpreter transcript contradicts its verdict")
                elif log.endswith(".sail.log"):
                    said = Path(log).read_bytes().decode("utf-8")
                    verdict, code, records = _simulator_transcript(said, process["returncode"],
                                                                   text=_linked_text(elf.read_bytes()))
                    if ((verdict, code) != ("pass" if expected[name] == 0 else "fail", expected[name])
                            or not records):
                        raise ValueError("first-slice receipt compiler target transcript contradicts its verdict")
                    if name == "first_slice" and (compiler.get("sail_records") != len(records)
                            or compiler.get("sail_trace_digest") != trace.digest(records)
                            or compiler.get("sail_cap_roundtrip") is not cd.cap_roundtrip(records)):
                        raise ValueError("first-slice receipt compiler target summary changed")
            regenerated = Path(temporary) / elf.name
            refused, image_bytes = cd.assemble(assembly.read_text(encoding="utf-8"), name, regenerated)
            if (refused or regenerated.read_bytes() != elf.read_bytes()
                    or type(program.get("image_bytes")) is not int or program["image_bytes"] != image_bytes):
                raise ValueError("first-slice receipt compiler image differs from retained assembly")


def _lowering_provenance(checked: CheckedElaboration, generated: str, operations: list[dict[str, object]]) -> dict[str, object]:
    return {"schema": 1, "source_sha256": checked.source_sha256, "syntax_sha256": _sha256(checked.syntax),
            "gallina_sha256": _sha256(checked.gallina.encode()), "lowered_c_sha256": _sha256(generated.encode()),
            "integer_arithmetic_and_literals": operations}


def _reconstruct_lowering(root: Path) -> dict[str, object]:
    source = (root / EXAMPLE).read_bytes()
    with vela_parser.cached_build(root) as local:
        parsed = vela_parser.parse_source(local, source, surface=True)
    checked = vela_elaborate.elaborate(source, parsed)
    operations: list[dict[str, object]] = []
    generated, _ = lower_to_c(source, parsed, checked=checked, observations=operations)
    return _lowering_provenance(checked, generated, operations)


def _retained_proof(root: Path, report: dict[str, object], directory: Path,
                    artifacts: dict[str, object]) -> None:
    """Recheck retained declarations and assumption ledgers without native proof replay."""
    for field, path in (("source", root / EXAMPLE), ("gallina", directory / "FirstSlice.v"),
                         ("lowered_c", directory / "first_slice.c")):
        if report.get(field) != str(path):
            raise ValueError(f"first-slice receipt {field} names another subject")
    outputs = _reported_outputs(report)
    if any(artifacts.get(str(directory / name)) != outputs.get(str(directory / name))
           for name in ("FirstSlice.v", "first_slice.c")):
        raise ValueError("first-slice receipt generated identities differ from its output inventory")
    for name in ("FirstSlice.vo", "FirstSliceCorrupted.v", "FirstSliceAssumptions.v", "FirstSliceAssumptions.vo",
                 "FirstSlice.assumptions.log"):
        if str(directory / name) not in artifacts:
            raise ValueError("first-slice receipt omits a required retained proof artifact")
    gallina = (directory / "FirstSlice.v").read_text(encoding="utf-8")
    if (directory / "FirstSliceCorrupted.v").read_bytes() != _corrupted_proof(gallina).encode("utf-8"):
        raise ValueError("first-slice receipt corrupted proof differs from its declared subject")
    modules = re.findall(r"^Module ((?:Vela_|VelaEncoded_)[A-Za-z0-9_]+)\.$", gallina, flags=re.MULTILINE)
    exports = solver_ledger.math_exports(gallina)
    if modules != [gallina_module_name("Vela.FirstSlice")] or len(set(exports)) != len(exports):
        raise ValueError("first-slice receipt Gallina module or exports are malformed")
    for suffix in (*EXPECTED_LAWS, *EXPECTED_CONTRACT_OBLIGATIONS, *EXPECTED_SCENARIO_THEOREMS):
        if not any(name.endswith(f"_{suffix}") for name in exports):
            raise ValueError(f"first-slice receipt omits required local obligation '{suffix}'")
    expected_query = "From VelaFirstSlice Require Import FirstSlice.\n" + "".join(
        f"Print Assumptions FirstSlice.{modules[0]}.{name}.\n" for name in exports)
    if (directory / "FirstSliceAssumptions.v").read_text(encoding="utf-8") != expected_query:
        raise ValueError("first-slice receipt assumption query omits or changes an audited export")
    assumption_output = _retained_steps(report, directory, artifacts)
    trusted = solver_ledger.ledger(gallina)
    reported = solver_ledger.audit(assumption_output, len(exports), modules[0], trusted)
    inventory = report.get("inventory")
    assumptions = ("Closed under the global context (0 axioms)" if not trusted
                   else f"{len(trusted)} solver-trusted axioms; no other assumptions")
    if (type(report.get("assumption_exports_count")) is not int
            or report["assumption_exports_count"] != len(exports)
            or type(report.get("solver_trusted_count")) is not int
            or report["solver_trusted_count"] != len(trusted)
            or report.get("solver_trusted_axioms") != reported
            or report.get("accepted") is not (not trusted)
            or report.get("kernel_checked") is not (not trusted)
            or not isinstance(inventory, dict)
            or inventory.get("solver_trusted_obligations") != [entry.as_json() for entry in trusted]
            or inventory.get("global_assumptions") != assumptions):
        raise ValueError("first-slice receipt source-proof status contradicts its retained assumption ledger")


def _opam(arguments: list[str]) -> list[str]:
    return ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *arguments]


def _run(command: list[str], cwd: Path, log_path: Path,
         steps: list[dict[str, object]], *, timing: packet_trace.Recorder | None = None) -> str:
    started = time.monotonic_ns()
    child: dict[str, object] = {}
    if timing is None:
        completed = subprocess.run(command, cwd=cwd, capture_output=True, encoding="utf-8",
                                   errors="replace", timeout=TIMEOUT, check=False)
    else:
        phase, worker = packet_trace.PROOF_STEPS[log_path.name]
        with timing.span(phase), subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                encoding="utf-8", errors="replace") as process:
            child["observed_pid"] = process.pid
            with timing.span(worker, process.pid):
                try:
                    stdout, stderr = process.communicate(timeout=TIMEOUT)
                except BaseException:
                    process.kill()
                    process.communicate()
                    raise
        completed = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    elapsed_ns = time.monotonic_ns() - started
    combined = completed.stdout + completed.stderr
    log_path.write_text(combined, encoding="utf-8", newline="")
    steps.append({
        "command": command,
        "cwd": str(cwd),
        "returncode": completed.returncode,
        "elapsed_ns": elapsed_ns,
        **child,
        "timeout_seconds": TIMEOUT,
        "log": str(log_path),
        "log_sha256": file_sha256(log_path),
        **_stream_identity(completed.stdout, completed.stderr),
    })
    if completed.returncode != 0:
        raise ValueError(f"command failed ({completed.returncode}): {' '.join(command)}\n{combined[-600:]}")
    return completed.stdout


def _work_root(root: Path) -> Path:
    directory = env.lane_root(env.lane_of(root)) / "vela-first-slice"
    kind = env.filesystem(directory)
    if not kind or kind in env.CROSS_OS_FILESYSTEMS | env.VOLATILE_FILESYSTEMS:
        raise ValueError("Vela first-slice outputs require a persistent native filesystem")
    directory.mkdir(parents=True, exist_ok=True)
    return directory


def _capacity_fixture(capacity_literal: str) -> bytes:
    text = f"""module Vela.FirstSlice.CapGate;

public Span<byte> PrepareSliceHeader(ref Span<byte> dst)
    effects writes(dst)
    requires dst.CanRead
    requires dst.CanWrite
    requires dst.Length >= 8usize
    ensures dst.Length == old(dst.Length)
    ensures result.Length == 4usize
    ensures !result.CanWrite
{{
    foreach (let i in 0usize..dst.Length)
        invariant i <= dst.Length
        invariant dst.CanRead && dst.CanWrite && dst.Base == old(dst.Base) && dst.Length == old(dst.Length)
        decreases dst.Length - i
    {{
        dst[i] = 0x00u8;
    }}
    dst[0usize] = 0x56u8;
    dst[3usize] = 0x01u8;
    let roView = Span.ReadOnly(Span.Slice(dst, 0usize, 4usize));
    return roView;
}}

theorem CapacityLaw(ref Span<byte> s)
    requires s.CanRead && s.CanWrite && s.Length == {capacity_literal}
    ensures (s.Length == {capacity_literal}
        && s[0usize] == 0x56u8
        && s[3usize] == 0x01u8) == true
proof {{
    let roView = PrepareSliceHeader(ref s);
    assert (s.Length == {capacity_literal}
        && roView.Length == 4usize
        && !roView.CanWrite
        && s[0usize] == 0x56u8
        && s[3usize] == 0x01u8) == true;
}}
"""
    return text.encode("utf-8")


def build_foundation_inventory() -> dict[str, object]:
    """Return the checked law, assumption, and blocking-dependency inventory."""
    return {
        "carrier_representation": (
            "vela_Span (vela_ByteStore = nat -> vela_u8, Base, Length, Tag, PermRead, PermWrite)"
        ),
        "carrier_laws": list(EXPECTED_LAWS),
        "validator_contract_obligations": [
            name.removeprefix("PrepareAndValidatePacket_") for name in EXPECTED_CONTRACT_OBLIGATIONS
        ],
        "scenario_theorems": list(EXPECTED_SCENARIO_THEOREMS),
        "global_assumptions": "exactly the solver-trust ledger recorded at qualification",
        "blocking_dependencies": {
            "Q35b / Q35o / Q35p": (
                "Canonical Sail machine term rv64d.v refuses Rocq 9.3.0 compilation at "
                "__WriteRAM_Meta / write_tag_bool (Prompt_monad.monad bool ?E0 vs outcome M unit; "
                "docs/assurance/canonical-machine-term.md#9-the-whole-term-compile-refusal) and "
                "rocq-sail-stdpp is not carried in the shared proof switch (F-778)."
            ),
            "Q35c / Q35m / Q35k / Q35l": (
                "Machine-logic dependency chain (Islaris / Lithium / Katamaran) reached its bounded "
                "refusal endpoint at Rocq 9.3.0 (Q35m, F-785, F-786), leaving Q35k (unary safety "
                "over rv64d.v) and Q35l (byte-instance laws over rv64d.v) blocked and byte-instance / "
                "scoped-resources uncommissioned in docs/hardware/cheri-foundation-map.md."
            ),
            "Q2b": (
                "tools/bedrock2-lowering/DescriptorCheck.v targets BasicC64Semantics (flat byte-array "
                "read-only check without destination initialization, byte copy or CHERI capability tags)."
            ),
            "Q35d / M1.2g / Q35j": (
                "Mechanized Sail-to-Clight/CompCert refinement and the stock-to-contained Clight "
                "bridge remain open."
            ),
        },
        "unrun_or_pending_checks": [
            "Whole-term rv64d.v Rocq 9.3.0 compilation and Q35l byte-instance refinement proof over rv64d.v (blocked by Q35o / Q35p / Q35m)",
            "Mechanized Sail-to-Clight/CompCert refinement theorem for first_slice.c (owned by Q35d / M1.2g)",
            "User-managed Host CI and Guest CI runs (deferred to user handoff)",
        ],
    }


def _extract_decl_map(parsed: object) -> dict[str, dict[str, object]]:
    envelope = cast("dict[str, object]", parsed)
    ast_root = cast("dict[str, object]", envelope.get("ast", envelope))
    decls = cast("list[dict[str, object]]", ast_root.get("declarations", []))
    found: dict[str, dict[str, object]] = {}
    for decl in decls:
        name_node = decl.get("name")
        if isinstance(name_node, dict) and isinstance(name_node.get("text"), str):
            found[str(name_node["text"])] = decl
    return found


def _node_text(node: object) -> str:
    if isinstance(node, str):
        return node
    if isinstance(node, dict):
        if isinstance(node.get("text"), str):
            return str(node["text"])
        if isinstance(node.get("name"), dict):
            return _node_text(node["name"])
    raise ValueError(f"expected named AST node, got {node!r}")


def _type_info(type_node: object) -> tuple[str | None, str]:
    if not isinstance(type_node, dict):
        raise TypeError(f"expected type AST node, got {type_node!r}")
    kind = str(type_node.get("kind", ""))
    if kind == "modified_type":
        mod = _node_text(type_node.get("modifier"))
        inner_node = type_node.get("type") if type_node.get("type") is not None else type_node.get("value")
        _, inner = _type_info(inner_node)
        return mod, inner
    if kind == "type":
        return None, _node_text(type_node.get("name"))
    raise ValueError(f"unsupported type AST node kind {kind!r}")


def _c_scalar_type(type_name: str) -> str:
    if type_name in ("u8", "byte"):
        return "unsigned char"
    if type_name == "usize":
        return "unsigned long"
    if type_name in ("bool", "ValidationError"):
        return "int"
    if type_name == "Span":
        return "struct vela_span_byte"
    if type_name == "ValidatedPacket":
        return "struct vela_ValidatedPacket"
    if type_name == "Result":
        return "struct vela_Result_ValidatedPacket_ValidationError"
    if type_name in ("unit", "Unit"):
        return "void"
    raise ValueError(f"unsupported C lowering type {type_name!r}")


def _unwrap_arg(node: object) -> dict[str, object]:
    if not isinstance(node, dict):
        raise TypeError(f"expected AST argument node, got {node!r}")
    if node.get("kind") == "argument":
        val = node.get("value")
        if isinstance(val, dict):
            return cast("dict[str, object]", val)
    return cast("dict[str, object]", node)


def _lower_union_to_c(decl: dict[str, object]) -> tuple[str, dict[str, int]]:
    uname = _node_text(decl.get("name"))
    ctors = cast("list[dict[str, object]]", decl.get("constructors", []))
    if not ctors:
        raise ValueError(f"union {uname} missing AST constructors")
    lines: list[str] = []
    ctor_map: dict[str, int] = {}
    for idx, ctor in enumerate(ctors, start=1):
        cname = _node_text(ctor.get("name"))
        ctor_map[cname] = idx
        lines.append(f"#define VOS_ERR_{cname} {idx}")
    return "\n".join(lines), ctor_map


def _lower_record_to_c(decl: dict[str, object]) -> tuple[str, list[tuple[str, str]]]:
    rname = _node_text(decl.get("name"))
    params = cast("list[dict[str, object]]", decl.get("parameters", []))
    if not params:
        raise ValueError(f"record {rname} missing AST parameters")
    lines = [f"struct vela_{rname} {{"]
    fields: list[tuple[str, str]] = []
    for param in params:
        pname = _node_text(param.get("name"))
        _, ptype = _type_info(param.get("type"))
        fields.append((pname, ptype))
        lines.append(f"    {_c_scalar_type(ptype)} {pname};")
    lines.append("};")
    return "\n".join(lines), fields


def _is_span_call(expr: dict[str, object], *methods: str) -> str | None:
    if expr.get("kind") != "call":
        return None
    callee = expr.get("callee")
    if not isinstance(callee, dict) or callee.get("kind") != "member":
        return None
    recv = callee.get("value")
    if not isinstance(recv, dict) or recv.get("kind") != "name" or _node_text(recv) != "Span":
        return None
    mname = _node_text(callee.get("name"))
    if not methods or mname in methods:
        return mname
    return None


def _lower_function_to_c(
    decl: dict[str, object],
    ctor_map: dict[str, int],
    record_fields: dict[str, list[tuple[str, str]]],
    literal_type: Callable[[dict[str, object]], str],
    function_results: dict[str, str],
    resolve_call: Callable[[dict[str, object]], str],
    integer_operation: Callable[[dict[str, object]], tuple[str, str]],
    observations: list[dict[str, object]] | None = None,
) -> str:
    fname = _node_text(decl.get("name"))
    params = cast("list[dict[str, object]]", decl.get("parameters", []))
    _, ret_type = _type_info(decl.get("result"))
    body = decl.get("body")
    if not isinstance(body, dict) or body.get("kind") != "block":
        raise ValueError(f"function {fname} missing executable AST block body")

    ptr_spans: set[str] = set()
    c_params: list[str] = []
    if ret_type == "Span":
        c_ret = "void"
        c_params.extend(["struct vela_span_byte *out", "unsigned char *backing"])
    elif ret_type == "Result":
        c_ret = "void"
        c_params.append("struct vela_Result_ValidatedPacket_ValidationError *out")
    elif ret_type in record_fields:
        c_ret = "void"
        c_params.append(f"struct vela_{ret_type} *out")
    else:
        c_ret = _c_scalar_type(ret_type)

    for param in params:
        pname = _node_text(param.get("name"))
        _, ptype = _type_info(param.get("type"))
        if ptype == "Span":
            ptr_spans.add(pname)
            c_params.append(f"struct vela_span_byte *{pname}")
        else:
            c_params.append(f"{_c_scalar_type(ptype)} {pname}")

    local_spans: list[str] = []
    local_scalars: list[tuple[str, str]] = []
    slice_parents: dict[str, str] = {}

    def add_local_span(vname: str) -> None:
        if vname not in local_spans and vname not in ptr_spans:
            local_spans.append(vname)

    def add_local_scalar(c_ty: str, vname: str) -> None:
        if all(existing != vname for _, existing in local_scalars):
            local_scalars.append((c_ty, vname))

    def infer_local_type(stmt: dict[str, object]) -> tuple[bool, str]:
        ty_node = stmt.get("type")
        if isinstance(ty_node, dict):
            _, tname = _type_info(ty_node)
            return (tname == "Span"), _c_scalar_type(tname)
        val = cast("dict[str, object]", stmt.get("value", {}))
        if _is_span_call(val) is not None:
            return True, "struct vela_span_byte"
        vkind = str(val.get("kind", ""))
        if vkind == "nat":
            return False, _c_scalar_type(literal_type(val))
        if vkind == "index":
            return False, "unsigned char"
        if vkind == "call":
            callee = val.get("callee")
            if (
                isinstance(callee, dict)
                and callee.get("kind") == "member"
                and _node_text(callee.get("value")) == "usize"
                and _node_text(callee.get("name")) == "From"
            ):
                return False, "unsigned long"
            if isinstance(callee, dict) and callee.get("kind") == "name":
                return False, _c_scalar_type(function_results[resolve_call(val)])
        if vkind == "unary" and _node_text(val.get("operator")) == "~":
            return False, _c_scalar_type(integer_operation(val)[1])
        if vkind == "binary" and _node_text(val.get("operator")) in {"+", "-", "*", "/", "%", "&", "|", "^"}:
            return False, _c_scalar_type(integer_operation(val)[1])
        raise ValueError(f"cannot infer local C type for statement in {fname}: {stmt!r}")

    def collect_locals(stmts: list[dict[str, object]]) -> None:
        for st in stmts:
            skind = str(st.get("kind", ""))
            if skind in ("var", "let"):
                vname = _node_text(st.get("name"))
                is_span, c_ty = infer_local_type(st)
                if is_span:
                    add_local_span(vname)
                    val = cast("dict[str, object]", st.get("value", {}))
                    if _is_span_call(val, "Slice") == "Slice":
                        args = [_unwrap_arg(a) for a in cast("list[object]", val.get("arguments", []))]
                        if args and args[0].get("kind") == "name":
                            slice_parents[vname] = _node_text(args[0])
                else:
                    add_local_scalar(c_ty, vname)
            elif skind == "foreach":
                iname = _node_text(st.get("name"))
                add_local_scalar("unsigned long", iname)
                fbody = st.get("body")
                if isinstance(fbody, dict):
                    collect_locals(cast("list[dict[str, object]]", fbody.get("statements", [])))
            elif skind == "if":
                then_b = st.get("then")
                if isinstance(then_b, dict):
                    collect_locals(cast("list[dict[str, object]]", then_b.get("statements", [])))
                else_b = st.get("else")
                if isinstance(else_b, dict):
                    collect_locals(cast("list[dict[str, object]]", else_b.get("statements", [])))

    body_stmts = cast("list[dict[str, object]]", body.get("statements", []))
    collect_locals(body_stmts)

    def span_ptr_expr(expr: dict[str, object]) -> str:
        node = _unwrap_arg(expr)
        if node.get("kind") == "unary" and _node_text(node.get("operator")) in ("ref", "in"):
            node = _unwrap_arg(node.get("value"))
        if node.get("kind") == "name":
            vname = _node_text(node)
            if vname in ptr_spans:
                return vname
            if vname in local_spans:
                return f"&{vname}"
        raise ValueError(f"expected Span variable in {fname}, got {expr!r}")

    scalar_types = {**{_node_text(p.get("name")): _c_scalar_type(_type_info(p.get("type"))[1]) for p in params},
                    **{name: c_ty for c_ty, name in local_scalars}}
    used_names = {*scalar_types, *local_spans, *ptr_spans, *function_results, "out", "backing"}
    temp_index = 0

    def temp(c_ty: str) -> str:
        nonlocal temp_index
        while True:
            name = f"vela_eval_{temp_index}"
            temp_index += 1
            if name not in used_names:
                used_names.add(name)
                add_local_scalar(c_ty, name)
                return name

    def scalar_type(node: dict[str, object]) -> str:
        kind = node["kind"]
        if kind == "name":
            return "int" if _node_text(node) in ctor_map else scalar_types[_node_text(node)]
        if kind == "nat":
            return _c_scalar_type(literal_type(node))
        if kind == "bool":
            return "int"
        if kind == "index":
            return "unsigned char"
        if kind == "member":
            return "int" if _node_text(node["name"]) == "Tag" else "unsigned long"
        if kind == "unary":
            return "int" if _node_text(node["operator"]) == "!" else scalar_type(_unwrap_arg(node["value"]))
        if kind == "binary":
            if _node_text(node["operator"]) in ("==", "!=", "<", "<=", ">", ">=", "&&", "||"):
                return "int"
            return _c_scalar_type(integer_operation(node)[1])
        if kind == "call":
            callee = _unwrap_arg(node["callee"])
            if callee.get("kind") == "member":
                return "int" if _is_span_call(node, "Disjoint") is not None else "unsigned long"
            name = _node_text(callee)
            return "int" if name in ctor_map else _c_scalar_type(function_results[resolve_call(node)])
        raise ValueError(f"unsupported scalar argument {node!r} in {fname}")

    def ordered(nodes: list[dict[str, object]], prefix: list[str]) -> list[str]:
        # Span arguments denote stable addresses. Scalar arguments can read or change the referenced storage.
        values = []
        for node in nodes:
            if ((node["kind"] == "unary" and _node_text(node["operator"]) in ("in", "ref"))
                or (node["kind"] == "name" and (_node_text(node) in ptr_spans or _node_text(node) in local_spans))):
                values.append(span_ptr_expr(node))
                continue
            value = lower_expr(node, prefix)
            if len(nodes) > 1 and node["kind"] not in ("bool", "nat", "name"):
                saved = temp(scalar_type(node))
                prefix.append(f"{saved} = {value};")
                value = saved
            values.append(value)
        return values

    def observed(node: dict[str, object], operation: str, width: str, expression: str) -> str:
        if observations is not None:
            observations.append({"declaration": fname, "span": node["span"], "kind": node["kind"],
                                 "operation": operation, "width": width, "c_expression": expression})
        return expression

    def lower_expr(expr: object, prefix: list[str]) -> str:
        node = _unwrap_arg(expr)
        ekind = str(node.get("kind", ""))
        if ekind == "nat":
            width = literal_type(node)
            digits = cast("str", node["value"]).replace("_", "")
            # C treats leading zeros as octal, while Vela uses decimal.
            magnitude = digits if digits.lower().startswith("0x") else str(_parse_numeric_magnitude(digits))
            return observed(node, "literal", width, magnitude + ("UL" if width == "usize" else "U"))
        if ekind == "bool":
            return "1" if node.get("value") is True else "0"
        if ekind == "name":
            vname = _node_text(node)
            if vname in ctor_map:
                return f"VOS_ERR_{vname}"
            return vname
        if ekind == "unary":
            op = _node_text(node.get("operator"))
            if op in ("ref", "in"):
                return span_ptr_expr(node)
            if op == "~":
                checked_op, width = integer_operation(node)
                c_type = _c_scalar_type(width)
                promoted = "unsigned int" if c_type == "unsigned char" else c_type
                operand = lower_expr(node["value"], prefix)
                return observed(node, checked_op, width, f"({c_type})({checked_op}({promoted})({operand}))")
            return f"{op}{lower_expr(node.get('value'), prefix)}"
        if ekind == "member":
            mname = _node_text(node.get("name"))
            rname = _node_text(node.get("value"))
            c_field = {"Length": "length", "Base": "base", "Tag": "tag"}.get(mname)
            if c_field is None:
                raise ValueError(f"unsupported member {mname!r} in {fname}")
            return f"{rname}->{c_field}" if rname in ptr_spans else f"{rname}.{c_field}"
        if ekind == "index":
            s_ptr = span_ptr_expr(cast("dict[str, object]", node.get("value")))
            idx_c = lower_expr(node.get("index"), prefix)
            return f"vela_span_read({s_ptr}, {idx_c})"
        if ekind == "binary":
            op = _node_text(node.get("operator"))
            if op in ("&&", "||"):
                left = lower_expr(node["left"], prefix)
                guarded: list[str] = []
                right = lower_expr(node["right"], guarded)
                if not guarded:
                    return f"({left} {op} {right})"
                result = temp("int")
                prefix.append(f"{result} = {left};")
                guard = result if op == "&&" else f"!{result}"
                prefix.append(f"if ({guard}) {{")
                prefix.extend(f"    {line}" for line in guarded)
                prefix.extend((f"    {result} = {right};", "}"))
                return result
            lhs, rhs = ordered([_unwrap_arg(node["left"]), _unwrap_arg(node["right"])], prefix)
            if op in {"&", "|", "^"}:
                bit_op, width = integer_operation(node)
                c_type = _c_scalar_type(width)
                promoted = "unsigned int" if c_type == "unsigned char" else c_type
                expression = f"({c_type})(({promoted}){lhs} {bit_op} ({promoted}){rhs})"
                return observed(node, bit_op, width, expression)
            if op in {"+", "-", "*", "/", "%"}:
                checked_op, width = integer_operation(node)
                return observed(node, checked_op, width, f"({lhs} {checked_op} {rhs})")
            return f"({lhs} {op} {rhs})"
        if ekind == "call":
            callee = cast("dict[str, object]", node.get("callee", {}))
            args = [_unwrap_arg(a) for a in cast("list[object]", node.get("arguments", []))]
            if callee.get("kind") == "member":
                rname = _node_text(callee.get("value"))
                mname = _node_text(callee.get("name"))
                if rname == "Span" and mname == "Disjoint":
                    return f"vela_span_disjoint({span_ptr_expr(args[0])}, {span_ptr_expr(args[1])})"
                if rname == "usize" and mname == "From":
                    return f"(unsigned long){lower_expr(args[0], prefix)}"
            if callee.get("kind") == "name":
                cname = _node_text(callee)
                if cname in ctor_map:
                    return f"VOS_ERR_{cname}"
                cname = resolve_call(node)
                c_args = ordered(args, prefix)
                return f"{cname}({', '.join(c_args)})"
        raise ValueError(f"unsupported expression in {fname}: {node!r}")

    def lower_span_init(dst_ptr: str, expr: dict[str, object], prefix: list[str]) -> list[str]:
        mname = _is_span_call(expr)
        args = [_unwrap_arg(a) for a in cast("list[object]", expr.get("arguments", []))]
        if mname == "AllocZeroed":
            return [f"vela_span_alloc_zeroed({dst_ptr}, backing, {', '.join(ordered(args, prefix))});"]
        if mname == "Slice":
            return [f"vela_span_slice({dst_ptr}, {', '.join(ordered(args, prefix))});"]
        if mname in ("Invalidate", "ReadOnly"):
            c_fn = "vela_span_invalidate" if mname == "Invalidate" else "vela_span_readonly"
            inner = args[0]
            if _is_span_call(inner) is not None:
                return [*lower_span_init(dst_ptr, inner, prefix), f"{c_fn}({dst_ptr}, {dst_ptr});"]
            return [f"{c_fn}({dst_ptr}, {span_ptr_expr(inner)});"]
        raise ValueError(f"unsupported Span initializer {mname!r} in {fname}")

    def compound_rhs(st: dict[str, object], read: str, prefix: list[str]) -> str:
        op, width = integer_operation(st)
        old = temp(_c_scalar_type(width))
        prefix.append(f"{old} = {read};")
        expression = f"({old} {op} {lower_expr(st['value'], prefix)})"
        return observed(st, op, width, expression)

    def lower_stmts(stmts: list[dict[str, object]], indent: str) -> list[str]:
        out_lines: list[str] = []
        for st in stmts:
            skind = str(st.get("kind", ""))
            if skind in {"assert", "proof", "calc"}:
                continue
            prefix: list[str] = []
            first_line = len(out_lines)
            if skind in ("var", "let"):
                vname = _node_text(st.get("name"))
                val = cast("dict[str, object]", st.get("value", {}))
                if vname in local_spans:
                    out_lines.extend(f"{indent}{line}" for line in lower_span_init(f"&{vname}", val, prefix))
                else:
                    out_lines.append(f"{indent}{vname} = {lower_expr(val, prefix)};")
            elif skind == "assignment":
                target = cast("dict[str, object]", st.get("target", {}))
                val = cast("dict[str, object]", st.get("value", {}))
                compound = _node_text(st["operator"]) != "="
                if target.get("kind") == "index":
                    s_ptr = span_ptr_expr(cast("dict[str, object]", target.get("value")))
                    if compound:
                        idx_c = temp("unsigned long")
                        index_value = lower_expr(target["index"], prefix)
                        prefix.append(f"{idx_c} = {index_value};")
                        rhs = compound_rhs(st, f"vela_span_read({s_ptr}, {idx_c})", prefix)
                    else:
                        idx_c, rhs = ordered([_unwrap_arg(target["index"]), val], prefix)
                    out_lines.append(f"{indent}vela_span_write({s_ptr}, {s_ptr}, {idx_c}, {rhs});")
                elif target.get("kind") == "name":
                    tname = _node_text(target)
                    rhs = compound_rhs(st, tname, prefix) if compound else lower_expr(val, prefix)
                    out_lines.append(f"{indent}{tname} = {rhs};")
                else:
                    raise ValueError(f"unsupported assignment target in {fname}: {target!r}")
            elif skind == "expression_statement":
                val = cast("dict[str, object]", st.get("value", {}))
                mname = _is_span_call(val)
                args = [_unwrap_arg(a) for a in cast("list[object]", val.get("arguments", []))]
                if mname == "Fill":
                    s_ptr = span_ptr_expr(args[0])
                    scalars = ", ".join(ordered(args[1:], prefix))
                    out_lines.append(f"{indent}vela_span_fill({s_ptr}, {s_ptr}, {scalars});")
                elif mname == "CopyPrefix":
                    d_ptr = span_ptr_expr(args[0])
                    s_ptr = span_ptr_expr(args[1])
                    out_lines.append(f"{indent}vela_span_copy_prefix({d_ptr}, {d_ptr}, {s_ptr}, {lower_expr(args[2], prefix)});")
                    target_node = _unwrap_arg(args[0])
                    if target_node.get("kind") == "unary" and _node_text(target_node.get("operator")) in ("ref", "in"):
                        target_node = _unwrap_arg(target_node.get("value"))
                    if target_node.get("kind") == "name":
                        view_nm = _node_text(target_node)
                        if view_nm in slice_parents:
                            parent_nm = slice_parents[view_nm]
                            p_ptr = parent_nm if parent_nm in ptr_spans else f"&{parent_nm}"
                            out_lines.append(f"{indent}vela_span_restore({p_ptr}, {p_ptr}, {d_ptr});")
                elif mname == "Restore":
                    p_ptr = span_ptr_expr(args[0])
                    v_ptr = span_ptr_expr(args[1])
                    out_lines.append(f"{indent}vela_span_restore({p_ptr}, {p_ptr}, {v_ptr});")
                else:
                    out_lines.append(f"{indent}{lower_expr(val, prefix)};")
            elif skind == "foreach":
                iname = _node_text(st.get("name"))
                rng = cast("dict[str, object]", st.get("range", {}))
                first, last = _unwrap_arg(rng["start"]), _unwrap_arg(rng["end"])
                start_c = lower_expr(first, prefix)
                if first["kind"] != "nat":
                    saved = temp("unsigned long")
                    prefix.append(f"{saved} = {start_c};")
                    start_c = saved
                end_c = lower_expr(last, prefix)
                if last["kind"] != "nat":
                    saved = temp("unsigned long")
                    prefix.append(f"{saved} = {end_c};")
                    end_c = saved
                fbody = cast("dict[str, object]", st.get("body", {}))
                out_lines.append(f"{indent}for ({iname} = {start_c}; {iname} < {end_c}; {iname}++) {{")
                out_lines.extend(lower_stmts(cast("list[dict[str, object]]", fbody.get("statements", [])), indent + "    "))
                out_lines.append(f"{indent}}}")
            elif skind == "if":
                cond_c = lower_expr(st.get("condition"), prefix)
                then_b = cast("dict[str, object]", st.get("then", {}))
                out_lines.append(f"{indent}if ({cond_c}) {{")
                out_lines.extend(lower_stmts(cast("list[dict[str, object]]", then_b.get("statements", [])), indent + "    "))
                else_b = st.get("else")
                if isinstance(else_b, dict):
                    out_lines.append(f"{indent}}} else {{")
                    out_lines.extend(lower_stmts(cast("list[dict[str, object]]", else_b.get("statements", [])), indent + "    "))
                out_lines.append(f"{indent}}}")
            elif skind == "return":
                raw_val = st.get("value")
                if raw_val is None:
                    out_lines.append(f"{indent}return;")
                    continue
                val = _unwrap_arg(raw_val)
                if ret_type == "Span":
                    out_lines.append(f"{indent}vela_span_copy_meta(out, {span_ptr_expr(val)});")
                    out_lines.append(f"{indent}return;")
                elif ret_type == "Result":
                    callee = cast("dict[str, object]", val.get("callee", {}))
                    cname = _node_text(callee)
                    r_args = [_unwrap_arg(a) for a in cast("list[object]", val.get("arguments", []))]
                    if cname == "Err" and len(r_args) == 1:
                        out_lines.append(f"{indent}out->is_ok = 0;")
                        out_lines.append(f"{indent}out->err = {lower_expr(r_args[0], prefix)};")
                        out_lines.append(f"{indent}out->ok.CopiedBytes = 0UL;")
                        out_lines.append(f"{indent}vela_span_invalidate(&out->ok.PayloadView, dst);")
                        out_lines.append(f"{indent}return;")
                    elif cname == "Ok" and len(r_args) == 1:
                        ok_inner = r_args[0]
                        ok_args = [_unwrap_arg(a) for a in cast("list[object]", ok_inner.get("arguments", []))]
                        fields = record_fields["ValidatedPacket"]
                        if len(ok_args) != len(fields):
                            raise ValueError(f"ValidatedPacket in {fname} expected {len(fields)} fields, got {len(ok_args)}")
                        out_lines.append(f"{indent}out->is_ok = 1;")
                        out_lines.append(f"{indent}out->err = 0;")
                        for (f_name, f_type), arg_val in zip(fields, ok_args, strict=True):
                            if f_type == "Span":
                                out_lines.append(f"{indent}vela_span_copy_meta(&out->ok.{f_name}, {span_ptr_expr(arg_val)});")
                            else:
                                out_lines.append(f"{indent}out->ok.{f_name} = {lower_expr(arg_val, prefix)};")
                        out_lines.append(f"{indent}return;")
                    else:
                        raise ValueError(f"unsupported Result return in {fname}: {val!r}")
                elif ret_type in record_fields:
                    fields = record_fields[ret_type]
                    args = [_unwrap_arg(a) for a in cast("list[object]", val.get("arguments", []))]
                    if len(args) != len(fields):
                        raise ValueError(f"record return in {fname} expected {len(fields)} fields, got {len(args)}")
                    for (f_name, f_type), arg_val in zip(fields, args, strict=True):
                        if f_type == "Span":
                            out_lines.append(f"{indent}vela_span_copy_meta(&out->{f_name}, {span_ptr_expr(arg_val)});")
                        else:
                            out_lines.append(f"{indent}out->{f_name} = {lower_expr(arg_val, prefix)};")
                    out_lines.append(f"{indent}return;")
                else:
                    out_lines.append(f"{indent}return {lower_expr(val, prefix)};")
            else:
                raise ValueError(f"unsupported statement kind {skind!r} in {fname}")
            out_lines[first_line:first_line] = [f"{indent}{line}" for line in prefix]
        return out_lines

    param_sig = ",\n    ".join(c_params) if c_params else "void"
    header = f"static {c_ret} {fname}(\n    {param_sig})\n{{"
    stmt_lines = lower_stmts(body_stmts, "    ")
    decl_lines = [
        *(f"    struct vela_span_byte {s_name};" for s_name in local_spans),
        *(f"    {c_ty} {v_name};" for c_ty, v_name in local_scalars),
    ]
    all_body = [*decl_lines, *([""] if decl_lines and stmt_lines else []), *stmt_lines]
    return "\n".join([header, *all_body, "}"])


def lower_to_c(
    source: bytes, parsed: object, *, perturb_check: int = 0, checked: CheckedElaboration | None = None,
    observations: list[dict[str, object]] | None = None,
) -> tuple[str, int]:
    """Lower the executable subset of `first_slice.vela` from its checked AST to C.

    Verifies that the parsed AST carries the expected executable type and callable
    declarations (`ValidationError`, `ValidatedPacket`, `WritePacket8`,
    `CopyPacketToDst`, `ComputePacketChecksum`, `PrepareAndValidatePacket`), the
    carrier laws, and the seven scenario theorems before lowering the
    executable union, record, and function AST nodes into a self-contained C
    translation unit in the `verifiedos-scalar-source-v1` subset.
    """
    if checked is None:
        checked = vela_elaborate.elaborate(source, parsed)
    elif checked.source_sha256 != _sha256(source) or checked.syntax != CheckedElaboration.encode_syntax(parsed):
        raise ValueError("packet elaboration belongs to different source or syntax")
    decl_map = _extract_decl_map(json.loads(checked.syntax))
    required_callables = (
        ("ValidationError", "union"),
        ("ValidatedPacket", "record"),
        ("WritePacket8", "function"),
        ("CopyPacketToDst", "function"),
        ("ComputePacketChecksum", "function"),
        ("PrepareAndValidatePacket", "function"),
        ("LawInhabitedByteCase", "theorem"),
        ("LawAllocZeroedRead", "theorem"),
        ("LawReadOverWriteSame", "theorem"),
        ("LawReadOverWriteOther", "theorem"),
        ("LawLoopFramePreservesDisjointSuffix", "theorem"),
        ("LawFillAndFrame", "theorem"),
        ("LawSymbolicFillFrame", "theorem"),
        ("LawSliceMetadataAndRead", "theorem"),
        ("LawReadOnlyAndInvalidate", "theorem"),
        ("LawDisjointCopyAndFrame", "theorem"),
        ("LawCapacityInvarianceSmall", "theorem"),
        ("LawCapacityInvarianceLarge", "theorem"),
        ("ValidateEmptyPacketOk", "theorem"),
        ("ValidateFullPacketOk", "theorem"),
        ("ValidatePartialPacketScrubsStaleAndTrailingBytes", "theorem"),
        ("RejectFramingShort", "theorem"),
        ("RejectBadMagic", "theorem"),
        ("RejectLengthOutOfBounds", "theorem"),
        ("RejectChecksumScrubsDestinationAndRestores", "theorem"),
    )
    for name, expected_kind in required_callables:
        decl_node = decl_map.get(name)
        actual = str(decl_node.get("kind", "")) if isinstance(decl_node, dict) else None
        if actual != expected_kind:
            raise ValueError(f"first_slice AST missing executable declaration {name} ({expected_kind}), got {actual}")
        if expected_kind == "function" and cast("list[int]", decl_map[name]["span"])[0] in checked.recursive_declarations:
            raise ValueError(f"packet function {name!r} is recursive and has no admitted stack bound")

    def literal_type(node: dict[str, object]) -> str:
        width = node.get("suffix")
        if not width:
            width = checked.contextual_literal_types.get(cast("list[int]", node["span"])[0])
        if width is None:
            raise ValueError("unconstrained packet integer literal requires an explicit type annotation or suffix")
        if width not in ("usize", "u8", "byte"):
            raise ValueError(f"packet literal requires a usize or byte representation, got {width!r}")
        return cast("str", width)

    union_c, ctor_map = _lower_union_to_c(decl_map["ValidationError"])
    record_c, packet_fields = _lower_record_to_c(decl_map["ValidatedPacket"])
    record_fields = {"ValidatedPacket": packet_fields}
    function_results = {name: _type_info(decl_map[name].get("result"))[1] for name, kind in required_callables if kind == "function"}
    functions_by_site = {cast("list[int]", decl_map[name]["span"])[0]: name for name in function_results}

    def resolve_call(node: dict[str, object]) -> str:
        site = checked.call_declarations.get(cast("list[int]", node["span"])[0])
        if site is None or site not in functions_by_site:
            raise ValueError("packet call requires a resolved declaration in the executable subset")
        return functions_by_site[site]

    def integer_operation(node: dict[str, object]) -> tuple[str, str]:
        operator = _unwrap_arg(node["operator"])
        start = cast("list[int]", operator["span"])[0]
        fact = checked.integer_operations.get(start)
        if fact is None or fact[0] != _node_text(operator).removesuffix("="):
            raise ValueError("packet integer operation lacks a checked representation")
        return fact

    fn_c_blocks = [
        _lower_function_to_c(decl_map[fn_name], ctor_map, record_fields, literal_type, function_results,
                             resolve_call, integer_operation, observations)
        for fn_name in (
            "WritePacket8",
            "CopyPacketToDst",
            "ComputePacketChecksum",
            "PrepareAndValidatePacket",
        )
    ]
    lowered_functions_c = "\n\n".join(fn_c_blocks)

    def exp(check_num: int, val: int) -> int:
        return val + (1 if check_num == perturb_check else 0)

    c_source = f"""/* SPDX-License-Identifier: Apache-2.0 */
/* Lowered from examples/first_slice.vela (SHA256: {_sha256(source)}) */
/* Source profile: verifiedos-scalar-source-v1 */

{union_c}

struct vela_span_byte {{
    unsigned char *ptr;
    unsigned long base;
    unsigned long length;
    int tag;
    int perm_read;
    int perm_write;
}};

{record_c}

struct vela_Result_ValidatedPacket_ValidationError {{
    int is_ok;
    int err;
    struct vela_ValidatedPacket ok;
}};

static void vela_span_copy_meta(struct vela_span_byte *dst, struct vela_span_byte *src)
{{
    dst->ptr = src->ptr;
    dst->base = src->base;
    dst->length = src->length;
    dst->tag = src->tag;
    dst->perm_read = src->perm_read;
    dst->perm_write = src->perm_write;
}}

static void vela_span_alloc_zeroed(
    struct vela_span_byte *out,
    unsigned char *backing,
    unsigned long base,
    unsigned long length)
{{
    unsigned long i;
    for (i = 0UL; i < length; i++) {{
        backing[base + i] = 0U;
    }}
    out->ptr = backing + base;
    out->base = base;
    out->length = length;
    out->tag = 1;
    out->perm_read = 1;
    out->perm_write = 1;
}}

static unsigned char vela_span_read(struct vela_span_byte *s, unsigned long idx)
{{
    return s->ptr[idx];
}}

static void vela_span_write(
    struct vela_span_byte *out,
    struct vela_span_byte *s,
    unsigned long idx,
    unsigned char val)
{{
    s->ptr[idx] = val;
    vela_span_copy_meta(out, s);
}}

static void vela_span_fill(
    struct vela_span_byte *out,
    struct vela_span_byte *s,
    unsigned long off,
    unsigned long count,
    unsigned char val)
{{
    unsigned long i;
    for (i = 0UL; i < count; i++) {{
        s->ptr[off + i] = val;
    }}
    vela_span_copy_meta(out, s);
}}

static void vela_span_slice(
    struct vela_span_byte *out,
    struct vela_span_byte *s,
    unsigned long off,
    unsigned long count)
{{
    out->ptr = s->ptr + off;
    out->base = s->base + off;
    out->length = count;
    out->tag = s->tag;
    out->perm_read = s->perm_read;
    out->perm_write = s->perm_write;
}}

static void vela_span_readonly(struct vela_span_byte *out, struct vela_span_byte *s)
{{
    vela_span_copy_meta(out, s);
    out->perm_write = 0;
}}

static void vela_span_invalidate(struct vela_span_byte *out, struct vela_span_byte *s)
{{
    vela_span_copy_meta(out, s);
    out->tag = 0;
    out->perm_read = 0;
    out->perm_write = 0;
}}

static int vela_span_disjoint(struct vela_span_byte *a, struct vela_span_byte *b)
{{
    if (a->length == 0UL || b->length == 0UL) {{
        return 1;
    }}
    if (a->base <= b->base) {{
        return a->length <= b->base - a->base;
    }}
    return b->length <= a->base - b->base;
}}

static void vela_span_copy_prefix(
    struct vela_span_byte *out,
    struct vela_span_byte *dst,
    struct vela_span_byte *src,
    unsigned long count)
{{
    unsigned long i;
    for (i = 0UL; i < count; i++) {{
        dst->ptr[i] = src->ptr[i];
    }}
    vela_span_copy_meta(out, dst);
}}

static void vela_span_restore(
    struct vela_span_byte *out,
    struct vela_span_byte *parent,
    struct vela_span_byte *view)
{{
    (void)view;
    vela_span_copy_meta(out, parent);
}}

{lowered_functions_c}

static int packet_view_matches(struct vela_span_byte *view, unsigned char *arena,
                               unsigned long base, unsigned long length)
{{
    return view->ptr == arena + base && view->base == base && view->length == length
        && view->tag == 1 && view->perm_read == 1 && view->perm_write == 0;
}}

int main(void)
{{
    unsigned char arena[136];
    unsigned char before[8];
    unsigned long i;
    struct vela_span_byte dst;
    struct vela_span_byte pkt;
    struct vela_Result_ValidatedPacket_ValidationError out;

    /* 1. ValidateEmptyPacketOk: valid 0-byte payload + live frame preservation at index 8 */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 10UL);
    vela_span_write(&dst, &dst, 8UL, 0xC3U);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x00U, 0x5AU, 0x01U, 0x00U, 0x00U, 0x00U, 0x00U);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != {exp(1, 1)})
        return 1;
    if (out.err != {exp(2, 0)})
        return 2;
    if (out.ok.CopiedBytes != {exp(3, 0)}UL)
        return 3;
    if (!packet_view_matches(&out.ok.PayloadView, arena, 68UL, 0UL))
        return 4;
    if (dst.base != 64UL || dst.length != {exp(5, 10)}UL || dst.perm_write != 1 || vela_span_read(&dst, 8UL) != 0xC3U)
        return 5;

    /* 2. ValidateFullPacketOk: valid 4-byte payload [0x10, 0x20, 0x30, 0x40] */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 8UL);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x04U, 0x1EU, 0x01U, 0x10U, 0x20U, 0x30U, 0x40U);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 1 || out.err != 0 || out.ok.CopiedBytes != 4UL
        || !packet_view_matches(&out.ok.PayloadView, arena, 68UL, 4UL))
        return 6;
    if (vela_span_read(&out.ok.PayloadView, 0UL) != {exp(7, 0x10)}U)
        return 7;
    if (vela_span_read(&out.ok.PayloadView, 1UL) != 0x20U
        || vela_span_read(&out.ok.PayloadView, 2UL) != 0x30U
        || vela_span_read(&out.ok.PayloadView, 3UL) != {exp(8, 0x40)}U)
        return 8;
    if (vela_span_read(&dst, 0UL) != 0x56U || vela_span_read(&dst, 7UL) != 0x40U)
        return 9;

    /* 3. ValidatePartialPacketScrubsStaleAndTrailingBytes: 2-byte payload scrubs [6..8) and preserves frame [8..10) */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 10UL);
    vela_span_fill(&dst, &dst, 0UL, 10UL, 0xAAU);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x02U, 0x6BU, 0x01U, 0x11U, 0x22U, 0xDEU, 0xADU);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 1 || out.ok.CopiedBytes != 2UL
        || !packet_view_matches(&out.ok.PayloadView, arena, 68UL, 2UL))
        return 10;
    if (vela_span_read(&out.ok.PayloadView, 0UL) != 0x11U || vela_span_read(&out.ok.PayloadView, 1UL) != 0x22U)
        return 11;
    if (vela_span_read(&dst, 6UL) != {exp(12, 0x00)}U || vela_span_read(&dst, 7UL) != 0x00U || vela_span_read(&dst, 9UL) != 0xAAU)
        return 12;

    /* 4. RejectFramingShort: pkt.length < 4 */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 8UL);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 3UL);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 0 || out.err != {exp(13, 1)} || out.ok.PayloadView.tag != 0)
        return 13;

    /* 5. RejectBadMagic: header magic != 0x56 */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 8UL);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x00U, 0x02U, 0x3AU, 0x01U, 0xAAU, 0xCCU, 0x00U, 0x00U);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 0 || out.err != {exp(14, 2)} || out.ok.PayloadView.tag != 0)
        return 14;

    /* 6. RejectLengthOutOfBounds: rawLen == 5 > 4 */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 8UL);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x05U, 0x5FU, 0x01U, 0x10U, 0x20U, 0x30U, 0x40U);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 0 || out.err != {exp(15, 3)} || out.ok.PayloadView.tag != 0)
        return 15;

    /* 7. RejectChecksumScrubsDestinationAndRestores: bad checksum scrubs [0..8), preserves frame at 8, restores dst */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 10UL);
    vela_span_fill(&dst, &dst, 0UL, 10UL, 0x77U);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x04U, 0xFFU, 0x01U, 0x10U, 0x20U, 0x30U, 0x40U);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 0 || out.err != {exp(16, 4)} || out.ok.PayloadView.tag != 0)
        return 16;
    if (vela_span_read(&dst, 0UL) != {exp(17, 0x00)}U
        || vela_span_read(&dst, 4UL) != 0x00U
        || vela_span_read(&dst, 7UL) != 0x00U
        || vela_span_read(&dst, 8UL) != 0x77U)
        return 17;
    if (dst.base != 64UL || dst.length != 10UL || dst.perm_write != 1)
        return 18;

    /* Overlapping byte views over the same allocation must be rejected before either view writes. */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 8UL);
    vela_span_alloc_zeroed(&pkt, arena, 68UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x04U, 0x1EU, 0x01U, 0x10U, 0x20U, 0x30U, 0x40U);
    vela_span_write(&dst, &dst, 0UL, 0xA3U);
    for (i = 0UL; i < 8UL; i++) {{
        before[i] = vela_span_read(&dst, i);
    }}
    if (before[4] != 0x56U || before[7] != 0x01U)
        return 19;
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 0 || out.err != VOS_ERR_FramingShort || out.ok.PayloadView.tag != 0)
        return 19;
    for (i = 0UL; i < 8UL; i++) {{
        if (vela_span_read(&dst, i) != before[i])
            return 19;
    }}

    /* Bad flags take precedence over the oversized length; preserve the suffix. */
    vela_span_alloc_zeroed(&dst, arena, 64UL, 10UL);
    vela_span_fill(&dst, &dst, 0UL, 10UL, 0xA5U);
    vela_span_alloc_zeroed(&pkt, arena, 128UL, 8UL);
    WritePacket8(&pkt, 0x56U, 0x05U, 0x00U, 0x00U, 0x11U, 0x22U, 0x33U, 0x44U);
    PrepareAndValidatePacket(&out, &dst, &pkt);
    if (out.is_ok != 0 || out.err != VOS_ERR_BadMagicOrFlags || out.ok.PayloadView.tag != 0)
        return 20;
    for (i = 0UL; i < 8UL; i++) {{
        if (vela_span_read(&dst, i) != 0x00U)
            return 20;
    }}
    if (vela_span_read(&dst, 8UL) != 0xA5U || vela_span_read(&dst, 9UL) != 0xA5U)
        return 20;

    return 0;
}}
"""
    return c_source, 20


def _linked_text(raw: bytes) -> memoryview:
    """Read the executable PT_LOAD bytes of the fixed-address differential harness."""
    if (len(raw) < image.EHDR_SIZE or raw[:7] != b"\x7fELF\x02\x01\x01"
            or struct.unpack_from("<HH", raw, 16) != (image.ET_EXEC, image.EM_RISCV)):
        raise ValueError("linked image requires a little-endian ELF64 RISC-V executable")
    entry, table = struct.unpack_from("<QQ", raw, 24)
    if entry != cd.asm.TEXT_BASE:
        raise ValueError(f"linked image entry {entry:#x} differs from the harness entry {cd.asm.TEXT_BASE:#x}")
    stride, count = struct.unpack_from("<HH", raw, 54)
    if (table != image.EHDR_SIZE or stride != image.PHDR_SIZE or count != 2
            or table + stride * count > len(raw)):
        raise ValueError("linked image requires the text and data load headers")
    text = memoryview(raw)[:0]
    for index, (flags, base) in enumerate(((image.PF_R | image.PF_X, cd.asm.TEXT_BASE),
                                           (image.PF_R | image.PF_W, cd.asm.DATA_BASE))):
        kind, perms, offset, virtual, physical, size, memory, _ = struct.unpack_from(
            "<IIQQQQQQ", raw, table + stride * index)
        if (kind != image.PT_LOAD or perms != flags or virtual != base or physical != base
                or size != memory or not size or offset < table + stride * count or offset + size > len(raw)):
            raise ValueError(f"linked image has an invalid load segment at {base:#x}")
        if flags & image.PF_X:
            if base + size > cd.asm.DATA_BASE:
                raise ValueError("linked executable text exceeds its slot")
            text = memoryview(raw)[offset:offset + size]
    return text


def _check_purecap_control_image(raw: bytes) -> memoryview:
    """Check all loaded instructions of the local control ELF, including untaken branches."""
    text = _linked_text(raw)
    if len(text) % 4:
        raise ValueError("purecap control text ends within an instruction")
    for at in range(0, len(text), 4):
        word, = struct.unpack_from("<I", text, at)
        if not any(dialect.matches_encoding(row, word) for row in PURECAP_CONTROL_ROWS):
            raise ValueError(f"purecap control instruction {word:#010x} at PC {cd.asm.TEXT_BASE + at:#x}"
                             " is outside its scalar instruction profile")
    return text


def _purecap_cheri_asm_stream(mode: str) -> str:
    """Emit a purecap CHERI-RISC-V assembly stream exercising hardware capability bounds/tags.

    - `mode == "pass"`: initializes a 16-byte stack frame with `dst` (8 bytes) and `pkt`
      (8 bytes), validates the header and checksum, copies the 4-byte payload into `dst+4`,
      narrows `PayloadView` (`c13`) to `[dst+4, dst+8)` with `csetbounds` and strips store
      permission (`candperm`), verifies `cgetlen == 4`, `cgettag == 1`, and all 4 payload
      bytes via capability loads, and restores the parent `dst` capability (`cgetlen == 8`).
    - `mode == "bounds-trap"`: narrows `PayloadView` (`c13`) to `[dst+4, dst+8)` with
      `csetbounds` and attempts an out-of-bounds byte load at offset 4 (`lbu t0, 4(c13)`),
      which MUST trigger a hardware CHERI bounds fault (`mcause == 28`, HTIF exit `284`).
    - `mode == "tag-trap"`: invalidates `emptyView` (`c13`) with `ccleartag` on the error
      exit path and attempts to dereference `lbu t0, 0(c13)`, which MUST trigger a hardware
      CHERI tag violation (`mcause == 28`, HTIF exit `284`).
    """
    tail_op = {
        "pass": """\
        lbu     t0, 0(c13)
        li      t1, 0x10
        bne     t0, t1, __slice_fail
        lbu     t0, 3(c13)
        li      t1, 0x40
        bne     t0, t1, __slice_fail
        cgetlen t0, c13
        li      t1, 4
        bne     t0, t1, __slice_fail
        cgettag t0, c13
        li      t1, 1
        bne     t0, t1, __slice_fail
        cgetlen t0, c12
        li      t1, 8
        bne     t0, t1, __slice_fail
        li      a0, 0
        j       __slice_ret
""",
        "bounds-trap": """\
        lbu     t0, 4(c13)
        li      a0, 99
        j       __slice_ret
""",
        "tag-trap": """\
        cmove   c13, cnull
        lbu     t0, 0(c13)
        li      a0, 98
        j       __slice_ret
""",
        "perm-trap": """\
        candperm c13, c13, x0
        sb      t0, 0(c13)
        li      a0, 97
        j       __slice_ret
""",
    }[mode]
    return f"""\
        .text
        .globl main
main:
        cincoffsetimm c2, c2, -32
        sc      c1, 16(c2)
        # Derive dst capability c12 = [c2, c2+8)
        cmove   c12, c2
        li      t0, 8
        csetbounds c12, c12, t0
        # Derive pkt capability c14 = [c2+8, c2+16)
        cincoffsetimm c14, c2, 8
        li      t0, 8
        csetbounds c14, c14, t0
        # Populate pkt = [0x56, 0x04, 0x1E, 0x01, 0x10, 0x20, 0x30, 0x40]
        li      t0, 0x56
        sb      t0, 0(c14)
        li      t0, 0x04
        sb      t0, 1(c14)
        li      t0, 0x1E
        sb      t0, 2(c14)
        li      t0, 0x01
        sb      t0, 3(c14)
        li      t0, 0x10
        sb      t0, 4(c14)
        li      t0, 0x20
        sb      t0, 5(c14)
        li      t0, 0x30
        sb      t0, 6(c14)
        li      t0, 0x40
        sb      t0, 7(c14)
        # Copy header + 4-byte payload into dst (c12)
        lbu     t0, 0(c14)
        sb      t0, 0(c12)
        lbu     t0, 1(c14)
        sb      t0, 1(c12)
        lbu     t0, 2(c14)
        sb      t0, 2(c12)
        lbu     t0, 3(c14)
        sb      t0, 3(c12)
        lbu     t0, 4(c14)
        sb      t0, 4(c12)
        lbu     t0, 5(c14)
        sb      t0, 5(c12)
        lbu     t0, 6(c14)
        sb      t0, 6(c12)
        lbu     t0, 7(c14)
        sb      t0, 7(c12)
        # Narrow PayloadView capability c13 = Span.ReadOnly(Span.Slice(dst, 4, 4))
        cincoffsetimm c13, c12, 4
        li      t0, 4
        csetbounds c13, c13, t0
        li      t0, 0xFF7
        candperm c13, c13, t0
{tail_op}\
__slice_fail:
        li      a0, 1
__slice_ret:
        lc      c1, 16(c2)
        cincoffsetimm c2, c2, 32
        cjalr   cnull, cra, 0
"""


def _cold_branch_image(original: bytes, word: int) -> tuple[bytes, int]:
    """Replace the passing control's error return instruction, preserving its layout."""
    stream = cd.compose(_purecap_cheri_asm_stream("pass"))
    _, symbols, _ = cd.asm.Assembler(stream).assemble()
    _, pc = symbols["__slice_fail"]
    start, = struct.unpack_from("<Q", original, image.EHDR_SIZE + 8)
    site = start + pc - cd.asm.TEXT_BASE
    if original[site:site + 4] != bytes.fromhex("1b051000"):  # addiw a0, zero, 1
        raise ValueError("purecap error-branch control did not find the one-word failure return")
    return original[:site] + word.to_bytes(4, "little") + original[site + 4:], pc


def _check_cold_branch_on_sail(simulator: list[str], profile: Path,
                               directory: Path, passing_process: dict[str, object]) -> None:
    """Execute the deliberately refused control in isolation and compare full commit records."""
    original = (directory / "purecap_pass.elf").read_bytes()
    word = 0x022180D7  # vadd.vv v1,v2,v3
    mutant, pc = _cold_branch_image(original, word)
    try:
        _check_purecap_control_image(mutant)
    except ValueError as error:
        if f"instruction {word:#010x} at PC {pc:#x}" not in str(error):
            raise
    else:
        raise ValueError("purecap error-branch control unexpectedly passed the scalar profile")
    with tempfile.TemporaryDirectory(prefix="cold-branch-", dir=directory) as temporary:
        work = Path(temporary)
        elf = work / "vector-error-branch.elf"
        elf.write_bytes(mutant)
        observations: list[dict[str, object]] = []
        ran = cd.run_image(simulator, profile, elf, work, observations=observations)
        if ran.verdict != "pass" or not observations:
            raise ValueError(f"purecap error-branch control lost its passing execution: {ran.detail}")
        original_trace, changed_trace = (
            _simulator_transcript(Path(str(process["log"])).read_text(encoding="utf-8"),
                                  int(str(process["returncode"])), text=_linked_text(subject))
            for process, subject in ((passing_process, original), (observations[0], mutant)))
        if original_trace != changed_trace:
            raise ValueError("purecap error-branch control changed the passing Sail trace")


def _resolve_ccomp(ccomp_path: Path | None) -> Path | None:
    if ccomp_path is not None:
        if not ccomp_path.is_file():
            raise ValueError(f"--ccomp requires the VerifiedOS typed compiler executable at {ccomp_path}")
        return ccomp_path.resolve()
    for candidate in DEFAULT_CCOMP_CANDIDATES:
        path = Path(candidate)
        if path.is_file():
            return path.resolve()
    return None


def _run_negative_controls(compiled: vela_parser.Build, directory: Path) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    sources = directory / "negative-controls"
    sources.mkdir()
    for ctrl in NEGATIVE_CONTROLS:
        raw = ctrl.source.encode("utf-8")
        (sources / f"{ctrl.name}.vela").write_bytes(raw)
        # Must parse cleanly as schema-2 surface syntax; syntax refusal is never a semantic control.
        parsed = vela_parser.parse_source(compiled, raw, surface=True)
        try:
            vela_elaborate.elaborate(raw, parsed)
        except VelaError as error:
            if error.kind != ctrl.expected_kind or ctrl.expected_substring not in error.message:
                raise ValueError(
                    f"negative control {ctrl.name}: expected {ctrl.expected_kind} containing "
                    f"'{ctrl.expected_substring}', got {error.kind}: {error.message}"
                ) from error
            ctrl.check_location(error.line, error.column)
            results.append({
                "name": ctrl.name,
                "parsed_surface": True,
                "category": error.kind,
                "line": error.line,
                "column": error.column,
                "message": error.message,
            })
        else:
            raise ValueError(f"negative control {ctrl.name} was unexpectedly accepted")
    return results


def _check_capacity_structure(small_state: vela_elaborate._Elaborator,
                              large_state: vela_elaborate._Elaborator) -> None:
    small_literal = small_state.render(_int_term(_INT_SPECS["usize"], 8))
    large_literal = large_state.render(_int_term(_INT_SPECS["usize"], 1_000_000_000))
    if not any(large_literal in decl for decl in large_state.output):
        raise ValueError("capacity-invariance gate did not exercise the large capacity numeral")
    if small_state.output != [decl.replace(large_literal, small_literal) for decl in large_state.output]:
        raise ValueError("capacity-invariance gate changed proof structure beyond the encoded capacity numeral")


def _run_capacity_invariance_gate(
    compiled: vela_parser.Build,
    directory: Path,
    steps: list[dict[str, object]],
) -> dict[str, object]:
    small_src = _capacity_fixture("8usize")
    large_src = _capacity_fixture("1_000_000_000usize")
    (directory / "CapSmall.vela").write_bytes(small_src)
    (directory / "CapLarge.vela").write_bytes(large_src)
    small_parsed = vela_parser.parse_source(compiled, small_src, surface=True)
    large_parsed = vela_parser.parse_source(compiled, large_src, surface=True)
    small_elab, small_state = vela_elaborate._checked_elaboration(small_src, small_parsed)
    large_elab, large_state = vela_elaborate._checked_elaboration(large_src, large_parsed)

    small_work = vela_elaborate.MAX_WORK - small_state.work
    large_work = vela_elaborate.MAX_WORK - large_state.work
    small_red = vela_elaborate.MAX_REDUCTIONS - small_state.reductions
    large_red = vela_elaborate.MAX_REDUCTIONS - large_state.reductions

    if len(small_state.output) != len(large_state.output):
        raise ValueError(
            f"capacity-invariance gate failed: obligation count differs ({len(small_state.output)} vs {len(large_state.output)})"
        )
    if small_work != large_work or small_red != large_red:
        raise ValueError(
            f"capacity-invariance gate failed: work/reduction profile differs "
            f"(small={small_work}/{small_red}, large={large_work}/{large_red})"
        )
    _check_capacity_structure(small_state, large_state)
    # The concrete usize encoder uses the same number of nibbles at both capacities.
    if len(small_elab.gallina) != len(large_elab.gallina):
        raise ValueError(
            f"capacity-invariance gate failed: emitted Gallina byte length differs "
            f"({len(small_elab.gallina)} vs {len(large_elab.gallina)})"
        )

    small_v = directory / "CapSmall.v"
    large_v = directory / "CapLarge.v"
    small_v.write_text(small_elab.gallina, encoding="utf-8", newline="")
    large_v.write_text(large_elab.gallina, encoding="utf-8", newline="")
    _run(_opam(["rocq", "c", "-q", "-R", str(directory), "VelaFirstSlice", small_v.name]),
         directory, directory / "CapSmall.compile.log", steps)
    _run(_opam(["rocq", "c", "-q", "-R", str(directory), "VelaFirstSlice", large_v.name]),
         directory, directory / "CapLarge.compile.log", steps)
    _run(_opam(["rocqchk", "-R", str(directory), "VelaFirstSlice",
                "VelaFirstSlice.CapSmall", "VelaFirstSlice.CapLarge"]),
         directory, directory / "CapGate.kernel.log", steps)
    return {
        "small_capacity": "8usize",
        "large_capacity": "1_000_000_000usize",
        "obligation_count": len(small_state.output),
        "work_steps": small_work,
        "reduction_steps": small_red,
        "gallina_bytes": len(small_elab.gallina),
        "kernel_checked": True,
    }


def _qualify_attempt(
    root: Path,
    directory: Path,
    steps: list[dict[str, object]],
    ccomp_path: Path | None,
    compiled: vela_parser.Build,
    timing: packet_trace.Recorder | None = None,
) -> dict[str, object]:
    source_path = root / EXAMPLE
    source = vela_parser.read_source(source_path)
    phase = nullcontext if timing is None else timing.span
    with phase("packet"):
        if timing is not None:
            timing.source_size(len(source))
        with phase("parse"):
            parsed = vela_parser.parse_source(compiled, source, surface=True)

        # 1. Elaborate first_slice.vela and verify determinism + exported obligations
        translated = vela_elaborate._checked_elaboration(source, parsed, phase=phase)[0]
        repeated = vela_elaborate.elaborate(source, parsed)
        if translated != repeated:
            raise ValueError("first_slice.vela elaboration is nondeterministic")

        exports = solver_ledger.math_exports(translated.gallina)
        for required_suffix in (*EXPECTED_LAWS, *EXPECTED_CONTRACT_OBLIGATIONS, *EXPECTED_SCENARIO_THEOREMS):
            if not any(exp.endswith(f"_{required_suffix}") for exp in exports):
                raise ValueError(f"emitted Gallina is missing required obligation '{required_suffix}'")

        gallina_path = directory / "FirstSlice.v"
        gallina_path.write_text(translated.gallina, encoding="utf-8", newline="")
        _run(
            _opam(["rocq", "c", "-q", "-R", str(directory), "VelaFirstSlice", gallina_path.name]),
            directory,
            directory / "FirstSlice.compile.log",
            steps,
            timing=timing,
        )

        module = gallina_module_name(translated.module)
        audited = [f"{module}.{name}" for name in exports]
        assumptions_path = directory / "FirstSliceAssumptions.v"
        assumptions_path.write_text(
            "From VelaFirstSlice Require Import FirstSlice.\n"
            + "".join(f"Print Assumptions FirstSlice.{name}.\n" for name in audited),
            encoding="utf-8",
            newline="",
        )
        assumptions_out = _run(
            _opam(["rocq", "c", "-q", "-R", str(directory), "VelaFirstSlice", assumptions_path.name]),
            directory,
            directory / "FirstSlice.assumptions.log",
            steps,
            timing=timing,
        )
        trusted = solver_ledger.ledger(translated.gallina)
        reported_trust = solver_ledger.audit(assumptions_out, len(audited), module, trusted)

        _run(
            _opam(["rocqchk", "-R", str(directory), "VelaFirstSlice", "VelaFirstSlice.FirstSlice"]),
            directory,
            directory / "FirstSlice.kernel.log",
            steps,
            timing=timing,
        )

        # Finish the compiler recording as soon as the C translation is available.
        operations: list[dict[str, object]] = []
        with phase("lower-to-c"):
            c_source, check_count = lower_to_c(source, parsed, checked=translated, observations=operations)

    # 2. Fail-closed proof-corruption control on FirstSlice.v
    corrupted_v = directory / "FirstSliceCorrupted.v"
    corrupted_text = _corrupted_proof(translated.gallina)
    corrupted_v.write_text(corrupted_text, encoding="utf-8", newline="")
    corrupt_proc = subprocess.run(
        _opam(["rocq", "c", "-q", "-R", str(directory), "VelaFirstSlice", corrupted_v.name]),
        cwd=directory,
        capture_output=True,
        encoding="utf-8",
        errors="replace",
        timeout=TIMEOUT,
        check=False,
    )
    corruption_log = directory / "FirstSliceCorrupted.compile.log"
    corruption_log.write_text(corrupt_proc.stdout + corrupt_proc.stderr, encoding="utf-8", newline="")
    steps.append({"command": corrupt_proc.args, "cwd": str(directory),
                  "returncode": corrupt_proc.returncode, "expected_refusal": True,
                  "log": str(corruption_log), "log_sha256": file_sha256(corruption_log),
                  **_stream_identity(corrupt_proc.stdout, corrupt_proc.stderr)})
    _check_corruption_refusal(translated.gallina, corrupt_proc.returncode,
                              corrupt_proc.stdout + corrupt_proc.stderr)

    # 3. Capacity-invariance gate (8usize vs 1_000_000_000usize)
    cap_gate = _run_capacity_invariance_gate(compiled, directory, steps)

    # 4. Semantic negative controls
    neg_controls = _run_negative_controls(compiled, directory)

    c_path = directory / "first_slice.c"
    c_path.write_text(c_source, encoding="utf-8", newline="\n")

    loaded_env = env.load(toolchain=False)
    profile = loaded_env.profile.resolve()
    sim_path = loaded_env.simulator.resolve()
    if not sim_path.is_file():
        raise ValueError(f"Sail emulator not found at {sim_path}; run `python tools/run.py model build`")
    simulator = [str(sim_path)]

    # 5a. Purecap hardware capability execution & fault controls on sail_riscv_sim
    purecap_runs: dict[str, object] = {}
    for mode, expected_verdict, expected_code in PURECAP_CASES:
        asm_stream = _purecap_cheri_asm_stream(mode)
        asm_elf = directory / f"purecap_{mode}.elf"
        refusals, img_bytes = cd.assemble(asm_stream, f"purecap_{mode}", asm_elf)
        if refusals:
            raise ValueError(f"purecap_{mode} assembly refused: {refusals}")
        _check_purecap_control_image(asm_elf.read_bytes())
        processes: list[dict[str, object]] = []
        ran = cd.run_image(simulator, profile, asm_elf, directory, observations=processes)
        if ran.verdict != expected_verdict or ran.code != expected_code:
            raise ValueError(
                f"purecap_{mode} expected ({expected_verdict}, {expected_code}), "
                f"got ({ran.verdict}, {ran.code}): {ran.detail}"
            )
        purecap_runs[mode] = {
            "verdict": ran.verdict,
            "code": ran.code,
            "records": ran.records,
            "trace_digest": ran.digest,
            "cap_roundtrip": ran.cap_roundtrip,
            "image_bytes": img_bytes,
            "process": processes[0],
        }
        if mode == "pass":
            _check_cold_branch_on_sail(simulator, profile, directory, processes[0])

    # 5b. CompCert Clight (-dclight), -interp, and purecap C-to-Sail execution
    resolved_ccomp = _resolve_ccomp(ccomp_path)
    ccomp_evidence: dict[str, object] = {"available": resolved_ccomp is not None}
    if resolved_ccomp is not None:
        ccomp_cmd = [str(resolved_ccomp), "-fverifiedos-typed", "-dclight"]
        main_prog = cd.Program("first_slice", "given", c_source, check_count, 0)
        main_processes: list[dict[str, object]] = []
        main_rep = cd.run_program(main_prog, ccomp_cmd, directory, simulator, profile, "", interp=True,
                                  observations=main_processes)
        if (
            main_rep.verdict != "pass"
            or main_rep.interpreted is None
            or main_rep.interpreted.code != 0
            or main_rep.ran is None
            or main_rep.compiled is None
        ):
            raise ValueError(
                f"CompCert/Sail execution of first_slice.c failed: verdict={main_rep.verdict}, "
                f"detail={main_rep.detail}, interp={main_rep.interpreted}"
            )
        clight_file = directory / "first_slice" / "first_slice.light.c"
        if not clight_file.is_file():
            raise ValueError("CompCert -dclight did not emit first_slice.light.c")

        programs: list[dict[str, object]] = [{
            "name": main_prog.name, "expect": 0, "source_sha256": main_rep.source_sha256,
            "preprocessed_sha256": main_rep.compiled.preprocessed.sha256,
            "image_bytes": main_rep.image_bytes, "processes": main_processes,
        }]
        perturbed_runs: list[dict[str, object]] = []
        for check_id, label in PERTURBED_CASES:
            p_src, p_checks = lower_to_c(source, parsed, perturb_check=check_id, checked=translated)
            p_prog = cd.Program(label, "given", p_src, p_checks, check_id)
            processes: list[dict[str, object]] = []
            p_rep = cd.run_program(p_prog, ccomp_cmd, directory, simulator, profile, "", interp=True,
                                   observations=processes)
            if (not cd.as_expected(p_rep) or p_rep.interpreted is None or p_rep.interpreted.code != check_id
                    or p_rep.compiled is None):
                raise ValueError(
                    f"perturbed C control {label} (check {check_id}) did not fail as expected: "
                    f"verdict={p_rep.verdict}, detail={p_rep.detail}, interp={p_rep.interpreted}"
                )
            perturbed_runs.append({
                "name": label,
                "check_id": check_id,
                "verdict": p_rep.verdict,
                "target_code": cd.target_code(p_rep.ran),
                "interp_code": p_rep.interpreted.code,
            })
            programs.append({
                "name": label, "expect": check_id, "source_sha256": p_rep.source_sha256,
                "preprocessed_sha256": p_rep.compiled.preprocessed.sha256,
                "image_bytes": p_rep.image_bytes, "processes": processes,
            })

        ccomp_evidence.update({
            "ccomp_path": str(resolved_ccomp),
            "ccomp_sha256": file_sha256(resolved_ccomp),
            "clight_path": str(clight_file),
            "clight_sha256": file_sha256(clight_file),
            "asm_sha256": main_rep.compiled.stream_sha256,
            "asm_lines": main_rep.compiled.lines,
            "interp_exit_code": main_rep.interpreted.code,
            "sail_verdict": main_rep.verdict,
            "sail_records": main_rep.ran.records,
            "sail_trace_digest": main_rep.ran.digest,
            "sail_cap_roundtrip": main_rep.ran.cap_roundtrip,
            "perturbed_controls": perturbed_runs,
            "programs": programs,
        })

    _retained_execution({"execution_inputs": _execution_inputs(ccomp_path), "purecap_cheri_runs": purecap_runs,
                         "compcert_sail": ccomp_evidence}, directory, dict(_artifacts(directory)))
    inventory = build_foundation_inventory()
    inventory["solver_trusted_obligations"] = [entry.as_json() for entry in trusted]
    inventory["global_assumptions"] = (
        "Closed under the global context (0 axioms)" if not trusted
        else f"{len(trusted)} solver-trusted axioms; no other assumptions"
    )
    return {
        # Harness steps ran; acceptance additionally needs an empty solver-trust ledger.
        "status": "passed",
        "accepted": not trusted,
        "source": str(source_path),
        "source_sha256": _sha256(source),
        "gallina": str(gallina_path),
        "gallina_sha256": file_sha256(gallina_path),
        "kernel_checked": not trusted,
        "solver_trusted_count": len(trusted),
        "solver_trusted_axioms": reported_trust,
        "assumption_exports_count": len(exports),
        "proof_corruption_refused": True,
        "capacity_invariance": cap_gate,
        "negative_controls_count": len(neg_controls),
        "negative_controls": neg_controls,
        "lowering_provenance": _lowering_provenance(translated, c_source, operations),
        "lowered_c": str(c_path),
        "lowered_c_sha256": file_sha256(c_path),
        "purecap_cheri_runs": purecap_runs,
        "compcert_sail": ccomp_evidence,
        "inventory": inventory,
    }


def qualify(root: Path, *, ccomp_path: Path | None = None, trace_phases: bool = False) -> dict[str, object]:
    """Qualify the development harness without a source or machine admission verdict."""
    work = _work_root(root)
    with FileLock(work / "qualification.lock", timeout=5):
        latest = work / "qualification.json"
        latest.unlink(missing_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="slice-", dir=work))
        steps: list[dict[str, object]] = []
        attempt: dict[str, object] = {
            "schema": 2,
            "scope": "vela-first-slice-qualification",
            "status": "running",
            "directory": str(directory),
            "steps": steps,
            "full_machine_refinement_closed": False,
            "source_correspondence": False,
            "artifact_accepted": False,
            "production_admission": False,
            "remaining_chain_owners": ["Q35o", "Q35p", "Q35k", "Q35l", "Q35d", "M1.2g"],
            "inventory": build_foundation_inventory(),
        }
        publish_report(directory / "attempt.json", attempt)
        timing = packet_trace.Recorder() if trace_phases else None
        try:
            execution = _execution_inputs(ccomp_path)
            inputs = _inputs(root)
            revision = _revision(root)
            tools = replay._toolchain(root, directory, steps)
            runtime = replay._runtime(directory, steps)
            compiled = vela_parser.build(root)
            parser_receipt = copy.deepcopy(compiled.receipt)
            outputs = replay._parser_outputs(compiled)
            attempt.update({"inputs": inputs, "producer_revision": revision,
                            "toolchain": tools, "runtime": runtime,
                            "execution_inputs": execution, "parser": parser_receipt,
                            "parser_outputs": outputs})
            publish_report(directory / "attempt.json", attempt)
            if timing is not None:
                prover_files = cast("dict[str, str]", runtime["files_sha256"])
                attempt["trace_runtime_sha256"] = packet_runtime.identity(compiled.executable, prover_files, directory)
            attempt.update(_qualify_attempt(root, directory, steps, ccomp_path, compiled, timing))
            if timing is not None:
                _require(packet_runtime.identity(compiled.executable, cast("dict[str, str]", runtime["files_sha256"]),
                                                 directory) == attempt["trace_runtime_sha256"],
                         "packet compiler runtime changed during measurement")
                timeline = timing.export(packet_trace.subjects(attempt), "passed")
                _check_trace(root, attempt, timeline, steps)
                publish_report(directory / packet_trace.FILENAME, timeline)
                attempt["compiler_trace"] = str(directory / packet_trace.FILENAME)
            reported_outputs = _reported_outputs(attempt)
            produced_outputs = _artifacts(directory)
            _require(_inputs(root) == inputs and _revision(root) == revision
                     and replay._toolchain(root, directory, steps) == tools
                     and replay._runtime(directory, steps) == runtime
                     and _execution_inputs(ccomp_path) == execution,
                     "first-slice inputs, toolchain or runtime changed during qualification")
            _require(compiled.receipt == parser_receipt and replay._parser_outputs(compiled) == outputs
                     and vela_parser._toolchain(root) == parser_receipt["toolchain"],
                     "first-slice parser identity changed during qualification")
            replay._observations([], steps)
            final_outputs = _artifacts(directory)
            _require(_reported_outputs(attempt) == reported_outputs
                     and all(final_outputs.get(name) == digest for name, digest in produced_outputs.items()),
                     "first-slice outputs changed during final identity checks")
            attempt["artifacts_sha256"] = final_outputs
        except (Exception, KeyboardInterrupt) as error:
            if timing is not None:
                outcome = "cancelled" if isinstance(error, KeyboardInterrupt) else "refused"
                publish_report(directory / packet_trace.FILENAME, timing.export(packet_trace.digest(attempt.get("inputs")), outcome))
            attempt.update({
                "status": "failed",
                "kernel_checked": False,
                "accepted": False,
                "error": f"{type(error).__name__}: {error}",
            })
            publish_report(directory / "attempt.json", attempt)
            raise
        else:
            publish_report(directory / "attempt.json", attempt)
            publish_report(latest, attempt)
            return attempt


def _check_trace(root: Path, receipt: dict[str, object], timeline: dict[str, object],
                 steps: list[dict[str, object]]) -> None:
    workers = {packet_trace.PROOF_STEPS[log][1]: cast("int", step.get("observed_pid")) for step in steps
               if (log := Path(str(step.get("log"))).name) in packet_trace.PROOF_STEPS}
    packet_trace.validate(timeline, packet_trace.subjects(receipt), (root / EXAMPLE).stat().st_size, workers)
    durations = {event["name"]: event["dur"] for event in cast("list[dict[str, object]]", timeline["traceEvents"])
                 if event["ph"] == "X"}
    proof_steps = [step for step in steps if Path(str(step.get("log"))).name in packet_trace.PROOF_STEPS]
    if len(proof_steps) != len(packet_trace.PROOF_STEPS):
        raise ValueError("packet trace proof step inventory is incomplete or duplicated")
    for step in proof_steps:
        phase, child = packet_trace.PROOF_STEPS[Path(str(step["log"])).name]
        elapsed = step.get("elapsed_ns")
        if type(elapsed) is not int or elapsed < 0 or any(
                cast("int", durations[name]) > (elapsed + 999) // 1000 for name in (phase, child)):
            raise ValueError("packet proof interval exceeds its observed command lifetime")


def verify_bindings(root: Path, receipt_path: Path) -> dict[str, object]:
    """Check retained identities; this supplies no proof replay or admission verdict."""
    with receipt_path.open("rb") as stream:
        raw = stream.read(RECEIPT_BYTES + 1)
    if len(raw) > RECEIPT_BYTES:
        raise ValueError("first-slice receipt exceeds its size bound")
    try:
        value = json.loads(raw, object_pairs_hook=unique_object)
    except (ValueError, RecursionError) as error:
        raise ValueError("first-slice receipt is malformed") from error
    if (not isinstance(value, dict) or type(value.get("schema")) is not int or value["schema"] != 2
            or value.get("scope") != "vela-first-slice-qualification" or value.get("status") != "passed"
            or any(value.get(key) is not False for key in (
                "artifact_accepted", "source_correspondence", "production_admission",
                "full_machine_refinement_closed"))):
        raise ValueError("first-slice receipt has unsupported scope, schema or status")
    receipt = cast("dict[str, object]", value)
    if receipt.get("inputs") != _inputs(root) or receipt.get("producer_revision") != _revision(root):
        raise ValueError("first-slice receipt source inputs or producer revision changed")
    execution = receipt.get("execution_inputs")
    if not isinstance(execution, dict) or not isinstance(execution.get("files"), dict):
        raise TypeError("first-slice receipt execution identities are malformed")
    ccomp = execution["files"].get("ccomp")
    if ccomp is not None and (not isinstance(ccomp, dict) or not isinstance(ccomp.get("path"), str)):
        raise ValueError("first-slice receipt compiler identity is malformed")
    compiler = None if ccomp is None else Path(ccomp["path"])
    if _execution_inputs(compiler) != execution:
        raise ValueError("first-slice receipt execution inputs changed")
    parser_receipt = receipt.get("parser")
    if (not isinstance(parser_receipt, dict) or not isinstance(parser_receipt.get("directory"), str)
            or not isinstance(parser_receipt.get("generated_sha256"), dict)):
        raise TypeError("first-slice receipt parser identity is malformed")
    directory = _receipt_directory(parser_receipt["directory"], vela_parser._work_root(root), "build-")
    compiled = vela_parser.Build(directory, directory / "vela-parser", parser_receipt)
    if (parser_receipt.get("inputs") != vela_parser._inputs(root)
            or parser_receipt.get("toolchain") != vela_parser._toolchain(root)
            or replay._parser_outputs(compiled) != receipt.get("parser_outputs")):
        raise ValueError("first-slice receipt parser identities changed")
    artifacts = receipt.get("artifacts_sha256")
    directory_name = receipt.get("directory")
    if not isinstance(directory_name, str) or not isinstance(artifacts, dict):
        raise TypeError("first-slice receipt output inventory is malformed")
    output_directory = _receipt_directory(directory_name, _work_root(root), "slice-")
    if _artifacts(output_directory) != artifacts:
        raise ValueError("first-slice receipt outputs changed")
    _retained_proof(root, receipt, output_directory, artifacts)
    timeline_path = output_directory / packet_trace.FILENAME
    if "compiler_trace" in receipt or str(timeline_path) in artifacts:
        if receipt.get("compiler_trace") != str(timeline_path) or timeline_path.stat().st_size > packet_trace.MAX_BYTES:
            raise ValueError("packet compiler trace path or size changed")
        timeline = json.loads(timeline_path.read_bytes(), object_pairs_hook=unique_object)
        _check_trace(root, receipt, timeline, cast("list[dict[str, object]]", receipt["steps"]))
    provenance = _reconstruct_lowering(root)
    if (CheckedElaboration.encode_syntax(receipt.get("lowering_provenance")) != CheckedElaboration.encode_syntax(provenance)
            or any(receipt.get(key) != provenance[key] for key in ("source_sha256", "gallina_sha256", "lowered_c_sha256"))):
        raise ValueError("retained integer lowering or generated subjects differ from the checked source")
    _retained_controls(receipt, output_directory, artifacts)
    _retained_execution(receipt, output_directory, artifacts)
    with tempfile.TemporaryDirectory(prefix="bindings-", dir=_work_root(root)) as temporary:
        steps: list[dict[str, object]] = []
        runtime = replay._runtime(Path(temporary), steps)
        if (replay._toolchain(root, Path(temporary), steps) != receipt.get("toolchain")
                or runtime != receipt.get("runtime")):
            raise ValueError("first-slice receipt prover or runtime changed")
        if "compiler_trace" in receipt and packet_runtime.identity(
                compiled.executable, cast("dict[str, str]", runtime["files_sha256"]),
                output_directory) != receipt.get("trace_runtime_sha256"):
            raise ValueError("packet compiler trace runtime changed")
    if (receipt.get("inputs") != _inputs(root) or receipt.get("producer_revision") != _revision(root)
            or _execution_inputs(compiler) != execution
            or parser_receipt.get("inputs") != vela_parser._inputs(root)
            or parser_receipt.get("toolchain") != vela_parser._toolchain(root)
            or replay._parser_outputs(compiled) != receipt.get("parser_outputs")
            or _artifacts(_receipt_directory(directory_name, _work_root(root), "slice-")) != artifacts):
        raise ValueError("first-slice receipt inputs or outputs changed during binding check")
    with receipt_path.open("rb") as stream:
        if stream.read(RECEIPT_BYTES + 1) != raw:
            raise ValueError("first-slice receipt changed during binding check")
    return {"schema": 1, "scope": "vela-first-slice-binding-check", "status": "matched",
            "receipt": str(receipt_path), "receipt_sha256": _sha256(raw),
            "proof_replayed": False, "artifact_accepted": False, "production_admission": False}
