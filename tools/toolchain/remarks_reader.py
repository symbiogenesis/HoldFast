# SPDX-License-Identifier: Apache-2.0
"""Qualify HoldFast optimization decisions through the stock LLVM remark reader."""

import subprocess
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path

from toolchain import compiler_trace, remarks
from toolchain.cli import holdfast
from toolchain.hashing import file_sha256, sha256_bytes

READER_SHA256 = "18bdbf0d5d387911b585cd97786ffcb3dcdcc8a539784a2963e293afdec208a3"
LIBRARY = Path("/usr/lib/aarch64-linux-gnu/libLLVM.so.21.1")
LIBRARY_SHA256 = "a8d595321c634d717fe5d8a03396837c5631b389698125b93061b7638d5a6e7c"
PREFIX = ("module Costs;\r\n// Scaling by a configured gain π.\r\n"
          "public Nat Scale(const Nat factor, Nat value) => factor * value;\r\n").encode()
SOURCE = PREFIX + (b"public Nat Forward(const Nat factor, Nat value) => Scale(factor, value);\r\n"
                   b"public Nat Render(Nat value) => Forward(3, value + 1);\r\n")
REFUSAL = PREFIX + b"public Nat Bad(Nat value) => Scale(value, value);\r\n"
FILENAME = "Costs.hf"
_APPLIED = "closed static inputs substituted; call eliminated"
_MISSED = "'call retained pending static parameter(s): factor'"
_REFUSED = "constant initializer depends on runtime binding 'value'; only earlier constants and static pure-call arguments are permitted"


def _run(reader: Path, arguments: list[str], data: bytes, *, malformed: bool = False) -> bytes:
    result = subprocess.run([reader, *arguments, "-"], input=data, capture_output=True, timeout=10,
                            cwd=reader.parent, env={"LC_ALL": "C", "LD_LIBRARY_PATH": str(LIBRARY.parent)}, check=False)
    if malformed:
        if result.returncode <= 0 or b"error" not in result.stderr.lower():
            raise ValueError("LLVM reader did not diagnose the malformed remark")
        return b""
    if result.returncode or result.stderr or len(result.stdout) > 65_536:
        raise ValueError(f"LLVM reader failed {arguments[0]}: {result.stderr[:512].decode(errors='replace')}")
    return result.stdout


def _loc(source: bytes, needle: bytes, filename: str) -> str:
    """Locate the marked token using an independently specified source fragment."""
    prefix, suffix = needle.split(b"|")
    if source.count(prefix + suffix) != 1:
        raise ValueError("ambiguous source location in remarks qualification fixture")
    before = source[:source.index(prefix + suffix) + len(prefix)].decode().split("\r\n")
    return f"{{ File: {filename}, Line: {len(before)}, Column: {len(before[-1]) + 1} }}"


def _oracle(source: bytes, *, refused: bool, filename: str) -> bytes:
    def location(mark: bytes) -> str:
        return _loc(source, mark, filename)
    scale = location(b"Nat |Scale(const")
    if refused:
        rows = [("!Failure", "SpecializationRefused", "f_Bad", location(b"=> |Scale(value"), [
            ("Callee", "f_Scale", scale), ("String", _REFUSED, location(b"Scale(|value, value)"))])]
    else:
        inner, outer = location(b"=> |Scale(factor"), location(b"=> |Forward(3")
        rows = [
            ("!Missed", "SymbolicStaticArgument", "f_Forward", inner,
             [("Callee", "f_Scale", scale), ("String", _MISSED, "")]),
            ("!Passed", "Specialized", "f_Render", inner,
             [("Callee", "f_Scale", scale), ("GeneratedFrom", "f_Forward", outer), ("String", _APPLIED, "")]),
            ("!Passed", "Specialized", "f_Render", outer,
             [("Callee", "f_Forward", location(b"Nat |Forward(const")), ("String", _APPLIED, "")])]
    lines: list[str] = []
    for tag, name, function, site, args in rows:
        lines += [f"--- {tag}", f"Function: {function}", f"Name: {name}", f"DebugLoc: {site}",
                  "Pass: holdfast-static-specialization", "Args:"]
        for key, value, loc in args:
            lines.append(f"  - {key}: {value}")
            if loc:
                lines.append(f"    DebugLoc: {loc}")
        lines.append("...")
    return ("\n".join(lines) + "\n").encode()


def _observe(reader: Path, yaml: bytes, oracle: bytes, counts: set[str]) -> dict[str, object]:
    bitstream = _run(reader, ["yaml2bitstream"], yaml)
    decoded = _run(reader, ["bitstream2yaml"], bitstream)
    expected = _run(reader, ["bitstream2yaml"], _run(reader, ["yaml2bitstream"], oracle))
    if not decoded or decoded != expected:
        raise ValueError("LLVM decoded different decisions, reasons or source locations")
    rows = _run(reader, ["count", "--parser=bitstream", "--group-by=function"], bitstream).decode().splitlines()
    if not rows or rows[0] != "Function,Count" or sorted(rows[1:]) != sorted(counts):
        raise ValueError("LLVM counted different specialization decisions per function")
    return {"records": decoded.decode(), "counts": sorted(rows[1:]), "bitstream_sha256": sha256_bytes(bitstream)}


def _validate_retained(source: Path, publication: Path, *, changed: bool) -> None:
    with redirect_stdout(StringIO()), redirect_stderr(err := StringIO()):
        status = holdfast.main(["remarks-validate", str(source), str(publication)])
    if status != int(changed) or (changed and "remarks differ" not in err.getvalue()):
        raise ValueError(f"wrong validation verdict for {'changed' if changed else 'current'} source: {err.getvalue()}")


def qualify(reader: Path) -> dict[str, object]:
    with reader.open("rb") as stream:
        executable = stream.read(175_985)
    if sha256_bytes(executable) != READER_SHA256 or file_sha256(LIBRARY) != LIBRARY_SHA256:
        raise ValueError("expected the Ubuntu ARM64 LLVM 21.1.8 remark reader and library")
    with tempfile.TemporaryDirectory(prefix="holdfast-llvm-remarks-") as temp:
        directory = Path(temp)
        tool = directory / "llvm-remarkutil"
        tool.write_bytes(executable)
        tool.chmod(0o700)
        producer = compiler_trace.producer_identity()
        success = remarks.compile_remarks(SOURCE, FILENAME, producer)
        if success.gallina is None or success.error is not None:
            raise ValueError("specialization fixture failed to compile")
        forward, separator, render = success.gallina.partition("Definition f_Forward")[2].partition("Definition f_Render")
        if (not separator or "(f_Scale v_factor v_value)" not in forward or "f_Forward" in render or "f_Scale" in render
                or render.count("Corelib.Init.Nat.add") != 1 or "Corelib.Init.Nat.mul (3 :" not in render):
            raise ValueError("retained and eliminated calls do not match the actual Gallina")
        oracle = _oracle(SOURCE, refused=False, filename=FILENAME)
        observed = _observe(tool, success.yaml, oracle, {"f_Render,2", "f_Forward,1"})
        refused = remarks.compile_remarks(REFUSAL, "Gain's %π.hf", producer)
        if refused.gallina is not None or refused.error is None or refused.error.message != _REFUSED:
            raise ValueError("runtime-argument fixture failed to reach the intended refusal")
        failed = _observe(tool, refused.yaml, _oracle(REFUSAL, refused=True, filename="Gain%27s%20%25%CF%80.hf"), {"f_Bad,1"})
        _run(tool, ["yaml2bitstream"], b"--- !Passed\nPass: holdfast-static-specialization\n...\n", malformed=True)
        source = directory / FILENAME
        publication = directory / "remarks.yaml"
        source.write_bytes(SOURCE)
        publication.write_bytes(success.yaml)
        _validate_retained(source, publication, changed=False)
        source.write_bytes(SOURCE.replace(b"Forward(3,", b"Forward(4,"))
        _validate_retained(source, publication, changed=True)
        source.write_bytes(SOURCE)
        publication.write_bytes(success.yaml.replace(b"GeneratedFrom: f_Forward", b"GeneratedFrom: f_Scale"))
        _validate_retained(source, publication, changed=True)
        try:
            _observe(tool, publication.read_bytes(), oracle, {"f_Render,2", "f_Forward,1"})
        except ValueError as error:
            if "LLVM decoded different" not in str(error):
                raise
        else:
            raise ValueError("LLVM reader qualification accepted a replaced generation origin")
        if (file_sha256(tool) != READER_SHA256 or file_sha256(LIBRARY) != LIBRARY_SHA256
                or compiler_trace.producer_identity() != producer):
            raise ValueError("reader or compiler identity changed during remarks qualification")
    return {"status": "qualified", "reader_sha256": READER_SHA256, "library_sha256": LIBRARY_SHA256,
            "producer_sha256": producer, "emitted_source_sha256": sha256_bytes(SOURCE),
            "refused_source_sha256": sha256_bytes(REFUSAL), "gallina_sha256": sha256_bytes(success.gallina.encode()),
            "emitted": observed, "refused": failed, "controls": ["malformed-remark", "changed-source", "changed-origin"]}
