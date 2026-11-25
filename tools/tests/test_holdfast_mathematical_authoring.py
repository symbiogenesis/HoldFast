# SPDX-License-Identifier: Apache-2.0
"""Independent original and canonical mathematical programs, edit races and refusal cases."""

import hashlib
import json
import stat
import tempfile
from contextlib import nullcontext
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from tests.test_holdfast_elaboration_cli import _invoke
from toolchain import elaboration_check, mathematical_authoring, mathematical_preview, parser
from toolchain.ast import HoldFastError
from toolchain.mathematical import Compilation

ROOT = Path(__file__).resolve().parents[2]
SOURCE = """module   Layout;
/// An orphan π.

public definition t id <t> (t Bad)=>Bad; // trailing
/// Compares 𝄞.
public definition bool Mask(u8 flags,u8 mask)=>flags /* a /* b */ c */& mask==0u8;
public lemma Check() ensures Mask(0u8,1u8)==true proof { assert Mask(0u8,1u8)==true; }
""".replace("\n", "\r\n").encode()
CANONICAL = """module Layout;

/// An orphan π.

public definition t id<t>(t Bad) => Bad; // trailing

/// Compares 𝄞.
public definition bool Mask(u8 flags, u8 mask) => flags /* a /* b */ c */ & mask == 0u8;

public lemma Check()
    ensures Mask(0u8, 1u8) == true
proof
{
    assert Mask(0u8, 1u8) == true;
}
""".encode()


def _protocol() -> None:
    source = b"module M;"
    ast = {"kind": "surface_file", "span": [0, len(source)], "declarations": []}
    for tokens in ([[0, 6], [8, 9]], [[0, 6], [7, 8]], [[0, 6], [6, 8], [8, 9]],
                   [[0, 6], [4, 6]], [[True, 6], [7, 8], [8, 9]], [[0, 6], [7, 99]]):
        publication = json.dumps({"schema": 2, "ast": ast, "tokens": tokens}).encode()
        with raises(ValueError, msg="detached mathematical token range accepted"):
            parser.decode_response(source, 0, publication, surface=True, layout=True)


def _edit_race() -> None:
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "source.hf"
        path.write_bytes(SOURCE)
        retained = Path(temp) / "result.v"
        retained.write_bytes(b"previous")
        def concurrent_edit(*_args: object) -> tuple[bytes, Compilation, Compilation]:
            path.write_bytes(b"edited during compilation")
            checked = Compilation("Demo", "candidate")
            return CANONICAL, checked, checked
        with (patch.object(parser, "cached_build", return_value=nullcontext(object())),
              patch.object(mathematical_authoring, "format_checked", side_effect=concurrent_edit)):
            code, out, err = _invoke(["elaborate", str(path), "--format", "write", "--output", str(retained)])
        ensure(code == 1 and not out and "source changed" in err
               and path.read_bytes() == b"edited during compilation" and retained.read_bytes() == b"previous",
               "stale mathematical formatting replaced an intervening edit or its output")


def _native() -> None:
    with tempfile.TemporaryDirectory() as temp, parser.cached_build(ROOT) as compiled:
        path = Path(temp) / "layout.hf"
        output = Path(temp) / "layout.v"
        path.write_bytes(SOURCE)
        output.write_bytes(b"previous")
        first = path.stat()
        code, out, err = _invoke(["fmt", str(path), "--check"])
        ensure(code == 1 and not out and "differs" in err, f"compact mathematical layout passed: {err}")
        code, out, err = _invoke(["lint", str(path)])
        ensure(code == 0 and not out and err.count("HOLDFAST102") == 1 and "member 'id'" in err and
               all(code in err for code in ("HOLDFAST100", "HOLDFAST101", "HOLDFAST105", "HOLDFAST107")),
               f"mathematical style or documentation attachment differs: {err}")
        code, out, err = _invoke(["elaborate", str(path), "--format", "write", "--deny", "HOLDFAST107",
                                  "--output", str(output)])
        ensure(code == 1 and not out and "HOLDFAST107" in err and output.read_bytes() == b"previous"
               and path.read_bytes() == SOURCE and path.stat().st_mtime_ns == first.st_mtime_ns,
               "denied lint or read-only commands changed source or output")
        code, out, err = _invoke(["elaborate", str(path), "--format", "write", "--output", str(output)])
        ensure(code == 0 and not out and path.read_bytes() == CANONICAL
               and hashlib.sha256(CANONICAL).hexdigest() in output.read_text()
               and stat.S_IMODE(path.stat().st_mode) == stat.S_IMODE(first.st_mode),
               f"formatted source, emitted provenance or file permissions differ: {path.read_bytes()!r} {err}")
        modified = path.stat().st_mtime_ns
        code, out, err = _invoke(["fmt", str(path), "--check"])
        ensure(code == 0 and not err and not out and path.stat().st_mtime_ns == modified, "canonical check wrote source")
        line = next((i, value) for i, value in enumerate(CANONICAL.decode().splitlines(), 1) if "&" in value)
        code, out, err = _invoke(["lint-preview", str(path), "--line", str(line[0]), "--column", str(line[1].index("&") + 1)])
        ensure(code == 0 and not err and mathematical_preview.validate(json.loads(out), compiled, CANONICAL) ==
               CANONICAL.replace(b"flags /* a /* b */ c */ & mask", b"(flags /* a /* b */ c */ & mask)"),
               "formatted lint coordinates selected a different mathematical operand")
        path.write_bytes(b"module Names; public record Counter(Nat Count);\n"
                         b"public Nat Value(Nat n) { let Nat Wrong = n; return Wrong; }")
        code, out, err = _invoke(["lint", str(path), "--deny", "HOLDFAST101", "--allow", "HOLDFAST102"])
        ensure(code == 1 and not out and err.count("HOLDFAST101") == 1 and "'Wrong'" in err and "'Count'" not in err,
               f"a public record field was mistaken for a local, or the local lint was lost: {err}")
        for bad in (b"module M; definition Nat Bad() => false;", b"module M; definition Nat Broken("):
            path.write_bytes(bad)
            code, out, err = _invoke(["fmt", str(path)])
            ensure(code == 1 and not out and bool(err) and path.read_bytes() == bad, "invalid mathematical input was rewritten")
        bad_proof = b"module M; public lemma Bad() ensures true==true proof{assert true==false;}"
        path.write_bytes(bad_proof)
        code, _, _ = _invoke(["fmt", str(path), "--syntax-only", "--check"])
        ensure(code == 1 and path.read_bytes() == bad_proof, "syntax-only check rewrote the proof")
        code, out, err = _invoke(["fmt", str(path), "--syntax-only"])
        ensure(code == 0 and not out and not err and path.read_bytes() ==
               b"module M;\n\npublic lemma Bad()\n    ensures true == true\nproof\n{\n    assert true == false;\n}\n",
               f"syntax-only formatting lost the broken proof or refused it: {err}")
        code, _, _ = _invoke(["elaborate", str(path)])
        ensure(code == 1, "layout granted semantic acceptance to a broken proof")
        bad_syntax = b"module M; definition Nat Broken("
        path.write_bytes(bad_syntax)
        code, _, _ = _invoke(["fmt", str(path), "--syntax-only"])
        ensure(code == 1 and path.read_bytes() == bad_syntax, "syntax-only mode rewrote malformed input")


def _ref_contract_redundancy() -> None:
    source = b"""module RefContractLint;

/// Writes one byte through a mutable view.
public Unit WriteByte(ref Span<byte> pkt, byte value)
    effects writes(pkt)
    requires pkt.CanRead && pkt.CanWrite && pkt.Length >= 8
    ensures pkt.Base == old(pkt.Base)
        && pkt.Length == old(pkt.Length)
        && pkt.CanRead
        && pkt.CanWrite
        && pkt[0] == value
{
    pkt[0] = value;
}

/// Checks metadata through a read-only view.
public Unit Inspect(in Span<byte> input)
    requires input.CanRead
    ensures input.Base == old(input.Base) && input.CanRead
{
    return ();
}

/// Retains the slot descriptor.
public Unit KeepSlots(ref Slots<byte, 4> slots)
    ensures old(slots).Capacity == slots.Capacity
{
    return ();
}

/// Reports whether the view is writable.
public bool WriteAccess(ref Span<byte> pkt)
    ensures result ==> pkt.CanWrite
{
    return pkt.CanWrite;
}

/// States a permission established by a Boolean comparison.
public Unit KeepReadAccess(ref Span<byte> pkt)
    requires pkt.CanRead == true
    ensures pkt.CanRead
{
    return ();
}
"""
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "contracts.hf"
        path.write_bytes(source)
        before = path.stat().st_mtime_ns
        command = ["lint", str(path), "--allow", "HOLDFAST103"]
        code, out, err = _invoke(command)
        sites = ((7, 13), (8, 12), (9, 12), (10, 12), (19, 13), (19, 46), (26, 13), (41, 13))
        expected = [f"{path}:{line}:{column}: warning HOLDFAST109:" for line, column in sites]
        warnings = err.splitlines()
        ensure(code == 0 and not out and len(warnings) == len(expected)
               and all(warning.startswith(prefix) for warning, prefix in zip(warnings, expected, strict=True)),
               f"mathematical lint did not locate exactly the redundant ref conjuncts: {err}")
        code, out, err = _invoke([*command, "--deny", "HOLDFAST109"])
        ensure(code == 1 and not out and err.count("error HOLDFAST109:") == len(sites),
               f"denied ref-contract lint did not fail: {err}")
        code, out, err = _invoke([*command, "--allow", "HOLDFAST109"])
        ensure(code == 0 and not out and not err, f"allowed ref-contract lint was reported: {err}")
        ensure(path.read_bytes() == source and path.stat().st_mtime_ns == before, "contract lint rewrote source")


def _proofs() -> None:
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "layout.hf"
        for snapshot in (SOURCE, CANONICAL):
            path.write_bytes(snapshot)
            receipt = elaboration_check.check_arithmetic(ROOT, path)
            ensure(receipt["status"] == "kernel-checked" and receipt["source_sha256"] == hashlib.sha256(snapshot).hexdigest(),
                   "mask proof failed independent source-bound replay")


def _accepted_corpus() -> None:
    fixtures = elaboration_check.fixtures((ROOT / elaboration_check.EXAMPLE).read_bytes(),
                                          (ROOT / elaboration_check.WORD_COUNT_EXAMPLE).read_bytes())
    with parser.cached_build(ROOT) as compiled:
        for fixture in fixtures:
            if not fixture.pure and fixture.expected == "accepted":
                try:
                    mathematical_authoring.format_checked(compiled, fixture.source)
                except (HoldFastError, ValueError, RuntimeError) as error:
                    raise AssertionError(f"{fixture.name}: {error}") from error


def cases() -> list[Case]:
    return [Case("reject detached mathematical lexical ranges", _protocol),
            Case("mathematical source rewrite refuses concurrent edit", _edit_race),
            Case("mathematical canonical bytes, diagnostics and preview lifecycle", _native, lane="toolchain"),
            Case("ref descriptor redundancy reports only implied conjuncts", _ref_contract_redundancy, lane="guest"),
            Case("mathematical canonical and original proofs replay", _proofs, slow=True, lane="toolchain"),
            Case("format and recheck the accepted mathematical replay corpus", _accepted_corpus,
                 slow=True, lane="toolchain")]
