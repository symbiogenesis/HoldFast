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
from tests.test_vela_elaboration_cli import _invoke
from toolchain import elaboration_check, mathematical_authoring, mathematical_preview, parser
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
        path = Path(temp) / "source.vela"
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
        path = Path(temp) / "layout.vela"
        output = Path(temp) / "layout.v"
        path.write_bytes(SOURCE)
        output.write_bytes(b"previous")
        first = path.stat()
        code, out, err = _invoke(["fmt", str(path), "--check"])
        ensure(code == 1 and not out and "differs" in err, f"compact mathematical layout passed: {err}")
        code, out, err = _invoke(["lint", str(path)])
        ensure(code == 0 and not out and err.count("VELA102") == 1 and "member 'id'" in err and
               all(code in err for code in ("VELA100", "VELA101", "VELA105", "VELA107")),
               f"mathematical style or documentation attachment differs: {err}")
        code, out, err = _invoke(["elaborate", str(path), "--format", "write", "--deny", "VELA107",
                                  "--output", str(output)])
        ensure(code == 1 and not out and "VELA107" in err and output.read_bytes() == b"previous"
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
        code, out, err = _invoke(["lint", str(path), "--deny", "VELA101", "--allow", "VELA102"])
        ensure(code == 1 and not out and err.count("VELA101") == 1 and "'Wrong'" in err and "'Count'" not in err,
               f"a public record field was mistaken for a local, or the local lint was lost: {err}")
        for bad in (b"module M; definition Nat Bad() => false;", b"module M; definition Nat Broken("):
            path.write_bytes(bad)
            code, out, err = _invoke(["fmt", str(path)])
            ensure(code == 1 and not out and bool(err) and path.read_bytes() == bad, "invalid mathematical input was rewritten")


def _proofs() -> None:
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / "layout.vela"
        for snapshot in (SOURCE, CANONICAL):
            path.write_bytes(snapshot)
            receipt = elaboration_check.check_arithmetic(ROOT, path)
            ensure(receipt["status"] == "kernel-checked" and receipt["source_sha256"] == hashlib.sha256(snapshot).hexdigest(),
                   "mask proof failed independent source-bound replay")


def cases() -> list[Case]:
    return [Case("reject detached mathematical lexical ranges", _protocol),
            Case("mathematical source rewrite refuses concurrent edit", _edit_race),
            Case("mathematical canonical bytes, diagnostics and preview lifecycle", _native, lane="toolchain"),
            Case("mathematical canonical and original proofs replay", _proofs, slow=True, lane="toolchain")]
