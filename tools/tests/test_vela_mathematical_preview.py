# SPDX-License-Identifier: Apache-2.0
"""Independent byte, operator, stale-edit and kernel controls for VELA107."""

import hashlib
import json
import tempfile
from collections.abc import Callable
from contextlib import nullcontext
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure
from tests.test_vela_elaborate import _binary, _Fixture, _group, _int_lit, _type, _variable
from tests.test_vela_elaboration_cli import _invoke
from toolchain import VelaError, elaboration_check, mathematical_preview, parser

ROOT = Path(__file__).resolve().parents[2]
SOURCE = """module Bits;
/// Masks café.
public definition bool Compare(u8 flags, u8 mask) =>
    /* π */ flags /* inside */ & // retain this comment
    mask == flags | mask;
public definition bool Odd(u8 flags) => 1u8 == flags ^ 0u8;
public lemma Answers()
    ensures Compare(3u8, 3u8) == true
    ensures Compare(3u8, 1u8) == false
    ensures Odd(1u8) == true
    ensures Odd(0u8) == false
    proof {
        assert Compare(3u8, 3u8) == true;
        assert Compare(3u8, 1u8) == false;
        assert Odd(1u8) == true;
        assert Odd(0u8) == false;
    }
""".replace("\n", "\r\n").encode()
LEFT = b"flags /* inside */ & // retain this comment\r\n    mask"


def _refuses(action: Callable[[], object], message: str) -> None:
    try:
        action()
    except (ValueError, TypeError, VelaError) as error:
        diagnostic = f"{error.kind}: {error}" if isinstance(error, VelaError) else str(error)
        ensure(message in diagnostic, f"expected {message!r}, got {diagnostic}")
    else:
        raise AssertionError("a refused mathematical preview was accepted")


def _site(source: bytes, token: bytes) -> tuple[int, int]:
    before = source[:source.index(token)].decode().split("\r\n")
    return len(before), len(before[-1]) + 1


def _host_preview() -> None:
    def fixture(*, grouped: bool) -> tuple[bytes, object]:
        authored = _Fixture("Preview")
        operand = _binary("&", _variable("flags"), _variable("mask"))
        authored.definition("Test", _type("bool"), (("flags", _type("u8")), ("mask", _type("u8"))),
                            _binary("==", _group(operand) if grouped else operand, _int_lit("0", "u8")))
        return authored.response()
    source, original = fixture(grouped=False)
    expected, grouped = fixture(grouped=True)
    trees = {source: original, expected: grouped}
    compiled = parser.Build(ROOT, ROOT / "README.md", {})
    prefix = source[:source.index(b"&")].decode().split("\n")
    line, column = len(prefix), len(prefix[-1]) + 1
    with (patch.object(parser, "parse_source", side_effect=lambda _build, data, **_kwargs: trees[data]),
          patch.object(mathematical_preview, "_producer", return_value={"version": "pinned"}) as producer):
        preview = mathematical_preview.preview(compiled, source, line, column)
        ensure(mathematical_preview.validate(preview, compiled, source) == expected, "wrong retained grouping")
        for changed in ({"span": [0, 1]}, {"replacement": "true"}, {"candidate_sha256": "0" * 64},
                        {"unexpected": 1}, {"schema": True}, {"producer": {"version": "other"}}):
            _refuses(lambda changed=changed: mathematical_preview.validate(preview | changed, compiled, source),
                     "stale or changed")
        producer.side_effect = [{"version": "old"}, {"version": "new"}]
        _refuses(lambda: mathematical_preview.preview(compiled, source, line, column), "producer changed")
    with (tempfile.TemporaryDirectory() as tmp,
          patch.object(parser, "parse_source", side_effect=lambda _build, data, **_kwargs: trees[data]),
          patch.object(mathematical_preview, "compiler_dependency_hashes", return_value={})):
        runtime = Path(tmp) / "ocamlrun"
        def build() -> parser.Build:
            digest = hashlib.sha256(runtime.read_bytes()).hexdigest()
            return parser.Build(ROOT, compiled.executable, {"toolchain": {"binary_sha256": {"ocamlrun": digest}}})
        with patch.object(parser, "bytecode_interpreter", return_value=runtime):
            runtime.write_bytes(b"first runtime")
            original_build = build()
            retained = mathematical_preview.preview(original_build, source, line, column)
            runtime.write_bytes(b"second runtime")
            _refuses(lambda: mathematical_preview.validate(retained, original_build, source), "interpreter differs")
            _refuses(lambda: mathematical_preview.validate(retained, build(), source), "stale or changed")
    with (tempfile.TemporaryDirectory() as tmp,
          patch.object(parser, "cached_build", return_value=nullcontext(compiled))):
        path = Path(tmp) / "preview.vela"
        path.write_bytes(source)
        with patch.object(parser, "read_source", side_effect=[source, expected]), patch.object(
                mathematical_preview, "preview", return_value=preview):
            code, out, err = _invoke(["lint-preview", str(path), "--line", str(line), "--column", str(column)])
        ensure(code == 1 and not out and "source changed" in err and path.read_bytes() == source,
               "CLI published a preview following a concurrent edit")


def _native_edits() -> None:
    with parser.cached_build(ROOT) as compiled, tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "input.vela"
        path.write_bytes(SOURCE)
        modified = path.stat().st_mtime_ns
        for operand, operator in ((LEFT, b"&"), (b"flags | mask", b"|"), (b"flags ^ 0u8", b"^")):
            line, column = _site(SOURCE, operator)
            code, out, err = _invoke(["lint-preview", str(path), "--line", str(line), "--column", str(column)])
            ensure(code == 0 and not err, f"native precedence preview failed: {err}")
            preview = json.loads(out)
            ensure(preview["producer"]["ocamlrun_sha256"] ==
                   hashlib.sha256(parser.bytecode_interpreter(compiled.executable).read_bytes()).hexdigest(),
                   "preview omits the OCaml runtime selected by the parser executable")
            candidate = SOURCE.replace(operand, b"(" + operand + b")", 1)
            start = SOURCE.index(operand)
            ensure(preview["span"] == [start, start + len(operand)] and
                   preview["candidate_sha256"] == hashlib.sha256(candidate).hexdigest() and
                   mathematical_preview.validate(preview, compiled, SOURCE) == candidate,
                   "grouping changed comments, outside bytes, or the selected operand")
            _refuses(lambda candidate=candidate, operator=operator:
                     mathematical_preview.preview(compiled, candidate, *_site(candidate, operator)),
                     "reported VELA107")
        ensure(path.stat().st_mtime_ns == modified and path.read_bytes() == SOURCE, "CLI rewrote its source")
        _refuses(lambda: mathematical_preview.validate(preview, compiled, SOURCE + b"// edit"), "stale or changed")
        _refuses(lambda: mathematical_preview.preview(compiled, SOURCE, *_site(SOURCE, b"==")), "reported VELA107")
        _refuses(lambda: mathematical_preview.preview(compiled, SOURCE + b"definition Nat Bad() => true;",
                                                       *_site(SOURCE, b"&")), "type")


def _kernel_replay() -> None:
    with parser.cached_build(ROOT) as compiled:
        candidate = SOURCE
        for token in (b"&", b"|", b"^"):
            edit = mathematical_preview.preview(compiled, candidate, *_site(candidate, token))
            candidate = mathematical_preview.validate(edit, compiled, candidate)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "bits.vela"
        for source in (SOURCE, candidate):
            path.write_bytes(source)
            result = elaboration_check.check_arithmetic(ROOT, path)
            ensure(result["source_sha256"] == hashlib.sha256(source).hexdigest()
                   and result["status"] == "kernel-checked", "independent bitwise observations failed kernel replay")


def cases() -> list[Case]:
    return [Case("checked mathematical grouping and retained preview integrity", _host_preview),
            Case("native precedence previews preserve UTF-8 comments and CRLF", _native_edits, lane="toolchain"),
            Case("original and grouped independent bitwise outcomes replay", _kernel_replay, slow=True, lane="toolchain")]
