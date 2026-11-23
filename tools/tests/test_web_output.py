# SPDX-License-Identifier: Apache-2.0
"""Independent Boolean web-export refusals and publication controls."""

import json
import tempfile
from collections.abc import Callable
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from toolchain import HoldFastError, web_output


def _refuses(action: Callable[[], object], message: str) -> None:
    with raises((HoldFastError, ValueError), msg=f"missing refusal for {message}") as raised:
        action()
    error = raised.exception
    ensure(message in str(error), f"wrong refusal: {error}")


def _rows() -> None:
    correct = [["00", False], ["01", True], ["10", False], ["11", False]]
    equations, results = web_output._equations(json.dumps(correct).encode(), "Example.f_Select", 2)
    ensure(results == [False, True, False, False] and
           "Example.f_Select false true = true := eq_refl." in equations and
           "Example.f_Select true false = false := eq_refl." in equations, "swapped inputs or observations")
    for rows, reason in ((correct[:-1], "incomplete"), ([*correct, correct[0]], "oversized"),
                         (correct[::-1], "input tuple"), ([correct[1], *correct[1:]], "input tuple"),
                         ([["00", 0], *correct[1:]], "invalid observation"),
                         ([["00", None], *correct[1:]], "invalid observation")):
        _refuses(lambda rows=rows: web_output._equations(json.dumps(rows).encode(), "Example.f_Select", 2), reason)


def _source_boundary() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "source.hf"
        output = Path(tmp) / "result.mjs"
        output.write_bytes(b"previous")
        huge = "x"
        for _ in range(7):
            huge = f"({huge} && {huge})"
        for body, name, reason in (
            ("public Nat F(Nat x) => x;", "F", "primitive bool"),
            ("public const bool F() => true;", "F", "ordinary function"),
            ("public bool F(const bool x) => x;", "F", "ordinary function"),
            ("public bool F(bool x) { let y = x; return y; }", "F", "single return"),
            ("public bool F(bool x) { if (x) { return true; } else { return false; } }", "F", "single return"),
            ("public const bool X = true; public bool F() => X;", "F", "only Boolean"),
            ("public bool G() => true; public bool F() => G();", "F", "only Boolean"),
            ("public bool F() => 2 < 3;", "F", "only Boolean"),
            ("public bool F(bool a, bool b, bool c, bool d, bool e, bool f, bool g, bool h, bool i) => a;",
             "F", "8 Boolean parameters"),
            (f"public bool F(bool x) => {huge};", "F", "128 nodes"),
            ("public bool F() => false;", "Missing", "declared public function"),
            ("public const bool X = true;", "X", "declared public function"),
            ("public bool F() => true; public Nat Invalid() => false;", "F", "return"),
        ):
            source.write_text(f"module W; {body}", encoding="ascii")
            with patch.object(web_output, "_qualify", side_effect=AssertionError("unsupported input reached Node")):
                _refuses(lambda name=name: web_output.publish(source, name, output), reason)
            ensure(output.read_bytes() == b"previous", "refusal replaced a previous module")


def _publication() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "source.hf"
        output = Path(tmp) / "result.mjs"
        original = b"module W; public bool F(bool x) => x;"
        source.write_bytes(original)
        _refuses(lambda: web_output.publish(source, "F", source), "aliases")
        hardlink = Path(tmp) / "alias.mjs"
        hardlink.hardlink_to(source)
        _refuses(lambda: web_output.publish(source, "F", hardlink), "aliases")
        ensure(source.read_bytes() == original, "alias check rewrote the source")
        output.write_bytes(b"previous")

        def change_source(*_args: object) -> list[bool]:
            source.write_bytes(original + b"// changed")
            return [False, True]

        with patch.object(web_output, "_qualify", side_effect=change_source):
            _refuses(lambda: web_output.publish(source, "F", output), "changed during qualification")
        ensure(output.read_bytes() == b"previous" and list(Path(tmp).glob("*.tmp")) == [],
               "concurrent edit left an obsolete output or pending file")


def cases() -> list[Case]:
    return [Case("complete ordered primitive observations", _rows),
            Case("closed Boolean function selection and budgets", _source_boundary),
            Case("exact-source atomic publication", _publication)]
