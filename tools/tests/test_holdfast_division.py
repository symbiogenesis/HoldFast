# SPDX-License-Identifier: Apache-2.0
"""Independent values, terms and source-bound controls for pure Nat division."""

import copy
import hashlib
from typing import cast
from unittest.mock import patch

import toolchain as holdfast
from tests.harness import Case, ensure, raises
from toolchain import ast as holdfast_ast
from toolchain.authoring import format_source

_NAT = "Corelib.Init.Datatypes.nat"
_BASE = b"module M; public Nat Id(Nat value) => value;"


def _refuses(source: str, kind: str, fragment: str = "") -> holdfast.HoldFastError:
    try:
        holdfast.translate(source.encode())
    except holdfast.HoldFastError as error:
        ensure(error.kind == kind and fragment in error.message,
               f"expected {kind}/{fragment!r}, got {error.kind}: {error.message}")
        return error
    raise AssertionError("accepted refused division source")


def _values() -> None:
    cases = {"17 / 5": 3, "17 % 5": 2, "0 / 5": 0, "0 % 5": 0,
             "5 / 8": 0, "5 % 8": 5, "5 / 5": 1, "5 % 5": 0,
             "17 / 1": 17, "17 % 1": 0,
             "20 / 3 * 2": 12, "20 / (3 * 2)": 3,
             "20 % 6 * 2": 4, "20 % (6 * 2)": 8,
             "30 / 4 % 3": 1, "30 % 4 / 2": 1,
             "2 + 19 % 6 * 3": 5, "32 / 4 / 2": 4, "32 / (4 / 2)": 16,
             "1_024 / 1_00": 10, "1_024 % 1_00": 24,
             "Id(value: 17) / Id(value: 5)": 3,
             "Id(value: 17) % Id(value: 5)": 2,
             "8// division follows this line comment\n/2": 4}
    for expression, expected in cases.items():
        ensure(holdfast.evaluate(_BASE, expression, "Nat") == holdfast.StaticEvaluation("Nat", expected),
               f"wrong quotient/remainder for {expression}")
    ensure(holdfast.evaluate(_BASE, "17 / 5 == 3 && 17 % 5 != 0", "bool").value is True,
           "division did not compose with Boolean comparisons")


def _terms() -> None:
    cases = (("a / b", "(Corelib.Init.Nat.div v_a v_b)"),
             ("a % b", "(Corelib.Init.Nat.modulo v_a v_b)"),
             ("a / b * c", "(Corelib.Init.Nat.mul (Corelib.Init.Nat.div v_a v_b) v_c)"),
             ("a % b * c", "(Corelib.Init.Nat.mul (Corelib.Init.Nat.modulo v_a v_b) v_c)"),
             ("a * b / c", "(Corelib.Init.Nat.div (Corelib.Init.Nat.mul v_a v_b) v_c)"),
             ("a / b % c", "(Corelib.Init.Nat.modulo (Corelib.Init.Nat.div v_a v_b) v_c)"),
             ("a / (b * c)", "(Corelib.Init.Nat.div v_a (Corelib.Init.Nat.mul v_b v_c))"))
    for expression, expected in cases:
        source = ("module Terms; public Nat F(Nat a, Nat b, Nat c) { "
                  "if (b != 0 && c != 0 && b * c != 0) { return " + expression + "; } else { return 0; } }").encode()
        ensure(f" then {expected} else " in holdfast.translate(source).gallina,
               f"wrong emitted multiplicative grouping for {expression}")
    source = (b"module Calls; public Nat Left() => 17; public Nat Right() => 5; "
              b"public Nat Divide() => Left() / Right(); public Nat Remain() => Left() % Right();")
    emitted = holdfast.translate(source).gallina
    ensure("(Corelib.Init.Nat.div f_Left f_Right)" in emitted
           and "(Corelib.Init.Nat.modulo f_Left f_Right)" in emitted,
           "division emission changed operand order or duplicated calls")


def _constants_and_static_parameters() -> None:
    source = (b"module Static; public const Nat Groups = 17 / 5; public const Nat Tail = 17 % 5; "
              b"public Nat Bucket(const Nat width, Nat value) { "
              b"const Nat step = width % 3 + 1; return value / step; } "
              b"public Nat Forward(const Nat width, Nat value) => Bucket(width: width, value: value); "
              b"public Nat F(Nat value) => Forward(width: 5, value: value);")
    for expression, expected in (("Groups", 3), ("Tail", 2), ("F(17)", 5),
                                 ("Forward(width: 0, value: 17)", 17)):
        ensure(holdfast.evaluate(source, expression, "Nat").value == expected,
               f"constant or static specialization changed {expression}")
    emitted = holdfast.translate(source).gallina
    for name, expected in (("Groups", 3), ("Tail", 2)):
        ensure(f"Definition c_{name} : {_NAT} :=\n  ({expected} : {_NAT})." in emitted,
               f"constant {name} did not normalize to its independent value")
    facts = holdfast.inspect_source(source)
    ensure(bool(facts["symbols"]) and bool(facts["occurrences"]),
           "division lost compiler facts for editor consumers")


def _semantic_and_syntax_refusals() -> None:
    for operation in ("/", "%"):
        for expression in (f"true {operation} 2", f"1 {operation} false", f"true {operation} false"):
            _refuses(f"module M; public Nat F() => {expression};", "type", f"'{operation}'")
        _refuses(f"module M; public bool F() => 8 {operation} 3;", "type", "returns Nat")
        _refuses(f"module M; public Nat F() => missing {operation} 0;", "name", "unbound")
        for expression in (f"17 {operation} 0", f"0 {operation} 0", f"17 {operation} runtime"):
            _refuses(f"module M; public Nat F(Nat runtime) => {expression};", "type", "nonzero divisor")
        _refuses(f"module M; public const Nat Wrong = 17 {operation} 0;", "type", "nonzero divisor")
        _refuses("module M; public Nat F(Nat value) { if (value == 0) "
                 f"{{ return 1 {operation} value; }} else {{ return 0; }} }}", "type", "nonzero divisor")
        for expression in (f"runtime {operation} 1", f"0 {operation} (runtime + 1)"):
            _refuses("module M; public Nat F(Nat runtime) { const Nat Wrong = "
                     + expression + "; return Wrong; }", "unsupported", "runtime binding 'runtime'")
        _refuses("module M; public bool F(Nat runtime) { "
                 f"const bool Wrong = false && (runtime {operation} 1 == 0); return Wrong; }}",
                 "unsupported", "runtime binding 'runtime'")
        for expression in (f"{operation} 2", f"2 {operation}", f"2 {operation} {operation} 3",
                           f"2 {operation}= 3", f"2 {operation} * 3"):
            _refuses(f"module M; public Nat F() => {expression};", "syntax")
        source = f"module M;\r\n// supplementary comment: \U0001f680\r\npublic Nat F() => true {operation} 2;"
        error = _refuses(source, "type", f"'{operation}'")
        ensure((error.line, error.column) == (3, 24), "operator diagnostic lost original Unicode/CRLF site")
    _refuses("module M; public Nat F() => 8 // comment hides the apparent operand / 2;", "syntax")
    _refuses("module M; public Nat F() => 1" + "/1" * 64 + ";", "limit")


def _short_circuit_premises() -> None:
    source = (b"module M; public bool HasGroup(Nat count, Nat size) => size != 0 && count / size > 0; "
              b"public bool IsWholeOrZero(Nat count, Nat size) => size == 0 || count % size == 0;")
    for expression, expected in (("HasGroup(17, 0)", False), ("HasGroup(17, 5)", True),
                                 ("IsWholeOrZero(17, 0)", True), ("IsWholeOrZero(17, 5)", False)):
        ensure(holdfast.evaluate(source, expression, "bool").value is expected,
               f"guarded divisor produced the wrong value for {expression}")
    _refuses("module M; public bool F(Nat size) => size != 0 || 17 / size > 0;", "type", "nonzero divisor")


def _guarded_static_specialization() -> None:
    source = (b"module StaticGuard; public Nat Read(Nat size) => size; "
              b"public Nat Quotient(const Nat size) { "
              b"let nonzero = Read(size) != 0; if (!nonzero) { return 0; } else { "
              b"const Nat groupCount = 17 / Read(size); return groupCount; } } "
              b"public Nat Empty() => Quotient(0); public Nat Nonempty() => Quotient(5); "
              b"public Nat Choose(const Nat size, bool flag) { "
              b"if (flag || size != 0) { return 11; } else { return 7; } } "
              b"public Nat Dynamic(bool flag) => Choose(0, flag);")
    for expression, expected in (("Empty()", 0), ("Nonempty()", 3), ("Dynamic(true)", 11), ("Dynamic(false)", 7)):
        ensure(holdfast.evaluate(source, expression, "Nat").value == expected,
               f"guarded specialization changed the result of {expression}")
    emitted = holdfast.translate(source).gallina
    empty, rest = emitted.split("Definition f_Empty")[1].split("Definition f_Nonempty", 1)
    dynamic = rest.split("Definition f_Dynamic")[1]
    ensure("Corelib.Init.Nat.div" not in empty and f"(0 : {_NAT})" in empty,
           "specializing a zero divisor kept the unreachable local constant")
    ensure(f"then (11 : {_NAT}) else (7 : {_NAT})" in dynamic,
           "specialization decided a branch that depended on a runtime argument")


def _numeric_and_work_limits() -> None:
    maximum = "9" * holdfast.MAX_LITERAL_DIGITS
    ensure(holdfast.evaluate(_BASE, maximum + " / 1", "Nat").value == int(maximum),
           "division narrowed the existing numeric range")
    ensure(holdfast.evaluate(_BASE, maximum + " % (" + maximum + ")", "Nat").value == 0,
           "remainder narrowed the existing numeric range")
    for expression in (f"({maximum} * 2) / 2", f"({maximum} * 2) % 2",
                       f"0 / ({maximum} * 2)", f"0 % ({maximum} * 2)"):
        with raises(holdfast.HoldFastError, msg="division hid a previously overflowing operand") as raised:
            holdfast.evaluate(_BASE, expression, "Nat")
        ensure(raised.exception.kind == "limit", "division changed an operand's numeric-limit refusal")
    declarations = ["module Work; public Nat F0(Nat value) => value;"]
    declarations.extend(f"public Nat F{index}(Nat value) => F{index - 1}(value) + F{index - 1}(value);"
                        for index in range(1, 16))
    source = " ".join(declarations).encode()
    for expression in ("F15(0) / 1", "F15(0) % 1", "0 / (F15(0) + 1)", "0 % (F15(0) + 1)"):
        with raises(holdfast.HoldFastError, msg="division/remainder skipped an expensive operand") as raised:
            holdfast.evaluate(source, expression, "Nat")
        ensure(raised.exception.kind == "limit", "operands changed the static work-limit refusal")
    for expression, fragment in ((f"({maximum} * 2) / (F15(0) + 1)", "constant result exceeds"),
                                 (f"F15(0) / ({maximum} * 2)", "work or nesting budget")):
        with raises(holdfast.HoldFastError, msg="costly division operands escaped static limits") as raised:
            holdfast.evaluate(source, expression, "Nat")
        error = raised.exception
        ensure(error.kind == "limit" and fragment in error.message,
               "division evaluated operands in the wrong source order")


def _node(kind: str, start: int, end: int, **fields: object) -> dict[str, object]:
    return {"kind": kind, "span": [start, end], **fields}


def _name(text: str, start: int) -> dict[str, object]:
    return {"text": text, "span": [start, start + len(text)]}


def _native_fixture(source: bytes, operator: str, *, left: bytes = b"17", right: bytes = b"5"
                    ) -> tuple[dict[str, object], dict[str, object]]:
    """Construct a nullary block and operator from independently located source bytes."""
    module = source.index(b"module")
    declaration = source.index(b"public")
    result = source.index(b"Nat", declaration)
    function_name = source.index(b"F()", result)
    brace = source.index(b"{", function_name)
    returned = source.index(b"return", brace)
    left_start = source.index(left, returned)
    operator_start = source.index(operator.encode(), left_start + len(left))
    right_start = source.index(right, operator_start + 1)
    terminal_end = source.index(b";", right_start) + 1
    end = source.index(b"}", terminal_end) + 1
    expression = _node("binary", left_start, right_start + len(right),
                       operator=_name(operator, operator_start),
                       left=_node("nat", left_start, left_start + len(left), value=left.decode()),
                       right=_node("nat", right_start, right_start + len(right), value=right.decode()))
    function = _node("function", declaration, end, name=_name("F", function_name),
                     result=_node("type", result, result + 3, name="Nat"), parameters=[],
                     body=_node("block", brace, end, bindings=[],
                                exit=_node("return", returned, terminal_end, value=expression)))
    tree: dict[str, object] = {
        "schema": 1, "source_sha256": hashlib.sha256(source).hexdigest(),
        "ast": _node("file", module, end, name=_name("M", module + 7), declarations=[function])}
    return tree, expression


def _native_source_binding() -> None:
    for operation, target in (("/", "div"), ("%", "modulo")):
        for newline in (b"\n", b"\r\n", b"\r"):
            source = (b"// caf\xc3\xa9" + newline + b"module M;" + newline + b"public Nat F() {" + newline
                      + b" return 17 " + operation.encode() + b" // operand comment" + newline
                      + b" 5;" + newline + b"}" + newline + b"// tail")
            tree, raw_expression = _native_fixture(source, operation)
            decoded = holdfast_ast.decode(source, tree)
            declaration = decoded.declarations[0]
            ensure(isinstance(declaration, holdfast_ast.Function), "native fixture lost its function")
            if not isinstance(declaration, holdfast_ast.Function):
                raise TypeError("native fixture lost its function")
            terminal = declaration.body.terminal
            ensure(isinstance(terminal, holdfast_ast.Return), "native fixture lost its return")
            if not isinstance(terminal, holdfast_ast.Return):
                raise TypeError("native fixture lost its return")
            ensure(terminal.value.value == operation and terminal.value.site == holdfast_ast.Site(4, 12),
                   "native division lost operator spelling or original newline coordinates")
            with patch.object(holdfast, "_tokens", side_effect=AssertionError("Python syntax fallback")):
                emitted = holdfast.translate_ast(source, tree).gallina
            ensure(f"(Corelib.Init.Nat.{target} (17 : {_NAT}) (5 : {_NAT}))" in emitted,
                   "native division emitted the wrong operation or source operands")
            for mutation in ("operator", "missing-right", "extra-field", "operator-span"):
                changed = copy.deepcopy(raw_expression)
                if mutation == "operator":
                    changed["operator"] = _name("%" if operation == "/" else "/",
                                                source.index(operation.encode(), source.index(b"17")))
                elif mutation == "missing-right":
                    del changed["right"]
                elif mutation == "extra-field":
                    changed["ignored"] = _node("nat", 0, 1, value="0")
                else:
                    changed["operator"] = _name(operation, source.index(b"// operand") + 1)
                changed_tree, _ = _native_fixture(source, operation)
                root = cast("dict[str, object]", changed_tree["ast"])
                declarations = cast("list[dict[str, object]]", root["declarations"])
                body = cast("dict[str, object]", declarations[0]["body"])
                raw_terminal = cast("dict[str, object]", body["exit"])
                raw_terminal["value"] = changed
                _refuses_native(source, changed_tree)
        for source_expression in (f"17 {operation} + 5", f"17 {operation}= 5",
                                  f"17 * 3 {operation} 5", f"17 {operation} 5 * 2"):
            source = ("module M; public Nat F() { return " + source_expression + "; }").encode()
            tree, _ = _native_fixture(source, operation)
            _refuses_native(source, tree)


def _refuses_native(source: bytes, tree: dict[str, object]) -> None:
    try:
        with patch.object(holdfast, "_tokens", side_effect=AssertionError("Python syntax fallback")):
            holdfast.translate_ast(source, tree)
    except (TypeError, ValueError):
        return
    raise AssertionError("native division accepted omitted, substituted or extra source tokens")


def _formatting() -> None:
    source = (b"module M;\r\n/// Quotient and remainder.\r\n"
              b"public Nat F(Nat count,Nat width)=>count/(width+1)%3*2;")
    expected = (b"module M;\n\n/// Quotient and remainder.\n"
                b"public Nat F(Nat count, Nat width) => count / (width + 1) % 3 * 2;\n")
    original = bytes(source)
    ensure(format_source(source) == expected, "division/remainder spacing changed canonical bytes")
    ensure(format_source(expected) == expected and source == original,
           "division formatting was not source-preserving and idempotent")
    ensure(holdfast.translate(source).gallina.splitlines()[2:] == holdfast.translate(expected).gallina.splitlines()[2:],
           "division formatting changed emitted terms")
    for expression in (b"count / // quotient\n(width + 1)", b"count // dividend\n/ (width + 1)",
                       b"count % // remainder\n(width + 1)", b"count // dividend\n% (width + 1)"):
        commented = b"module M; public Nat F(Nat count, Nat width) => " + expression + b";"
        formatted = format_source(commented)
        ensure(format_source(formatted) == formatted, "division comment formatting did not stabilize")
        ensure(holdfast.translate(commented).gallina.splitlines()[2:] == holdfast.translate(formatted).gallina.splitlines()[2:],
               "division comment formatting changed interpretation")


def cases() -> list[Case]:
    return [Case("natural-division-independent-values", _values),
            Case("natural-division-exact-terms-and-precedence", _terms),
            Case("natural-division-constants-static-parameters-and-facts", _constants_and_static_parameters),
            Case("natural-division-semantic-and-syntax-refusals", _semantic_and_syntax_refusals),
            Case("natural-division-short-circuit-premises", _short_circuit_premises),
            Case("natural-division-guarded-static-specialization", _guarded_static_specialization),
            Case("natural-division-numeric-work-limits-and-evaluation-order", _numeric_and_work_limits),
            Case("natural-division-independent-native-ast-source-binding", _native_source_binding),
            Case("natural-division-formatting-comments-and-source-preservation", _formatting)]
