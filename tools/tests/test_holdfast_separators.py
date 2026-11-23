# SPDX-License-Identifier: Apache-2.0
"""Independent digit-separator values, source bindings and bounded neighbors."""

import copy
from typing import cast

import toolchain as holdfast
from tests.harness import Case, ensure, raises
from tests.test_holdfast_ast import _fixture, _literal
from tests.test_holdfast_elaborate import _NAT, Form, Node, _call, _Fixture, _type
from toolchain import (
    ast as holdfast_ast,
)
from toolchain import (
    surface as holdfast_surface,
)
from toolchain.ast import MAX_LITERAL_DIGITS, HoldFastError
from toolchain.elaborate import elaborate
from toolchain.parser import Json


def _body(gallina: str) -> str:
    return "\n".join(gallina.splitlines()[2:])


def _decimal(spelling: str) -> Form:
    def form(fixture: _Fixture) -> Node:
        start = fixture.offset
        fixture.write(spelling)
        return fixture.node("nat", start, value=spelling, suffix="")
    return form


def _pure_values_and_constants() -> None:
    source = (b"module M; public const Nat Capacity = 1_024; "
              b"public const Nat Twice(Nat value) => value * 2; "
              b"public Nat Scale(const Nat factor, Nat count) { "
              b"const Nat multiplier = Twice(factor); return count * multiplier + Capacity; } "
              b"public Nat Run(Nat count) => Scale(factor: 2_000, count: count);")
    plain = source.replace(b"1_024", b"1024").replace(b"2_000", b"2000")
    actual = holdfast.translate(source).gallina
    ensure(_body(actual) == _body(holdfast.translate(plain).gallina),
           "separators changed constants, specialization or runtime terms")
    ensure("1024" in actual and "4000" in actual,
           "separator values differ from the independently selected numbers")
    ensure(holdfast.inspect_source(source)["status"] == "ok", "separators broke compiler inspection")
    holdfast.translate(b"module M; public Nat Identity(Nat _1) => _1;")


def _pure_protocol_and_spelling() -> None:
    for newline in (b"\n", b"\r\n", b"\r"):
        source = b"// caf\xc3\xa9" + newline + b"module M; public Nat F() { return 0_001; }"
        tree = _fixture(source, _literal(source, b"0_001"))
        ensure(holdfast.translate_ast(source, tree) == holdfast.translate(source),
               "pure native consumer changed separated-literal term or provenance")
        parsed = holdfast.parse_module(source)
        function = parsed.declarations[0]
        if not isinstance(function, holdfast_ast.Function) or not isinstance(function.body.terminal, holdfast_ast.Return):
            raise TypeError("separated literal changed the function/return syntax roles")
        ensure(function.body.terminal.value.value == "0_001",
               "Python syntax normalized the original separated spelling")
        for corruption in ("normalized", "shifted", "malformed"):
            changed = copy.deepcopy(tree)
            module = cast("dict[str, object]", changed["ast"])
            function_node = cast("list[dict[str, object]]", module["declarations"])[0]
            block = cast("dict[str, object]", function_node["body"])
            terminal = cast("dict[str, object]", block["exit"])
            literal = cast("dict[str, object]", terminal["value"])
            if corruption == "normalized":
                literal["value"] = "0001"
            elif corruption == "shifted":
                start, end = cast("list[int]", literal["span"])
                literal["span"] = [start + 1, end]
            else:
                literal["value"] = "0__001"
            with raises((TypeError, ValueError, HoldFastError),
                        msg=f"accepted separated decimal {corruption} corruption"):
                holdfast.translate_ast(source, changed)


def _malformed_and_digit_limits() -> None:
    for spelling in (b"1_", b"1__0", b"1_024_", b"1_Nat", b"1_usize", b"0b1_0", b"0xA_F"):
        with raises(HoldFastError, msg=f"invalid pure decimal was accepted: {spelling!r}") as raised:
            holdfast.translate(b"module M; public Nat F() => " + spelling + b";")
        ensure(raised.exception.kind == "syntax", f"invalid decimal has wrong refusal: {spelling!r}")
    maximum = b"_".join([b"9"] * MAX_LITERAL_DIGITS)
    source = b"module M; public Nat F() { return " + maximum + b"; }"
    tree = _fixture(source, _literal(source, maximum))
    ensure(holdfast.translate_ast(source, tree) == holdfast.translate(source),
           "separators consumed the actual-digit budget")
    for native in (False, True):
        oversized = maximum + b"_9"
        source = b"module M; public Nat F() { return " + oversized + b"; }"
        with raises(HoldFastError, msg="separated decimal bypassed the digit budget") as raised:
            if native:
                holdfast.translate_ast(source, _fixture(source, _literal(source, oversized)))
            else:
                holdfast.translate(source)
        ensure(raised.exception.kind == "limit", "actual-digit overflow has wrong refusal")


def _mathematical_values_and_indices() -> None:
    fixture = _Fixture("Separators")
    fixture.constant("Capacity", _NAT, _decimal("1_024"))
    fixture.alias("Level", _type("Type", _decimal("0_0")))
    fixture.definition("Value", _NAT, (), _decimal("0_001"))
    fixture.definition("One", _type("Vec", _NAT, _decimal("0_001")), (),
                       _call("VCons", _decimal("1_024"), _call("VNil", generics=(_NAT,))))
    source, response = fixture.response()
    actual = elaborate(source, response).gallina
    ensure("1024" in actual, "mathematical separator value is not 1024")
    normalized = _Fixture("Separators")
    normalized.constant("Capacity", _NAT, _decimal("1024"))
    normalized.alias("Level", _type("Type", _decimal("00")))
    normalized.definition("Value", _NAT, (), _decimal("0001"))
    normalized.definition("One", _type("Vec", _NAT, _decimal("0001")), (),
                          _call("VCons", _decimal("1024"), _call("VNil", generics=(_NAT,))))
    ensure(_body(actual) == _body(elaborate(*normalized.response()).gallina),
           "separator normalization changed mathematical terms or dependent indices")
    changed = copy.deepcopy(response)
    for node in holdfast_surface.nodes(cast("Json", changed["ast"])):
        if node.get("kind") == "nat" and node.get("value") == "1_024":
            node["value"] = "1024"
            break
    with raises(HoldFastError, msg="mathematical consumer accepted a normalized source forgery") as raised:
        elaborate(source, changed)
    ensure(raised.exception.kind == "protocol", "normalized forged literal lost its source-protocol refusal")
    for digits, expected in ((256, None), (257, "limit")):
        bounded = _Fixture()
        bounded.definition("Wide", _NAT, (), _decimal("_".join(["9"] * digits)))
        try:
            elaborate(*bounded.response())
        except HoldFastError as error:
            ensure(error.kind == expected, "mathematical actual-digit bound differs")
        else:
            ensure(expected is None, "mathematical separated literal bypassed its digit bound")


def cases() -> list[Case]:
    return [Case("pure-values-constants-and-static-parameters", _pure_values_and_constants),
            Case("raw-spelling-native-source-binding-and-newlines", _pure_protocol_and_spelling),
            Case("malformed-neighbors-and-actual-digit-budgets", _malformed_and_digit_limits),
            Case("mathematical-values-universes-and-dependent-indices", _mathematical_values_and_indices)]
