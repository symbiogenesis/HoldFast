# SPDX-License-Identifier: Apache-2.0
"""Independent syntax-word refusals at the mathematical consumer boundary."""

import copy
from typing import cast

from tests.harness import Case, ensure, raises
from tests.test_holdfast_elaborate import (
    _NAT,
    Form,
    Node,
    _assert,
    _binary,
    _contract,
    _Fixture,
    _function_type,
    _lambda,
    _natural,
    _type,
    _type_constraint,
    _variable,
)
from toolchain.ast import HoldFastError
from toolchain.elaborate import elaborate
from toolchain.elaborate_protocol import _Protocol


def _quantifier(word: str) -> Form:
    def form(fixture: _Fixture) -> Node:
        start = fixture.offset
        fixture.write(word + " ")
        parameters = fixture.parameters((("value", _NAT),))
        fixture.write(" => ")
        value = _binary("==", _variable("value"), _variable("value"))(fixture)
        return fixture.node("quantifier", start, quantifier=word, parameters=parameters, value=value)
    return form


def _callable_mode_type(mode: str) -> Form:
    def form(fixture: _Fixture) -> Node:
        start = fixture.offset
        fixture.write(mode)
        params = fixture.parameters((("value", _NAT),))
        fixture.write(" -> ")
        output = _NAT(fixture)
        return fixture.node("function_type", start, mode=mode, generics=[], parameters=params,
                            result=output, captures=None, effects=[], contracts=[])
    return form


def _fixture(word: str = "forall") -> _Fixture:
    fixture = _Fixture("ProtocolWords")
    fixture.definition("Identity", _function_type((("value", _NAT),), _NAT), (),
                       _lambda((("value", _NAT),), _variable("value")))
    fixture.definition("Generic", _type("T"), (("value", _type("T")),), _variable("value"),
                       generics=(("type", "T", None),))
    fixture.theorem("Reflexive", (), _quantifier(word),
                    _assert(_binary("==", _variable("value"), _variable("value"))))
    return fixture


def _malformed_words() -> None:
    source, response = _fixture().response()
    elaborate(source, response)
    for role in ("callable", "generic", "quantifier"):
        for malformed in (None, False, 7, [], {}, "unknown", "\ud800"):
            changed = copy.deepcopy(response)
            declarations = cast("list[Node]", cast("Node", changed["ast"])["declarations"])
            if role == "callable":
                node, field = cast("Node", declarations[0]["result"]), "mode"
            elif role == "generic":
                node, field = cast("list[Node]", declarations[1]["generics"])[0], "mode"
            else:
                contract = cast("list[Node]", declarations[2]["contracts"])[0]
                node, field = cast("Node", contract["value"]), "quantifier"
            node[field] = malformed
            with raises(HoldFastError, msg=f"malformed {role} word was accepted") as raised:
                elaborate(source, changed)
            error = raised.exception
            ensure(error.kind == "protocol" and "syntax word" in error.message,
                   f"malformed {role} word lost its protocol refusal: {error.kind}")
    ensure(elaborate(source, response).module == "ProtocolWords",
           "a refused syntax word damaged the next valid elaboration")


def _supported_and_unsupported_words() -> None:
    fixture = _fixture()
    output = elaborate(*fixture.response()).gallina
    ensure("Definition holdfast_d2_Reflexive" in output and "Corelib.Init.Logic.eq_refl" in output,
           "universal proof failed to emit its explicit equality witness")
    with raises(HoldFastError, msg="existential binder was treated as universally introduced") as raised:
        elaborate(*_fixture("exists").response())
    ensure(raised.exception.kind == "name",
           "an unwitnessed existential assertion did not reject the unbound quantifier variable")
    ex_fixture = _Fixture("ExistentialWitness")
    ex_fixture.theorem("HasWitness", (), _quantifier("exists"),
                       _assert(_quantifier("exists"), by=_natural(0)))
    ex_output = elaborate(*ex_fixture.response()).gallina
    ensure("@Corelib.Init.Logic.ex " in ex_output and "@Corelib.Init.Logic.ex_intro " in ex_output,
           "existential proof failed to emit ex and ex_intro")
    fnonce_fixture = _Fixture("UnsupportedCallableMode")
    fnonce_fixture.definition("Once", _callable_mode_type("FnOnce"), (),
                              _lambda((("value", _NAT),), _variable("value")))
    with raises(HoldFastError, msg="FnOnce callable mode acquired a mathematical interpretation") as raised:
        elaborate(*fnonce_fixture.response())
    error = raised.exception
    ensure(error.kind == "unsupported" and "pure Fn" in error.message,
           "a source-bound FnOnce callable failed before its semantic boundary")
    source, response = fixture.response()
    declarations = cast("list[Node]", cast("Node", response["ast"])["declarations"])
    cast("Node", declarations[0]["result"])["mode"] = "FnOnce"
    with raises(HoldFastError, msg="a callable mode absent from source was accepted") as raised:
        elaborate(source, response)
    ensure(raised.exception.kind == "protocol", "a forged valid syntax word escaped source binding")


def _type_constraint_binding() -> None:
    fixture = _Fixture("Constraints")
    fixture.definition(
        "Keep", _type("T"), (("value", _type("T")),), _variable("value"),
        generics=(("type", "T", None),),
        contracts=(_type_constraint("T", _type("Core.ISized", _type("T")), _type("ICopy", _type("T"))),),
    )
    source, response = fixture.response()
    tree = _Protocol(source).decode(response)
    declaration = cast("list[Node]", tree["declarations"])[0]
    constraint = cast("list[Node]", declaration["contracts"])[0]
    bounds = cast("list[Node]", constraint["bounds"])
    for field, replacement in (("parameter", {"text": "T"}), ("bounds", []), ("bounds", bounds[::-1])):
        changed = copy.deepcopy(response)
        declaration = cast("list[Node]", cast("Node", changed["ast"])["declarations"])[0]
        constraint = cast("list[Node]", declaration["contracts"])[0]
        constraint[field] = replacement
        with raises(HoldFastError, msg=f"forged constraint {field} was accepted") as raised:
            _Protocol(source).decode(changed)
        ensure(raised.exception.kind == "protocol", "constraint corruption was not refused at the source boundary")
    retired = _Fixture("Retired")
    retired.definition("Keep", _NAT, (("value", _NAT),), _variable("value"),
                       contracts=(_contract("where", _binary(">", _variable("value"), _natural(0))),))
    source, response = retired.response()
    with raises(HoldFastError, msg="old where proposition entered through the AST protocol") as raised:
        _Protocol(source).decode(response)
    ensure(raised.exception.kind == "protocol", "a retired where proposition reached elaboration")


def cases() -> list[Case]:
    return [Case("mathematical-malformed-syntax-words", _malformed_words),
            Case("mathematical-word-semantics-and-source-binding", _supported_and_unsupported_words),
            Case("mathematical-type-constraint-source-binding", _type_constraint_binding)]
