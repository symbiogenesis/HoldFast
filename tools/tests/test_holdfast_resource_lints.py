# SPDX-License-Identifier: Apache-2.0
"""Checked resource lint findings and neighbors with meaningful capabilities."""

from tests.harness import Case, ensure
from tests.test_holdfast_elaborate import (
    _BOOL,
    _assign_stmt,
    _binary,
    _block_stmts,
    _call,
    _contract,
    _effects_clause,
    _Fixture,
    _foreach_coll,
    _index_expr,
    _int_lit,
    _invariant_contract,
    _let_stmt,
    _member,
    _modified,
    _open_lifts,
    _ref_arg,
    _return_stmt,
    _type,
    _var_stmt,
    _variable,
)
from toolchain.elaborate import elaborate


def _effect_and_mode_findings() -> None:
    fixture = _Fixture("ResourceModes")
    word, unit = _type("u32"), _type("Unit")
    ref_word = _modified("ref", word)
    read, destination = _variable("input"), _variable("destination")
    fixture.function(
        "Read", word, (("input", ref_word),), _block_stmts(
            _var_stmt("fixed", read), _var_stmt("counter", _variable("fixed")),
            _assign_stmt(_variable("counter"), "=", read), _return_stmt(_variable("counter")),
        ),
        private=True, block=True,
        contracts=(_effects_clause(_call("reads", read, read), _variable("none")),),
    )
    fixture.function(
        "Initialize", unit, (("destination", ref_word), ("value", word)), _block_stmts(
            _assign_stmt(destination, "=", _variable("value")), _return_stmt(),
        ),
        private=True, block=True, contracts=(_effects_clause(_call("writes", destination)),),
    )
    fixture.function(
        "Restore", unit, (("destination", ref_word),), _block_stmts(
            _let_stmt("entry", destination), _assign_stmt(destination, "=", _int_lit("0", "u32")),
            _assign_stmt(destination, "=", _variable("entry")), _return_stmt(),
        ),
        private=True, block=True, contracts=(_effects_clause(_call("writes", destination)),),
    )
    for public in (False, True):
        fixture.function(
            "PublicIdle" if public else "Idle", unit, (("destination", ref_word),),
            _block_stmts(_return_stmt()), private=not public, block=True,
            contracts=(_effects_clause(_call("writes", destination)),),
        )
    fixture.function(
        "LocalRead", word, (("input", ref_word),), _block_stmts(
            _let_stmt("loan", _ref_arg(read), ref_word), _return_stmt(_variable("loan")),
        ),
        block=True, contracts=(_effects_clause(_call("reads", read)),),
    )
    source, response = fixture.response()
    checked = elaborate(source, response)
    expected = {
        ("HOLDFAST118", source.index(b"input), none")): "duplicate effect allowance 'reads(input)'",
        ("HOLDFAST118", source.index(b"none")): "'none' adds nothing to this effect bound",
        ("HOLDFAST119", source.index(b"destination) { return; }")):
            "effect allowance 'writes(destination)' is unused by the checked body",
        ("HOLDFAST122", source.index(b"input) effects")): "parameter 'input' can use a shared 'in' loan",
        ("HOLDFAST122", source.index(b"loan = ref")): "local 'loan' can use a shared 'in' loan",
        ("HOLDFAST123", source.index(b"destination, u32 value")):
            "parameter 'destination' is fully initialized before any use and can use 'out'",
        ("HOLDFAST124", source.index(b"fixed =")): "local 'fixed' can be declared with 'let'",
        ("HOLDFAST134", source.rindex(b"destination) { return; }")):
            "effect allowance 'writes(destination)' is unused by the checked body",
    }
    actual = {key: message for key, message in checked.semantic_lints.items() if key[0] in {
        "HOLDFAST118", "HOLDFAST119", "HOLDFAST122", "HOLDFAST123", "HOLDFAST124", "HOLDFAST134",
    }}
    ensure(actual == expected, f"unexpected resource findings: {actual}; expected {expected}")


def _frames_and_lifts() -> None:
    fixture = _Fixture("ResourceFrames")
    word, unit = _type("u32"), _type("Unit")
    fixture.record("State", (("Count", word), ("Enabled", _BOOL)), contracts=(
        _invariant_contract(_binary("<=", _member(_variable("this"), "Count"), _int_lit("8", "u32")), "Bounded"),
        _invariant_contract(_member(_variable("this"), "Enabled"), "Active"),
    ))
    state = _variable("state")
    fixture.function(
        "Reset", unit, (("state", _modified("ref", _type("State"))),), _block_stmts(
            _open_lifts((_ref_arg(state),), ("Bounded", "Active"), (
                _assign_stmt(_member(state, "Count"), "=", _int_lit("0", "u32")),
            )),
            _return_stmt(),
        ), block=True, contracts=(_effects_clause(_call("writes", state)),),
    )
    span, index = _variable("span"), _variable("index")
    item = _index_expr(span, index)
    fixture.function(
        "Read", _type("byte"), (("span", _modified("in", _type("Span", _type("byte")))), ("index", _type("usize"))),
        item, contracts=(
            _effects_clause(_call("reads", span)),
            _contract("requires", _binary("&&", _member(span, "CanRead"), _binary("<", index, _member(span, "Length")))),
            _contract("ensures", _binary("==", item, _index_expr(_call("old", span), index))),
        ),
    )
    section = _member(_call(
        _member(_variable("Span"), "Slice"), span, _int_lit("0", "usize"), _int_lit("1", "usize"),
    ), "Model")
    fixture.function(
        "FrameRange", unit, (("span", _modified("in", _type("Span", _type("byte")))),),
        _block_stmts(_return_stmt()), block=True, contracts=(
            _effects_clause(_variable("none")),
            _contract("requires", _binary(
                "&&", _member(span, "CanRead"), _binary(">=", _member(span, "Length"), _int_lit("1", "usize")),
            )),
            _contract("ensures", _binary("==", section, _call("old", section))),
        ),
    )
    vec = _variable("values")
    fixture.function(
        "Iterate", _type("byte"), (), _block_stmts(
            _var_stmt("values", _call(_member(_variable("Span"), "AllocZeroed"), _int_lit("1", "usize"))),
            _var_stmt("observed", _int_lit("0", "byte")),
            _foreach_coll("ref", "element", vec, (
                _assign_stmt(_variable("observed"), "=", _variable("element")),
            )),
            _return_stmt(_variable("observed")),
        ), block=True,
    )
    source, response = fixture.response()
    actual = {key: message for key, message in elaborate(source, response).semantic_lints.items()
              if key[0] in {"HOLDFAST120", "HOLDFAST121", "HOLDFAST122", "HOLDFAST124"}}
    expected = {
        ("HOLDFAST120", source.index(b"span[index] ==")):
            "frame equality follows from the shared loan 'span' and write-free footprint",
        ("HOLDFAST120", source.index(b"Span.Slice(span,")):
            "frame equality follows from the shared loan 'span' and write-free footprint",
        ("HOLDFAST121", source.index(b"Active {")):
            "invariant 'Active' does not depend on the fields written in this block",
        ("HOLDFAST122", source.index(b"element in")): "element 'element' can use a shared 'in' loan",
    }
    ensure(actual == expected, f"unexpected frame and lift findings: {actual}; expected {expected}")


def cases() -> list[Case]:
    return [
        Case("effect and loan-mode lints use the checked body", _effect_and_mode_findings),
        Case("loan frames and unchanged invariant dependencies", _frames_and_lifts),
    ]
