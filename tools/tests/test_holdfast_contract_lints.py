# SPDX-License-Identifier: Apache-2.0
"""Checked contract findings on independent mathematical syntax fixtures."""

from tests.harness import Case, ensure
from tests.test_holdfast_elaborate import (
    _NAT,
    Form,
    _assign_stmt,
    _binary,
    _block_stmts,
    _boolean,
    _call,
    _contract,
    _Fixture,
    _foreach_range,
    _group,
    _impl_decl,
    _int_lit,
    _interface_decl,
    _interface_fn_sig,
    _invariant_contract,
    _is_expr,
    _lambda,
    _member,
    _modified,
    _natural,
    _pat_ctor,
    _pat_wild,
    _record_def_member,
    _return_stmt,
    _type,
    _unary_op,
    _var_stmt,
    _variable,
)
from toolchain.elaborate import elaborate


def _findings(fixture: _Fixture) -> dict[tuple[str, int], str]:
    source, parsed = fixture.response()
    return dict(elaborate(source, parsed).semantic_lints)


def _require_findings(fixture: _Fixture, expected: list[tuple[str, str]]) -> None:
    findings = _findings(fixture)
    source, _ = fixture.response()
    ensure(len(findings) == len(expected), f"unexpected findings: {findings}")
    for (code, offset), (expected_code, expression) in zip(
        sorted(findings, key=lambda key: key[1]), expected, strict=True,
    ):
        ensure(code == expected_code and source[offset:].startswith(expression.encode()),
               f"incorrect finding {code} on {source[offset:offset + 35]!r}")


def _scalar_contracts() -> None:
    fixture = _Fixture("ScalarContractLints")
    n = _variable("n")
    fixture.definition(
        "Check",
        _NAT,
        (("n", _NAT),),
        n,
        contracts=(
            _contract("requires", _binary(">=", n, _natural(0))),
            _contract("requires", _binary(">=", n, _natural(8))),
            _contract("requires", _binary("<=", _natural(8), n)),
            _contract("requires", _binary(">=", n, _natural(3))),
            _contract("ensures", _binary(">=", n, _natural(2))),
            _contract("ensures", _binary("==>", _binary("<", n, _natural(2)), _binary(">", n, _natural(1)))),
            _contract("ensures", _binary("==", n, n)),
            _contract("ensures", _binary("==", _variable("result"), n)),
        ),
    )
    fixture.definition(
        "Impossible",
        _NAT,
        (("n", _NAT),),
        n,
        contracts=(
            _contract("requires", _binary("<", n, _natural(4))),
            _contract("requires", _binary(">=", n, _natural(4))),
        ),
    )
    _require_findings(fixture, [
        ("HOLDFAST112", "n >= 0"),
        ("HOLDFAST113", "8 <= n"),
        ("HOLDFAST114", "n >= 3"),
        ("HOLDFAST114", "n >= 2"),
        ("HOLDFAST116", "n < 2 ==>"),
        ("HOLDFAST115", "n == n"),
        ("HOLDFAST116", "n >= 4"),
    ])


def _library_and_record_contracts() -> None:
    fixture = _Fixture("LibraryContractLints")
    window = _variable("window")
    invariant = _binary("<=", _member(_variable("this"), "Low"), _member(_variable("this"), "High"))
    fixture.record(
        "Window",
        (("Low", _NAT), ("High", _NAT)),
        contracts=(_invariant_contract(invariant, "Ordered"), _invariant_contract(invariant, "Repeated")),
    )
    slots = _variable("slots")
    slot_type = _type("Slots", _type("byte"), _natural(8))
    lo, hi = _int_lit("0", "usize"), _int_lit("4", "usize")
    fixture.definition(
        "Observe",
        _NAT,
        (("window", _type("Window")), ("slots", slot_type)),
        _natural(0),
        contracts=(
            _contract("requires", _binary("<=", _member(window, "Low"), _member(window, "High"))),
            _contract("requires", _call("VacantRange", slots, lo, hi)),
            _contract("requires", _member(slots, "CanWrite")),
            _contract("requires", _member(slots, "Tag")),
            _contract("requires", _binary("==", _member(slots, "Capacity"), _int_lit("8", "usize"))),
        ),
    )
    _require_findings(fixture, [
        ("HOLDFAST113", "this.Low <= this.High"),
        ("HOLDFAST112", "window.Low <= window.High"),
        ("HOLDFAST112", "slots.CanWrite"),
        ("HOLDFAST112", "slots.Tag"),
        ("HOLDFAST112", "slots.Capacity"),
    ])


def _returned_views_and_outcomes() -> None:
    fixture = _Fixture("ReturnContractLints")
    span = _type("Span", _type("byte"))
    buf, count = _variable("buf"), _variable("count")
    result = _variable("result")
    slice_value = _call(_member(_variable("Span"), "Slice"), buf, _int_lit("0", "usize"), count)
    fixture.definition(
        "SliceView", span, (("buf", _modified("in", span)), ("count", _type("usize"))), slice_value,
        contracts=(
            _contract("requires", _member(buf, "CanRead")),
            _contract("requires", _binary("<=", count, _member(buf, "Length"))),
            _contract("ensures", _binary("==", result, slice_value)),
            _contract("ensures", _binary("==", _member(result, "Length"), count)),
        ),
    )
    readonly = _call(_member(_variable("Span"), "ReadOnly"), buf)
    fixture.definition(
        "ReadOnlyView", span, (("buf", _modified("in", span)),), readonly,
        contracts=(
            _contract("ensures", _binary("==", result, readonly)),
            _contract("ensures", _unary_op("!", _member(result, "CanWrite"))),
        ),
    )
    verdict = _variable("verdict")
    ok = _is_expr(verdict, _pat_ctor("Ok", _pat_wild()))
    err = _is_expr(verdict, _pat_ctor("Err", _pat_wild()))
    fixture.definition(
        "CheckOutcome", _NAT, (("verdict", _type("Result", _NAT, _NAT)),), _natural(0),
        contracts=(_contract("requires", _binary("||", ok, err)),),
    )
    guarantee = _binary("==", result, _natural(0))
    fixture.definition(
        "BothOutcomes", _NAT, (("verdict", _type("Result", _NAT, _NAT)),), _natural(0),
        contracts=(
            _contract("ensures", _binary("==>", ok, guarantee)),
            _contract("ensures", _binary("==>", err, guarantee)),
        ),
    )
    _require_findings(fixture, [
        ("HOLDFAST112", "result.Length == count"),
        ("HOLDFAST112", "!result.CanWrite"),
        ("HOLDFAST115", "verdict is Ok(_)"),
        ("HOLDFAST115", "verdict is Err(_)"),
    ])


def _quantified_and_inherited_contracts() -> None:
    fixture = _Fixture("ProofContractLints")

    def empty_range(f: _Fixture) -> dict[str, object]:
        start = f.offset
        f.write("forall ")
        params = f.parameters((("i", _NAT),))
        f.write(" => ")
        i = _variable("i")
        body = _binary("==>", _binary("<", i, _natural(0)), _binary("==", i, i))(f)
        return f.node("quantifier", start, quantifier="forall", parameters=params, value=body)

    empty: Form = _member(_variable("Seq"), "Empty")
    all_empty = _call(_member(_call(empty, generics=(_type("Nat"),)), "All"), _lambda((("i", _NAT),), _boolean(False)))
    fixture.definition(
        "Vacuous", _NAT, (("n", _NAT),), _variable("n"),
        contracts=(_contract("ensures", _group(empty_range)), _contract("ensures", all_empty)),
    )
    spec_value, impl_value = _variable("limit"), _variable("count")
    _interface_decl(
        fixture, "Restricted", (("type", "T", None),),
        (_interface_fn_sig(
            "Keep", _NAT, (("value", _type("T")), ("limit", _NAT)),
            contracts=(
                _contract("requires", _binary(">=", spec_value, _natural(1))),
                _contract("ensures", _binary("==", _variable("result"), spec_value)),
            ),
        ),),
    )
    _impl_decl(
        fixture, _type("Restricted", _NAT),
        (_record_def_member(
            "Keep", _NAT, (("value", _NAT), ("count", _NAT)), impl_value,
            contracts=(
                _contract("requires", _binary(">=", impl_value, _natural(1))),
                _contract("ensures", _binary("==", _variable("result"), impl_value)),
            ),
        ),),
    )
    _require_findings(fixture, [
        ("HOLDFAST116", "forall "),
        ("HOLDFAST116", "Seq.Empty"),
        ("HOLDFAST117", "count >= 1"),
        ("HOLDFAST117", "result == count"),
    ])


def _repeated_loop_invariant() -> None:
    fixture = _Fixture("LoopContractLints")
    count, i = _variable("count"), _variable("i")
    invariant = _binary("==", count, i)
    fixture.function(
        "Repeat", _NAT, (),
        _block_stmts(
            _var_stmt("count", _natural(0)),
            _foreach_range(
                "i", _natural(0), _natural(2), (_assign_stmt(count, "+=", _natural(1)),),
                (_contract("invariant", invariant), _contract("invariant", invariant)),
            ),
            _return_stmt(count),
        ),
        block=True,
    )
    _require_findings(fixture, [("HOLDFAST113", "count == i")])


def cases() -> list[Case]:
    return [
        Case("checked scalar contract redundancies and vacuity", _scalar_contracts),
        Case("library and nominal type facts in contracts", _library_and_record_contracts),
        Case("returned view descriptors and exhaustive verdict contracts", _returned_views_and_outcomes),
        Case("empty specifications and inherited implementation contracts", _quantified_and_inherited_contracts),
        Case("identical checked loop invariants", _repeated_loop_invariant),
    ]
