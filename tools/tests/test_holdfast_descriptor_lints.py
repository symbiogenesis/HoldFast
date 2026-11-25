# SPDX-License-Identifier: Apache-2.0
"""Descriptor lints use stable values, preserved metadata and exact source ranges."""

from tests.harness import Case, ensure
from tests.test_holdfast_elaborate import (
    Form,
    Node,
    _assign_stmt,
    _binary,
    _block_stmts,
    _boolean,
    _call,
    _contract,
    _Fixture,
    _group,
    _if_expr,
    _let_stmt,
    _member,
    _modified,
    _natural,
    _return_stmt,
    _type,
    _unary_op,
    _unit,
    _variable,
)
from toolchain.mathematical import inspect_source


def _forall(name: str, annotation: Form, body: Form) -> Form:
    def form(fixture: _Fixture) -> Node:
        start = fixture.offset
        fixture.write("forall ")
        parameters = fixture.parameters(((name, annotation),))
        fixture.write(" => ")
        return fixture.node("quantifier", start, quantifier="forall", parameters=parameters, value=body(fixture))
    return form


def _descriptor_contracts() -> None:
    fixture = _Fixture("DescriptorLints")
    span = _type("Span", _type("byte"))
    ref_span = _modified("ref", span)
    unit = _type("Unit")
    usize = _type("usize")
    pkt = _variable("pkt")
    length = _member(pkt, "Length")
    base = _member(pkt, "Base")
    read = _member(pkt, "CanRead")
    write = _member(pkt, "CanWrite")
    below = _binary("<", _variable("i"), length)
    old_below = _binary("<", _variable("i"), _member(_call("old", pkt), "Length"))
    eight = _natural(8)
    fixture.function(
        "Keep", unit, (("pkt", ref_span), ("choose", _type("bool"))), _unit(),
        contracts=(
            _contract("requires", _binary("==", read, _boolean(True))),
            _contract("requires", _unary_op("!", write)),
            _contract("requires", _binary(">=", length, eight)),
            _contract("ensures", _binary("==", _group(_binary("&&", read, _unary_op("!", write))), _boolean(True))),
            _contract("ensures", _if_expr(_variable("choose"), _binary("<=", eight, length),
                                          _binary("==", base, _call("old", base)))),
            _contract("ensures", _group(_forall("i", usize,
                                                _if_expr(_binary("&&", below, old_below), _boolean(True), _boolean(True))))),
            _contract("restores", pkt),
        ),
    )
    fixture.function(
        "Inspect", usize, (("pkt", _modified("in", span)),), length,
        contracts=(_contract("ensures", _binary("==", _variable("result"), _member(_call("old", pkt), "Length"))),),
    )
    fixture.function(
        "Stable", usize, (("value", usize),), _variable("value"),
        contracts=(_contract("ensures", _binary("==", _variable("result"), _call("old", _variable("value")))),),
    )
    value = _variable("value")
    fixture.function(
        "Before", usize, (("value", _modified("ref", usize)),),
        _block_stmts(_let_stmt("saved", value), _assign_stmt(value, "=", _natural(0)), _return_stmt(_variable("saved"))),
        block=True,
        contracts=(_contract("ensures", _binary("==", _variable("result"), _call("old", value))),),
    )
    source, parsed = fixture.response()
    findings = inspect_source(source, parsed).findings
    lines = source.splitlines()
    sites = [(f.code, lines[f.line - 1][f.column - 1:]) for f in findings
             if f.code in {"HOLDFAST109", "HOLDFAST110", "HOLDFAST111"}]
    prefixes = [
        ("HOLDFAST109", b"pkt.CanRead &&"),
        ("HOLDFAST109", b"!pkt.CanWrite)"),
        ("HOLDFAST109", b"8 <= pkt.Length else"),
        ("HOLDFAST109", b"pkt.Base == old(pkt.Base)"),
        ("HOLDFAST109", b"i < old(pkt).Length"),
        ("HOLDFAST110", b"restores pkt"),
        ("HOLDFAST111", b"old(pkt).Length"),
        ("HOLDFAST111", b"old(value)"),
    ]
    ensure(len(sites) == len(prefixes) and all(code == expected and site.startswith(prefix)
           for (code, site), (expected, prefix) in zip(sites, prefixes, strict=True)), f"descriptor lint sites: {sites}")


def cases() -> list[Case]:
    return [Case("checked descriptor bits, bounds, branches and stable snapshots", _descriptor_contracts)]
