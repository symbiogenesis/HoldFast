# SPDX-License-Identifier: Apache-2.0
"""Tests for bounded grade-directed program synthesis (Q25ca)."""

from tests.harness import Case, ensure, raises
from toolchain import graded_combinators as gc
from toolchain import graded_synthesis as gs


def _inc(x: object) -> int:
    if not isinstance(x, int):
        raise TypeError(f"expected int, got {x!r}")
    return x + 1


def _add(x: object) -> object:
    if not isinstance(x, int):
        raise TypeError(f"expected int, got {x!r}")

    def _inner(y: object) -> int:
        if not isinstance(y, int):
            raise TypeError(f"expected int, got {y!r}")
        return x + y

    return _inner


def _nat_library() -> tuple[gs.Component, ...]:
    nat = gc.NAT_TYPE
    return (
        gs.Component("zero", nat, semantics=0),
        gs.Component("inc", gc.ArrowType(gs.gi.GradeLit(1), nat, nat), semantics=_inc),
        gs.Component(
            "add",
            gc.ArrowType(
                gs.gi.GradeLit(1),
                nat,
                gc.ArrowType(gs.gi.GradeLit(1), nat, nat),
            ),
            semantics=_add,
        ),
    )


def _test_grade_pruning_and_oracle_selection() -> None:
    lib = _nat_library()
    # Goal: Nat from x @ NatExact(2), where oracle requires f(x) == 2 * x + 1!
    # Well-typed candidates like add(x, x) or inc(x) fail either grade exactness (inc(x) only uses x once!)
    # or behavioral oracle (add(x, x) == 2*x != 2*x + 1).
    # Synthesis must prune inc(x) by NatExact, reject add(x, x) via oracle, and find inc(add(x, x))!
    x = gs.ContextVar("x", gc.NAT_TYPE, allowance=2)
    res = gs.synthesize(
        gc.NAT_TYPE,
        domain="NatExact",
        context=(x,),
        components=lib,
        budget=gs.SynthesisBudget(max_nodes=500, max_depth=4, timeout_ms=2000),
        examples=[((0,), 1), ((3,), 7), ((5,), 11)],
    )
    if not isinstance(res, gs.SynthesisSuccess):
        raise TypeError(f"expected synthesis success, got {res}")
    ensure(res.used_grades == {"x": 2}, f"wrong exact grade usage: {res.used_grades}")
    ensure(res.behavioral_rejections >= 1, f"expected oracle to reject add(x, x) first: {res}")
    ensure(res.pruned_branches >= 1, f"expected immediate grade pruning on over-use: {res}")

    # Linear domain: variable with allowance 1 cannot be duplicated into f(x)=2*x
    lin_x = gs.ContextVar("x", gc.NAT_TYPE, allowance=1, duplicable=False, disposable=False)
    lin_res = gs.synthesize(
        gc.NAT_TYPE,
        domain="Linear",
        context=(lin_x,),
        components=lib,
        budget=gs.SynthesisBudget(max_nodes=500, max_depth=2, timeout_ms=2000),
        examples=[((0,), 0), ((4,), 8)],
    )
    ensure(isinstance(lin_res, gs.SynthesisResidual) and lin_res.status == "unsatisfiable",
           f"Linear synthesis must refuse f(x)=2*x: {lin_res}")


def _test_behavioral_rejection_and_budget_exhaustion() -> None:
    lib = _nat_library()
    x = gs.ContextVar("x", gc.NAT_TYPE, allowance=2)

    # Behaviorally wrong candidates: oracle always rejects -> unsatisfiable with NO accepted partial result!
    rejected = gs.synthesize(
        gc.NAT_TYPE,
        domain="NatBound",
        context=(x,),
        components=lib,
        budget=gs.SynthesisBudget(max_nodes=500, max_depth=2, timeout_ms=2000),
        oracle=lambda fn: fn(1) == 999,
    )
    ensure(isinstance(rejected, gs.SynthesisResidual) and rejected.status == "unsatisfiable"
           and rejected.behavioral_rejections >= 1,
           f"expected unsatisfiable residual after behavioral rejections: {rejected}")

    # Budget exhaustion: tiny max_nodes=2 must stop and return SynthesisResidual(status="exhausted")
    exhausted = gs.synthesize(
        gc.NAT_TYPE,
        domain="NatExact",
        context=(x,),
        components=lib,
        budget=gs.SynthesisBudget(max_nodes=2, max_depth=4, timeout_ms=2000),
        examples=[((3,), 7)],
    )
    ensure(isinstance(exhausted, gs.SynthesisResidual) and exhausted.status == "exhausted"
           and exhausted.explored_nodes <= 2 and bool(exhausted.remaining_goals),
           f"expected exhausted residual: {exhausted}")

    # Box promotion + unboxing synthesis in Affine / NatBound
    bx = gs.ContextVar("bx", gc.BoxType(gc.NAT_TYPE, gs.gi.GradeLit(2)), allowance=1)
    pair_res = gs.synthesize(
        gc.PairType(gc.NAT_TYPE, gc.NAT_TYPE),
        domain="NatExact",
        context=(bx,),
        components=(),
        budget=gs.SynthesisBudget(max_nodes=100, max_depth=4, timeout_ms=2000),
    )
    ensure(isinstance(pair_res, gs.SynthesisSuccess), f"box->pair synthesis failed: {pair_res}")


def _test_rocq_synthesis_replay_and_tamper() -> None:
    lib = _nat_library()
    x = gs.ContextVar("x", gc.NAT_TYPE, allowance=2)
    res = gs.synthesize(
        gc.NAT_TYPE,
        domain="NatExact",
        context=(x,),
        components=lib,
        budget=gs.SynthesisBudget(max_nodes=500, max_depth=4, timeout_ms=2000),
        examples=[((2,), 5), ((4,), 9)],
        verify_rocq=True,
    )
    if not isinstance(res, gs.SynthesisSuccess):
        raise TypeError(f"Rocq synthesis replay failed: {res}")

    # Box unboxing into pair with Rocq kernel replay
    bx = gs.ContextVar("bx", gc.BoxType(gc.NAT_TYPE, gs.gi.GradeLit(2)), allowance=1)
    box_res = gs.synthesize(
        gc.PairType(gc.NAT_TYPE, gc.NAT_TYPE),
        domain="NatExact",
        context=(bx,),
        components=(),
        budget=gs.SynthesisBudget(max_nodes=100, max_depth=4, timeout_ms=2000),
        verify_rocq=True,
    )
    ensure(isinstance(box_res, gs.SynthesisSuccess), f"Rocq box synthesis replay failed: {box_res}")

    # Tampering with allowance in generated Gallina (2 -> 1) MUST be rejected by Rocq!
    tampered_gallina = res.gallina.replace("(GLit 2)", "(GLit 1)", 1)
    ensure(tampered_gallina != res.gallina, "tamper did not alter synthesis Gallina")
    tampered = gs.SynthesisSuccess(
        status="synthesized",
        domain=res.domain,
        term=res.term,
        goal_type=res.goal_type,
        used_grades=res.used_grades,
        holdfast_source=res.holdfast_source,
        gallina=tampered_gallina,
        module_name=res.module_name,
        theorem_name=res.theorem_name,
        explored_nodes=res.explored_nodes,
        pruned_branches=res.pruned_branches,
        behavioral_rejections=res.behavioral_rejections,
        source_sha256=res.source_sha256,
    )
    with raises(ValueError):
        gs.verify_synthesis(tampered)


def cases() -> list[Case]:
    return [
        Case("grade-directed pruning and behavioral oracle selection", _test_grade_pruning_and_oracle_selection),
        Case("behavioral rejection, budget exhaustion, and box synthesis",
             _test_behavioral_rejection_and_budget_exhaustion),
        Case("Rocq replay of synthesized terms and tampered certificate refusal",
             _test_rocq_synthesis_replay_and_tamper, lane="toolchain"),
    ]
