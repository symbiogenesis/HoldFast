# SPDX-License-Identifier: Apache-2.0
"""Tests for derived distributive modality combinators (Q25bz)."""

from tests.harness import Case, ensure, raises
from toolchain import graded_combinators as gc
from toolchain import graded_inference as gi


def _test_all_seven_combinators_positive() -> None:
    a = gc.BaseType("A")
    b = gc.BaseType("B")
    pair = gc.PairType(a, b)
    either = gc.SumType(a, b)
    q = gi.GradeVar("q")
    r = gi.GradeVar("r")

    dist = gc.derive_combinator("dist_pair", domain="NatExact", pair_type=pair, grade=q)
    ensure("DistPair" in dist.holdfast_source and "Box<A, q>" in dist.holdfast_source, dist.holdfast_source)

    pull = gc.derive_combinator("pull_pair", domain="NatExact", pair_type=pair, grade=q)
    ensure("PullPair" in pull.holdfast_source and "Box<(A, B), q>" in pull.holdfast_source, pull.holdfast_source)

    push = gc.derive_combinator("push_sum", domain="NatExact", sum_type=either, grade=gi.GradeLit(2))
    ensure("PushSum" in push.holdfast_source and "Either<Box<A, 2>, Box<B, 2>>" in push.holdfast_source,
           push.holdfast_source)

    flat = gc.derive_combinator("flatten_box", domain="NatExact", payload_type=a, grade=q, inner_grade=r)
    ensure("FlattenBox" in flat.holdfast_source and "(q * r)" in flat.holdfast_source, flat.holdfast_source)

    dup = gc.derive_combinator("duplicate_box", domain="NatExact", payload_type=a, grade=q, inner_grade=r)
    ensure("DuplicateBox" in dup.holdfast_source, dup.holdfast_source)

    ext = gc.derive_combinator("extract_box", domain="NatExact", payload_type=a, grade=gi.GradeLit(1))
    ensure("ExtractBox" in ext.holdfast_source, ext.holdfast_source)

    weak = gc.derive_combinator(
        "weaken_box",
        domain="NatBound",
        payload_type=a,
        grade=gi.GradeLit(3),
        target_grade=gi.GradeLit(1),
    )
    ensure("WeakenBox" in weak.holdfast_source and "Box<A, 1>" in weak.holdfast_source, weak.holdfast_source)


def _test_structure_inspection_and_refusals() -> None:
    src = """
    module Structures;
    public record Box<T, grade q : NatExact>(T Value @ q);
    public record Pair<A, B>(A First, B Second);
    public union Either<A, B> { Left(A left), Right(B right) };
    """
    spec = gc.inspect_holdfast_structures(src)
    ensure(spec.box_domain == gi.InferenceDomain.NAT_EXACT, f"wrong box domain: {spec}")
    ensure("Pair" in spec.records and "Either" in spec.unions, f"missing inspected decls: {spec}")

    a = gc.BaseType("A")
    # Refusal 1: weaken_box in NatExact when q != q'
    with raises(gc.CombinatorRefusalError):
        gc.derive_combinator(
            "weaken_box",
            domain="NatExact",
            payload_type=a,
            grade=gi.GradeLit(3),
            target_grade=gi.GradeLit(1),
        )
    exact_same = gc.derive_combinator(
        "weaken_box",
        domain="NatExact",
        payload_type=a,
        grade=gi.GradeLit(2),
        target_grade=gi.GradeLit(2),
    )
    ensure("Box<A, 2>" in exact_same.holdfast_source, "same-grade NatExact identity failed")

    # Refusal 2: weaken_box in NatBound when target > source (1 -> 3)
    bad_bound = gc.try_derive_combinator(
        "weaken_box",
        domain="NatBound",
        payload_type=a,
        grade=gi.GradeLit(1),
        target_grade=gi.GradeLit(3),
    )
    ensure(isinstance(bad_bound, gc.CombinatorRefusal) and bad_bound.kind == "grade",
           f"unsound NatBound increase accepted: {bad_bound}")

    # Refusal 3: Dup/contraction on Linear domain or owned/non-duplicable payload
    owned_handle = gc.BaseType("OwnedHandle", duplicable=False, disposable=False, owned=True)
    bad_dup_owned = gc.try_derive_combinator(
        "duplicate_box",
        domain="NatExact",
        payload_type=owned_handle,
        grade=gi.GradeLit(2),
        inner_grade=gi.GradeLit(1),
    )
    ensure(isinstance(bad_dup_owned, gc.CombinatorRefusal) and bad_dup_owned.kind == "authority",
           f"Dup derived for owned handle: {bad_dup_owned}")

    bad_dup_linear = gc.try_derive_combinator(
        "duplicate_box",
        domain="Linear",
        payload_type=a,
        grade=gi.GradeLit(1),
        inner_grade=gi.GradeLit(1),
    )
    ensure(isinstance(bad_dup_linear, gc.CombinatorRefusal) and bad_dup_linear.kind == "authority",
           f"Dup derived for Linear domain: {bad_dup_linear}")

    # Refusal 4: pull_pair when domain refuses pairing distribution (Linear)
    bad_pull = gc.try_derive_combinator(
        "pull_pair",
        domain="Linear",
        pair_type=gc.PairType(a, gc.BaseType("B")),
        grade=gi.GradeLit(1),
    )
    ensure(isinstance(bad_pull, gc.CombinatorRefusal) and bad_pull.kind == "domain",
           f"pull_pair allowed in non-pairing Linear domain: {bad_pull}")

    # Refusal 5: push_sum at grade 0 (erased scrutinee cannot match constructor tags)
    bad_sum = gc.try_derive_combinator(
        "push_sum",
        domain="NatBound",
        sum_type=gc.SumType(a, gc.BaseType("B")),
        grade=gi.GradeLit(0),
    )
    ensure(isinstance(bad_sum, gc.CombinatorRefusal) and bad_sum.kind == "grade",
           f"push_sum allowed at grade 0: {bad_sum}")

    # Refusal 6: dropping non-disposable resource via weaken_box to 0 in NatBound
    bad_drop = gc.try_derive_combinator(
        "weaken_box",
        domain="NatBound",
        payload_type=owned_handle,
        grade=gi.GradeLit(1),
        target_grade=gi.GradeLit(0),
    )
    ensure(isinstance(bad_drop, gc.CombinatorRefusal) and bad_drop.kind == "authority",
           f"weaken_box dropped non-disposable owned handle: {bad_drop}")


def _test_rocq_combinator_replay_and_tamper() -> None:
    a = gc.BaseType("A")
    b = gc.BaseType("B")
    pair = gc.PairType(a, b)
    either = gc.SumType(a, b)
    q = gi.GradeVar("q")
    r = gi.GradeVar("r")

    derivations = [
        gc.derive_combinator("dist_pair", domain="NatExact", pair_type=pair, grade=q, verify_rocq=True),
        gc.derive_combinator("pull_pair", domain="NatExact", pair_type=pair, grade=q, verify_rocq=True),
        gc.derive_combinator("push_sum", domain="NatExact", sum_type=either, grade=gi.GradeLit(2), verify_rocq=True),
        gc.derive_combinator("push_sum", domain="NatBound", sum_type=either,
                             grade=gi.GradeAdd(gi.GradeLit(1), q), verify_rocq=True),
        gc.derive_combinator("flatten_box", domain="NatExact", payload_type=a, grade=q, inner_grade=r, verify_rocq=True),
        gc.derive_combinator("duplicate_box", domain="NatExact", payload_type=a, grade=q, inner_grade=r, verify_rocq=True),
        gc.derive_combinator("extract_box", domain="NatExact", payload_type=a, grade=gi.GradeLit(1), verify_rocq=True),
        gc.derive_combinator("weaken_box", domain="NatBound", payload_type=a,
                             grade=gi.GradeLit(3), target_grade=gi.GradeLit(1), verify_rocq=True),
        gc.derive_combinator("weaken_box", domain="Affine", payload_type=a,
                             grade=gi.GradeLit(1), target_grade=gi.GradeLit(0), verify_rocq=True),
        gc.derive_combinator("weaken_box", domain="Presence", payload_type=a,
                             grade=gi.GradeLit(1), target_grade=gi.GradeLit(0), verify_rocq=True),
    ]
    ensure(len(derivations) == 10, "missing expected combinator derivations")

    # Tampered Rocq proof (e.g. changing GMul to GAdd in flatten_box) MUST fail Rocq kernel replay!
    flat = derivations[4]
    tampered_gallina = flat.gallina.replace("(GMul (GVar 0) (GVar 1))", "(GAdd (GVar 0) (GVar 1))", 1)
    ensure(tampered_gallina != flat.gallina, "tamper did not alter flatten_box Gallina")
    tampered = gc.CombinatorDerivation(
        combinator=flat.combinator,
        domain=flat.domain,
        signature=flat.signature,
        holdfast_source=flat.holdfast_source,
        gallina=tampered_gallina,
        module_name=flat.module_name,
        theorem_name=flat.theorem_name,
        source_sha256=flat.source_sha256,
    )
    with raises(ValueError):
        gc.verify_combinator(tampered)


def cases() -> list[Case]:
    return [
        Case("all seven derived distributive modality combinators", _test_all_seven_combinators_positive),
        Case("structure inspection and domain/authority refusal controls", _test_structure_inspection_and_refusals),
        Case("Rocq kernel replay and tampered combinator certificate refusal",
             _test_rocq_combinator_replay_and_tamper, lane="toolchain"),
    ]
