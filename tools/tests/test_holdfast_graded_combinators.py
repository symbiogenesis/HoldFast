# SPDX-License-Identifier: Apache-2.0
"""Tests for derived distributive modality combinators (Q25bz)."""

from pathlib import Path
import subprocess
import tempfile

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, parser, proofenv, rocq_cache, solver_ledger
from toolchain import graded_combinators as gc
from toolchain import graded_inference as gi
from toolchain.ast import HoldFastError


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


def _test_structure_inspection() -> None:
    src = """
    module Structures;
    // record Ignored(Nat fake);
    public record Box<T, grade q : NatExact>(T Value @ q);
    public record Pair<A, B>(A First, B Second);
    public union Either<A, B> { Left(A left); Right(B right); }
    """
    spec = gc.inspect_holdfast_structures(src)
    ensure(spec.box_domain == gi.InferenceDomain.NAT_EXACT, f"wrong box domain: {spec}")
    ensure("Pair" in spec.records and "Either" in spec.unions, f"missing inspected decls: {spec}")
    ensure("Ignored" not in spec.records, f"commented record leaked into AST inspection: {spec}")


def _test_domain_and_authority_refusals() -> None:

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


def _test_mode_crossing_derivation_and_refusals() -> None:
    u32_ty = gc.BaseType("u32")
    pair_pure = gc.PairType(gc.NAT_TYPE, gc.BOOL_TYPE)
    sum_pure = gc.SumType(gc.UNIT_TYPE, u32_ty)
    q = gi.GradeVar("q")

    for domain, grade in (
        ("NatExact", q),
        ("NatBound", q),
        ("Presence", q),
        ("Affine", gi.GradeLit(1)),
        ("Linear", gi.GradeLit(1)),
    ):
        derived = gc.derive_combinator("cross_mode", domain=domain, payload_type=pair_pure, grade=grade)
        ensure("CrossMode" in derived.holdfast_source, derived.holdfast_source)
        ensure("ModeCrossAdmits pure_base" in derived.gallina, derived.gallina)

    nested_box = gc.derive_combinator(
        "cross_mode",
        domain="NatExact",
        payload_type=gc.BoxType(sum_pure, q),
        grade=gi.GradeLit(2),
    )
    ensure("Box<Either<Unit, u32>, q>" in nested_box.holdfast_source, nested_box.holdfast_source)

    owned = gc.BaseType("OwnedHandle", duplicable=False, disposable=False, owned=True)
    for bad_ty in (
        owned,
        gc.PairType(gc.NAT_TYPE, owned),
        gc.SumType(gc.NAT_TYPE, owned),
        gc.ArrowType(gi.GradeLit(1), gc.NAT_TYPE, gc.NAT_TYPE),
    ):
        res = gc.try_derive_combinator("cross_mode", domain="NatExact", payload_type=bad_ty, grade=q)
        ensure(
            isinstance(res, gc.CombinatorRefusal) and res.kind == "authority",
            f"unsafe mode crossing accepted for {bad_ty}: {res}",
        )

    bad_affine = gc.try_derive_combinator("cross_mode", domain="Affine", payload_type=u32_ty, grade=gi.GradeLit(2))
    ensure(isinstance(bad_affine, gc.CombinatorRefusal) and bad_affine.kind == "grade", str(bad_affine))
    bad_linear = gc.try_derive_combinator("cross_mode", domain="Linear", payload_type=u32_ty, grade=gi.GradeLit(2))
    ensure(isinstance(bad_linear, gc.CombinatorRefusal) and bad_linear.kind == "domain", str(bad_linear))


def _test_mode_profile_structure_inspection() -> None:
    src = """
    module ModeProfiles;
    public record Point(Nat X, Nat Y);
    public record PacketHeader(u16 Len, u8 Flags);
    public record Nested(Point Origin, PacketHeader Header);
    public union Color { Red(Unit u); Indexed(u8 idx); }
    public record BorrowedView<region 'owner>(in<'owner> Span<byte> Bytes, usize Len);
    public record OwnedContainer(OwnedHandle Handle, usize Len);
    public record WithCallback(Fn(Nat value) -> Nat Callback);
    public record GenericBox<T>(T Inner);
    """
    spec = gc.inspect_holdfast_structures(src)
    profiles = gc.derive_mode_profiles(spec)
    for name in ("Point", "PacketHeader", "Nested", "Color"):
        ensure(profiles[name].crosses_all_modes, f"pure type {name} failed to mode-cross: {profiles[name]}")
    for name in ("BorrowedView", "OwnedContainer", "WithCallback", "GenericBox"):
        ensure(not profiles[name].crosses_all_modes, f"authority/generic type {name} unsafely mode-crossed")


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
        gc.derive_combinator("cross_mode", domain="NatExact",
                             payload_type=gc.PairType(gc.NAT_TYPE, gc.BOOL_TYPE), grade=q, verify_rocq=True),
        gc.derive_combinator("cross_mode", domain="NatBound",
                             payload_type=gc.SumType(gc.UNIT_TYPE, gc.BaseType("u32")), grade=q, verify_rocq=True),
    ]
    ensure(len(derivations) == 12, "missing expected combinator derivations")

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

    # Tampering cross_mode payload to reference an uncertified base id (CBase 99) MUST fail Rocq replay!
    cross = derivations[10]
    tampered_cross_gallina = cross.gallina.replace("(CBase 0)", "(CBase 99)", 1)
    ensure(tampered_cross_gallina != cross.gallina, "tamper did not alter cross_mode Gallina")
    tampered_cross = gc.CombinatorDerivation(
        combinator=cross.combinator,
        domain=cross.domain,
        signature=cross.signature,
        holdfast_source=cross.holdfast_source,
        gallina=tampered_cross_gallina,
        module_name=cross.module_name,
        theorem_name=cross.theorem_name,
        source_sha256=cross.source_sha256,
    )
    with raises(ValueError):
        gc.verify_combinator(tampered_cross)


def _test_mode_crossing_slots_relocation_replay() -> None:
    positive_source = b"""module ModeCrossReloc;

public record Point(u32 X, u32 Y);

public union FlagOrByte
{
    Flag(bool On);
    Byte(u8 Val);
    Empty();
}

public Unit RelocatePoint<ghost usize M, ghost usize N>(
    ref Slots<Point, M> dst, ref Slots<Point, N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
    ensures LivePrefix(dst, count)
    ensures VacantSuffix(dst, count)
    ensures VacantRange(src, 0usize, N)
    ensures PrefixModel(dst, count) == old(PrefixModel(src, count))
{
    CopyRepresentation(src, ref dst, count);
    TransferType<Point>(ref src, ref dst, count);
    return ();
}

public Unit RelocatePair<ghost usize M, ghost usize N>(
    ref Slots<type (u32, bool), M> dst, ref Slots<type (u32, bool), N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
    ensures LivePrefix(dst, count)
    ensures VacantSuffix(dst, count)
    ensures VacantRange(src, 0usize, N)
    ensures PrefixModel(dst, count) == old(PrefixModel(src, count))
{
    CopyRepresentation(src, ref dst, count);
    TransferType<type (u32, bool)>(ref src, ref dst, count);
    return ();
}

public Unit RelocateUnion<ghost usize M, ghost usize N>(
    ref Slots<FlagOrByte, M> dst, ref Slots<FlagOrByte, N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
    ensures LivePrefix(dst, count)
    ensures VacantSuffix(dst, count)
    ensures VacantRange(src, 0usize, N)
    ensures PrefixModel(dst, count) == old(PrefixModel(src, count))
{
    CopyRepresentation(src, ref dst, count);
    TransferType<FlagOrByte>(ref src, ref dst, count);
    return ();
}
"""
    root = TOOLS.parent
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, positive_source, surface=True)
        checked = elaborate.elaborate(positive_source, parsed)
        with tempfile.TemporaryDirectory(prefix="holdfast-mode-cross-reloc-") as temporary:
            directory = Path(temporary)
            thms = [
                name
                for name in solver_ledger.math_exports(checked.gallina)
                if "_ensures_" in name
            ]
            ensure(len(thms) >= 12, f"expected 12 relocation postcondition theorems, got {thms}")
            unit_text, used_prelude = rocq_cache.use_cached_prelude(
                checked.gallina
                + "\nImport HoldFast_ModeCrossReloc.\n"
                + "".join(f"Print Assumptions {thm}.\n" for thm in thms),
                directory,
            )
            unit = directory / "ModeCrossRelocCheck.v"
            unit.write_text(unit_text, encoding="utf-8")
            compiler = [*proofenv.rocq_command(), "-q"]
            res = subprocess.run([*compiler, unit.name], cwd=directory, capture_output=True, text=True, check=False, timeout=180)
            ensure(res.returncode == 0, f"Rocq replay failed:\n{res.stdout}\n{res.stderr}")
            solver_ledger.audit(res.stdout, len(thms), "HoldFast_ModeCrossReloc", ())
            units = ["HoldFastPrelude", "ModeCrossRelocCheck"] if used_prelude else ["ModeCrossRelocCheck"]
            rocq_cache.check_kernel(directory, units)

        negatives = (
            ("span-record", b"""module BadSpanReloc;
public record SpanWrap(Span<byte> View);
public Unit Bad<ghost usize M, ghost usize N>(
    ref Slots<SpanWrap, M> dst, ref Slots<SpanWrap, N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
{
    CopyRepresentation(src, ref dst, count);
    return ();
}
"""),
            ("cell-record", b"""module BadCellReloc;
public record CellWrap(LocalCell<u32> Cell);
public Unit Bad<ghost usize M, ghost usize N>(
    ref Slots<CellWrap, M> dst, ref Slots<CellWrap, N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
{
    CopyRepresentation(src, ref dst, count);
    return ();
}
"""),
            ("region-record", b"""module BadRegionReloc;
public record BorrowedView<region 'r>(in<'r> Span<byte> View);
public Unit Bad<region 'a, ghost usize M, ghost usize N>(
    ref Slots<BorrowedView<'a>, M> dst, ref Slots<BorrowedView<'a>, N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
{
    CopyRepresentation(src, ref dst, count);
    return ();
}
"""),
            ("generic-param", b"""module BadGenericReloc;
public Unit Bad<T, ghost usize M, ghost usize N>(
    ref Slots<T, M> dst, ref Slots<T, N> src, usize count)
    requires Slots.Disjoint(dst, src)
    requires count <= N
    requires count <= M
    requires src.CanWrite
    requires dst.CanRead
    requires LivePrefix(src, count)
    requires VacantSuffix(src, count)
    requires VacantRange(dst, 0usize, M)
{
    CopyRepresentation(src, ref dst, count);
    return ();
}
"""),
        )
        for label, bad_src in negatives:
            bad_parsed = parser.parse_source(compiled, bad_src, surface=True)
            with raises(HoldFastError, msg=f"mode crossing allowed non-crossing relocation for {label}") as raised:
                elaborate.elaborate(bad_src, bad_parsed)
            ensure(
                raised.exception.kind == "unsupported"
                and "mode-crossing represented value type" in raised.exception.message,
                f"wrong refusal for {label}: {raised.exception}",
            )


def cases() -> list[Case]:
    return [
        Case("all seven derived distributive modality combinators", _test_all_seven_combinators_positive),
        Case("domain and authority refusal controls", _test_domain_and_authority_refusals),
        Case("mode crossing derivation and refusals", _test_mode_crossing_derivation_and_refusals),
        Case("structure inspection via canonical HoldFast parser", _test_structure_inspection, lane="toolchain"),
        Case("mode profile derivation over HoldFast declarations", _test_mode_profile_structure_inspection, lane="toolchain"),
        Case("mode crossing slots relocation Rocq replay and refusals",
             _test_mode_crossing_slots_relocation_replay, lane="toolchain"),
        Case("Rocq kernel replay and tampered combinator certificate refusal",
             _test_rocq_combinator_replay_and_tamper, lane="toolchain"),
    ]
