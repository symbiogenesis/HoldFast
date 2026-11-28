# SPDX-License-Identifier: Apache-2.0
"""Host and Rocq kernel replay tests for versioned e-graphs and order certificates."""

import contextlib
import subprocess
import tempfile
from functools import partial
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, parser, proofenv, rocq_cache, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.elaborate import _Elaborator
from toolchain.elaborate_protocol import _Protocol
from toolchain.elaborate_types import _BOOL, _NAT, _apps, _Binding, _constant, _term
from toolchain.proof_certificates import (
    MAX_POLY_DEGREE,
    MAX_POLY_VARS,
    NatPolyEqualizer,
    PropositionalPrechecker,
    VersionedEGraph,
)


def _versioned_egraph_unit_cases() -> None:
    proto = _Protocol(b"module M;")
    elab = _Elaborator(proto)
    eg = VersionedEGraph(elab)
    a, b, c, d, e, g = (_constant(name) for name in ("a", "b", "c", "d", "e", "g"))
    f = _constant("f")
    # 5-step transitivity chain: a == b == c == d == e == g
    p_ab = _constant("p_ab")
    p_bc = _constant("p_bc")
    p_cd = _constant("p_cd")
    p_de = _constant("p_de")
    p_eg = _constant("p_eg")
    elab.constants["f"] = elaborate._Binding(f, elab.pi(_NAT, elab.pi(_NAT, _NAT)))
    for sym in (a, b, c, d, e, g):
        elab.constants[str(sym.value)] = elaborate._Binding(sym, _NAT)
    elab.constants["p_ab"] = elaborate._Binding(p_ab, _apps(_constant("Eq"), _NAT, a, b))
    elab.constants["p_bc"] = elaborate._Binding(p_bc, _apps(_constant("Eq"), _NAT, b, c))
    elab.constants["p_cd"] = elaborate._Binding(p_cd, _apps(_constant("Eq"), _NAT, c, d))
    elab.constants["p_de"] = elaborate._Binding(p_de, _apps(_constant("Eq"), _NAT, d, e))
    elab.constants["p_eg"] = elaborate._Binding(p_eg, _apps(_constant("Eq"), _NAT, e, g))

    ensure(eg.assert_equality(_NAT, a, b, p_ab), "failed to assert a == b")
    ensure(eg.assert_equality(_NAT, b, c, p_bc), "failed to assert b == c")
    ensure(eg.assert_equality(_NAT, c, d, p_cd), "failed to assert c == d")
    ensure(eg.assert_equality(_NAT, d, e, p_de), "failed to assert d == e")
    ensure(eg.assert_equality(_NAT, e, g, p_eg), "failed to assert e == g")
    proof_ag = eg.explain(_NAT, a, g)
    if proof_ag is None:
        raise AssertionError("5-step transitivity chain failed to reconstruct")
    ensure(elab.convertible(elab.infer(proof_ag), _apps(_constant("Eq"), _NAT, a, g)),
           "reconstructed 5-step proof has wrong type")

    # Push/pop version isolation: branch equality must not leak after pop_version().
    x, y = _constant("x"), _constant("y")
    elab.constants["x"] = elaborate._Binding(x, _NAT)
    elab.constants["y"] = elaborate._Binding(y, _NAT)
    p_xy = _constant("p_xy")
    elab.constants["p_xy"] = elaborate._Binding(p_xy, _apps(_constant("Eq"), _NAT, x, y))

    depth = eg.push_version()
    ensure(depth == 1, "expected version depth 1")
    ensure(eg.assert_equality(_NAT, x, y, p_xy), "failed to assert x == y in child version")
    ensure(eg.equivalent(_apps(f, a, x), _apps(f, g, y)),
           "multi-arg congruence failed inside child version")
    congr_proof = eg.explain(_NAT, _apps(f, a, x), _apps(f, g, y))
    if congr_proof is None:
        raise AssertionError("multi-arg congruence proof reconstruction failed")
    ensure(elab.convertible(elab.infer(congr_proof), _apps(_constant("Eq"), _NAT, _apps(f, a, x), _apps(f, g, y))),
           "reconstructed congruence proof has wrong type")
    eg.pop_version()

    ensure(not eg.equivalent(x, y), "child-version equality leaked across pop_version")
    ensure(not eg.equivalent(_apps(f, a, x), _apps(f, g, y)),
           "child-version congruence leaked across pop_version")
    ensure(eg.equivalent(a, g), "parent-version equality lost after pop_version")

    # Budget exhaustion check
    eg_small = VersionedEGraph(elab)
    eg_small.merge_count = 512
    ensure(not eg_small.assert_equality(_NAT, a, b, p_ab),
           "merge budget exhaustion was not refused")


def _replay_gallina(module_name: str, source: bytes, consumers: str, expected_reports: int, *,
                    batch: rocq_cache.BatchChecker | None = None) -> None:
    with parser.cached_build(TOOLS.parent) as compiled:
        result = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True))
    ensure(not solver_ledger.ledger(result.gallina),
           f"proof certificates introduced solver-trust axioms:\n{result.gallina}")
    module = elaborate.gallina_module_name(module_name)
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-cert-")))
            stem = module_name
        else:
            directory = batch.work_dir
            stem = batch.unique_stem(module_name)
        target = directory / f"{stem}.v"
        unit_text, used_prelude = rocq_cache.use_cached_prelude(result.gallina + "\n" + consumers, directory)
        target.write_text(unit_text, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", target.name], cwd=directory,
                                capture_output=True, check=False, text=True, timeout=180)
        ensure(replay.returncode == 0, f"rocq c failed:\n{replay.stderr}")
        solver_ledger.audit(replay.stdout, expected_reports, module, ())
        if batch is not None:
            if used_prelude:
                batch.register("HoldFastPrelude")
            batch.register(stem)
        else:
            rocq_cache.check_kernel(directory, ["HoldFastPrelude", stem] if used_prelude else [stem])


def _egraph_congruence_and_branch_isolation(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module EGraphReplay;
public definition Nat StepF(Nat x) => x + 1;
public definition Nat Combine(Nat x, Nat y) => x + y;

public lemma LongChainAndMultiArg(Nat a, Nat b, Nat c, Nat d, Nat e, Nat g, Nat p, Nat q)
    requires a == b
    requires b == c
    requires c == d
    requires d == e
    requires e == g
    requires p == q
    ensures Combine(a, p) == Combine(g, q)
    proof
    {
        assert Combine(a, p) == Combine(g, q);
    }

public lemma NestedCongruence(Nat a, Nat b, Nat c, Nat d)
    requires a == b
    requires b == c
    requires StepF(c) == d
    ensures StepF(StepF(a)) == StepF(d)
    proof
    {
        assert StepF(StepF(a)) == StepF(d);
    }

public Nat ScopedBranch(Nat a, Nat b, Nat x, Nat y)
{
    if (a == b && x == y) {
        assert Combine(a, x) == Combine(b, y);
        return 1;
    } else {
        return 0;
    }
}
"""
    mod = elaborate.gallina_module_name("EGraphReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if "_assert_" in name or name.endswith(("_LongChainAndMultiArg", "_NestedCongruence"))
    ]
    ensure(len(checked_exports) == 3, f"expected 3 EGraph exports, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("EGraphReplay", source, consumers, 3, batch=batch)

    # Negative control: equality in `if` branch must not leak into `else` branch.
    leaked = source.replace(b"return 0;", b"assert Combine(a, x) == Combine(b, y);\n        return 0;")
    with parser.cached_build(TOOLS.parent) as compiled:
        with raises(HoldFastError, msg="branch equality leaked into else branch") as raised:
            elaborate.elaborate(leaked, parser.parse_source(compiled, leaked, surface=True))
        ensure(raised.exception.kind == "type", f"unexpected error kind: {raised.exception}")


def _weighted_nat_difference_logic(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module NatDiffReplay;
public Nat ChainedOffsets(Nat a, Nat b, Nat c)
{
    if (a + 2 <= b) {
        if (b + 1 <= c) {
            assert a + 3 <= c;
            assert a + 1 <= c;
        }
    }
    return c;
}

public Nat StrictToWeighted(Nat a, Nat b, Nat c)
{
    if (a < b && b < c) {
        assert a + 2 <= c;
        assert a + 1 < c;
    }
    return a;
}

public Nat ContradictoryNatBranch(Nat a, Nat b, Nat x)
{
    if (a + 2 <= b) {
        if (b <= a) {
            assert x == 0;
        }
    }
    return x;
}
"""
    mod = elaborate.gallina_module_name("NatDiffReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    assert_exports = [name for name in solver_ledger.math_exports(gallina) if "_assert_" in name]
    ensure(len(assert_exports) == 5, f"expected 5 Nat difference witnesses, got {assert_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in assert_exports) + "\n"
    _replay_gallina("NatDiffReplay", source, consumers, 5, batch=batch)

    for bad_old, bad_new in (
        (b"assert a + 3 <= c;", b"assert a + 4 <= c;"),
        (b"assert a + 1 < c;", b"assert a + 2 < c;"),
        (b"if (b <= a)", b"if (a <= b)"),
    ):
        bad = source.replace(bad_old, bad_new)
        with (
            parser.cached_build(TOOLS.parent) as compiled,
            raises(HoldFastError, msg=f"invalid Nat difference assertion accepted: {bad_new!r}"),
        ):
            elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))


def _fixed_int_order_certificates(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module IntOrderReplay;
public usize UsizeGuards(usize a, usize b, usize c)
{
    if (a <= b) {
        if (b < c) {
            assert a < c;
            assert a <= c;
        }
    }
    if (b < a) {
        return b;
    } else {
        assert a <= b;
        return a;
    }
}

public i32 SignedGuards(i32 x, i32 y, i32 z)
{
    if (x < y && y <= z) {
        assert x < z;
    }
    return x;
}

public usize ContradictoryUsizeBranch(usize a, usize b, usize z)
{
    if (a < b) {
        if (b <= a) {
            assert z == 0usize;
        }
    }
    return z;
}
"""
    mod = elaborate.gallina_module_name("IntOrderReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    assert_exports = [name for name in solver_ledger.math_exports(gallina) if "_assert_" in name]
    ensure(len(assert_exports) == 5, f"expected 5 integer order witnesses, got {assert_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in assert_exports) + "\n"
    _replay_gallina("IntOrderReplay", source, consumers, 5, batch=batch)

    for bad_old, bad_new in (
        (b"assert a <= b;", b"assert a < b;"),
        (b"assert x < z;", b"assert z < x;"),
        (b"if (b <= a)", b"if (a <= b)"),
    ):
        bad = source.replace(bad_old, bad_new)
        with (
            parser.cached_build(TOOLS.parent) as compiled,
            raises(HoldFastError, msg=f"invalid fixed-int assertion accepted: {bad_new!r}"),
        ):
            elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))


def _slotted_egraph_unit_cases() -> None:
    proto = _Protocol(b"module SlottedUnit;")
    elab = _Elaborator(proto)
    eg = VersionedEGraph(elab)
    a, b, c, d = (_constant(name) for name in ("a", "b", "c", "d"))
    f = _constant("f")
    ho_apply = _constant("ho_apply")
    fn_ty = elab.pi(_NAT, _NAT)
    elab.constants["f"] = elaborate._Binding(f, elab.pi(_NAT, fn_ty))
    elab.constants["ho_apply"] = elaborate._Binding(ho_apply, elab.pi(fn_ty, fn_ty))
    for sym in (a, b, c, d):
        elab.constants[str(sym.value)] = elaborate._Binding(sym, _NAT)
    p_ab = _constant("p_ab")
    p_cd = _constant("p_cd")
    elab.constants["p_ab"] = elaborate._Binding(p_ab, _apps(_constant("Eq"), _NAT, a, b))
    elab.constants["p_cd"] = elaborate._Binding(p_cd, _apps(_constant("Eq"), _NAT, c, d))

    # Distinct binder variable IDs with structurally identical bodies: alpha-equivalence.
    x = elab.fresh(_NAT)
    y = elab.fresh(_NAT)
    u = elab.fresh(_NAT)
    v = elab.fresh(_NAT)
    lam_alpha_1 = _term("lam", _NAT, _apps(f, x, _term("nat", value=1)), value=x.value)
    lam_alpha_2 = _term("lam", _NAT, _apps(f, y, _term("nat", value=1)), value=y.value)
    ensure(eg.equivalent(lam_alpha_1, lam_alpha_2), "alpha-equivalent lambdas did not merge in slotted e-graph")
    alpha_proof = eg.explain(fn_ty, lam_alpha_1, lam_alpha_2)
    if alpha_proof is None:
        raise AssertionError("alpha-equivalence proof synthesis failed")
    ensure(
        elab.convertible(elab.infer(alpha_proof), _apps(_constant("Eq"), fn_ty, lam_alpha_1, lam_alpha_2)),
        "alpha-equivalence proof has wrong type",
    )

    # Binder-crossing congruence without funext, isolated inside a push_version/pop_version scope.
    lam_a = _term("lam", _NAT, _apps(f, x, a), value=x.value)
    lam_b = _term("lam", _NAT, _apps(f, y, b), value=y.value)
    ensure(not eg.equivalent(lam_a, lam_b), "unrelated hole lambdas merged prematurely")

    nested_a = _term("lam", _NAT, _term("lam", _NAT, _apps(f, _apps(f, x, y), a), value=y.value), value=x.value)
    nested_b = _term("lam", _NAT, _term("lam", _NAT, _apps(f, _apps(f, u, v), b), value=v.value), value=u.value)
    nested_ty = elab.pi(_NAT, fn_ty)

    depth = eg.push_version()
    ensure(depth == 1, f"expected depth 1, got {depth}")
    ensure(eg.assert_equality(_NAT, a, b, p_ab), "failed to assert a == b in slotted child version")
    ensure(eg.assert_equality(_NAT, c, d, p_cd), "failed to assert c == d in slotted child version")

    ensure(eg.equivalent(lam_a, lam_b), "binder-crossing congruence failed under slotted lambdas")
    lam_proof = eg.explain(fn_ty, lam_a, lam_b)
    if lam_proof is None:
        raise AssertionError("binder-crossing lambda congruence failed to synthesize proof")
    ensure(
        elab.convertible(elab.infer(lam_proof), _apps(_constant("Eq"), fn_ty, lam_a, lam_b)),
        "binder-crossing lambda congruence proof has wrong type",
    )

    ensure(eg.equivalent(nested_a, nested_b), "nested slotted binder congruence failed")
    nested_proof = eg.explain(nested_ty, nested_a, nested_b)
    if nested_proof is None:
        raise AssertionError("nested slotted binder proof failed")
    ensure(
        elab.convertible(elab.infer(nested_proof), _apps(_constant("Eq"), nested_ty, nested_a, nested_b)),
        "nested slotted binder proof has wrong type",
    )

    outer_l = _apps(ho_apply, lam_a, c)
    outer_r = _apps(ho_apply, lam_b, d)
    ensure(eg.equivalent(outer_l, outer_r), "higher-order congruence with slotted lambda arg failed")
    outer_proof = eg.explain(_NAT, outer_l, outer_r)
    if outer_proof is None:
        raise AssertionError("higher-order slotted congruence proof synthesis failed")
    ensure(
        elab.convertible(elab.infer(outer_proof), _apps(_constant("Eq"), _NAT, outer_l, outer_r)),
        "higher-order slotted congruence proof has wrong type",
    )

    # Capture-avoidance control: (fun x => f x x) must NOT merge with (fun y => f y x).
    lam_diag = _term("lam", _NAT, _apps(f, x, x), value=x.value)
    lam_free = _term("lam", _NAT, _apps(f, y, x), value=y.value)
    ensure(not eg.equivalent(lam_diag, lam_free), "slotted e-graph conflated bound slot with free variable")

    eg.pop_version()
    ensure(not eg.equivalent(lam_a, lam_b), "slotted lambda congruence leaked across pop_version")
    ensure(eg.equivalent(lam_alpha_1, lam_alpha_2), "alpha-equivalence lost after pop_version")


def _slotted_egraph_and_int_congruence(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module SlottedIntReplay;
public definition Nat Combine(Nat x, Nat y) => x + y;
public definition Nat ApplyNat(Fn(Nat x) -> Nat f, Nat z) => f(z);
public definition usize MixUsize(usize x, usize y) => x;
public definition bool FlipBool(bool b) => !b;

public lemma HigherOrderLambdaCongr(Nat a, Nat b, Nat c, Nat d)
    requires a == b
    requires c == d
    ensures ApplyNat(Fn(Nat x) -> Nat => Combine(x, a), c)
         == ApplyNat(Fn(Nat y) -> Nat => Combine(y, b), d)
    proof
    {
        assert ApplyNat(Fn(Nat x) -> Nat => Combine(x, a), c)
            == ApplyNat(Fn(Nat y) -> Nat => Combine(y, b), d);
    }

public usize ScopedIntAndBoolCongr(usize a, usize b, usize c, usize p, usize q, bool f1, bool f2, bool f3)
{
    if (a == b && b == c && p == q) {
        assert MixUsize(a, p) == MixUsize(c, q);
    } else {
        return a;
    }
    if (f1 == f2 && f2 == f3) {
        assert FlipBool(f1) == FlipBool(f3);
        return a;
    } else {
        return b;
    }
}
"""
    mod = elaborate.gallina_module_name("SlottedIntReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if "_assert_" in name or name.endswith("_HigherOrderLambdaCongr")
    ]
    ensure(len(checked_exports) == 3, f"expected 3 slotted/int e-graph exports, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("SlottedIntReplay", source, consumers, 3, batch=batch)

    leaked = source.replace(b"return a;\n    } else {\n        return b;", b"return a;\n    } else {\n        assert FlipBool(f1) == FlipBool(f3);\n        return b;")
    with (
        parser.cached_build(TOOLS.parent) as compiled,
        raises(HoldFastError, msg="bool branch equality leaked into else branch"),
    ):
        elaborate.elaborate(leaked, parser.parse_source(compiled, leaked, surface=True))


def _assert_by_slotted_egraph_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module AssertBySlottedReplay;
public definition Nat Combine(Nat x, Nat y) => x + y;
public definition u32 Bump(u32 x) => x;

public lemma BridgeNat(Nat x, Nat y)
    requires x == y
    ensures x == y
    proof
    {
        assert x == y;
    }

public lemma BridgeU32(u32 a, u32 b)
    requires a == b
    ensures a == b
    proof
    {
        assert a == b;
    }

public lemma ByLambdaCongrAndTrans(Nat a, Nat b, Nat c)
    requires a == b
    requires b == c
    ensures (Fn(Nat x) -> Nat => Combine(x, a)) == (Fn(Nat y) -> Nat => Combine(y, c))
    proof
    {
        assert (Fn(Nat x) -> Nat => Combine(x, a)) == (Fn(Nat y) -> Nat => Combine(y, c))
            by BridgeNat(b, c);
    }

public lemma ByU32LiftAndCongr(u32 x, u32 y, u32 z)
    requires x == y
    requires y == z
    ensures Bump(x) == Bump(z)
    proof
    {
        assert Bump(x) == Bump(z) by BridgeU32(y, z);
    }

public u32 FnAssertByEGraph(u32 x, u32 y, u32 z)
{
    if (x == y && y == z) {
        assert Bump(x) == Bump(z) by BridgeU32(y, z);
        return x;
    } else {
        return z;
    }
}
"""
    mod = elaborate.gallina_module_name("AssertBySlottedReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if name.endswith(("_ByLambdaCongrAndTrans", "_ByU32LiftAndCongr")) or "_assert_" in name
    ]
    ensure(len(checked_exports) >= 3, f"expected >= 3 assert-by egraph exports, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("AssertBySlottedReplay", source, consumers, len(checked_exports), batch=batch)


def _mizar_unit_limits() -> None:
    proto = _Protocol(b"module MizarLimits;")
    elab = _Elaborator(proto)
    poly = NatPolyEqualizer(elab)

    # Exceeding MAX_POLY_VARS must fail closed cleanly (return None).
    many_l = _term("nat", value=0)
    many_r = _term("nat", value=0)
    for idx in range(MAX_POLY_VARS + 2):
        sym = _constant(f"v_{idx}")
        elab.constants[f"v_{idx}"] = elaborate._Binding(sym, _NAT)
        many_l = _apps(_constant("+"), many_l, sym)
        many_r = _apps(_constant("+"), sym, many_r)
    ensure(poly.prove_equal(many_l, many_r) is None, "NatPolyEqualizer accepted expression past MAX_POLY_VARS")

    # Exceeding MAX_POLY_DEGREE must fail closed cleanly (return None).
    x = _constant("v_0")
    high_deg = x
    for _ in range(MAX_POLY_DEGREE + 1):
        high_deg = _apps(_constant("*"), high_deg, x)
    ensure(poly.prove_equal(high_deg, high_deg) is not None, "identical high-degree reflexive check should use Refl")
    ensure(
        poly.prove_equal(_apps(_constant("+"), high_deg, _term("nat", value=0)), high_deg) is None,
        "NatPolyEqualizer accepted polynomial past MAX_POLY_DEGREE",
    )

    # PropositionalPrechecker tableau refuses tautologies above MAX_PRECHECKER_ATOMS (5).
    pre = PropositionalPrechecker(elab)
    atoms = [_constant(f"b_{i}") for i in range(6)]
    for i, atom in enumerate(atoms):
        elab.constants[f"b_{i}"] = elaborate._Binding(atom, _BOOL)
    big_taut = _apps(_constant("||"), atoms[0], _apps(_constant("!"), atoms[0]))
    for atom in atoms[1:]:
        big_taut = _apps(_constant("||"), big_taut, _apps(_constant("||"), atom, _apps(_constant("!"), atom)))
    big_goal = _apps(_constant("Eq"), _BOOL, big_taut, _term("bool", value=1))
    ensure(pre.prove(big_goal, ()) is None, "PropositionalPrechecker tableau accepted > 5 atoms")

    # Unit propagation still works with > 5 distinct atoms when forward-chaining suffices.
    facts: list[_Binding] = []
    p0 = _constant("p_0")
    elab.constants["p_0"] = elaborate._Binding(p0, _BOOL)
    facts.append(_Binding(p0, _apps(_constant("Eq"), _BOOL, atoms[0], _term("bool", value=1))))
    for i in range(5):
        imp_term = _apps(_constant("==>"), atoms[i], atoms[i + 1])
        h_name = f"imp_{i}"
        elab.constants[h_name] = elaborate._Binding(
            _constant(h_name), _apps(_constant("Eq"), _BOOL, imp_term, _term("bool", value=1)),
        )
        facts.append(_Binding(_constant(h_name), elab.constants[h_name].type))
    target_goal = _apps(_constant("Eq"), _BOOL, atoms[5], _term("bool", value=1))
    prop_proof = pre.prove(target_goal, tuple(facts))
    ensure(prop_proof is not None, "PropositionalPrechecker unit propagation failed on 6-atom chain")


def _mizar_equalizer_nat_poly_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module MizarNatPolyReplay;
public definition Nat StepF(Nat x) => x + 1;

public lemma PolyIdentities(Nat a, Nat b, Nat c)
    ensures (a + b) * (c + 1) + 0 == c * b + a * c + b + a
    proof
    {
        assert a + b == b + a;
        assert (a + b) * (c + 1) + 0 == c * b + a * c + b + a;
        assert (a + b) * (a + b) == a * a + 2 * a * b + b * b;
        assert Succ(a + b) == b + 1 + a;
    }

public lemma PolyModEGraph(Nat a, Nat b, Nat c)
    requires a == b
    ensures StepF((a + c) * 2) == StepF(2 * c + b + b)
    proof
    {
        assert StepF((a + c) * 2) == StepF(2 * c + b + b);
    }

public Nat InlinePolyBranch(Nat a, Nat b, Nat c)
{
    if (a == b) {
        assert StepF((a + c) * 2) == StepF(2 * c + b + b);
        return 1;
    } else {
        return 0;
    }
}
"""
    mod = elaborate.gallina_module_name("MizarNatPolyReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if "_assert_" in name or name.endswith(("_PolyIdentities", "_PolyModEGraph"))
    ]
    ensure(len(checked_exports) == 3, f"expected 3 Nat poly equalizer exports, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("MizarNatPolyReplay", source, consumers, 3, batch=batch)

    for bad_old, bad_new in (
        (b"assert a + b == b + a;", b"assert a + b == a + c;"),
        (b"assert (a + b) * (a + b) == a * a + 2 * a * b + b * b;", b"assert (a + b) * c == a * c + b;"),
        (b"return 0;", b"assert StepF((a + c) * 2) == StepF(2 * c + b + b);\n        return 0;"),
    ):
        bad = source.replace(bad_old, bad_new)
        with (
            parser.cached_build(TOOLS.parent) as compiled,
            raises(HoldFastError, msg=f"invalid Nat polynomial assertion accepted: {bad_new!r}"),
        ):
            elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))


def _mizar_equalizer_properties_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module MizarPropertiesReplay;
public definition bool FlipBool(bool b) => !b;
public definition usize MixUsize(usize x, usize y) => x & y;

public lemma BoolAndIntProperties(bool b, bool c, u32 x, u32 y, u32 z, usize u, usize v, usize w, usize k)
    requires x <= 100u32
    requires y <= 100u32
    requires z <= 100u32
    ensures MixUsize(u & v, w | k) == MixUsize(v & u, k | w)
    proof
    {
        assert !(!b) == b;
        assert FlipBool(!(!b)) == FlipBool(b);
        assert ~(~x) == x;
        assert (b && b) == b;
        assert (c || c) == c;
        assert (x & x) == x;
        assert (y | y) == y;
        assert ((x + y) + z) == (z + (x + y));
        assert ((x ^ y) ^ z) == (z ^ (y ^ x));
        assert (x ^ x) == 0u32;
        assert (x ^ 0u32) == x;
        assert (x + 0u32) == x;
        assert (x & 0u32) == 0u32;
        assert (x | 0u32) == x;
        assert (b && true) == b;
        assert (b || false) == b;
        assert MixUsize(u & v, w | k) == MixUsize(v & u, k | w);
    }
"""
    mod = elaborate.gallina_module_name("MizarPropertiesReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if "_assert_" in name or name.endswith("_BoolAndIntProperties")
    ]
    ensure(len(checked_exports) == 1, f"expected 1 equalizer property export, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("MizarPropertiesReplay", source, consumers, 1, batch=batch)

    for bad_old, bad_new in (
        (b"assert (x ^ x) == 0u32;", b"assert (x ^ y) == 0u32;"),
        (b"assert (x + 0u32) == x;", b"assert (x + 1u32) == x;"),
        (b"assert !(!b) == b;", b"assert !b == b;"),
    ):
        bad = source.replace(bad_old, bad_new)
        with (
            parser.cached_build(TOOLS.parent) as compiled,
            raises(HoldFastError, msg=f"invalid property/reduction assertion accepted: {bad_new!r}"),
        ):
            elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))


def _mizar_prechecker_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module MizarPrecheckerReplay;
public lemma NaturalDeductionRules(bool p, bool q, bool r)
    requires p == true ==> q == true
    requires (q ==> r) == true
    requires p == true
    ensures r == true
    proof
    {
        assert q;
        assert r;
        assert p || r;
    }

public lemma ModusTollensAndSyllogism(bool p, bool q, bool s)
    requires p == true ==> q == true
    requires (p || s) == true
    requires !q == true
    ensures s == true
    proof
    {
        assert !p;
        assert s;
    }

public lemma TautologiesAndDeMorgan(bool p, bool q)
    ensures !(p && q) == (!p || !q)
    proof
    {
        assert p || !p;
        assert !(p && !p);
        assert (p ==> q) ==> (!q ==> !p);
        assert !(p && q) == (!p || !q);
    }

public Nat ContradictionBranches(bool p, Nat a, Nat b, Nat c, Nat x)
{
    if (p && !p) {
        assert x == 0;
        return 0;
    }
    if (a == b) {
        if (a != b) {
            assert x == 0;
            return 0;
        }
    }
    if (a == b && b == c) {
        if (a != c) {
            assert x == 0;
            return 0;
        }
    }
    return x;
}
"""
    mod = elaborate.gallina_module_name("MizarPrecheckerReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if "_assert_" in name
        or name.endswith(("_NaturalDeductionRules", "_ModusTollensAndSyllogism", "_TautologiesAndDeMorgan"))
    ]
    ensure(len(checked_exports) == 6, f"expected 6 prechecker exports, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("MizarPrecheckerReplay", source, consumers, 6, batch=batch)

    for bad_old, bad_new in (
        (b"requires p == true ==> q == true\n    requires (q ==> r) == true\n    requires p == true\n    ensures r == true",
         b"requires p == true ==> q == true\n    requires q == true\n    ensures p == true"),
        (b"assert !p;\n        assert s;", b"assert p;"),
        (b"if (a != b) {", b"if (a != c) {"),
    ):
        bad = source.replace(bad_old, bad_new)
        with (
            parser.cached_build(TOOLS.parent) as compiled,
            raises(HoldFastError, msg=f"invalid prechecker assertion accepted: {bad_new!r}"),
        ):
            elaborate.elaborate(bad, parser.parse_source(compiled, bad, surface=True))


def _mizar_multi_by_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module MizarMultiByReplay;
public definition Nat Combine(Nat x, Nat y) => x + y;

public lemma BridgeNat(Nat x, Nat y)
    requires x == y
    ensures x == y
    proof
    {
        assert x == y;
    }

public lemma StepImp(bool a, bool b)
    requires a == true ==> b == true
    ensures a == true ==> b == true
    proof
    {
        assert b;
    }

public lemma FactTrue(bool a)
    requires a == true
    ensures a == true
    proof
    {
        assert a;
    }

public lemma MultiFactByEq(Nat a, Nat b, Nat c, Nat x, Nat z)
    requires a == b
    requires b == c
    requires x == z
    ensures Combine(a, x) == Combine(c, z)
    proof
    {
        assert Combine(a, x) == Combine(c, z) by (BridgeNat(a, b), BridgeNat(b, c), BridgeNat(x, z));
    }

public lemma MultiFactByProp(bool p, bool q, bool r)
    requires p == true ==> q == true
    requires q == true ==> r == true
    requires p == true
    ensures r == true
    proof
    {
        assert r by (StepImp(p, q), StepImp(q, r), FactTrue(p));
    }
"""
    mod = elaborate.gallina_module_name("MizarMultiByReplay")
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
    checked_exports = [
        name
        for name in solver_ledger.math_exports(gallina)
        if "_assert_" in name or name.endswith(("_MultiFactByEq", "_MultiFactByProp"))
    ]
    ensure(len(checked_exports) == 2, f"expected 2 multi-by exports, got {checked_exports}")
    consumers = "\n".join(f"Print Assumptions {mod}.{name}." for name in checked_exports) + "\n"
    _replay_gallina("MizarMultiByReplay", source, consumers, 2, batch=batch)

    bad_unlinked = source.replace(
        b"public lemma MultiFactByEq(Nat a, Nat b, Nat c, Nat x, Nat z)",
        b"public lemma MultiFactByEq(Nat a, Nat b, Nat c, Nat x, Nat z, Nat w)",
    ).replace(
        b"ensures Combine(a, x) == Combine(c, z)",
        b"ensures Combine(a, x) == Combine(c, w)",
    ).replace(
        b"assert Combine(a, x) == Combine(c, z)",
        b"assert Combine(a, x) == Combine(c, w)",
    )
    with (
        parser.cached_build(TOOLS.parent) as compiled,
        raises(HoldFastError, msg="insufficient multi-fact by tuple was accepted"),
    ):
        elaborate.elaborate(bad_unlinked, parser.parse_source(compiled, bad_unlinked, surface=True))

    bad_nonprop = source.replace(
        b"by (BridgeNat(a, b), BridgeNat(b, c), BridgeNat(x, z));",
        b"by (BridgeNat(a, b), 42);",
    )
    with (
        parser.cached_build(TOOLS.parent) as compiled,
        raises(HoldFastError, msg="non-proposition in multi-fact by tuple was accepted") as raised,
    ):
        elaborate.elaborate(bad_nonprop, parser.parse_source(compiled, bad_nonprop, surface=True))
    ensure(raised.exception.kind == "type", f"unexpected error kind: {raised.exception}")


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("versioned-egraph-unit", _versioned_egraph_unit_cases),
        Case("slotted-egraph-unit", _slotted_egraph_unit_cases),
        Case("mizar-equalizer-prechecker-unit-limits", _mizar_unit_limits),
        Case("egraph-congruence-and-branch-isolation",
             partial(_egraph_congruence_and_branch_isolation, batch=batch), lane="toolchain"),
        Case("slotted-egraph-and-int-congruence",
             partial(_slotted_egraph_and_int_congruence, batch=batch), lane="toolchain"),
        Case("assert-by-slotted-egraph-replay",
             partial(_assert_by_slotted_egraph_replay, batch=batch), lane="toolchain"),
        Case("weighted-nat-difference-logic",
             partial(_weighted_nat_difference_logic, batch=batch), lane="toolchain"),
        Case("fixed-int-order-certificates",
             partial(_fixed_int_order_certificates, batch=batch), lane="toolchain"),
        Case("mizar-equalizer-nat-poly-replay",
             partial(_mizar_equalizer_nat_poly_replay, batch=batch), lane="toolchain"),
        Case("mizar-equalizer-properties-replay",
             partial(_mizar_equalizer_properties_replay, batch=batch), lane="toolchain"),
        Case("mizar-prechecker-replay",
             partial(_mizar_prechecker_replay, batch=batch), lane="toolchain"),
        Case("mizar-multi-by-replay",
             partial(_mizar_multi_by_replay, batch=batch), lane="toolchain"),
        Case("kernel check proof certificates with rocqchk", batch.verify_all, lane="toolchain"),
    ]
