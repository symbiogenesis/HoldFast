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
from toolchain.elaborate_types import _NAT, _apps, _constant
from toolchain.proof_certificates import VersionedEGraph


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


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("versioned-egraph-unit", _versioned_egraph_unit_cases),
        Case("egraph-congruence-and-branch-isolation",
             partial(_egraph_congruence_and_branch_isolation, batch=batch), lane="toolchain"),
        Case("weighted-nat-difference-logic",
             partial(_weighted_nat_difference_logic, batch=batch), lane="toolchain"),
        Case("fixed-int-order-certificates",
             partial(_fixed_int_order_certificates, batch=batch), lane="toolchain"),
        Case("kernel check proof certificates with rocqchk", batch.verify_all, lane="toolchain"),
    ]
