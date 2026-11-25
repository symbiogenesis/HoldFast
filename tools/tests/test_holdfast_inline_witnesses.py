# SPDX-License-Identifier: Apache-2.0
"""Kernel replay of executable assertions whose witnesses erase from the result."""

import subprocess
import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, elaborate_proofs, parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError


def _unused_witness() -> None:
    source = b"""module InlineWitness;
public Nat Observe(Nat n) requires n <= 4 {
    proof { assert (n <= 5) == true; assert n < 7; }
    return n;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(program: bytes) -> str:
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(source)
        for comparison in (b"n <= 3", b"n < 4"):
            with raises(HoldFastError) as failure:
                check(source.replace(b"n <= 5", comparison))
            ensure(failure.exception.line == 3 and comparison.decode() in failure.exception.message,
                   f"wrong refusal for inline assertion: {failure.exception}")

    start = source.index(b"assert")
    end = source.index(b";", start) + 1
    [name] = [item for item in solver_ledger.math_exports(gallina) if item.startswith(f"holdfast_assert_{start}_{end}_")]
    module = elaborate.gallina_module_name("InlineWitness")
    consumer = (f"\nExample bound : forall n, Nat.leb n 4 = true -> Nat.leb n 5 = true := {module}.{name}.\n"
                "Print Assumptions bound.\n")
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        target = directory / "Witness.v"
        target.write_text(gallina + consumer, encoding="utf-8")
        launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
        compile_unit = [*launch, "rocq", "c", "-q", target.name]
        replay = subprocess.run(compile_unit, cwd=directory, capture_output=True, check=True, timeout=180)
        solver_ledger.audit(replay.stdout.decode(), 1, module, ())
        subprocess.run([*launch, "rocqchk", "-silent", "Witness"], cwd=directory, check=True, timeout=180)
        target.write_text(gallina + consumer.replace("n 5 = true", "n 3 = true"), encoding="utf-8")
        rejected = subprocess.run(compile_unit, cwd=directory, capture_output=True, check=False, timeout=180)
        ensure(rejected.returncode != 0 and b"expected to have type" in rejected.stderr,
               "the checked witness satisfied a stronger independent conclusion")


def _branch_witnesses() -> None:
    source = b"""module InlineBranches;
public lemma AddZeroRight(Nat n) ensures n + 0 == n
proof {
    match (n) {
        0 => assert 0 + 0 == 0;
        Succ(p) => assert Succ(p) + 0 == Succ(p) by AddZeroRight(p);
    }
}
public Nat Observe(Nat n) {
    if (n < 5) {
        assert n <= 4;
        return n;
    } else {
        assert n > 3;
        assert n + 0 == n by AddZeroRight(n);
        return n;
    }
}
public Nat Clamp(Nat n) {
    var result = n;
    if (n <= 4) {
        assert n < 6;
    } else {
        assert 5 <= n;
        result = 4;
    }
    return result;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(program: bytes) -> str:
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(source)
        for original, replacement in (
            (b"n <= 4;", b"n <= 3;"),
            (b"n > 3;", b"n < 5;"),
            (b"n + 0 == n by AddZeroRight(n);", b"n + 0 == n;"),
        ):
            neighbor = source.replace(original, replacement)
            with raises(HoldFastError) as failure:
                check(neighbor)
            line = neighbor[:neighbor.index(b"assert " + replacement)].count(b"\n") + 1
            ensure(failure.exception.line == line and replacement[:-1].decode() in failure.exception.message,
                   f"wrong outstanding assertion: {failure.exception}")
        escaped = source.replace(b"    return result;", b"    assert n < 6;\n    return result;")
        with raises(HoldFastError) as failure:
            check(escaped)
        ensure("assertion could not be established: n < 6" in failure.exception.message,
               f"a branch proof survived the join: {failure.exception}")

    _replay_witnesses("InlineBranches", source, gallina, (
        ("small", b"assert n <= 4;", "forall n, Nat.ltb n 5 = true -> Nat.leb n 4 = true"),
        ("large", b"assert n > 3;", "forall n, Nat.ltb n 5 = false -> Nat.ltb 3 n = true"),
        ("explicit", b"assert n + 0 == n by AddZeroRight(n);", "forall n, Nat.add n 0 = n"),
        ("before_join", b"assert n < 6;", "forall n, Nat.leb n 4 = true -> Nat.ltb n 6 = true"),
        ("non_strict_false", b"assert 5 <= n;", "forall n, Nat.leb n 4 = false -> Nat.leb 5 n = true"),
    ))


def _replay_witnesses(
    module_name: str, source: bytes, gallina: str, witnesses: tuple[tuple[str, bytes, str], ...],
) -> None:
    module = elaborate.gallina_module_name(module_name)
    consumers = []
    for label, assertion, statement in witnesses:
        start = source.index(assertion)
        end = start + len(assertion)
        [name] = [item for item in solver_ledger.math_exports(gallina)
                  if item.startswith(f"holdfast_assert_{start}_{end}_")]
        consumers.append(f"Example {label} : {statement} := {module}.{name}.\nPrint Assumptions {label}.\n")
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        target = directory / "BranchWitnesses.v"
        target.write_text(gallina + "\n" + "".join(consumers), encoding="utf-8")
        launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
        replay = subprocess.run([*launch, "rocq", "c", "-q", target.name], cwd=directory,
                                capture_output=True, check=False, text=True, timeout=180)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(consumers), module, ())
        subprocess.run([*launch, "rocqchk", "-silent", target.stem], cwd=directory, check=True, timeout=180)


def _joined_branch_witnesses() -> None:
    source = b"""module JoinedBranches;
public Nat Observe(Nat n, Nat m, Nat k, Fn(Nat value) -> type[Eq<bool>(n < k, true)] supplied) {
    if (n < m) {
        if (k < m) {
            return n;
        } else {
            assert n < k;
            return n;
        }
    } else {
        return n;
    }
}
"""
    assertion = b"assert n < k;"
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(program: bytes) -> str:
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(source)
        changed = source.replace(b"k < m", b"m < k")
        with raises(HoldFastError) as failure:
            check(changed)
        ensure(failure.exception.line == 7 and "assertion could not be established: n < k" in failure.exception.message,
               f"changing the consumed guard gave the wrong refusal: {failure.exception}")
        explicit = b"assert n < k by supplied(k);"
        repaired = source.replace(assertion, explicit)
        with patch.object(elaborate_proofs, "_MAX_NAT_BOUND_JOINS", 0):
            with raises(HoldFastError) as failure:
                check(source)
            ensure(failure.exception.kind == "limit" and failure.exception.line == 7
                   and "exhausted 0 Nat bound joins: n < k" in failure.exception.message,
                   f"exhaustion lost the residual assertion: {failure.exception}")
            repaired_gallina = check(repaired)

    _replay_witnesses("JoinedBranches", source, gallina, (
        ("joined", assertion, "forall n m k, Nat.ltb n m = true -> Nat.ltb k m = false -> Nat.ltb n k = true"),
    ))
    _replay_witnesses("JoinedBranches", repaired, repaired_gallina, (
        ("repaired", explicit, "forall n k, (nat -> Nat.ltb n k = true) -> Nat.ltb n k = true"),
    ))


def cases() -> list[Case]:
    return [Case("erased assertion exports its exact conditional proof", _unused_witness, lane="toolchain"),
            Case("strict branch bounds replay with their own guard", _branch_witnesses, lane="toolchain"),
            Case("strict bounds join only scoped premises within the search limit", _joined_branch_witnesses,
                 lane="toolchain")]
