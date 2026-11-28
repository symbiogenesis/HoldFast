# SPDX-License-Identifier: Apache-2.0
"""Kernel replay of executable assertions whose witnesses erase from the result."""

import contextlib
import subprocess
import tempfile
from functools import partial
from pathlib import Path
from unittest.mock import patch

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, elaborate_proofs, parser, proofenv, rocq_cache, solver_ledger
from toolchain.ast import HoldFastError


def _unused_witness(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory()))
            stem = "Witness"
        else:
            directory = batch.work_dir
            stem = batch.unique_stem("Witness")
        target = directory / f"{stem}.v"
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + consumer, directory)
        target.write_text(unit_text, encoding="utf-8")
        compile_unit = [*proofenv.rocq_command(), "-q", target.name]
        replay = subprocess.run(compile_unit, cwd=directory, capture_output=True, check=True, timeout=180)
        solver_ledger.audit(replay.stdout.decode(), 1, module, ())
        if batch is not None:
            if used_prelude:
                batch.register("HoldFastPrelude")
            batch.register(stem)
        else:
            rocq_cache.check_kernel(directory, ["HoldFastPrelude", stem] if used_prelude else [stem])
        tampered = directory / "TamperedWitness.v"
        tampered_text, _ = rocq_cache.use_cached_prelude(
            gallina + consumer.replace("n 5 = true", "n 3 = true"), directory,
        )
        tampered.write_text(tampered_text, encoding="utf-8")
        rejected = subprocess.run([*proofenv.rocq_command(), "-q", tampered.name], cwd=directory,
                                  capture_output=True, check=False, timeout=180)
        ensure(rejected.returncode != 0 and b"expected to have type" in rejected.stderr,
               "the checked witness satisfied a stronger independent conclusion")


def _branch_witnesses(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module InlineBranches;
public definition Nat IdNat(Nat n) => match (n) { 0 => 0, Succ(p) => Succ(IdNat(p)) };
public lemma IdNatEq(Nat n) ensures IdNat(n) == n
proof {
    match (n) {
        0 => assert IdNat(0) == 0;
        Succ(p) => assert IdNat(Succ(p)) == Succ(p) by IdNatEq(p);
    }
}
public Nat Observe(Nat n) {
    if (n < 5) {
        assert n <= 4;
        return n;
    } else {
        assert n > 3;
        assert IdNat(n) == n by IdNatEq(n);
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
            (b"IdNat(n) == n by IdNatEq(n);", b"IdNat(n) == n;"),
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
        ("explicit", b"assert IdNat(n) == n by IdNatEq(n);", "forall n, HoldFast_InlineBranches.holdfast_d0_IdNat n = n"),
        ("before_join", b"assert n < 6;", "forall n, Nat.leb n 4 = true -> Nat.ltb n 6 = true"),
        ("non_strict_false", b"assert 5 <= n;", "forall n, Nat.leb n 4 = false -> Nat.leb 5 n = true"),
    ), batch=batch)


def _replay_witnesses(
    module_name: str, source: bytes, gallina: str, witnesses: tuple[tuple[str, bytes, str], ...], *,
    batch: rocq_cache.BatchChecker | None = None,
) -> None:
    module = elaborate.gallina_module_name(module_name)
    consumers = []
    for label, assertion, statement in witnesses:
        start = source.index(assertion)
        end = start + len(assertion)
        [name] = [item for item in solver_ledger.math_exports(gallina)
                  if item.startswith(f"holdfast_assert_{start}_{end}_")]
        consumers.append(f"Example {label} : {statement} := {module}.{name}.\nPrint Assumptions {label}.\n")
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory()))
            stem = "BranchWitnesses"
        else:
            directory = batch.work_dir
            stem = batch.unique_stem(module_name)
        target = directory / f"{stem}.v"
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + "\n" + "".join(consumers), directory)
        target.write_text(unit_text, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", target.name], cwd=directory,
                                capture_output=True, check=False, text=True, timeout=180)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(consumers), module, ())
        if batch is not None:
            if used_prelude:
                batch.register("HoldFastPrelude")
            batch.register(stem)
        else:
            rocq_cache.check_kernel(directory, ["HoldFastPrelude", stem] if used_prelude else [stem])


def _joined_branch_witnesses(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    ), batch=batch)
    _replay_witnesses("JoinedBranches", repaired, repaired_gallina, (
        ("repaired", explicit, "forall n k, (nat -> Nat.ltb n k = true) -> Nat.ltb n k = true"),
    ), batch=batch)


def _translated_branch_bounds(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module TranslatedBounds;
public Nat Strict(Nat n, Nat m, Nat k, Nat offset, Nat base) {
    if (n < m) {
        if (k < m) {
            return n;
        } else {
            assert base + (n + offset) < base + (k + offset);
            return n;
        }
    } else {
        return n;
    }
}
public Nat Left(Nat n, Nat m, Nat offset) {
    if (n <= m) {
        assert offset + n <= offset + m;
    }
    return n;
}
public Nat Right(Nat n, Nat m, Nat offset) {
    if (m <= n) {
        return n;
    } else {
        assert n + offset <= m + offset;
        return n;
    }
}
"""
    strict = b"base + (n + offset) < base + (k + offset)"
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(program: bytes) -> str:
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(source)
        mismatched = strict.replace(b"k + offset", b"k + m")
        for program, outstanding in (
            (source.replace(strict, mismatched), mismatched),
            (source.replace(b"if (k < m)", b"if (m < k)"), strict),
        ):
            with raises(HoldFastError) as failure:
                check(program)
            ensure(failure.exception.line == 7
                   and f"assertion could not be established: {outstanding.decode()}" in failure.exception.message,
                   f"wrong translated bound refusal: {failure.exception}")

    _replay_witnesses("TranslatedBounds", source, gallina, (
        ("strict", b"assert " + strict + b";",
         "forall n m k offset base, Nat.ltb n m = true -> Nat.ltb k m = false -> "
         "Nat.ltb (Nat.add base (Nat.add n offset)) (Nat.add base (Nat.add k offset)) = true"),
        ("on_left", b"assert offset + n <= offset + m;",
         "forall n m offset, Nat.leb n m = true -> Nat.leb (Nat.add offset n) (Nat.add offset m) = true"),
        ("on_right", b"assert n + offset <= m + offset;",
         "forall n m offset, Nat.leb m n = false -> Nat.leb (Nat.add n offset) (Nat.add m offset) = true"),
    ), batch=batch)


def _cancelled_branch_bounds(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""module RelativeBounds;
public Nat Observe(Nat used, Nat limit, Nat capacity, Nat base, Nat offset) {
    if (base + (used + offset) < base + (limit + offset)) {
        if (limit <= capacity) {
            assert used < capacity;
        }
    }
    return limit;
}
public Nat Remaining(Nat first, Nat last, Nat base) {
    if (last + base <= first + base) {
        return last;
    } else {
        assert first < last;
        return first;
    }
}
public Nat Ordered(Nat first, Nat last, Nat base) {
    if (base + last < base + first) {
        return last;
    } else {
        assert first <= last;
        return first;
    }
}
public Nat Within(Nat used, Nat limit, Nat base) {
    if (used + base <= limit + base) {
        assert used <= limit;
    }
    return used;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(program: bytes) -> str:
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(source)
        for program, assertion in (
            (source.replace(b"limit + offset", b"limit + capacity"), b"used < capacity"),
            (source.replace(b"last + base <= first + base", b"first + base <= last + base"), b"first < last"),
            (source.replace(b"        assert used <= limit;\n    }", b"    }\n    assert used <= limit;"),
             b"used <= limit"),
        ):
            with raises(HoldFastError) as failure:
                check(program)
            line = program[:program.index(b"assert " + assertion + b";")].count(b"\n") + 1
            ensure(failure.exception.line == line
                   and f"assertion could not be established: {assertion.decode()}" in failure.exception.message,
                   f"wrong relative bound refusal: {failure.exception}")

    _replay_witnesses("RelativeBounds", source, gallina, (
        ("strict_nested", b"assert used < capacity;",
         "forall used limit capacity base offset, "
         "Nat.ltb (base + (used + offset)) (base + (limit + offset)) = true -> "
         "Nat.leb limit capacity = true -> Nat.ltb used capacity = true"),
        ("strict_false", b"assert first < last;",
         "forall first last base, Nat.leb (last + base) (first + base) = false -> Nat.ltb first last = true"),
        ("non_strict_false", b"assert first <= last;",
         "forall first last base, Nat.ltb (base + last) (base + first) = false -> Nat.leb first last = true"),
        ("non_strict", b"assert used <= limit;",
         "forall used limit base, Nat.leb (used + base) (limit + base) = true -> Nat.leb used limit = true"),
    ), batch=batch)


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [Case("erased assertion exports its exact conditional proof",
                 partial(_unused_witness, batch=batch), lane="toolchain"),
            Case("strict branch bounds replay with their own guard",
                 partial(_branch_witnesses, batch=batch), lane="toolchain"),
            Case("strict bounds join only scoped premises within the search limit",
                 partial(_joined_branch_witnesses, batch=batch), lane="toolchain"),
            Case("Nat bounds preserve order under common addends",
                 partial(_translated_branch_bounds, batch=batch), lane="toolchain"),
            Case("Nat bounds cancel common addends from scoped guards",
                 partial(_cancelled_branch_bounds, batch=batch), lane="toolchain"),
            Case("kernel check inline witness proofs with rocqchk", batch.verify_all, lane="toolchain")]
