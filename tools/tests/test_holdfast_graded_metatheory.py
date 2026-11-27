# SPDX-License-Identifier: Apache-2.0
"""Audit mechanized GrTT metatheory, symbolic semiring polymorphism, and erasure proofs."""

import subprocess
import tempfile
import time
from functools import partial
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from tests.test_holdfast_graded import _replay
from toolchain import proofenv, rocq_cache

_METATHEORY_PROOFS = (
    "derives_allows_mono",
    "context_equiv_derives",
    "exchange_derives",
    "weakening_index",
    "weakening_type",
    "weakening_universe",
    "weakening_derives",
    "value_substitution_derives",
    "type_substitution_derives",
)
_GRTT_CORE_PROOFS = (
    "grtt_infer_with_sound",
    "grtt_pure_dependent_id",
    "grtt_sigma_asymmetric_box",
    "grtt_sum_exact_vs_bound",
)
_SEMIRING_PROOFS = (
    "normalize_grade_sound",
    "grade_eqb_sound",
    "grade_leb_sound",
    "semiring_laws_universal",
    "semiring_axioms_concrete",
    "poly_infer_sound",
    "poly_derives_all_valuations",
    "poly_duplicate_verified",
    "poly_split_verified",
    "poly_extract_verified",
    "poly_discard_verified",
    "poly_negative_controls",
)
_COMBINATOR_KERNEL_PROOFS = (
    "cty_eqb_sound",
    "cbranch_join_sound",
    "cinfer_sound",
    "affine_leb_sound",
    "presence_grade_leb_sound",
    "presence_contraction_sound",
)
_ERASURE_PROOFS = (
    "eval_dty_canonical",
    "eval_dty_subst_type_var",
    "erasure_simulation",
    "closed_erasure_sound",
    "zero_computation_irrelevance",
    "zero_var_non_interference",
    "apply_nat_skip_agrees",
    "apply_type_skip_agrees",
    "let_nat_skip_agrees",
    "erasure_unused_nat_example",
    "erasure_polymorphic_identity_example",
)
_GRADED_CORE_PROOFS = (
    "cidx_eqb_sound",
    "cty_alpha_eqb_sound",
    "vec_allowsb_spec",
    "cidx_demand_sound",
    "ctype_demand_sound",
    "cuniverse_level_sound",
    "check_cenv_sound",
    "subtyb_sound",
    "fix_recurrence_okb_sound",
    "check_record_allows_sound",
    "extend_record_env_sound",
    "core_infer_sound",
)
_GRADED_CORE_METATHEORY_PROOFS = (
    "core_derives_lengths",
    "core_weakening",
    "core_weakening_erasure",
    "core_exchange",
    "core_derives_cenv_rel",
    "core_derives_nat_safe",
    "core_value_substitution",
)


def _replay_grtt_core(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    _replay(
        "graded_metatheory",
        "GradedMetatheory.GrttCore",
        _GRTT_CORE_PROOFS,
        ("graded_pure", "graded_domains"),
        batch=batch,
    )


def _q25cb_substitution_skipping_benchmark() -> None:
    """Verify zero-type-use skipping matches full substitution and measure deep telescope timing."""
    depth = 40
    entries = "; ".join(f"dependent_entry {k + 2} (IndexVar 0) [(0, 1)]" for k in range(depth))
    deep_type = " -> ".join(["Natural"] * depth)
    _ = deep_type
    # Build nested Pi type over Natural with zero occurrences of binder 1
    nested_pi = "Natural"
    for k in range(depth):
        nested_pi = f"Pi {k + 100} 1 (Vector (IndexVar 0)) ({nested_pi})"
    bench = f"""
From Stdlib Require Import List.
Require Import graded_pure graded_domains graded_cbv graded_type_irrelevance graded_erasure.
Import ListNotations GradedPure GradedErasure.

Definition deep_env : context :=
  [{entries}; natural_binding 0].
Definition deep_cod : ty := {nested_pi}.

Theorem q25cb_deep_skip_agrees :
  exists b,
    (type_demand ({{| binder := 1; annotation := Natural; type_uses := [] |}} :: deep_env) deep_cod = Some b) /\\
    (uses b 1 = 0) /\\
    (match apply_nat_spec deep_env 1 0 deep_cod [] (twice 0),
           apply_nat_skip deep_env 1 0 deep_cod [] (twice 0) with
     | Some r1, Some r2 =>
         (result_type r1 = result_type r2) /\\
         (computation_demand r1 = computation_demand r2) /\\
         same_demand (type_demand_row r1) (type_demand_row r2)
     | _, _ => False
     end).
Proof.
  eexists.
  split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |].
  exact (apply_nat_skip_agrees deep_env 1 0 deep_cod [] (twice 0)).
Qed.
"""
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-q25cb-") as tmp:
        directory = Path(tmp)
        rocq_cache.materialize_repo_units(
            TOOLS.parent,
            directory,
            ("graded_pure.v", "graded_domains.v", "graded_cbv.v",
             "graded_type_irrelevance.v", "graded_erasure.v"),
            compiler=compiler,
        )
        bench_file = directory / "Q25cbBench.v"
        bench_file.write_text(bench, encoding="utf-8")
        t0 = time.perf_counter_ns()
        res = subprocess.run([*compiler, bench_file.name], cwd=directory, capture_output=True,
                             text=True, encoding="utf-8", check=False, timeout=60)
        elapsed_ns = time.perf_counter_ns() - t0
        ensure(res.returncode == 0 and elapsed_ns > 0,
               f"Q25cb deep-telescope benchmark failed: {res.stderr}")


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("graded structural and substitution metatheory",
             partial(_replay, "graded_metatheory", "GradedMetatheory", _METATHEORY_PROOFS,
                     ("graded_pure", "graded_domains"), batch=batch),
             lane="toolchain"),
        Case("full GrTT explicit (s, r) core calculus", partial(_replay_grtt_core, batch=batch), lane="toolchain"),
        Case("graded symbolic semiring polymorphism",
             partial(_replay, "graded_semiring", "GradedSemiring", _SEMIRING_PROOFS,
                     ("graded_pure", "graded_domains"), batch=batch),
             lane="toolchain"),
        Case("graded combinator kernel soundness",
             partial(_replay, "graded_semiring", "CombinatorKernel", _COMBINATOR_KERNEL_PROOFS,
                     ("graded_pure", "graded_domains"), batch=batch),
             lane="toolchain"),
        Case("graded erasure, non-interference, and Q25cb skipping",
             partial(_replay, "graded_erasure", "GradedErasure", _ERASURE_PROOFS,
                     ("graded_pure", "graded_domains", "graded_cbv", "graded_type_irrelevance"), batch=batch),
             lane="toolchain"),
        Case("unified GradedCore soundness and checker completeness",
             partial(_replay, "graded_core", "GradedCore", _GRADED_CORE_PROOFS,
                     ("graded_pure", "graded_domains"), batch=batch),
             lane="toolchain"),
        Case("unified GradedCore structural and substitution metatheory",
             partial(_replay, "graded_core_metatheory", "GradedCoreMetatheory", _GRADED_CORE_METATHEORY_PROOFS,
                     ("graded_pure", "graded_domains", "graded_core"), batch=batch),
             lane="toolchain"),
        Case("kernel check metatheory, semiring, and erasure proofs with rocqchk",
             batch.verify_all,
             lane="toolchain"),
        Case("Q25cb zero-type-use substitution skipping on deep telescope",
             _q25cb_substitution_skipping_benchmark,
             lane="toolchain"),
    ]
