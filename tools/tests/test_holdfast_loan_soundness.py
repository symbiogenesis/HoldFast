# SPDX-License-Identifier: Apache-2.0
"""Audit mechanized HoldFast loan soundness proofs and certificate checking."""

import contextlib
import subprocess
import tempfile
from functools import partial
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from tests.test_holdfast_graded import _replay
from toolchain import proofenv, rocq_cache

_LOAN_SEMANTICS_PROOFS = (
    "places_disjoint_elem_ne",
    "places_disjoint_cell2d",
    "places_disjoint_slice",
    "places_disjoint_elem_slice",
    "write_stable_mem_preserves_addr",
    "write_stable_mem_frame",
    "write_tag_preserving_stamps",
    "push_cap_preserving_stamps",
    "polonius_closure_sound",
)

_LOAN_SOUNDNESS_PROOFS = (
    "step_preserves_state_wf",
    "polonius_origin_flow_sound",
    "exclusive_return_restoration_sound",
    "two_phase_borrow_sound",
    "loop_cursor_folding_sound",
    "symbolic_disjoint_write_frame",
    "stable_shared_mut_preserves_address",
    "shared_mut_refinement_invalidation_sound",
    "tag_preserving_union_mutation_sound",
    "capacity_preserving_push_sound",
    "check_loan_certificate_sound",
    "cert_pos_tag_preserving_union",
    "cert_pos_cap_preserving_push",
    "cert_pos_shared_mut_disjoint_refinement",
    "cert_neg_overlapping_refinement_invalidated",
    "cert_neg_two_phase_write_while_reserved",
    "cert_neg_dangling_read_after_retag",
)

_CERTIFICATE_HARNESS = r"""
From Stdlib Require Import List.
Require Import loan_semantics loan_soundness.
Import ListNotations LoanSemantics LoanSoundness.

(* Positive: Polonius branching CFG with subset closure across join *)
Example pos_polonius_branch_cfg :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem := [(1, {| oe_borrowed := false; oe_val := VScalar 11 |})];
            st_loans := []; st_refs := []; st_next_bid := 10 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpBorrow 1 10 None (PRoot 1) LShared);
                  cn_succs := [1; 2] |};
               {| cn_point := 1;
                  cn_instr := IStep (OpRead (PRoot 1) (Some 1));
                  cn_succs := [3] |};
               {| cn_point := 2;
                  cn_instr := INop;
                  cn_succs := [3] |};
               {| cn_point := 3;
                  cn_instr := IStep (OpEndLoan 1);
                  cn_succs := [4] |}];
            cfg_exits := [4];
            cfg_issues := [(0, 10, 1)];
            cfg_subsets := [(0, 10, 20)];
            cfg_live := [(0, 10); (0, 20); (1, 20); (2, 20); (3, 20)];
            cfg_kills := [(4, 1)];
            cfg_contains := [(0, 10, 1); (0, 20, 1); (1, 20, 1); (2, 20, 1); (3, 20, 1)] |};
       lc_trace :=
         [(0, OpBorrow 1 10 None (PRoot 1) LShared, 1);
          (1, OpRead (PRoot 1) (Some 1), 3);
          (3, OpEndLoan 1, 4)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = true.
Proof. vm_compute. reflexivity. Qed.

(* Positive: 2D grid disjunctive coordinates and half-open sub-slices preserve sibling refinements *)
Example pos_symbolic_2d_and_slice_refinements :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem :=
              [(1, {| oe_borrowed := false;
                      oe_val := VGrid 5 3 3 [((0, 0), 7); ((0, 1), 8)] |});
               (2, {| oe_borrowed := false;
                      oe_val := VContainer 6 4 [VScalar 1; VScalar 2; VScalar 3; VScalar 4] |})];
            st_loans := []; st_refs := []; st_next_bid := 20 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpBorrow 1 10 None (PRoot 1) LSharedMut);
                  cn_succs := [1] |};
               {| cn_point := 1;
                  cn_instr := IStep (OpBorrow 2 11 None (PSlice (PRoot 2) 2 2) LExclusive);
                  cn_succs := [2] |};
               {| cn_point := 2;
                  cn_instr := IStep (OpAssumeRefinement 100 (PCell2D (PRoot 1) 0 1) (FEquals 8));
                  cn_succs := [3] |};
               {| cn_point := 3;
                  cn_instr := IStep (OpAssumeRefinement 101 (PElem (PSlice (PRoot 2) 0 2) 0) (FEquals 1));
                  cn_succs := [4] |};
               {| cn_point := 4;
                  cn_instr := IStep (OpStableWrite (PCell2D (PRoot 1) 0 0) (Some 1) 99);
                  cn_succs := [5] |};
               {| cn_point := 5;
                  cn_instr := IStep (OpStableWrite (PSlice (PRoot 2) 2 2) (Some 2) 55);
                  cn_succs := [6] |};
               {| cn_point := 6;
                  cn_instr := IStep (OpUseRefinement 100);
                  cn_succs := [7] |};
               {| cn_point := 7;
                  cn_instr := IStep (OpUseRefinement 101);
                  cn_succs := [8] |}];
            cfg_exits := [8];
            cfg_issues := [(0, 10, 1); (1, 11, 2)];
            cfg_subsets := [];
            cfg_live := [(0, 10); (1, 10); (1, 11); (2, 10); (2, 11); (3, 10); (3, 11);
                         (4, 10); (4, 11); (5, 10); (5, 11); (6, 10); (6, 11); (7, 10); (7, 11)];
            cfg_kills := [];
            cfg_contains := [(0, 10, 1); (1, 10, 1); (1, 11, 2); (2, 10, 1); (2, 11, 2);
                             (3, 10, 1); (3, 11, 2); (4, 10, 1); (4, 11, 2);
                             (5, 10, 1); (5, 11, 2); (6, 10, 1); (6, 11, 2);
                             (7, 10, 1); (7, 11, 2)] |};
       lc_trace :=
         [(0, OpBorrow 1 10 None (PRoot 1) LSharedMut, 1);
          (1, OpBorrow 2 11 None (PSlice (PRoot 2) 2 2) LExclusive, 2);
          (2, OpAssumeRefinement 100 (PCell2D (PRoot 1) 0 1) (FEquals 8), 3);
          (3, OpAssumeRefinement 101 (PElem (PSlice (PRoot 2) 0 2) 0) (FEquals 1), 4);
          (4, OpStableWrite (PCell2D (PRoot 1) 0 0) (Some 1) 99, 5);
          (5, OpStableWrite (PSlice (PRoot 2) 2 2) (Some 2) 55, 6);
          (6, OpUseRefinement 100, 7);
          (7, OpUseRefinement 101, 8)];
       lc_observed_loans := [1; 2];
       lc_checked_facts := [100; 101] |} = true.
Proof. vm_compute. reflexivity. Qed.

(* Positive: two-phase reserve admits read then activates cleanly *)
Example pos_two_phase_reserve_read_activate :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem := [(1, {| oe_borrowed := false; oe_val := VScalar 12 |})];
            st_loans := []; st_refs := []; st_next_bid := 10 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpReserve 1 10 None (PRoot 1));
                  cn_succs := [1] |};
               {| cn_point := 1;
                  cn_instr := IStep (OpRead (PRoot 1) None);
                  cn_succs := [2] |};
               {| cn_point := 2;
                  cn_instr := IStep (OpActivate 1);
                  cn_succs := [3] |};
               {| cn_point := 3;
                  cn_instr := IStep (OpStableWrite (PRoot 1) (Some 1) 44);
                  cn_succs := [4] |}];
            cfg_exits := [4];
            cfg_issues := [(0, 10, 1)];
            cfg_subsets := [];
            cfg_live := [(0, 10); (1, 10); (2, 10); (3, 10)];
            cfg_kills := [];
            cfg_contains := [(0, 10, 1); (1, 10, 1); (2, 10, 1); (3, 10, 1)] |};
       lc_trace :=
         [(0, OpReserve 1 10 None (PRoot 1), 1);
          (1, OpRead (PRoot 1) None, 2);
          (2, OpActivate 1, 3);
          (3, OpStableWrite (PRoot 1) (Some 1) 44, 4)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = true.
Proof. vm_compute. reflexivity. Qed.

(* Positive: exclusive ref return restoration on borrowed parameter *)
Example pos_exclusive_return_restoration :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem := [(1, {| oe_borrowed := true; oe_val := VScalar 7 |})];
            st_loans := []; st_refs := []; st_next_bid := 10 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpBorrow 1 10 None (PRoot 1) LExclusive);
                  cn_succs := [1] |};
               {| cn_point := 1;
                  cn_instr := IStep (OpReturnLoan 1);
                  cn_succs := [2] |}];
            cfg_exits := [2];
            cfg_issues := [(0, 10, 1)];
            cfg_subsets := [];
            cfg_live := [(0, 10); (1, 10)];
            cfg_kills := [];
            cfg_contains := [(0, 10, 1); (1, 10, 1)] |};
       lc_trace :=
         [(0, OpBorrow 1 10 None (PRoot 1) LExclusive, 1);
          (1, OpReturnLoan 1, 2)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = true.
Proof. vm_compute. reflexivity. Qed.

(* Negative: tag-changing retag is rejected while interior payload loan is live *)
Example neg_retag_with_live_payload_loan :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem := ex_union_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpBorrow 1 1 None (PUnionPayload (PRoot 1)) LShared);
                  cn_succs := [1] |};
               {| cn_point := 1;
                  cn_instr := IStep (OpUnstableWrite (PRoot 1) (URetag 9 (VScalar 0)));
                  cn_succs := [2] |}];
            cfg_exits := [2];
            cfg_issues := [(0, 1, 1)];
            cfg_subsets := [];
            cfg_live := [(0, 1); (1, 1)];
            cfg_kills := [];
            cfg_contains := [(0, 1, 1); (1, 1, 1)] |};
       lc_trace :=
         [(0, OpBorrow 1 1 None (PUnionPayload (PRoot 1)) LShared, 1);
          (1, OpUnstableWrite (PRoot 1) (URetag 9 (VScalar 0)), 2)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = false.
Proof. vm_compute. reflexivity. Qed.

(* Negative: push at full capacity (len = cap) fails without reallocation *)
Example neg_push_at_full_capacity :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem := [(1, {| oe_borrowed := false; oe_val := VContainer 20 2 [VScalar 10; VScalar 20] |})];
            st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpCapPreservingPush (PRoot 1) None (VScalar 30));
                  cn_succs := [1] |}];
            cfg_exits := [1];
            cfg_issues := [];
            cfg_subsets := [];
            cfg_live := [];
            cfg_kills := [];
            cfg_contains := [] |};
       lc_trace := [(0, OpCapPreservingPush (PRoot 1) None (VScalar 30), 1)];
       lc_observed_loans := [];
       lc_checked_facts := [] |} = false.
Proof. vm_compute. reflexivity. Qed.

(* Negative: incomplete Polonius edge propagation fails closure check *)
Example neg_incomplete_polonius_closure :
  check_loan_certificate
    {| lc_init_state :=
         {| st_mem := [(1, {| oe_borrowed := false; oe_val := VScalar 1 |})];
            st_loans := []; st_refs := []; st_next_bid := 10 |};
       lc_cfg :=
         {| cfg_entry := 0;
            cfg_nodes :=
              [{| cn_point := 0;
                  cn_instr := IStep (OpBorrow 1 10 None (PRoot 1) LShared);
                  cn_succs := [1] |}];
            cfg_exits := [1];
            cfg_issues := [(0, 10, 1)];
            cfg_subsets := [];
            cfg_live := [(0, 10); (1, 10)];
            cfg_kills := [];
            cfg_contains := [(0, 10, 1)] |};
       lc_trace := [(0, OpBorrow 1 10 None (PRoot 1) LShared, 1)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = false.
Proof. vm_compute. reflexivity. Qed.
"""


def _replay_certificate_harness(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    """Compile and kernel-check positive and negative loan certificates."""
    compile_unit = [*proofenv.rocq_command(), "-q"]
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-loan-certs-")))
        else:
            directory = batch.work_dir
        rocq_cache.materialize_repo_units(
            TOOLS.parent,
            directory,
            ("loan_semantics.v", "loan_soundness.v"),
            compiler=compile_unit,
        )
        harness = directory / "LoanCertHarness.v"
        harness.write_text(_CERTIFICATE_HARNESS.lstrip(), encoding="utf-8")
        result = subprocess.run(
            [*compile_unit, harness.name],
            cwd=directory,
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            timeout=180,
        )
        ensure(
            result.returncode == 0,
            f"Loan certificate harness failed: {result.stderr or result.stdout}",
        )
        if batch is not None:
            batch.register("LoanCertHarness")
        else:
            rocq_cache.check_kernel(directory, ["loan_semantics", "loan_soundness", "LoanCertHarness"])


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case(
            "loan semantics zero-axiom Rocq audit",
            partial(_replay, "loan_semantics", "LoanSemantics", _LOAN_SEMANTICS_PROOFS, batch=batch),
            lane="toolchain",
        ),
        Case(
            "loan soundness zero-axiom Rocq audit",
            partial(_replay, "loan_soundness", "LoanSoundness", _LOAN_SOUNDNESS_PROOFS, ("loan_semantics",),
                    batch=batch),
            lane="toolchain",
        ),
        Case(
            "loan certificate positive and negative kernel checks",
            partial(_replay_certificate_harness, batch=batch),
            lane="toolchain",
        ),
        Case(
            "kernel check loan soundness and certificate proofs with rocqchk",
            batch.verify_all,
            lane="toolchain",
        ),
    ]
