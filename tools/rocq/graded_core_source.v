(* SPDX-License-Identifier: Apache-2.0 *)

From Corelib Require Import Init.Datatypes.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Require Import graded_pure graded_domains graded_core.
Import ListNotations GradedDomains GradedCore.

Module GradedCoreSource.

Definition source_check_core {D : JoinDomain} (env : cenv D) (subject : cterm D) (expected : cty D)
  : result (list (list (grade D))) (grade_error D) :=
  let* _ := check_cenv env in
  let* j := core_infer env subject in
  let* exp_row := ctype_demand env expected in
  if cty_alpha_eqb (cresult_type j) expected then
    Ok (ccomp_demand j :: ctype_demand_row j :: exp_row :: map ctype_uses env)
  else Err (ErrTypeMismatch (cresult_type j) expected).

Theorem source_check_core_sound : forall (D : JoinDomain) (env : cenv D) subject expected rows,
  source_check_core env subject expected = Ok rows ->
  exists j exp_row,
    CEnvWf env /\
    CoreDerives env subject j /\
    CTypeDemand env expected exp_row /\
    cty_alpha_eq (cresult_type j) expected /\
    rows = ccomp_demand j :: ctype_demand_row j :: exp_row :: map ctype_uses env.
Proof.
  intros D env subject expected rows Hchk. unfold source_check_core in Hchk.
  destruct (check_cenv env) as [[] |] eqn:Hwf; [| discriminate].
  cbn in Hchk. destruct (core_infer env subject) as [j |] eqn:Hj; [| discriminate].
  cbn in Hchk. destruct (ctype_demand env expected) as [exp_row |] eqn:Hexp; [| discriminate].
  cbn in Hchk. destruct (cty_alpha_eqb (cresult_type j) expected) eqn:Heq; inversion Hchk; subst.
  exists j, exp_row. repeat split.
  - apply check_cenv_sound; exact Hwf.
  - apply core_infer_sound; exact Hj.
  - apply ctype_demand_sound; exact Hexp.
  - apply cty_alpha_eqb_sound; exact Heq.
Qed.

Definition source_check_core_sub {D : JoinDomain} (env : cenv D) (subject : cterm D) (expected : cty D)
  : result (list (list (grade D))) (grade_error D) :=
  let* _ := check_cenv env in
  let* j := core_infer env subject in
  let* exp_row := ctype_demand env expected in
  if subtyb env (cresult_type j) expected then
    Ok (ccomp_demand j :: ctype_demand_row j :: exp_row :: map ctype_uses env)
  else Err (ErrSubgradeFailed (cresult_type j) expected).

Theorem source_check_core_sub_sound : forall (D : JoinDomain) (env : cenv D) subject expected rows,
  source_check_core_sub env subject expected = Ok rows ->
  exists j exp_row,
    CEnvWf env /\
    CoreDerives env subject j /\
    CTypeDemand env expected exp_row /\
    Subty env (cresult_type j) expected /\
    rows = ccomp_demand j :: ctype_demand_row j :: exp_row :: map ctype_uses env.
Proof.
  intros D env subject expected rows Hchk. unfold source_check_core_sub in Hchk.
  destruct (check_cenv env) as [[] |] eqn:Hwf; [| discriminate].
  cbn in Hchk. destruct (core_infer env subject) as [j |] eqn:Hj; [| discriminate].
  cbn in Hchk. destruct (ctype_demand env expected) as [exp_row |] eqn:Hexp; [| discriminate].
  cbn in Hchk.
  match type of Hchk with
  | (if ?s then _ else _) = Ok rows => destruct s eqn:Hsub
  end; inversion Hchk; subst.
  fold (subtyb env (cresult_type j) expected) in Hsub.
  exists j, exp_row. repeat split.
  - apply check_cenv_sound; exact Hwf.
  - apply core_infer_sound; exact Hj.
  - apply ctype_demand_sound; exact Hexp.
  - apply subtyb_sound; exact Hsub.
Qed.

Definition source_check_closed {D : JoinDomain} (subject : cterm D) (expected : cty D)
  : result (list (list (grade D))) (grade_error D) :=
  source_check_core [] subject expected.

Theorem source_check_closed_sound : forall (D : JoinDomain) subject expected rows,
  source_check_closed (D := D) subject expected = Ok rows ->
  exists j exp_row,
    CoreDerives [] subject j /\
    CTypeDemand [] expected exp_row /\
    cty_alpha_eq (cresult_type j) expected /\
    rows = [ccomp_demand j; ctype_demand_row j; exp_row].
Proof.
  intros D subject expected rows H.
  apply source_check_core_sound in H as [j [exp_row [_ [Hd [Ht [Heq ->]]]]]].
  exists j, exp_row. repeat split; assumption.
Qed.

End GradedCoreSource.
