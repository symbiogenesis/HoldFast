(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import Lists.List Arith.PeanoNat.
Require Import graded_pure.
Import ListNotations GradedPure.

Module GradedTypeIrrelevance.

Lemma zero_index_use : forall env i row,
  IndexDemand env i row -> forall x argument,
  uses row x = 0 -> substitute_index x argument i = i.
Proof.
  intros env i row typed.
  induction typed as [y entry found natural | n | left right p q typed_left IHleft typed_right IHright];
    intros x argument unused; cbn in *.
  - now destruct (Nat.eqb x y).
  - reflexivity.
  - rewrite uses_append in unused.
    apply Nat.eq_add_0 in unused as [left_unused right_unused].
    now rewrite IHleft, IHright.
Qed.

Theorem zero_type_use : forall env kind row,
  TypeDemand env kind row -> forall x argument,
  uses row x = 0 -> substitute_type x argument kind = kind.
Proof.
  intros env kind row typed.
  induction typed as [env | env length d typed | env y allowance domain codomain a b new
    typed_domain IHdomain typed_codomain IHcodomain | env level | env y entry level found typed];
    intros x argument unused; cbn.
  - reflexivity.
  - f_equal. eapply zero_index_use; eauto.
  - rewrite uses_append, uses_without in unused.
    apply Nat.eq_add_0 in unused as [domain_unused codomain_unused].
    rewrite IHdomain by exact domain_unused.
    destruct (Nat.eqb x y); [reflexivity | now rewrite IHcodomain].
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_type_var_use : forall env kind row,
  TypeDemand env kind row -> forall x argument,
  uses row x = 0 -> substitute_type_variable x argument kind = kind.
Proof.
  intros env kind row typed.
  induction typed as [env | env length d typed | env y allowance domain codomain a b new
    typed_domain IHdomain typed_codomain IHcodomain | env level | env y entry level found typed];
    intros x argument unused; cbn in *.
  - reflexivity.
  - reflexivity.
  - rewrite uses_append, uses_without in unused.
    apply Nat.eq_add_0 in unused as [domain_unused codomain_unused].
    rewrite IHdomain by exact domain_unused.
    destruct (Nat.eqb x y); [reflexivity | now rewrite IHcodomain].
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:equal; [discriminate | reflexivity].
Qed.

Lemma zero_scaled_use : forall argument y, uses (scale 0 argument) y = 0.
Proof.
  intros argument y. now rewrite GradedPure.uses_scale.
Qed.

Theorem zero_use_preserves_row : forall row argument x,
  uses row x = 0 -> same_demand (substitute_demand x argument row) row.
Proof.
  intros row argument x unused y.
  unfold substitute_demand.
  rewrite uses_append, unused, zero_scaled_use, Nat.add_0_r, uses_without.
  destruct (Nat.eqb y x) eqn:equal; [| reflexivity].
  apply Nat.eqb_eq in equal. now subst y.
Qed.

Theorem checked_zero_type_use : forall env subject result x argument argument_row,
  infer env subject = Some result -> uses (type_demand_row result) x = 0 ->
  substitute_type x argument (result_type result) = result_type result /\
  same_demand (substitute_demand x argument_row (type_demand_row result)) (type_demand_row result).
Proof.
  intros env subject result x argument argument_row checked unused.
  split.
  - apply infer_sound, derives_type_demand in checked.
    destruct checked as [row [typed agrees]].
    eapply zero_type_use; eauto. now rewrite <- agrees.
  - now apply zero_use_preserves_row.
Qed.

Theorem checked_zero_type_var_use : forall env subject result x argument argument_row,
  infer env subject = Some result -> uses (type_demand_row result) x = 0 ->
  substitute_type_variable x argument (result_type result) = result_type result /\
  same_demand (substitute_demand x argument_row (type_demand_row result)) (type_demand_row result).
Proof.
  intros env subject result x argument argument_row checked unused.
  split.
  - apply infer_sound, derives_type_demand in checked.
    destruct checked as [row [typed agrees]].
    eapply zero_type_var_use; eauto. now rewrite <- agrees.
  - now apply zero_use_preserves_row.
Qed.

End GradedTypeIrrelevance.
