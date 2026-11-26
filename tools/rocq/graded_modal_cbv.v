(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat.
Require Import graded_pure graded_domains graded_modal graded_cbv.
Import ListNotations.

Module GradedModalCbv.

Import GradedModal GradedCbv.

Definition open_box (name motive_name q : nat) (packed : boxed) (body : GradedPure.index) : value :=
  LetBox name motive_name packed (ProductKind NatKind (type_identity (BoxContents motive_name)))
    (Pair (NaturalValue body) (vec_identity (PromotedContents q (GradedPure.IndexVar name)))).

Lemma dependent_pair_counts_reads : forall allows scope body extent k computation dependency values name,
  DerivesWith allows scope (Pair (NaturalValue body) (vec_identity extent))
    (used k computation dependency) ->
  count_occ Nat.eq_dec (snd (evaluate_index values body)) name = GradedPure.uses computation name.
Proof.
  intros allows scope body extent k computation dependency values name typed.
  inversion typed as [| | | | | left right a b u v w z arithmetic vector | |]; subst.
  inversion arithmetic; subst.
  unfold vec_identity in vector.
  inversion vector as [| | | | binder allowance domain term codomain a' u' v' row
    fresh domain_ok identity allowed formed | | |]; subst.
  inversion identity; subst.
  rewrite GradedPure.uses_append, GradedPure.uses_without.
  assert ((if name =? 3 then 0 else GradedPure.uses [(3, 1)] name) = 0) as no_reads.
  { destruct (name =? 3) eqn:eq_name; [reflexivity |]. cbn. now rewrite eq_name. }
  rewrite no_reads, Nat.add_0_r.
  eapply index_reads_match_demand. eassumption.
Qed.

Theorem checked_box_open_preserves_argument_with : forall
  (allows : nat -> nat -> Prop) allowsb
  (sound : forall actual allowance, allowsb actual allowance = true -> allows actual allowance)
  State Event scope name motive_name packed q body checked values
  (argument : State -> execution State Event) initial after effects payload,
  check_with allowsb scope (open_box name motive_name q packed body) = Some checked ->
  argument initial = {| final_state := after; trace := effects; result := Returned payload |} ->
  exists box_grade source_uses contents returned reads,
    BoxDerives scope packed box_grade source_uses contents /\
    value_kind checked = ProductKind NatKind (type_identity contents) /\
    evaluate_index (extend_values values name payload) body = (returned, reads) /\
    apply_natural_lambda values name body argument initial =
      {| final_state := after;
         trace := map ArgumentEvent effects ++ ArgumentReturned payload :: map BodyRead reads;
         result := Returned returned |} /\
    allows (count_occ Nat.eq_dec reads name) box_grade.
Proof.
  intros allows allowsb sound State Event scope name motive_name packed q body checked values
    argument initial after effects payload accepted evaluated.
  unfold open_box in accepted.
  pose proof (checked_let_box_demands_with allows allowsb sound _ _ _ _ _ _ _ accepted) as opened.
  destruct opened as (box_grade & source_uses & contents & computation & dependency & motive_row
    & boxed_ok & _ & body_ok & admitted & _ & output_kind & _).
  cbn [specialize map_indices type_identity] in body_ok.
  rewrite Nat.eqb_refl in body_ok.
  cbn [specialize map_indices type_identity] in output_kind.
  rewrite Nat.eqb_refl in output_kind.
  pose proof (dependent_pair_counts_reads _ _ _ _ _ _ _ (extend_values values name payload) name body_ok)
    as read_count.
  unfold apply_natural_lambda, sequence_argument. rewrite evaluated. cbn.
  unfold evaluate_natural_body.
  destruct (evaluate_index (extend_values values name payload) body) as [returned reads].
  cbn in read_count.
  exists box_grade, source_uses, contents, returned, reads.
  repeat split; try assumption; try reflexivity.
  now rewrite read_count.
Qed.

Example unused_box_payload_keeps_effect_and_type :
  check [(0, BoxNat 0)] (open_box 1 2 0 (BoxName 0) (GradedPure.IndexLit 9)) =
    Some (used (ProductKind NatKind (type_identity (BoxContents 0))) [(0, 1)] [(0, 1); (0, 1)]) /\
  apply_natural_lambda (fun _ => 0) 1 (GradedPure.IndexLit 9) incrementing_argument 4 =
    {| final_state := 5; trace := [ArgumentEvent 4; ArgumentReturned 11]; result := Returned 9 |}.
Proof. split; reflexivity. Qed.

Example repeated_box_payload_reuses_one_effect :
  let body := GradedPure.IndexAdd (GradedPure.IndexVar 1) (GradedPure.IndexVar 1) in
  bounded_check [(0, BoxNat 3)] (open_box 1 2 3 (BoxName 0) body) =
    Some (used (ProductKind NatKind (type_identity (BoxContents 0))) [(0, 1)] [(0, 1); (0, 1)]) /\
  apply_natural_lambda (fun _ => 0) 1 body incrementing_argument 4 =
    {| final_state := 5; trace := [ArgumentEvent 4; ArgumentReturned 11; BodyRead 1; BodyRead 1];
       result := Returned 22 |}.
Proof. split; reflexivity. Qed.

End GradedModalCbv.
