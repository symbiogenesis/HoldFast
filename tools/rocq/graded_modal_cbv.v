(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat.
Require Import graded_pure graded_domains graded_modal graded_cbv graded_cbv_span_carrier graded_cbv_span.
Import ListNotations.

Module GradedModalCbv.

Import GradedModal GradedCbv GradedCbvSpan.

Definition open_box (name motive_name q : nat) (packed : boxed) (body : GradedPure.index) : value :=
  LetBox name motive_name packed (ProductKind NatKind (type_identity (BoxContents motive_name)))
    (Pair (NaturalValue body) (vec_identity (PromotedContents q (GradedPure.IndexVar name)))).

Lemma dependent_pair_counts_reads : forall allows exact_branches scope body extent k computation dependency values name,
  DerivesModal allows exact_branches scope (Pair (NaturalValue body) (vec_identity extent))
    (used k computation dependency) ->
  count_occ Nat.eq_dec (snd (evaluate_index values body)) name = GradedPure.uses computation name.
Proof.
  intros allows exact_branches scope body extent k computation dependency values name typed.
  inversion typed as [| | | | | left right a b u v w z arithmetic vector | | | | | | | | | | | | |]; subst.
  inversion arithmetic; subst.
  unfold vec_identity in vector.
  inversion vector as [| | | | binder allowance domain term codomain a' u' v' row
    fresh domain_ok identity allowed formed | | | | | | | | | | | | | |]; subst.
  inversion identity; subst.
  rewrite GradedPure.uses_append, GradedPure.uses_without.
  assert ((if name =? 3 then 0 else GradedPure.uses [(3, 1)] name) = 0) as no_reads.
  { destruct (name =? 3) eqn:eq_name; [reflexivity |]. cbn. now rewrite eq_name. }
  rewrite no_reads, Nat.add_0_r.
  eapply index_reads_match_demand. eassumption.
Qed.

Theorem checked_box_open_preserves_argument_with : forall
  (allows : nat -> nat -> Prop) allowsb exact_branches
  (sound : forall actual allowance, allowsb actual allowance = true -> allows actual allowance)
  State Event scope name motive_name packed q body checked values
  (argument : State -> execution State Event) initial after effects payload,
  check_modal allowsb exact_branches scope (open_box name motive_name q packed body) = Some checked ->
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
  intros allows allowsb exact_branches sound State Event scope name motive_name packed q body checked values
    argument initial after effects payload accepted evaluated.
  unfold open_box in accepted.
  pose proof (checked_let_box_demands_with allows allowsb exact_branches sound _ _ _ _ _ _ _ accepted) as opened.
  destruct opened as (box_grade & source_uses & contents & computation & dependency & motive_row
    & boxed_ok & _ & body_ok & admitted & _ & output_kind & _).
  cbn [specialize map_indices type_identity] in body_ok.
  rewrite Nat.eqb_refl in body_ok.
  cbn [specialize map_indices type_identity] in output_kind.
  rewrite Nat.eqb_refl in output_kind.
  pose proof (dependent_pair_counts_reads _ _ _ _ _ _ _ _ (extend_values values name payload) name body_ok)
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

Definition slice_payload (argument : slice_argument) (owner : byte_span) : nat :=
  holdfast_int_to_nat 0
    (span_read (span_slice owner (start argument) (length argument)) (element argument)).

Definition open_slice_box (values : nat -> nat) (body : GradedPure.index)
    (argument : slice_argument) (owner : byte_span) :
    execution byte_span (observation span_event) * option nat :=
  let evaluated := run_slice_argument argument owner in
  let opened := apply_natural_lambda values (fst (binder_grade argument)) body (fun _ => evaluated) owner in
  (opened, match result evaluated with Returned extent => Some extent | Failed _ => None end).

Theorem checked_slice_box_preserves_owner_with : forall
  (allows : nat -> nat -> Prop) allowsb exact_branches
  (sound : forall actual allowance, allowsb actual allowance = true -> allows actual allowance)
  scope motive_name box body checked values argument owner,
  let '(name, allowance) := binder_grade argument in
  find_kind scope box = Some (BoxNat allowance) ->
  check_modal allowsb exact_branches scope (open_box name motive_name allowance (BoxName box) body) = Some checked ->
  let evaluated := run_slice_argument argument owner in
  let '(opened, extent) := open_slice_box values body argument owner in
  value_kind checked = ProductKind NatKind (type_identity (BoxContents box)) /\
  final_state opened = final_state evaluated /\
  span_descriptor (final_state opened) = span_descriptor owner /\
  (forall index, holdfast_int_ne 4 (owner_index argument) index = true ->
    span_read (final_state opened) index = span_read owner index) /\
  match result evaluated with
  | Failed reason =>
      extent = None /\ trace opened = map ArgumentEvent (trace evaluated) /\
      result opened = Failed reason
  | Returned payload =>
      extent = Some (slice_payload argument owner) /\
      exists returned reads,
        evaluate_index (extend_values values name payload) body = (returned, reads) /\
        trace opened = map ArgumentEvent (trace evaluated) ++ ArgumentReturned payload :: map BodyRead reads /\
        result opened = Returned returned /\
        allows (count_occ Nat.eq_dec reads name) allowance
  end.
Proof.
  intros allows allowsb exact_branches sound scope motive_name box body checked values argument owner.
  destruct (binder_grade argument) as [name q] eqn:binder.
  intros box_kind accepted.
  pose proof (checked_let_box_demands_with allows allowsb exact_branches sound _ _ _ _ _ _ _ accepted)
    as (grade & uses & contents & computation & dependency & motive_row & boxed & _ & _ & _ & _ &
      kind_checked & _).
  inversion boxed as [key allowance found |]; subst.
  cbn [specialize map_indices type_identity] in kind_checked. rewrite Nat.eqb_refl in kind_checked.
  pose proof (scoped_argument_preserves_owner argument owner) as preserved.
  unfold open_slice_box. rewrite binder.
  destruct (run_slice_argument argument owner) as [after effects outcome] eqn:evaluated.
  cbn [fst final_state trace result] in *.
  destruct outcome as [payload | reason].
  - pose proof (checked_box_open_preserves_argument_with allows allowsb exact_branches sound byte_span span_event
      scope name motive_name (BoxName box) q body checked values
      (fun _ => {| final_state := after; trace := effects; result := Returned payload |})
      owner after effects payload accepted eq_refl)
      as (box_grade & source_uses & box_contents & returned & reads & typed & _ & body_result & opened & allowed).
    rewrite opened. cbn [final_state trace result].
    destruct preserved as [descriptor frame].
    assert (payload = slice_payload argument owner) as same_payload.
    { unfold run_slice_argument in evaluated.
      destruct (usable_slice argument owner); [| discriminate].
      destruct (failure_after_write argument); [discriminate |].
      now inversion evaluated. }
    repeat split; try assumption; try reflexivity.
    + now rewrite same_payload.
    + inversion typed as [key actual found_kind |]; subst.
      rewrite box_kind in found_kind. inversion found_kind; subst.
      exists returned, reads. repeat split; assumption.
  - unfold apply_natural_lambda, sequence_argument. cbn [final_state trace result].
    destruct preserved as [descriptor frame]. repeat split; assumption || reflexivity.
Qed.

Local Definition exact_box_open := check [(0, BoxNat 0)]
  (open_box 1 2 0 (BoxName 0) (GradedPure.IndexLit 9)).

Local Definition slice_box_argument (grade : nat) (failure : option nat) : slice_argument :=
  {| binder_grade := (1, grade); start := holdfast_nat_to_usize 0;
     length := holdfast_nat_to_usize 1; element := holdfast_nat_to_usize 0;
     replacement := holdfast_mk_int 0 (holdfast_nat_to_bits 8 7); failure_after_write := failure |}.

Local Definition slice_box_owner (n : nat) : byte_span :=
  span_write (holdfast_Span_AllocZeroed _ (holdfast_nat_to_usize 11) (holdfast_nat_to_usize 2))
    (holdfast_nat_to_usize 0) (holdfast_mk_int 0 (holdfast_nat_to_bits 8 n)).

Example unused_slice_box_keeps_extent_and_restores_owner :
  let argument := slice_box_argument 0 None in
  let owner := slice_box_owner 5 in
  let '(opened, extent) := open_slice_box (fun _ => 0) (GradedPure.IndexLit 9) argument owner in
  exact_box_open = Some (used (ProductKind NatKind (type_identity (BoxContents 0))) [(0, 1)] [(0, 1); (0, 1)]) /\
  extent = Some 5 /\ result opened = Returned 9 /\
  trace opened = [ArgumentEvent (SliceBorrowed (start argument) (length argument));
    ArgumentEvent (ElementWritten (element argument) (replacement argument)); ArgumentEvent OwnerRestored;
    ArgumentReturned 5] /\
  span_read (final_state opened) (element argument) = replacement argument.
Proof. vm_compute. repeat split. Qed.

Example bounded_slice_box_reuses_the_original_payload :
  let body := GradedPure.IndexAdd (GradedPure.IndexVar 1) (GradedPure.IndexVar 1) in
  let argument := slice_box_argument 3 None in
  let owner := slice_box_owner 5 in
  let '(opened, extent) := open_slice_box (fun _ => 0) body argument owner in
  bounded_check [(0, BoxNat 3)] (open_box 1 2 3 (BoxName 0) body) =
    Some (used (ProductKind NatKind (type_identity (BoxContents 0))) [(0, 1)] [(0, 1); (0, 1)]) /\
  bounded_check [(0, BoxNat 1)] (open_box 1 2 1 (BoxName 0) body) = None /\
  extent = Some 5 /\ result opened = Returned 10 /\
  trace opened = [ArgumentEvent (SliceBorrowed (start argument) (length argument));
    ArgumentEvent (ElementWritten (element argument) (replacement argument)); ArgumentEvent OwnerRestored;
    ArgumentReturned 5; BodyRead 1; BodyRead 1] /\
  span_read (final_state opened) (element argument) = replacement argument.
Proof. vm_compute. repeat split. Qed.

Example failed_slice_box_keeps_writeback_without_an_extent :
  let argument := slice_box_argument 0 (Some 4) in
  let owner := slice_box_owner 0 in
  let '(opened, extent) := open_slice_box (fun _ => 0) (GradedPure.IndexLit 9) argument owner in
  extent = None /\ result opened = Failed 4 /\
  trace opened = [ArgumentEvent (SliceBorrowed (start argument) (length argument));
    ArgumentEvent (ElementWritten (element argument) (replacement argument)); ArgumentEvent OwnerRestored] /\
  span_read (final_state opened) (element argument) = replacement argument.
Proof. vm_compute. repeat split. Qed.

End GradedModalCbv.
