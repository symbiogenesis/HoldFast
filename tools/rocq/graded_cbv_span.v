(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat.
Require Import graded_pure graded_cbv graded_cbv_span_carrier.
Import ListNotations GradedPure GradedCbv.

Module GradedCbvSpan.

Definition byte_span := holdfast_Span (holdfast_int 0).
Definition span_index := holdfast_int 4.
Definition span_byte := holdfast_int 0.
Definition span_read := holdfast_Span_Read (holdfast_int 0).
Definition span_write := holdfast_Span_Write (holdfast_int 0).
Definition span_slice := holdfast_Span_Slice (holdfast_int 0).
Definition span_restore := holdfast_Span_Restore (holdfast_int 0).

Definition span_descriptor (owner : byte_span) :=
  (holdfast_Span_Base _ owner, holdfast_Span_Length _ owner,
   holdfast_Span_Tag _ owner, holdfast_Span_PermRead _ owner, holdfast_Span_PermWrite _ owner).

Record slice_argument := {
  binder_grade : nat * nat;
  start : span_index;
  length : span_index;
  element : span_index;
  replacement : span_byte;
  failure_after_write : option nat;
}.

Inductive span_event :=
| SliceBorrowed (offset size : span_index)
| ElementWritten (index : span_index) (value : span_byte)
| OwnerRestored.

Definition owner_index (argument : slice_argument) : span_index :=
  holdfast_int_add 4 (start argument) (element argument).

Definition usable_slice (argument : slice_argument) (owner : byte_span) : bool :=
  let extent := holdfast_Span_Length _ owner in
  holdfast_Span_CanRead _ owner && holdfast_Span_CanWrite _ owner &&
  holdfast_int_le 4 (start argument) extent &&
  holdfast_int_le 4 (length argument) (holdfast_int_sub 4 extent (start argument)) &&
  holdfast_int_lt 4 (element argument) (length argument).

Definition run_slice_argument (argument : slice_argument) (owner : byte_span)
    : execution byte_span span_event :=
  if usable_slice argument owner then
    let view := span_slice owner (start argument) (length argument) in
    let after := span_write view (element argument) (replacement argument) in
    let previous := holdfast_int_to_nat 0 (span_read view (element argument)) in
    {| final_state := span_restore owner after;
       trace := [SliceBorrowed (start argument) (length argument);
         ElementWritten (owner_index argument) (replacement argument); OwnerRestored];
       result := match failure_after_write argument with
         | Some reason => Failed reason
         | None => Returned previous
         end |}
  else {| final_state := owner; trace := []; result := Failed 0 |}.

Definition scoped_argument (argument : slice_argument) : natural_argument byte_span span_event :=
  {| parameter := binder_grade argument; run_argument := run_slice_argument argument |}.

Definition evaluate_span_sequence (arguments : list slice_argument) :=
  evaluate_natural_sequence (map scoped_argument arguments).

Lemma restore_written_slice : forall parent offset size index byte,
  span_restore parent (span_write (span_slice parent offset size) index byte) =
    span_write parent (holdfast_int_add 4 offset index) byte.
Proof. reflexivity. Qed.

Lemma scoped_argument_preserves_owner : forall argument owner,
  let final := final_state (run_slice_argument argument owner) in
  span_descriptor final = span_descriptor owner /\
  (forall index, holdfast_int_ne 4 (owner_index argument) index = true ->
    span_read final index = span_read owner index).
Proof.
  intros argument owner. unfold run_slice_argument.
  destruct (usable_slice argument owner); cbn [final_state].
  - rewrite restore_written_slice. split; [reflexivity |].
    intros index outside. now apply holdfast_Span_Read_write_other_ne.
  - split; reflexivity.
Qed.

Theorem span_sequence_preserves_owner : forall arguments values body owner,
  let final := final_state (evaluate_span_sequence arguments values body owner) in
  span_descriptor final = span_descriptor owner /\
  (forall index,
    (forall argument, In argument arguments -> holdfast_int_ne 4 (owner_index argument) index = true) ->
    span_read final index = span_read owner index).
Proof.
  induction arguments as [| argument rest IH]; intros values body owner.
  - unfold evaluate_span_sequence. cbn [map evaluate_natural_sequence].
    unfold evaluate_natural_body. destruct (evaluate_index values body). split; reflexivity.
  - change (let final := final_state
      (sequence_argument (run_slice_argument argument)
        (fun value => evaluate_span_sequence rest (extend_values values (fst (binder_grade argument)) value)
          body) owner) in
      span_descriptor final = span_descriptor owner /\
      (forall index,
        (forall a, In a (argument :: rest) -> holdfast_int_ne 4 (owner_index a) index = true) ->
        span_read final index = span_read owner index)).
    pose proof (scoped_argument_preserves_owner argument owner) as preserved.
    unfold sequence_argument. destruct (run_slice_argument argument owner) as [after events outcome].
    cbn [final_state trace result] in *. destruct preserved as [descriptor frame].
    destruct outcome as [value | reason]; cbn [final_state].
    + destruct (IH (extend_values values (fst (binder_grade argument)) value) body after)
        as [descriptor_rest frame_rest].
      split; [now rewrite descriptor_rest |].
      intros index outside. rewrite frame_rest by (intros a member; apply outside; now right).
      apply frame, outside. now left.
    + split; [exact descriptor |]. intros index outside. apply frame, outside. now left.
Qed.

Theorem checked_bounded_span_sequence : forall arguments env body checked
    values owner ready final effects,
  infer_bounded env (natural_telescope (map binder_grade arguments) body) = Some checked ->
  ArgumentsReturned (map scoped_argument arguments) values owner ready final effects ->
  exists value reads,
    evaluate_index ready body = (value, reads) /\
    evaluate_span_sequence arguments values body owner =
      {| final_state := final; trace := effects ++ map BodyRead reads; result := Returned value |} /\
    span_descriptor final = span_descriptor owner /\
    (forall name allowance, In (name, allowance) (map binder_grade arguments) ->
      count_occ Nat.eq_dec reads name <= allowance).
Proof.
  intros arguments env body checked values owner ready final effects accepted returned.
  assert (map parameter (map scoped_argument arguments) = map binder_grade arguments) as parameters.
  { rewrite map_map. reflexivity. }
  rewrite <- parameters in accepted.
  destruct (checked_bounded_sequence_preserves_arguments byte_span span_event _ _ _ _ _ _ _ _ _ accepted returned)
    as [value [reads [evaluated [sequence grades]]]].
  pose proof (span_sequence_preserves_owner arguments values body owner) as preserved.
  unfold evaluate_span_sequence in preserved |- *.
  rewrite sequence in preserved. cbn [final_state] in preserved.
  exists value, reads. repeat split; try assumption.
  - exact (proj1 preserved).
  - now rewrite <- parameters.
Qed.

Local Definition at_index (n : nat) := holdfast_nat_to_usize n.
Local Definition byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition empty_owner : byte_span := holdfast_Span_AllocZeroed _ (at_index 11) (at_index 4).
Local Definition initial_owner := span_write (span_write empty_owner (at_index 2) (byte 6)) (at_index 3) (byte 21).
Local Definition store_at base index to name grade failure :=
  {| binder_grade := (name, grade); start := at_index base; length := at_index 2;
     element := at_index index; replacement := byte to; failure_after_write := failure |}.
Local Definition store_prefix := store_at 1 0 9 1 0 None.
Local Definition store_next := store_at 1 1 15 2 3 None.
Local Definition store_failing := store_at 1 1 15 2 3 (Some 9).
Local Definition store_suffix := store_at 0 0 17 3 0 None.

Local Definition slice_events argument := map ArgumentEvent
  [SliceBorrowed (start argument) (length argument);
   ElementWritten (owner_index argument) (replacement argument); OwnerRestored].

Example zero_and_repeated_uses_restore_the_scoped_owner :
  let arguments := [store_prefix; store_next] in
  let subject := natural_telescope (map binder_grade arguments) (twice 2) in
  let executed := evaluate_span_sequence arguments (fun _ => 0) (twice 2) initial_owner in
  (exists checked, infer_bounded [] subject = Some checked) /\
  result executed = Returned 12 /\
  trace executed = slice_events store_prefix ++ [ArgumentReturned 0] ++
    slice_events store_next ++ [ArgumentReturned 6; BodyRead 2; BodyRead 2] /\
  span_descriptor (final_state executed) = span_descriptor initial_owner /\
  span_read (final_state executed) (at_index 1) = byte 9 /\
  span_read (final_state executed) (at_index 2) = byte 15 /\
  span_read (final_state executed) (at_index 3) = byte 21.
Proof. cbn zeta. split; [eexists; reflexivity | vm_compute; repeat split]. Qed.

Example failure_restores_after_write_and_skips_suffix :
  let executed := evaluate_span_sequence [store_prefix; store_failing; store_suffix]
    (fun _ => 0) (twice 2) initial_owner in
  result executed = Failed 9 /\
  trace executed = slice_events store_prefix ++ [ArgumentReturned 0] ++ slice_events store_failing /\
  span_descriptor (final_state executed) = span_descriptor initial_owner /\
  span_read (final_state executed) (at_index 0) = byte 0 /\
  span_read (final_state executed) (at_index 1) = byte 9 /\
  span_read (final_state executed) (at_index 2) = byte 15 /\
  span_read (final_state executed) (at_index 3) = byte 21.
Proof. vm_compute. repeat split. Qed.

Example out_of_bounds_slice_fails_without_taking_the_loan :
  run_slice_argument (store_at 3 0 5 1 1 None) initial_owner =
    {| final_state := initial_owner; trace := []; result := Failed 0 |}.
Proof. reflexivity. Qed.

Example shared_owner_fails_without_taking_the_exclusive_loan :
  let shared := holdfast_Span_ReadOnly _ initial_owner in
  run_slice_argument store_prefix shared =
    {| final_state := shared; trace := []; result := Failed 0 |}.
Proof. reflexivity. Qed.

End GradedCbvSpan.
