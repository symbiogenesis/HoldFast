(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool.
Require Import graded_pure graded_domains graded_cbv graded_cbv_span_carrier graded_cbv_span.
Import ListNotations GradedPure GradedDomains GradedCbv GradedCbvSpan.

Module GradedCbvErasure.

Definition erased_parameter : Type := nat.

Definition retain_parameter (param : nat * nat) : option erased_parameter :=
  let '(name, allowance) := param in
  if Nat.eqb allowance 0 then None else Some name.

Definition keep_nonzero_parameters (parameters : list (nat * nat)) : list erased_parameter :=
  flat_map (fun param =>
    match retain_parameter param with
    | Some name => [name]
    | None => []
    end) parameters.

Record erased_argument (State Event : Type) := {
  retained_binder : option erased_parameter;
  run_erased_argument : State -> execution State Event;
}.

Arguments retained_binder {State Event} _.
Arguments run_erased_argument {State Event} _ _.

Definition erase_argument {State Event : Type} (argument : natural_argument State Event)
    : erased_argument State Event :=
  {| retained_binder := retain_parameter (parameter argument);
     run_erased_argument := run_argument argument |}.

Fixpoint evaluate_erased_arguments {State Event : Type}
    (arguments : list (erased_argument State Event)) (values : nat -> nat)
    (body : index) (initial : State) : execution State (observation Event) :=
  match arguments with
  | [] => evaluate_natural_body values body initial
  | argument :: rest =>
      sequence_argument (run_erased_argument argument)
        (fun value =>
          evaluate_erased_arguments rest
            (match retained_binder argument with
             | Some name => extend_values values name value
             | None => values
             end) body) initial
  end.

Definition erased_cbv_eval {State Event : Type}
    (arguments : list (natural_argument State Event)) (values : nat -> nat)
    (body : index) (initial : State) : execution State (observation Event) :=
  evaluate_erased_arguments (map erase_argument arguments) values body initial.

Definition evaluate_erased_sequence {State Event : Type} :=
  @erased_cbv_eval State Event.

Fixpoint evaluate_sentinel_arguments {State Event : Type}
    (arguments : list (natural_argument State Event)) (values : nat -> nat)
    (body : index) (initial : State) : execution State (observation Event) :=
  match arguments with
  | [] => evaluate_natural_body values body initial
  | argument :: rest =>
      sequence_argument (run_argument argument)
        (fun value =>
          evaluate_sentinel_arguments rest
            (if Nat.eqb (snd (parameter argument)) 0
             then extend_values values (fst (parameter argument)) 0
             else extend_values values (fst (parameter argument)) value)
            body) initial
  end.

Fixpoint index_reads (subject : index) : list nat :=
  match subject with
  | IndexVar x => [x]
  | IndexLit _ => []
  | IndexAdd lhs rhs => index_reads lhs ++ index_reads rhs
  end.

Lemma evaluate_index_reads : forall values subject,
  snd (evaluate_index values subject) = index_reads subject.
Proof.
  intros values subject. induction subject as [x | n | lhs IHl rhs IHr]; cbn.
  - reflexivity.
  - reflexivity.
  - destruct (evaluate_index values lhs), (evaluate_index values rhs).
    cbn in *. now rewrite IHl, IHr.
Qed.

Lemma evaluate_index_extensional : forall values1 values2 subject,
  (forall name, In name (index_reads subject) -> values1 name = values2 name) ->
  evaluate_index values1 subject = evaluate_index values2 subject.
Proof.
  intros values1 values2 subject agree.
  induction subject as [x | n | lhs IHl rhs IHr]; cbn in *.
  - rewrite agree; [reflexivity | now left].
  - reflexivity.
  - rewrite IHl by (intros name present; apply agree; apply in_or_app; now left).
    rewrite IHr by (intros name present; apply agree; apply in_or_app; now right).
    reflexivity.
Qed.

Fixpoint eval_zero_grade_sequence {State Event : Type}
    (on_zero : nat -> (nat -> nat) -> (nat -> nat))
    (arguments : list (natural_argument State Event)) (values : nat -> nat)
    (body : index) (initial : State) : execution State (observation Event) :=
  match arguments with
  | [] => evaluate_natural_body values body initial
  | argument :: rest =>
      sequence_argument (run_argument argument)
        (fun value =>
          eval_zero_grade_sequence on_zero rest
            (let '(name, allowance) := parameter argument in
             if Nat.eqb allowance 0 then on_zero name values else extend_values values name value)
            body) initial
  end.

Lemma erased_cbv_eval_as_zero_grade : forall State Event
    (arguments : list (natural_argument State Event)) values body initial,
  erased_cbv_eval arguments values body initial =
    eval_zero_grade_sequence (fun _ vals => vals) arguments values body initial.
Proof.
  intros State Event arguments. induction arguments as [| [[name allowance] run] rest IH];
    intros values body initial; [reflexivity |].
  unfold erased_cbv_eval.
  cbn [map evaluate_erased_arguments eval_zero_grade_sequence].
  unfold sequence_argument, erase_argument, retain_parameter.
  cbn [retained_binder run_erased_argument parameter run_argument].
  destruct (run initial) as [after effects [value | reason]];
    cbn [final_state trace result]; [| reflexivity].
  destruct (Nat.eqb allowance 0);
    unfold erased_cbv_eval in IH; rewrite IH; reflexivity.
Qed.

Lemma sentinel_eval_as_zero_grade : forall State Event
    (arguments : list (natural_argument State Event)) values body initial,
  evaluate_sentinel_arguments arguments values body initial =
    eval_zero_grade_sequence (fun name vals => extend_values vals name 0) arguments values body initial.
Proof.
  intros State Event arguments. induction arguments as [| [[name allowance] run] rest IH];
    intros values body initial; [reflexivity |].
  cbn [evaluate_sentinel_arguments eval_zero_grade_sequence].
  unfold sequence_argument. cbn [parameter run_argument fst snd].
  destruct (run initial) as [after effects [value | reason]];
    cbn [final_state trace result]; [| reflexivity].
  destruct (Nat.eqb allowance 0);
    rewrite IH; reflexivity.
Qed.

Lemma zero_grade_sequence_agrees_derives : forall (allows : nat -> nat -> Prop),
  (forall actual, allows actual 0 -> actual = 0) ->
  forall (on_zero : nat -> (nat -> nat) -> (nat -> nat)),
  (forall name values1 values2 y, y <> name -> values1 y = values2 y ->
    values1 y = on_zero name values2 y) ->
  forall State Event (arguments : list (natural_argument State Event)) env body checked
    values1 values2 initial,
  DerivesWith allows env (natural_telescope (map parameter arguments) body) checked ->
  (forall name, In name (index_reads body) -> values1 name = values2 name) ->
  eval_zero_grade_sequence on_zero arguments values2 body initial =
    evaluate_natural_sequence arguments values1 body initial.
Proof.
  intros allows zero_is_0 on_zero on_zero_other State Event.
  induction arguments as [| argument rest IH];
    intros env body checked values1 values2 initial typed agree.
  - cbn. unfold evaluate_natural_body.
    erewrite evaluate_index_extensional; [reflexivity |].
    intros name present. symmetry. now apply agree.
  - destruct argument as [[name allowance] run].
    cbn [map parameter natural_telescope] in typed.
    pose proof (natural_telescope_reads_with allows
      ((name, allowance) :: map parameter rest) env body checked typed values1)
      as [bound _].
    inversion typed as [| | x q domain body' codomain a u v
      fresh_x typed_domain derives_rest allowed_x | | | |]; subst.
    cbn [eval_zero_grade_sequence evaluate_natural_sequence parameter fst snd run_argument].
    unfold sequence_argument.
    destruct (run initial) as [after effects [value | reason]] eqn:ran;
      cbn [final_state trace result]; [| reflexivity].
    destruct (Nat.eqb allowance 0) eqn:is_zero.
    + apply Nat.eqb_eq in is_zero. subst allowance.
      destruct (bound name 0 (or_introl eq_refl)) as [_ allowed_reads].
      rewrite evaluate_index_reads in allowed_reads.
      apply zero_is_0 in allowed_reads.
      apply (count_occ_not_In Nat.eq_dec) in allowed_reads.
      erewrite (IH _ _ _ (extend_values values1 name value) (on_zero name values2) after derives_rest);
        [reflexivity |].
      intros reader present. unfold extend_values.
      destruct (Nat.eqb reader name) eqn:eq_reader.
      * apply Nat.eqb_eq in eq_reader. subst reader. contradiction.
      * apply Nat.eqb_neq in eq_reader. apply on_zero_other; [exact eq_reader | now apply agree].
    + erewrite (IH _ _ _ (extend_values values1 name value) (extend_values values2 name value) after derives_rest);
        [reflexivity |].
      intros reader present. unfold extend_values.
      destruct (Nat.eqb reader name); [reflexivity | now apply agree].
Qed.

Lemma erased_sequence_agrees_derives : forall (allows : nat -> nat -> Prop),
  (forall actual, allows actual 0 -> actual = 0) ->
  forall State Event (arguments : list (natural_argument State Event)) env body checked
    values1 values2 initial,
  DerivesWith allows env (natural_telescope (map parameter arguments) body) checked ->
  (forall name, In name (index_reads body) -> values1 name = values2 name) ->
  erased_cbv_eval arguments values2 body initial =
    evaluate_natural_sequence arguments values1 body initial.
Proof.
  intros allows zero_is_0 State Event arguments env body checked values1 values2 initial typed agree.
  rewrite erased_cbv_eval_as_zero_grade.
  eapply zero_grade_sequence_agrees_derives; eauto.
Qed.

Lemma sentinel_sequence_agrees_derives : forall (allows : nat -> nat -> Prop),
  (forall actual, allows actual 0 -> actual = 0) ->
  forall State Event (arguments : list (natural_argument State Event)) env body checked
    values1 values2 initial,
  DerivesWith allows env (natural_telescope (map parameter arguments) body) checked ->
  (forall name, In name (index_reads body) -> values1 name = values2 name) ->
  evaluate_sentinel_arguments arguments values2 body initial =
    evaluate_natural_sequence arguments values1 body initial.
Proof.
  intros allows zero_is_0 State Event arguments env body checked values1 values2 initial typed agree.
  rewrite sentinel_eval_as_zero_grade.
  eapply zero_grade_sequence_agrees_derives; eauto.
  intros name v1 v2 y Hneq Heq. unfold extend_values.
  apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Theorem cbv_zero_grade_erasure_sound_with : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  (forall actual, allows actual 0 -> actual = 0) ->
  forall State Event (arguments : list (natural_argument State Event)) env body checked
    values initial,
  infer_with allowsb env (natural_telescope (map parameter arguments) body) = Some checked ->
  erased_cbv_eval arguments values body initial =
    evaluate_natural_sequence arguments values body initial.
Proof.
  intros allows allowsb sound zero_is_0 State Event arguments env body checked values initial checked_ok.
  apply (infer_with_sound allows allowsb sound) in checked_ok.
  eapply erased_sequence_agrees_derives; eauto.
Qed.

Inductive graded_mode :=
| ExactMode
| BoundMode.

Definition mode_allows (mode : graded_mode) : nat -> nat -> Prop :=
  match mode with
  | ExactMode => @allows NatExact
  | BoundMode => @allows NatBound
  end.

Definition mode_allowsb (mode : graded_mode) : nat -> nat -> bool :=
  match mode with
  | ExactMode => @allowsb NatExact
  | BoundMode => @allowsb NatBound
  end.

Lemma mode_allows_sound : forall mode actual allowance,
  mode_allowsb mode actual allowance = true -> mode_allows mode actual allowance.
Proof.
  intros [|] actual allowance accepted; cbn in *.
  - now apply Nat.eqb_eq.
  - now apply Nat.leb_le.
Qed.

Lemma mode_allows_zero : forall mode actual,
  mode_allows mode actual 0 -> actual = 0.
Proof.
  intros [|] actual admitted; cbn in *.
  - exact admitted.
  - apply Nat.le_0_r. exact admitted.
Qed.

Theorem cbv_zero_grade_erasure_sound : forall mode State Event
    (arguments : list (natural_argument State Event)) env body checked values initial,
  infer_with (mode_allowsb mode) env (natural_telescope (map parameter arguments) body) = Some checked ->
  erased_cbv_eval arguments values body initial =
    evaluate_natural_sequence arguments values body initial.
Proof.
  intros mode.
  apply (cbv_zero_grade_erasure_sound_with (mode_allows mode) (mode_allowsb mode)
    (mode_allows_sound mode) (mode_allows_zero mode)).
Qed.

Theorem cbv_exact_zero_grade_erasure_sound : forall State Event
    (arguments : list (natural_argument State Event)) env body checked values initial,
  infer env (natural_telescope (map parameter arguments) body) = Some checked ->
  erased_cbv_eval arguments values body initial =
    evaluate_natural_sequence arguments values body initial.
Proof. exact (cbv_zero_grade_erasure_sound ExactMode). Qed.

Theorem cbv_bounded_zero_grade_erasure_sound : forall State Event
    (arguments : list (natural_argument State Event)) env body checked values initial,
  infer_bounded env (natural_telescope (map parameter arguments) body) = Some checked ->
  erased_cbv_eval arguments values body initial =
    evaluate_natural_sequence arguments values body initial.
Proof. exact (cbv_zero_grade_erasure_sound BoundMode). Qed.

Theorem cbv_sentinel_erasure_sound : forall mode State Event
    (arguments : list (natural_argument State Event)) env body checked values initial,
  infer_with (mode_allowsb mode) env (natural_telescope (map parameter arguments) body) = Some checked ->
  evaluate_sentinel_arguments arguments values body initial =
    evaluate_natural_sequence arguments values body initial.
Proof.
  intros mode State Event arguments env body checked values initial checked_ok.
  apply (infer_with_sound (mode_allows mode) (mode_allowsb mode) (mode_allows_sound mode)) in checked_ok.
  eapply sentinel_sequence_agrees_derives; [apply (mode_allows_zero mode) | exact checked_ok |].
  intros. reflexivity.
Qed.

Theorem cbv_zero_grade_erasure_preserves_failure : forall mode State Event
    (prefix : list (natural_argument State Event)) values initial ready after effects
    failed suffix body checked final failure_effects reason,
  infer_with (mode_allowsb mode) [] (natural_telescope (map parameter (prefix ++ failed :: suffix)) body) =
    Some checked ->
  ArgumentsReturned prefix values initial ready after effects ->
  run_argument failed after =
    {| final_state := final; trace := failure_effects; result := Failed reason |} ->
  erased_cbv_eval (prefix ++ failed :: suffix) values body initial =
    {| final_state := final;
       trace := effects ++ map ArgumentEvent failure_effects; result := Failed reason |}.
Proof.
  intros mode State Event prefix values initial ready after effects failed suffix body checked
    final failure_effects reason checked_ok returned failure.
  erewrite cbv_zero_grade_erasure_sound by eassumption.
  eapply sequence_preserves_failure; eassumption.
Qed.

Definition evaluate_erased_span_sequence (arguments : list slice_argument) :=
  erased_cbv_eval (map scoped_argument arguments).

Lemma slice_writeback_exact : forall argument owner,
  usable_slice argument owner = true ->
  span_read (final_state (run_slice_argument argument owner)) (owner_index argument) =
    replacement argument.
Proof.
  intros argument owner usable.
  unfold run_slice_argument. rewrite usable. cbn [final_state].
  rewrite restore_written_slice.
  apply holdfast_Span_Read_write_same.
Qed.

Lemma span_sequence_prefix_writeback : forall prefix argument suffix values owner ready after
    prefix_effects body,
  ArgumentsReturned (map scoped_argument prefix) values owner ready after prefix_effects ->
  usable_slice argument after = true ->
  (forall later, In later suffix ->
    holdfast_int_ne 4 (owner_index later) (owner_index argument) = true) ->
  span_read (final_state (evaluate_span_sequence (prefix ++ argument :: suffix) values body owner))
    (owner_index argument) = replacement argument.
Proof.
  intros prefix argument suffix values owner ready after prefix_effects body
    returned usable disjoint.
  unfold evaluate_span_sequence.
  rewrite map_app. cbn [map].
  rewrite (sequence_preserves_returned_prefix byte_span span_event _ _ _ _ _ _ _ _ returned).
  unfold prepend_observations. cbn [final_state].
  cbn [evaluate_natural_sequence]. unfold sequence_argument.
  cbn [scoped_argument run_argument parameter].
  pose proof (slice_writeback_exact argument after usable) as written.
  destruct (run_slice_argument argument after) as [after1 events outcome] eqn:step.
  cbn [final_state trace result] in *.
  destruct outcome as [value | reason]; cbn [final_state].
  - pose proof (span_sequence_preserves_owner suffix
      (extend_values ready (fst (binder_grade argument)) value) body after1)
      as [_ frame_suffix].
    unfold evaluate_span_sequence in frame_suffix.
    rewrite frame_suffix by exact disjoint.
    exact written.
  - exact written.
Qed.

Theorem cbv_span_erasure_preserves_owner_and_frame : forall mode
    (arguments : list slice_argument) env body checked values owner,
  infer_with (mode_allowsb mode) env (natural_telescope (map binder_grade arguments) body) = Some checked ->
  let executed := evaluate_erased_span_sequence arguments values body owner in
  executed = evaluate_span_sequence arguments values body owner /\
  span_descriptor (final_state executed) = span_descriptor owner /\
  (forall index,
    (forall argument, In argument arguments -> holdfast_int_ne 4 (owner_index argument) index = true) ->
    span_read (final_state executed) index = span_read owner index) /\
  (forall prefix argument suffix ready after prefix_effects,
    arguments = prefix ++ argument :: suffix ->
    ArgumentsReturned (map scoped_argument prefix) values owner ready after prefix_effects ->
    usable_slice argument after = true ->
    (forall later, In later suffix ->
      holdfast_int_ne 4 (owner_index later) (owner_index argument) = true) ->
    span_read (final_state executed) (owner_index argument) = replacement argument) /\
  (forall prefix failed suffix ready after prefix_effects final failure_effects reason,
    arguments = prefix ++ failed :: suffix ->
    ArgumentsReturned (map scoped_argument prefix) values owner ready after prefix_effects ->
    run_slice_argument failed after =
      {| final_state := final; trace := failure_effects; result := Failed reason |} ->
    executed =
      {| final_state := final;
         trace := prefix_effects ++ map ArgumentEvent failure_effects;
         result := Failed reason |} /\
    span_descriptor final = span_descriptor owner /\
    (forall index,
      (forall argument, In argument (prefix ++ [failed]) ->
        holdfast_int_ne 4 (owner_index argument) index = true) ->
      span_read final index = span_read owner index)).
Proof.
  intros mode arguments env body checked values owner checked_ok.
  cbn zeta.
  assert (map parameter (map scoped_argument arguments) = map binder_grade arguments) as params.
  { rewrite map_map. reflexivity. }
  rewrite <- params in checked_ok.
  pose proof (cbv_zero_grade_erasure_sound mode byte_span span_event
    (map scoped_argument arguments) env body checked values owner checked_ok) as same_exec.
  unfold evaluate_erased_span_sequence, evaluate_span_sequence in *.
  rewrite same_exec.
  pose proof (span_sequence_preserves_owner arguments values body owner) as [desc frame].
  unfold evaluate_span_sequence in desc, frame.
  split; [reflexivity |].
  split; [exact desc |].
  split; [exact frame |].
  split.
  - intros prefix argument suffix ready after prefix_effects -> returned usable disjoint.
    eapply span_sequence_prefix_writeback; eassumption.
  - intros prefix failed suffix ready after prefix_effects final failure_effects reason
      -> returned failure.
    repeat split.
    + rewrite map_app. cbn [map].
      eapply sequence_preserves_failure; eassumption.
    + pose proof (span_sequence_preserves_owner (prefix ++ [failed]) values body owner)
        as [prefix_desc _].
      unfold evaluate_span_sequence in prefix_desc.
      rewrite map_app in prefix_desc. cbn [map] in prefix_desc.
      rewrite (sequence_preserves_failure byte_span span_event
        (map scoped_argument prefix) values owner ready after prefix_effects
        (scoped_argument failed) [] body final failure_effects reason returned failure)
        in prefix_desc.
      cbn [final_state] in prefix_desc. exact prefix_desc.
    + intros index outside.
      pose proof (span_sequence_preserves_owner (prefix ++ [failed]) values body owner)
        as [_ prefix_frame].
      unfold evaluate_span_sequence in prefix_frame.
      rewrite map_app in prefix_frame. cbn [map] in prefix_frame.
      rewrite (sequence_preserves_failure byte_span span_event
        (map scoped_argument prefix) values owner ready after prefix_effects
        (scoped_argument failed) [] body final failure_effects reason returned failure)
        in prefix_frame.
      cbn [final_state] in prefix_frame.
      now apply prefix_frame.
Qed.

Theorem cbv_span_erasure_preserves_returned_reads : forall mode
    (arguments : list slice_argument) env body checked values owner ready final effects,
  infer_with (mode_allowsb mode) env (natural_telescope (map binder_grade arguments) body) = Some checked ->
  ArgumentsReturned (map scoped_argument arguments) values owner ready final effects ->
  exists value reads,
    evaluate_index ready body = (value, reads) /\
    evaluate_erased_span_sequence arguments values body owner =
      {| final_state := final; trace := effects ++ map BodyRead reads; result := Returned value |} /\
    span_descriptor final = span_descriptor owner /\
    (forall name allowance, In (name, allowance) (map binder_grade arguments) ->
      mode_allows mode (count_occ Nat.eq_dec reads name) allowance).
Proof.
  intros mode arguments env body checked values owner ready final effects checked_ok returned.
  assert (map parameter (map scoped_argument arguments) = map binder_grade arguments) as params.
  { rewrite map_map. reflexivity. }
  rewrite <- params in checked_ok.
  pose proof (cbv_zero_grade_erasure_sound mode byte_span span_event
    (map scoped_argument arguments) env body checked values owner checked_ok) as same_exec.
  destruct (checked_sequence_preserves_arguments_with (mode_allows mode) (mode_allowsb mode)
    (mode_allows_sound mode) byte_span span_event (map scoped_argument arguments)
    env body checked values owner ready final effects checked_ok returned)
    as [value [reads [evaluated [sequence grades]]]].
  pose proof (span_sequence_preserves_owner arguments values body owner) as [desc _].
  unfold evaluate_erased_span_sequence, evaluate_span_sequence in *.
  rewrite same_exec. rewrite sequence in desc |- *. cbn [final_state] in desc.
  exists value, reads. repeat split; try assumption.
  now rewrite <- params.
Qed.

Example exact_zero_grade_erasure_example :
  let arguments :=
    [sample_argument 1 0 incrementing_argument; sample_argument 2 2 incrementing_argument] in
  let subject := natural_telescope (map parameter arguments) (twice 2) in
  (exists checked, infer [] subject = Some checked) /\
  keep_nonzero_parameters (map parameter arguments) = [2] /\
  erased_cbv_eval arguments (fun _ => 99) (twice 2) 3 =
    evaluate_natural_sequence arguments (fun _ => 99) (twice 2) 3 /\
  erased_cbv_eval arguments (fun _ => 99) (twice 2) 3 =
    {| final_state := 5;
       trace := [ArgumentEvent 3; ArgumentReturned 10; ArgumentEvent 4; ArgumentReturned 11;
         BodyRead 2; BodyRead 2];
       result := Returned 22 |}.
Proof. cbn. split; [eexists; reflexivity | repeat split; reflexivity]. Qed.

Example bound_zero_grade_erasure_example :
  let arguments :=
    [sample_argument 1 0 incrementing_argument; sample_argument 2 3 incrementing_argument] in
  let subject := natural_telescope (map parameter arguments) (twice 2) in
  (exists checked, infer_bounded [] subject = Some checked) /\
  infer [] subject = None /\
  keep_nonzero_parameters (map parameter arguments) = [2] /\
  erased_cbv_eval arguments (fun _ => 99) (twice 2) 3 =
    evaluate_natural_sequence arguments (fun _ => 99) (twice 2) 3 /\
  erased_cbv_eval arguments (fun _ => 99) (twice 2) 3 =
    {| final_state := 5;
       trace := [ArgumentEvent 3; ArgumentReturned 10; ArgumentEvent 4; ArgumentReturned 11;
         BodyRead 2; BodyRead 2];
       result := Returned 22 |}.
Proof. cbn. split; [eexists; reflexivity | repeat split; reflexivity]. Qed.

Example erasure_preserves_failure_prefix_example :
  let arguments :=
    [sample_argument 1 0 incrementing_argument;
     sample_argument 2 2 failing_argument;
     sample_argument 3 0 incrementing_argument] in
  let subject := natural_telescope (map parameter arguments) (twice 2) in
  (exists checked, infer [] subject = Some checked) /\
  erased_cbv_eval arguments (fun _ => 99) (twice 2) 3 =
    evaluate_natural_sequence arguments (fun _ => 99) (twice 2) 3 /\
  erased_cbv_eval arguments (fun _ => 99) (twice 2) 3 =
    {| final_state := 5;
       trace := [ArgumentEvent 3; ArgumentReturned 10; ArgumentEvent 4];
       result := Failed 9 |}.
Proof. cbn. split; [eexists; reflexivity | split; reflexivity]. Qed.

Example span_zero_grade_erasure_preserves_owner_and_writeback :
  let arguments := [store_prefix; store_next] in
  let subject := natural_telescope (map binder_grade arguments) (twice 2) in
  let executed := evaluate_erased_span_sequence arguments (fun _ => 99) (twice 2) initial_owner in
  (exists checked, infer_bounded [] subject = Some checked) /\
  keep_nonzero_parameters (map binder_grade arguments) = [2] /\
  executed = evaluate_span_sequence arguments (fun _ => 99) (twice 2) initial_owner /\
  result executed = Returned 12 /\
  trace executed = slice_events store_prefix ++ [ArgumentReturned 0] ++
    slice_events store_next ++ [ArgumentReturned 6; BodyRead 2; BodyRead 2] /\
  span_descriptor (final_state executed) = span_descriptor initial_owner /\
  span_read (final_state executed) (at_index 0) = byte 0 /\
  span_read (final_state executed) (at_index 1) = byte 9 /\
  span_read (final_state executed) (at_index 2) = byte 15 /\
  span_read (final_state executed) (at_index 3) = byte 21.
Proof. cbn zeta. split; [eexists; reflexivity | vm_compute; repeat split]. Qed.

Example span_erasure_failure_preserves_prefix_and_writeback :
  let arguments := [store_prefix; store_failing; store_suffix] in
  let subject := natural_telescope (map binder_grade arguments) (twice 2) in
  let executed := evaluate_erased_span_sequence arguments (fun _ => 99) (twice 2) initial_owner in
  (exists checked, infer_bounded [] subject = Some checked) /\
  executed = evaluate_span_sequence arguments (fun _ => 99) (twice 2) initial_owner /\
  result executed = Failed 9 /\
  trace executed = slice_events store_prefix ++ [ArgumentReturned 0] ++ slice_events store_failing /\
  span_descriptor (final_state executed) = span_descriptor initial_owner /\
  span_read (final_state executed) (at_index 0) = byte 0 /\
  span_read (final_state executed) (at_index 1) = byte 9 /\
  span_read (final_state executed) (at_index 2) = byte 15 /\
  span_read (final_state executed) (at_index 3) = byte 21.
Proof. cbn zeta. split; [eexists; reflexivity | vm_compute; repeat split]. Qed.

End GradedCbvErasure.
