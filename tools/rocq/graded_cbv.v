(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat.
Require Import graded_pure graded_domains.
Import ListNotations GradedPure.

Module GradedCbv.

Fixpoint evaluate_index (values : nat -> nat) (subject : index) : nat * list nat :=
  match subject with
  | IndexVar x => (values x, [x])
  | IndexLit n => (n, [])
  | IndexAdd lhs rhs =>
      let '(left_value, left_reads) := evaluate_index values lhs in
      let '(right_value, right_reads) := evaluate_index values rhs in
      (left_value + right_value, left_reads ++ right_reads)
  end.

Lemma index_reads_match_demand : forall env subject row,
  IndexDemand env subject row -> forall values name,
  count_occ Nat.eq_dec (snd (evaluate_index values subject)) name = uses row name.
Proof.
  intros env subject row derivation.
  induction derivation as [x entry found natural | n | lhs rhs p q left IHleft right IHright];
    intros values name.
  - cbn [evaluate_index snd count_occ uses].
    destruct (Nat.eq_dec x name) as [same | distinct].
    + subst name. now rewrite Nat.eqb_refl.
    + assert (Nat.eqb name x = false) as different by (apply Nat.eqb_neq; congruence).
      now rewrite different.
  - reflexivity.
  - specialize (IHleft values name). specialize (IHright values name).
    cbn [evaluate_index].
    destruct (evaluate_index values lhs), (evaluate_index values rhs).
    cbn in *. now rewrite count_occ_app, uses_append, IHleft, IHright.
Qed.

Lemma checked_lambda_reads : forall env name allowance body checked values,
  infer env (Lambda name allowance Natural (NatValue body)) = Some checked ->
  count_occ Nat.eq_dec (snd (evaluate_index values body)) name = allowance.
Proof.
  intros env name allowance body checked values accepted.
  apply infer_sound in accepted.
  inversion accepted as [| | x q domain body' codomain a u v fresh typed derives exact_use | |]; subst.
  inversion derives; subst.
  now erewrite index_reads_match_demand by eassumption.
Qed.

Inductive outcome :=
| Returned (value : nat)
| Failed (reason : nat).

Record execution (State Event : Type) := {
  final_state : State;
  trace : list Event;
  result : outcome;
}.

Arguments final_state {State Event} _.
Arguments trace {State Event} _.
Arguments result {State Event} _.

Inductive observation (Event : Type) :=
| ArgumentEvent (event : Event)
| ArgumentReturned (value : nat)
| BodyRead (name : nat).

Arguments ArgumentEvent {Event} _.
Arguments ArgumentReturned {Event} _.
Arguments BodyRead {Event} _.

Definition extend_values (values : nat -> nat) (binder value : nat) : nat -> nat :=
  fun name => if Nat.eqb name binder then value else values name.

Definition sequence_argument {State Event : Type} (argument : State -> execution State Event)
    (continue : nat -> State -> execution State (observation Event))
    (initial : State) : execution State (observation Event) :=
  let evaluated := argument initial in
  let effects := map ArgumentEvent (trace evaluated) in
  match result evaluated with
  | Failed reason =>
      {| final_state := final_state evaluated; trace := effects; result := Failed reason |}
  | Returned value =>
      let next := continue value (final_state evaluated) in
      {| final_state := final_state next;
         trace := effects ++ ArgumentReturned value :: trace next;
         result := result next |}
  end.

Definition evaluate_natural_body {State Event : Type} (values : nat -> nat)
    (body : index) (state : State) : execution State (observation Event) :=
  let '(value, reads) := evaluate_index values body in
  {| final_state := state; trace := map BodyRead reads; result := Returned value |}.

Definition apply_natural_lambda {State Event : Type} (values : nat -> nat)
    (binder : nat) (body : index) (argument : State -> execution State Event)
    (initial : State) : execution State (observation Event) :=
  sequence_argument argument
    (fun value => evaluate_natural_body (extend_values values binder value) body) initial.

Theorem checked_application_preserves_argument :
  forall State Event env binder allowance body checked values
    (argument : State -> execution State Event) initial after effects value,
  infer env (Lambda binder allowance Natural (NatValue body)) = Some checked ->
  argument initial = {| final_state := after; trace := effects; result := Returned value |} ->
  exists returned reads,
    evaluate_index (extend_values values binder value) body = (returned, reads) /\
    apply_natural_lambda values binder body argument initial =
      {| final_state := after;
         trace := map ArgumentEvent effects ++ ArgumentReturned value :: map BodyRead reads;
         result := Returned returned |} /\
    count_occ Nat.eq_dec reads binder = allowance.
Proof.
  intros State Event env binder allowance body checked values argument initial after effects value
    accepted evaluated.
  pose proof (checked_lambda_reads env binder allowance body checked
    (extend_values values binder value) accepted) as exact_reads.
  unfold apply_natural_lambda, sequence_argument. rewrite evaluated. cbn.
  unfold evaluate_natural_body.
  destruct (evaluate_index (extend_values values binder value) body) as [returned reads].
  exists returned, reads. repeat split. exact exact_reads.
Qed.

Theorem application_preserves_argument_failure :
  forall State Event values binder body (argument : State -> execution State Event)
    initial after effects reason,
  argument initial = {| final_state := after; trace := effects; result := Failed reason |} ->
  apply_natural_lambda values binder body argument initial =
    {| final_state := after; trace := map ArgumentEvent effects; result := Failed reason |}.
Proof.
  intros State Event values binder body argument initial after effects reason evaluated.
  unfold apply_natural_lambda, sequence_argument. now rewrite evaluated.
Qed.

Fixpoint natural_telescope (parameters : list (nat * nat)) (body : index) : term :=
  match parameters with
  | [] => NatValue body
  | (name, allowance) :: rest =>
      Lambda name allowance Natural (natural_telescope rest body)
  end.

Lemma natural_telescope_reads_with : forall allows parameters env body checked,
  DerivesWith allows env (natural_telescope parameters body) checked ->
  forall values,
    (forall name allowance, In (name, allowance) parameters ->
      fresh env name = true /\
      allows (count_occ Nat.eq_dec (snd (evaluate_index values body)) name) allowance) /\
    (forall name, ~ In name (map fst parameters) ->
      count_occ Nat.eq_dec (snd (evaluate_index values body)) name =
        uses (computation_demand checked) name).
Proof.
  intros allows.
  induction parameters as [| [x grade] rest IH]; intros env body checked typed values.
  - inversion typed; subst. split.
    + contradiction.
    + intros name _. now erewrite index_reads_match_demand by eassumption.
  - inversion typed as [| | name allowance domain inner codomain a u v
      new typed_domain typed_inner admitted | |]; subst.
    inversion typed_domain; subst.
    destruct (IH _ _ _ typed_inner values) as [bound unbound].
    split.
    + intros name allowance [head | tail].
      * inversion head; subst name allowance. split; [exact new |].
        assert (~ In x (map fst rest)) as absent.
        { intro repeated.
          apply in_map_iff in repeated as [[repeated_name repeated_grade] [same member]].
          cbn in same. subst repeated_name.
          destruct (bound x repeated_grade member) as [impossible _].
          unfold fresh, lookup in impossible. cbn in impossible.
          now rewrite Nat.eqb_refl in impossible. }
        now rewrite (unbound x absent).
      * destruct (bound name allowance tail) as [new_inner admitted_reads].
        split; [| exact admitted_reads].
        unfold fresh, lookup in new_inner. cbn in new_inner.
        now destruct (Nat.eqb name x).
    + intros name absent. cbn in absent.
      cbn [computation_demand]. rewrite uses_without.
      assert (Nat.eqb name x = false) as distinct.
      { apply Nat.eqb_neq. intro same. apply absent. now left. }
      rewrite distinct. apply unbound. intro present. apply absent. now right.
Qed.

Lemma natural_telescope_reads : forall parameters env body checked,
  Derives env (natural_telescope parameters body) checked ->
  forall values,
    (forall name allowance, In (name, allowance) parameters ->
      fresh env name = true /\
      count_occ Nat.eq_dec (snd (evaluate_index values body)) name = allowance) /\
    (forall name, ~ In name (map fst parameters) ->
      count_occ Nat.eq_dec (snd (evaluate_index values body)) name =
        uses (computation_demand checked) name).
Proof. exact (natural_telescope_reads_with (@eq nat)). Qed.

Record natural_argument (State Event : Type) := {
  parameter : nat * nat;
  run_argument : State -> execution State Event;
}.

Arguments parameter {State Event} _.
Arguments run_argument {State Event} _ _.

Definition prepend_observations {State Event : Type} (prefix : list (observation Event))
    (next : execution State (observation Event)) : execution State (observation Event) :=
  {| final_state := final_state next; trace := prefix ++ trace next; result := result next |}.

Fixpoint evaluate_natural_sequence {State Event : Type}
    (arguments : list (natural_argument State Event)) (values : nat -> nat)
    (body : index) (initial : State) : execution State (observation Event) :=
  match arguments with
  | [] => evaluate_natural_body values body initial
  | argument :: rest =>
      sequence_argument (run_argument argument)
        (fun value =>
          evaluate_natural_sequence rest (extend_values values (fst (parameter argument)) value)
            body) initial
  end.

Lemma singleton_sequence_matches_application : forall State Event values binder allowance body
    (argument : State -> execution State Event) initial,
  evaluate_natural_sequence [{| parameter := (binder, allowance); run_argument := argument |}]
    values body initial = apply_natural_lambda values binder body argument initial.
Proof. reflexivity. Qed.

Inductive ArgumentsReturned {State Event : Type} :
    list (natural_argument State Event) ->
    (nat -> nat) -> State -> (nat -> nat) -> State -> list (observation Event) -> Prop :=
| ArgumentsDone : forall values state, ArgumentsReturned [] values state values state []
| ArgumentStep : forall argument rest values initial value after effects ready final tail,
    run_argument argument initial =
      {| final_state := after; trace := effects; result := Returned value |} ->
    ArgumentsReturned rest (extend_values values (fst (parameter argument)) value)
      after ready final tail ->
    ArgumentsReturned (argument :: rest) values initial ready final
      (map ArgumentEvent effects ++ ArgumentReturned value :: tail).

Lemma sequence_preserves_returned_prefix : forall State Event prefix values initial ready final
    (effects : list (observation Event)) suffix body,
  ArgumentsReturned prefix values initial ready final effects ->
  evaluate_natural_sequence (prefix ++ suffix) values body initial =
    prepend_observations (State := State) effects
      (evaluate_natural_sequence suffix ready body final).
Proof.
  intros State Event prefix values initial ready final effects suffix body returned.
  induction returned as
    [values state | argument rest values initial value after effects ready final tail step rest_done IH].
  - cbn. now destruct (evaluate_natural_sequence suffix values body state).
  - cbn [app evaluate_natural_sequence]. unfold sequence_argument. rewrite step. cbn.
    rewrite IH. unfold prepend_observations. cbn.
    now rewrite <- !app_assoc.
Qed.

Theorem sequence_preserves_failure : forall State Event
    (prefix : list (natural_argument State Event)) values initial ready after effects
    failed suffix body final failure_effects reason,
  ArgumentsReturned prefix values initial ready after effects ->
  run_argument failed after =
    {| final_state := final; trace := failure_effects; result := Failed reason |} ->
  evaluate_natural_sequence (prefix ++ failed :: suffix) values body initial =
    {| final_state := final;
       trace := effects ++ map ArgumentEvent failure_effects; result := Failed reason |}.
Proof.
  intros State Event prefix values initial ready after effects failed suffix body final
    failure_effects reason returned failure.
  rewrite (sequence_preserves_returned_prefix State Event _ _ _ _ _ _ _ _ returned).
  cbn [evaluate_natural_sequence]. unfold sequence_argument. now rewrite failure.
Qed.

Theorem checked_sequence_preserves_arguments_with : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall State Event
    (arguments : list (natural_argument State Event)) env body checked
    values initial ready final effects,
  infer_with allowsb env (natural_telescope (map parameter arguments) body) = Some checked ->
  ArgumentsReturned arguments values initial ready final effects ->
  exists value reads,
    evaluate_index ready body = (value, reads) /\
    evaluate_natural_sequence arguments values body initial =
      {| final_state := final; trace := effects ++ map BodyRead reads; result := Returned value |} /\
    (forall name allowance, In (name, allowance) (map parameter arguments) ->
      allows (count_occ Nat.eq_dec reads name) allowance).
Proof.
  intros allows allowsb sound State Event arguments env body checked values initial ready final effects
    accepted returned.
  apply (infer_with_sound allows allowsb sound) in accepted.
  destruct (natural_telescope_reads_with _ _ _ _ _ accepted ready) as [bound _].
  pose proof (sequence_preserves_returned_prefix State Event _ _ _ _ _ _ [] body returned)
    as preserves.
  rewrite app_nil_r in preserves.
  cbn [evaluate_natural_sequence] in preserves. unfold evaluate_natural_body in preserves.
  destruct (evaluate_index ready body) as [value reads].
  exists value, reads. repeat split.
  - exact preserves.
  - intros name allowance present. now destruct (bound name allowance present).
Qed.

Theorem checked_sequence_preserves_arguments : forall State Event
    (arguments : list (natural_argument State Event)) env body checked
    values initial ready final effects,
  infer env (natural_telescope (map parameter arguments) body) = Some checked ->
  ArgumentsReturned arguments values initial ready final effects ->
  exists value reads,
    evaluate_index ready body = (value, reads) /\
    evaluate_natural_sequence arguments values body initial =
      {| final_state := final; trace := effects ++ map BodyRead reads; result := Returned value |} /\
    (forall name allowance, In (name, allowance) (map parameter arguments) ->
      count_occ Nat.eq_dec reads name = allowance).
Proof.
  apply (checked_sequence_preserves_arguments_with (@eq nat) Nat.eqb).
  intros. now apply Nat.eqb_eq.
Qed.

Definition infer_bounded : context -> term -> option judgment :=
  infer_with (@GradedDomains.allowsb GradedDomains.NatBound).

Theorem checked_bounded_sequence_preserves_arguments : forall State Event
    (arguments : list (natural_argument State Event)) env body checked
    values initial ready final effects,
  infer_bounded env (natural_telescope (map parameter arguments) body) = Some checked ->
  ArgumentsReturned arguments values initial ready final effects ->
  exists value reads,
    evaluate_index ready body = (value, reads) /\
    evaluate_natural_sequence arguments values body initial =
      {| final_state := final; trace := effects ++ map BodyRead reads; result := Returned value |} /\
    (forall name allowance, In (name, allowance) (map parameter arguments) ->
      count_occ Nat.eq_dec reads name <= allowance).
Proof.
  apply (checked_sequence_preserves_arguments_with
    (@GradedDomains.allows GradedDomains.NatBound) (@GradedDomains.allowsb GradedDomains.NatBound)).
  intros actual allowance accepted.
  destruct (GradedDomains.allows_reflect GradedDomains.NatBound actual allowance);
    [assumption | discriminate].
Qed.

Definition incrementing_argument (state : nat) : execution nat nat :=
  {| final_state := S state; trace := [state]; result := Returned (state + 7) |}.

Definition failing_argument (state : nat) : execution nat nat :=
  {| final_state := S state; trace := [state]; result := Failed 9 |}.

Example zero_grade_keeps_the_argument_observations :
  (exists checked, infer [] (Lambda 1 0 Natural (NatValue (IndexLit 4))) = Some checked) /\
  apply_natural_lambda (fun _ => 0) 1 (IndexLit 4) incrementing_argument 3 =
    {| final_state := 4; trace := [ArgumentEvent 3; ArgumentReturned 10]; result := Returned 4 |}.
Proof. split; [eexists |]; reflexivity. Qed.

Example two_reads_reuse_the_returned_value :
  (exists checked, infer [] (Lambda 1 2 Natural (NatValue (twice 1))) = Some checked) /\
  apply_natural_lambda (fun _ => 0) 1 (twice 1) incrementing_argument 3 =
    {| final_state := 4;
       trace := [ArgumentEvent 3; ArgumentReturned 10; BodyRead 1; BodyRead 1];
       result := Returned 20 |}.
Proof. split; [eexists |]; reflexivity. Qed.

Example failure_stops_at_the_argument_effects :
  apply_natural_lambda (fun _ => 0) 1 (twice 1) failing_argument 3 =
    {| final_state := 4; trace := [ArgumentEvent 3]; result := Failed 9 |}.
Proof. reflexivity. Qed.

Definition sample_argument (name allowance : nat) (run : nat -> execution nat nat)
    : natural_argument nat nat :=
  {| parameter := (name, allowance); run_argument := run |}.

Example sequenced_zero_and_repeated_uses :
  (exists checked,
    infer [] (natural_telescope [(1, 0); (2, 2)] (twice 2)) = Some checked) /\
  evaluate_natural_sequence
    [sample_argument 1 0 incrementing_argument; sample_argument 2 2 incrementing_argument]
    (fun _ => 0) (twice 2) 3 =
    {| final_state := 5;
       trace := [ArgumentEvent 3; ArgumentReturned 10; ArgumentEvent 4; ArgumentReturned 11;
         BodyRead 2; BodyRead 2];
       result := Returned 22 |}.
Proof. split; [eexists |]; reflexivity. Qed.

Example sequenced_failure_keeps_prior_effects_and_skips_later_arguments :
  evaluate_natural_sequence
    [sample_argument 1 0 incrementing_argument; sample_argument 2 2 failing_argument;
      sample_argument 3 0 incrementing_argument]
    (fun _ => 0) (twice 2) 3 =
    {| final_state := 5;
       trace := [ArgumentEvent 3; ArgumentReturned 10; ArgumentEvent 4];
       result := Failed 9 |}.
Proof. reflexivity. Qed.

Example sequenced_telescope_rejects_wrong_exact_grade :
  infer [] (natural_telescope [(1, 0); (2, 1)] (twice 2)) = None.
Proof. reflexivity. Qed.

Example sequenced_bounds_admit_unused_and_repeated_values :
  let arguments :=
    [sample_argument 1 1 incrementing_argument; sample_argument 2 3 incrementing_argument] in
  let subject := natural_telescope (map parameter arguments) (twice 2) in
  (exists checked, infer_bounded [] subject = Some checked) /\
  infer [] subject = None /\
  evaluate_natural_sequence arguments (fun _ => 0) (twice 2) 3 =
    {| final_state := 5;
       trace := [ArgumentEvent 3; ArgumentReturned 10; ArgumentEvent 4; ArgumentReturned 11;
         BodyRead 2; BodyRead 2];
       result := Returned 22 |}.
Proof. cbn. split; [eexists | split]; reflexivity. Qed.

Example sequenced_bounds_reject_overuse :
  infer_bounded [] (natural_telescope [(1, 1); (2, 1)] (twice 2)) = None.
Proof. reflexivity. Qed.

End GradedCbv.
