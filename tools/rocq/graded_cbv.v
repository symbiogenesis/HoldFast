(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat.
Require Import graded_pure.
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
  inversion accepted as [| | x q domain body' codomain a u v fresh typed derives exact_use |]; subst.
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

Definition apply_natural_lambda {State Event : Type} (values : nat -> nat)
    (binder : nat) (body : index) (argument : State -> execution State Event)
    (initial : State) : execution State (observation Event) :=
  let evaluated := argument initial in
  let effects := map ArgumentEvent (trace evaluated) in
  match result evaluated with
  | Failed reason =>
      {| final_state := final_state evaluated; trace := effects; result := Failed reason |}
  | Returned value =>
      let '(returned, reads) := evaluate_index (extend_values values binder value) body in
      {| final_state := final_state evaluated;
         trace := effects ++ ArgumentReturned value :: map BodyRead reads;
         result := Returned returned |}
  end.

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
  unfold apply_natural_lambda. rewrite evaluated. cbn.
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
  unfold apply_natural_lambda. now rewrite evaluated.
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

End GradedCbv.
