(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import Lists.List Arith.PeanoNat.
Require Import graded_pure graded_modal.
Import ListNotations GradedPure GradedModal.

Module GradedModalSource.

Record parameter := {
  name : nat;
  domain : kind;
  allowance : nat;
}.

Definition scope (parameters : list parameter) : env :=
  map (fun entry => (name entry, domain entry)) parameters.

Definition expected_computation (parameters : list parameter) (row : demand) : bool :=
  forallb (fun entry => Nat.eqb (uses row (name entry)) (allowance entry)) parameters.

Fixpoint row_entries (outer : env) (row : demand) : list nat :=
  match outer with
  | [] => []
  | (binder, _) :: earlier =>
      let rest := row_entries earlier row in
      match uses row binder with
      | 0 => rest
      | count => binder :: count :: rest
      end
  end.

Fixpoint signature_demands (parameters : list parameter) (trailing : demand) : list (list nat) :=
  match parameters with
  | [] => []
  | entry :: earlier =>
      match type_uses (scope earlier) (domain entry) with
      | Some annotation =>
          signature_demands earlier (annotation ++ trailing) ++
          [name entry :: allowance entry :: uses trailing (name entry) ::
            row_entries (scope earlier) annotation]
      | None => []
      end
  end.

Definition source_check (parameters : list parameter) (subject : value) (expected : kind)
    : list (list nat) :=
  let outer := scope parameters in
  match GradedModal.check outer subject with
  | None => [[0]]
  | Some result =>
      if expected_computation parameters (subject_uses result) then
        if kind_eq_dec (value_kind result) expected then
          match type_uses outer expected with
          | Some row => [2] :: signature_demands parameters row ++ [row_entries outer row]
          | None => [[1]]
          end
        else [[1]]
      else [[0]]
  end.

Definition accepted (summary : list (list nat)) : bool :=
  match summary with [2] :: _ => true | _ => false end.

Theorem source_check_sound : forall parameters subject expected,
  accepted (source_check parameters subject expected) = true ->
  exists result row,
    WellFormed (scope parameters) /\ GradedModal.Derives (scope parameters) subject result /\
    value_kind result = expected /\ TypeUses (scope parameters) expected row /\
    (forall entry, In entry parameters -> uses (subject_uses result) (name entry) = allowance entry).
Proof.
  intros parameters subject expected verified. unfold source_check in verified.
  destruct (GradedModal.check (scope parameters) subject) as [result |] eqn:checked; try discriminate.
  destruct (expected_computation parameters (subject_uses result)) eqn:computation; try discriminate.
  destruct (kind_eq_dec (value_kind result) expected) as [matches |]; try discriminate.
  destruct (type_uses (scope parameters) expected) as [row |] eqn:typed; try discriminate.
  apply GradedModal.check_sound in checked as [well_formed derivation].
  exists result, row. repeat split; auto using type_uses_sound.
  intros entry present. unfold expected_computation in computation.
  rewrite forallb_forall in computation. apply Nat.eqb_eq. now apply computation.
Qed.

End GradedModalSource.
