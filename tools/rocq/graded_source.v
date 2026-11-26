(* SPDX-License-Identifier: Apache-2.0 *)
From Corelib Require Import Init.Datatypes.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Require Import graded_pure graded_domains.
Import ListNotations GradedPure.

Module GradedSource.

Fixpoint row_entries (env : context) (used : demand) : list nat :=
  match env with
  | [] => []
  | entry :: earlier =>
      let rest := row_entries earlier used in
      match uses used (binder entry) with
      | 0 => rest
      | count => binder entry :: count :: rest
      end
  end.

Fixpoint signature_demands (env : context) (kind : ty) : list (list nat) :=
  match kind with
  | Pi x allowance domain codomain =>
      match type_demand env domain with
      | Some row =>
          let extended := {| binder := x; annotation := domain; type_uses := row |} :: env in
          match type_demand extended codomain with
          | Some used =>
              (x :: allowance :: uses used x :: row_entries env row) ::
                signature_demands extended codomain
          | None => []
          end
      | None => []
      end
  | _ => match type_demand env kind with
         | Some used => [row_entries env used]
         | None => []
         end
  end.

Definition source_check_with (allowsb : nat -> nat -> bool) (subject : term) (expected : ty) : list (list nat) :=
  match check_with allowsb [] subject with
  | None => [[0]]
  | Some result =>
      match type_demand [] expected with
      | None => [[1]]
      | Some _ =>
          if ty_eq_dec (canonical_type [] (result_type result)) (canonical_type [] expected)
          then [2] :: signature_demands [] expected
          else [[1]]
      end
  end.

Definition accepted (summary : list (list nat)) : bool :=
  match summary with [2] :: _ => true | _ => false end.

Lemma source_check_with_sound : forall (allows : nat -> nat -> Prop) allowsb,
  (forall demand allowance, allowsb demand allowance = true -> allows demand allowance) ->
  forall subject expected,
    accepted (source_check_with allowsb subject expected) = true ->
    exists result row,
      DerivesWith allows [] subject result /\ TypeDemand [] expected row /\
      canonical_type [] (result_type result) = canonical_type [] expected.
Proof.
  intros allows allowsb admission_sound subject expected verified. unfold source_check_with in verified.
  destruct (check_with allowsb [] subject) as [result |] eqn:checked; try discriminate.
  destruct (type_demand [] expected) as [row |] eqn:typed; try discriminate.
  destruct (ty_eq_dec (canonical_type [] (result_type result)) (canonical_type [] expected))
    as [matches |]; try discriminate.
  unfold check_with in checked. cbn in checked.
  exists result, row. eauto using infer_with_sound, type_demand_sound.
Qed.

Definition source_check := source_check_with (@GradedDomains.allowsb GradedDomains.NatExact).
Definition bounded_source_check := source_check_with (@GradedDomains.allowsb GradedDomains.NatBound).

Theorem source_check_sound : forall subject expected,
  accepted (source_check subject expected) = true ->
  exists result row,
    Derives [] subject result /\ TypeDemand [] expected row /\
    canonical_type [] (result_type result) = canonical_type [] expected.
Proof.
  unfold source_check, Derives. apply source_check_with_sound.
  intros. now apply Nat.eqb_eq.
Qed.

Theorem bounded_source_check_sound : forall subject expected,
  accepted (bounded_source_check subject expected) = true ->
  exists result row,
    DerivesWith (@GradedDomains.allows GradedDomains.NatBound) [] subject result /\
    TypeDemand [] expected row /\
    canonical_type [] (result_type result) = canonical_type [] expected.
Proof.
  unfold bounded_source_check. apply source_check_with_sound.
  intros demand allowance admitted.
  destruct (GradedDomains.allows_reflect GradedDomains.NatBound demand allowance);
    [assumption | discriminate].
Qed.

End GradedSource.
