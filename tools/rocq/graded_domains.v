(* SPDX-License-Identifier: Apache-2.0 *)
From Corelib Require Import Init.Datatypes.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.
Require Import graded_pure.
Import ListNotations.

Module GradedDomains.

Record Domain := {
  grade : Type;
  zero : grade;
  one : grade;
  add : grade -> grade -> grade;
  mul : grade -> grade -> grade;
  allows : grade -> grade -> Prop;
  allowsb : grade -> grade -> bool;
  allows_reflect : forall demand allowance,
    reflect (allows demand allowance) (allowsb demand allowance);
  allows_refl : forall q, allows q q;
  allows_trans : forall a b c, allows a b -> allows b c -> allows a c;
  add_comm : forall a b, add a b = add b a;
  add_assoc : forall a b c, add a (add b c) = add (add a b) c;
  add_zero : forall a, add zero a = a;
  mul_comm : forall a b, mul a b = mul b a;
  mul_assoc : forall a b c, mul a (mul b c) = mul (mul a b) c;
  mul_one : forall a, mul one a = a;
  mul_zero : forall a, mul zero a = zero;
  mul_add : forall a b c, mul a (add b c) = add (mul a b) (mul a c);
  add_monotone : forall a b c d, allows a b -> allows c d -> allows (add a c) (add b d);
  mul_monotone : forall a b c d, allows a b -> allows c d -> allows (mul a c) (mul b d)
}.

Arguments grade _ : clear implicits.
Arguments zero {_}.
Arguments one {_}.
Arguments add {_} _ _.
Arguments mul {_} _ _.
Arguments allows {_} _ _.
Arguments allowsb {_} _ _.

Definition NatExact : Domain.
Proof.
  refine {| grade := nat; zero := 0; one := 1; add := Nat.add; mul := Nat.mul;
            allows := @eq nat; allowsb := Nat.eqb;
            add_comm := Nat.add_comm; add_assoc := Nat.add_assoc; add_zero := Nat.add_0_l;
            mul_comm := Nat.mul_comm; mul_assoc := Nat.mul_assoc; mul_one := Nat.mul_1_l;
            mul_zero := Nat.mul_0_l; mul_add := Nat.mul_add_distr_l |}.
  - exact Nat.eqb_spec.
  - intros. reflexivity.
  - intros a b c -> ->. reflexivity.
  - intros a b c d -> ->. reflexivity.
  - intros a b c d -> ->. reflexivity.
Defined.

Definition NatBound : Domain.
Proof.
  refine {| grade := nat; zero := 0; one := 1; add := Nat.add; mul := Nat.mul;
            allows := le; allowsb := Nat.leb;
            allows_refl := Nat.le_refl; allows_trans := Nat.le_trans;
            add_comm := Nat.add_comm; add_assoc := Nat.add_assoc; add_zero := Nat.add_0_l;
            mul_comm := Nat.mul_comm; mul_assoc := Nat.mul_assoc; mul_one := Nat.mul_1_l;
            mul_zero := Nat.mul_0_l; mul_add := Nat.mul_add_distr_l;
            add_monotone := Nat.add_le_mono; mul_monotone := Nat.mul_le_mono |}.
  intros a b. apply iff_reflect. symmetry. apply Nat.leb_le.
Defined.

Definition presence_le (demand allowance : bool) : Prop :=
  demand = true -> allowance = true.

Definition Presence : Domain.
Proof.
  refine {| grade := bool; zero := false; one := true; add := orb; mul := andb;
            allows := presence_le; allowsb := implb |};
    unfold presence_le; intros; repeat match goal with
    | b : bool |- _ => destruct b
    end; cbn in *; try (solve [intuition discriminate]);
    constructor; intuition discriminate.
Defined.

Record DomainMap (A B : Domain) := {
  translate : grade A -> grade B;
  translate_zero : translate zero = zero;
  translate_one : translate one = one;
  translate_add : forall a b, translate (add a b) = add (translate a) (translate b);
  translate_mul : forall a b, translate (mul a b) = mul (translate a) (translate b);
  translate_allows : forall a b, allows a b -> allows (translate a) (translate b)
}.

Arguments translate {_ _} _ _.

Definition exact_to_bound : DomainMap NatExact NatBound.
Proof.
  refine (@Build_DomainMap NatExact NatBound (fun q => q) _ _ _ _ _);
    cbn; try reflexivity.
  intros a b ->. apply Nat.le_refl.
Defined.

Definition bound_to_presence : DomainMap NatBound Presence.
Proof.
  refine (@Build_DomainMap NatBound Presence (fun q => negb (Nat.eqb q 0)) _ _ _ _ _);
    cbn; try reflexivity.
  - intros [|a] [|b]; reflexivity.
  - intros [|a] [|b]; cbn; try reflexivity.
    rewrite Nat.mul_0_r. reflexivity.
  - intros [|a] [|b] ordered present; try discriminate; try reflexivity.
    inversion ordered.
Defined.

Definition Row (D : Domain) := nat -> grade D.

Definition apply_row {D} (weight : grade D) (ambient argument : Row D) : Row D :=
  fun i => add (ambient i) (mul weight (argument i)).

Record Demands (D : Domain) := {
  computation : Row D;
  type_use : Row D;
  dependencies : list (Row D)
}.

Arguments computation {_} _ _.
Arguments type_use {_} _ _.
Arguments dependencies {_} _.

Definition substitute_row {D} (binder : nat) (argument row : Row D) : Row D :=
  fun i => if Nat.eqb binder i then zero else apply_row (row binder) row argument i.

(* The caller supplies only the declaration rows after the substituted binder.
   See [substitution and structural rules](../../docs/extensions/graded-foundation.md#substitution-and-structural-rules). *)
Definition substitute {D} (binder : nat) (argument : Row D) (used : Demands D) : Demands D :=
  {| computation := substitute_row binder argument (computation used);
     type_use := substitute_row binder argument (type_use used);
     dependencies := map (substitute_row binder argument) (dependencies used) |}.

Theorem substitution_commutes_with_translation :
  forall A B (m : DomainMap A B) binder argument row i,
    translate m (substitute_row binder argument row i) =
    substitute_row binder (fun j => translate m (argument j)) (fun j => translate m (row j)) i.
Proof.
  intros. unfold substitute_row, apply_row.
  destruct (Nat.eqb binder i).
  - apply translate_zero.
  - now rewrite translate_add, translate_mul.
Qed.

Theorem exact_substitution_agrees_with_pure :
  forall binder argument row i,
    GradedPure.uses argument binder = 0 ->
    substitute_row (D := NatExact) binder (GradedPure.uses argument) (GradedPure.uses row) i =
    GradedPure.uses (GradedPure.substitute_demand binder argument row) i.
Proof.
  intros binder argument row i fresh. unfold substitute_row, apply_row, GradedPure.substitute_demand.
  rewrite GradedPure.uses_append, GradedPure.uses_without.
  assert (scaled : forall weight entries,
      GradedPure.uses (GradedPure.scale weight entries) i =
      weight * GradedPure.uses entries i).
  { intros weight entries. induction entries as [|[name count] rest IH].
    - cbn. now rewrite Nat.mul_0_r.
    - change ((if Nat.eqb i name then weight * count else 0) +
        GradedPure.uses (GradedPure.scale weight rest) i =
        weight * ((if Nat.eqb i name then count else 0) + GradedPure.uses rest i)).
      rewrite IH, Nat.mul_add_distr_l.
      destruct (Nat.eqb i name); simpl; try rewrite Nat.mul_0_r; reflexivity. }
  rewrite scaled, (Nat.eqb_sym i binder).
  destruct (Nat.eqb binder i) eqn:removed; cbn.
  - apply Nat.eqb_eq in removed. subst i. now rewrite fresh, Nat.mul_0_r.
  - reflexivity.
Qed.

Fixpoint check_row {D} (actual allowance : list (grade D)) : bool :=
  match actual, allowance with
  | [], [] => true
  | a :: actual', b :: allowance' => @allowsb D a b && check_row actual' allowance'
  | _, _ => false
  end.

Theorem check_row_spec : forall D actual allowance,
  check_row (D := D) actual allowance = true <-> Forall2 (@allows D) actual allowance.
Proof.
  intros D actual. induction actual as [|a actual IH]; intros [|b allowance]; cbn.
  - split; constructor.
  - split; discriminate || inversion 1.
  - split; discriminate || inversion 1.
  - rewrite andb_true_iff, IH.
    destruct (allows_reflect D a b); split; intros evidence; try discriminate.
    + constructor; tauto.
    + inversion evidence. tauto.
    + destruct evidence as [contradiction _]. discriminate.
    + inversion evidence. contradiction.
Qed.

Definition materialize {D} (width : nat) (row : Row D) : list (grade D) :=
  map row (seq 0 width).

Definition materialize_demands {D} (width : nat) (used : Demands D) : list (list (grade D)) :=
  map (materialize width) (computation used :: type_use used :: dependencies used).

Fixpoint check_rows {D} (actual allowance : list (list (grade D))) : bool :=
  match actual, allowance with
  | [], [] => true
  | a :: actual', b :: allowance' => check_row (D := D) a b && check_rows actual' allowance'
  | _, _ => false
  end.

Theorem check_rows_spec : forall D actual allowance,
  check_rows (D := D) actual allowance = true <->
  Forall2 (Forall2 (@allows D)) actual allowance.
Proof.
  intros D actual. induction actual as [|a actual IH]; intros [|b allowance]; cbn.
  - split; constructor.
  - split; discriminate || inversion 1.
  - split; discriminate || inversion 1.
  - rewrite andb_true_iff, check_row_spec, IH.
    split; intros evidence.
    + constructor; tauto.
    + inversion evidence. tauto.
Qed.

Definition client_demands {D} (count : grade D) : Demands D :=
  {| computation := fun _ => zero;
     type_use := fun i => if Nat.eqb i 1 then one else zero;
     dependencies := [fun i => if Nat.eqb i 1 then count else zero] |}.

Definition client_argument {D} : Row D :=
  fun i => if Nat.eqb i 0 then add one one else zero.

Definition client_rows {D} : list (list (grade D)) :=
  materialize_demands 2 (substitute 1 client_argument (client_demands (D := D) (add one one))).

Example exact_reconstructs_containing_telescope :
  check_rows (D := NatExact) client_rows [[0; 0]; [2; 0]; [4; 0]] = true.
Proof. reflexivity. Qed.

Example exact_rejects_relaxation :
  check_rows (D := NatExact) client_rows [[1; 0]; [2; 0]; [4; 0]] = false.
Proof. reflexivity. Qed.

Example bound_accepts_relaxation :
  check_rows (D := NatBound) client_rows [[1; 0]; [2; 0]; [4; 0]] = true.
Proof. reflexivity. Qed.

Example exact_rejects_stale_dependency :
  check_rows (D := NatExact) client_rows [[0; 0]; [2; 0]; [0; 2]] = false.
Proof. reflexivity. Qed.

Example bound_rejects_stale_dependency :
  check_rows (D := NatBound) client_rows [[0; 0]; [2; 0]; [0; 2]] = false.
Proof. reflexivity. Qed.

Example presence_reconstructs_dependency :
  check_rows (D := Presence) client_rows [[false; false]; [true; false]; [true; false]] = true.
Proof. reflexivity. Qed.

Theorem presence_cannot_recover_counts :
  forall recover : grade Presence -> grade NatExact,
    recover (translate bound_to_presence 1) <> 1 \/
    recover (translate bound_to_presence 2) <> 2.
Proof.
  intros recover. cbn. destruct (Nat.eq_dec (recover true) 1) as [-> | different].
  - right. discriminate.
  - now left.
Qed.

End GradedDomains.
