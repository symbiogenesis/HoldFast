(* SPDX-License-Identifier: Apache-2.0 *)
From Corelib Require Import Init.Datatypes.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
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

(* Supply the term and result-type demands and the dependency rows for later declarations.
   The caller retains earlier rows and drops the replaced declaration's row.
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

(* ================================================================= *)
(* JoinDomain Extension, Additional Domains, and Symbolic GradeExpr  *)
(* ================================================================= *)

Record JoinDomain := {
  base_domain :> Domain;
  grade_eq_dec : forall a b : grade base_domain, {a = b} + {a <> b};
  grade_join : option (grade base_domain -> grade base_domain -> grade base_domain);
  join_left : forall j, grade_join = Some j -> forall a b, allows a (j a b);
  join_right : forall j, grade_join = Some j -> forall a b, allows b (j a b);
  join_least : forall j, grade_join = Some j -> forall a b c,
    allows a c -> allows b c -> allows (j a b) c
}.

Definition grade_eqb {D : JoinDomain} (a b : grade D) : bool :=
  if grade_eq_dec D a b then true else false.

Lemma grade_eqb_spec : forall (D : JoinDomain) (a b : grade D),
  reflect (a = b) (grade_eqb a b).
Proof.
  intros D a b. unfold grade_eqb.
  destruct (grade_eq_dec D a b); constructor; assumption.
Qed.

Definition NatExactJoin : JoinDomain.
Proof.
  refine {| base_domain := NatExact;
            grade_eq_dec := Nat.eq_dec;
            grade_join := None |};
    intros j Hj; discriminate.
Defined.

Definition NatBoundJoin : JoinDomain.
Proof.
  refine {| base_domain := NatBound;
            grade_eq_dec := Nat.eq_dec;
            grade_join := Some Nat.max |};
    intros j Hj; inversion Hj; subst; intros; cbn in *.
  - apply Nat.le_max_l.
  - apply Nat.le_max_r.
  - apply Nat.max_lub; assumption.
Defined.

Definition PresenceJoin : JoinDomain.
Proof.
  refine {| base_domain := Presence;
            grade_eq_dec := bool_dec;
            grade_join := Some orb |};
    intros j Hj; inversion Hj; subst; unfold presence_le; cbn.
  - intros [] [] ?; try reflexivity; discriminate.
  - intros [] [] ?; try reflexivity; discriminate.
  - intros [] [] [] Ha Hb ?; try reflexivity; auto.
Defined.

(* Exact linear domain {LZero, LOne, LMany}:
   no contraction of 1 + 1 into 1, and no weakening 0 <= 1. *)
Inductive lin_grade : Type :=
| LZero
| LOne
| LMany.

Definition lin_grade_eq_dec : forall a b : lin_grade, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition lin_eqb (a b : lin_grade) : bool :=
  match a, b with
  | LZero, LZero | LOne, LOne | LMany, LMany => true
  | _, _ => false
  end.

Definition lin_add (a b : lin_grade) : lin_grade :=
  match a, b with
  | LZero, x | x, LZero => x
  | _, _ => LMany
  end.

Definition lin_mul (a b : lin_grade) : lin_grade :=
  match a, b with
  | LZero, _ | _, LZero => LZero
  | LOne, x | x, LOne => x
  | LMany, LMany => LMany
  end.

Definition LinearBase : Domain.
Proof.
  refine {| grade := lin_grade; zero := LZero; one := LOne;
            add := lin_add; mul := lin_mul;
            allows := @eq lin_grade; allowsb := lin_eqb |}.
  - intros [] []; constructor; congruence.
  - intros; reflexivity.
  - intros a b c -> ->; reflexivity.
  - intros [] []; reflexivity.
  - intros [] [] []; reflexivity.
  - intros []; reflexivity.
  - intros [] []; reflexivity.
  - intros [] [] []; reflexivity.
  - intros []; reflexivity.
  - intros []; reflexivity.
  - intros [] [] []; reflexivity.
  - intros ? ? ? ? -> ->; reflexivity.
  - intros ? ? ? ? -> ->; reflexivity.
Defined.

Definition LinearDomain : JoinDomain.
Proof.
  refine {| base_domain := LinearBase;
            grade_eq_dec := lin_grade_eq_dec;
            grade_join := None |};
    intros j Hj; discriminate.
Defined.

Lemma linear_no_contraction :
  @add LinearDomain one one = LMany /\
  ~ @allows LinearDomain (add one one) one.
Proof.
  split; [reflexivity | discriminate].
Qed.

Lemma linear_no_weakening :
  ~ @allows LinearDomain zero one.
Proof. discriminate. Qed.

(* Affine domain {AZero, AOne, AMany} with 0 <= 1 <= many and join = max. *)
Inductive aff_grade : Type :=
| AZero
| AOne
| AMany.

Definition aff_grade_eq_dec : forall a b : aff_grade, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition aff_add (a b : aff_grade) : aff_grade :=
  match a, b with
  | AZero, x | x, AZero => x
  | _, _ => AMany
  end.

Definition aff_mul (a b : aff_grade) : aff_grade :=
  match a, b with
  | AZero, _ | _, AZero => AZero
  | AOne, x | x, AOne => x
  | AMany, AMany => AMany
  end.

Definition aff_le (a b : aff_grade) : Prop :=
  match a, b with
  | AZero, _ => True
  | AOne, AOne | AOne, AMany => True
  | AMany, AMany => True
  | _, _ => False
  end.

Definition aff_leb (a b : aff_grade) : bool :=
  match a, b with
  | AZero, _ => true
  | AOne, AOne | AOne, AMany => true
  | AMany, AMany => true
  | _, _ => false
  end.

Definition aff_max (a b : aff_grade) : aff_grade :=
  match a, b with
  | AMany, _ | _, AMany => AMany
  | AOne, _ | _, AOne => AOne
  | AZero, AZero => AZero
  end.

Definition AffineBase : Domain.
Proof.
  refine {| grade := aff_grade; zero := AZero; one := AOne;
            add := aff_add; mul := aff_mul;
            allows := aff_le; allowsb := aff_leb |};
    intros; repeat match goal with x : aff_grade |- _ => destruct x end;
    cbn in *; try constructor; try contradiction; try discriminate; try reflexivity;
    auto.
Defined.

Definition AffineDomain : JoinDomain.
Proof.
  refine {| base_domain := AffineBase;
            grade_eq_dec := aff_grade_eq_dec;
            grade_join := Some aff_max |};
    intros j Hj; inversion Hj; subst; cbn.
  - intros [] []; exact I.
  - intros [] []; exact I.
  - intros [] [] [] Ha Hb; cbn in *; try exact I; assumption.
Defined.

Lemma affine_allows_weakening :
  @allows AffineDomain zero one /\
  ~ @allows AffineDomain (add one one) one /\
  @allows AffineDomain one AMany.
Proof.
  cbn. intuition.
Qed.

(* Security lattice {Lo, Hi} with Lo <= Hi, Lo + Hi = Hi, zero = Lo, one = Hi. *)
Inductive sec_grade : Type :=
| Lo
| Hi.

Definition sec_grade_eq_dec : forall a b : sec_grade, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition sec_add (a b : sec_grade) : sec_grade :=
  match a, b with
  | Lo, Lo => Lo
  | _, _ => Hi
  end.

Definition sec_mul (a b : sec_grade) : sec_grade :=
  match a, b with
  | Hi, Hi => Hi
  | _, _ => Lo
  end.

Definition sec_le (a b : sec_grade) : Prop :=
  a = Hi -> b = Hi.

Definition sec_leb (a b : sec_grade) : bool :=
  match a, b with
  | Hi, Lo => false
  | _, _ => true
  end.

Definition SecurityBase : Domain.
Proof.
  refine {| grade := sec_grade; zero := Lo; one := Hi;
            add := sec_add; mul := sec_mul;
            allows := sec_le; allowsb := sec_leb |};
    unfold sec_le; intros;
    repeat match goal with x : sec_grade |- _ => destruct x end;
    cbn in *; try constructor; try discriminate; try reflexivity;
    intuition discriminate.
Defined.

Definition SecurityLoHi : JoinDomain.
Proof.
  refine {| base_domain := SecurityBase;
            grade_eq_dec := sec_grade_eq_dec;
            grade_join := Some sec_add |};
    intros j Hj; inversion Hj; subst; unfold sec_le; cbn.
  - intros [] [] ?; try reflexivity; discriminate.
  - intros [] [] ?; try reflexivity; discriminate.
  - intros [] [] [] Ha Hb ?; try reflexivity; auto.
Defined.

Lemma security_lattice_laws :
  @allows SecurityLoHi Lo Hi /\
  ~ @allows SecurityLoHi Hi Lo /\
  @add SecurityLoHi Lo Hi = Hi.
Proof.
  cbn. unfold sec_le. split; [intros _; reflexivity | split; [intro H; discriminate (H eq_refl) | reflexivity]].
Qed.

Record JoinDomainMap (A B : JoinDomain) := {
  jmap_base :> DomainMap A B;
  jmap_join_compat : forall jA, grade_join A = Some jA ->
    exists jB, grade_join B = Some jB /\
      forall a b, translate jmap_base (jA a b) = jB (translate jmap_base a) (translate jmap_base b)
}.

Definition exact_to_bound_join : JoinDomainMap NatExactJoin NatBoundJoin.
Proof.
  refine (@Build_JoinDomainMap NatExactJoin NatBoundJoin exact_to_bound _).
  intros jA Hj. discriminate.
Defined.

Definition bound_to_presence_join : JoinDomainMap NatBoundJoin PresenceJoin.
Proof.
  refine (@Build_JoinDomainMap NatBoundJoin PresenceJoin bound_to_presence _).
  intros jA Hj. inversion Hj; subst.
  exists orb. split; [reflexivity |].
  intros [| a] [| b]; reflexivity.
Defined.

Definition linear_to_affine_fn (q : lin_grade) : aff_grade :=
  match q with LZero => AZero | LOne => AOne | LMany => AMany end.

Definition linear_to_affine_base : DomainMap LinearBase AffineBase.
Proof.
  refine (@Build_DomainMap LinearBase AffineBase linear_to_affine_fn _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - intros [] []; reflexivity.
  - intros [] []; reflexivity.
  - intros [] [] H; inversion H; subst; cbn; exact I.
Defined.

Definition linear_to_affine_join : JoinDomainMap LinearDomain AffineDomain.
Proof.
  refine (@Build_JoinDomainMap LinearDomain AffineDomain linear_to_affine_base _).
  intros jA Hj. discriminate.
Defined.

(* Symbolic Grade Expressions and Normalization over Arbitrary Domains *)

Inductive GradeExpr (D : Domain) : Type :=
| GLit (q : grade D)
| GVar (x : nat)
| GAdd (e1 e2 : GradeExpr D)
| GMul (e1 e2 : GradeExpr D).

Arguments GLit {D} q.
Arguments GVar {D} x.
Arguments GAdd {D} e1 e2.
Arguments GMul {D} e1 e2.

Fixpoint eval_gexpr {D : Domain} (rho : nat -> grade D) (e : GradeExpr D) : grade D :=
  match e with
  | GLit q => q
  | GVar x => rho x
  | GAdd e1 e2 => add (eval_gexpr rho e1) (eval_gexpr rho e2)
  | GMul e1 e2 => mul (eval_gexpr rho e1) (eval_gexpr rho e2)
  end.

Definition gexpr_eq {D : Domain} (e1 e2 : GradeExpr D) : Prop :=
  forall rho, eval_gexpr rho e1 = eval_gexpr rho e2.

Definition gexpr_allows {D : Domain} (e1 e2 : GradeExpr D) : Prop :=
  forall rho, allows (eval_gexpr rho e1) (eval_gexpr rho e2).

Definition gvars := list nat.

Fixpoint eval_gvars {D : Domain} (rho : nat -> grade D) (vs : gvars) : grade D :=
  match vs with
  | [] => one
  | x :: rest => mul (rho x) (eval_gvars rho rest)
  end.

Fixpoint insert_gvar (x : nat) (xs : gvars) : gvars :=
  match xs with
  | [] => [x]
  | y :: rest => if Nat.leb x y then x :: xs else y :: insert_gvar x rest
  end.

Lemma eval_gvars_insert : forall (D : Domain) rho x xs,
  eval_gvars (D := D) rho (insert_gvar x xs) = mul (rho x) (eval_gvars rho xs).
Proof.
  intros D rho x xs. induction xs as [| y rest IH]; cbn.
  - reflexivity.
  - destruct (Nat.leb x y); cbn; [reflexivity |].
    rewrite IH, mul_assoc, (mul_comm D (rho y) (rho x)), <- mul_assoc. reflexivity.
Qed.

Fixpoint mul_gvars (xs ys : gvars) : gvars :=
  match xs with
  | [] => ys
  | x :: rest => insert_gvar x (mul_gvars rest ys)
  end.

Lemma eval_gvars_mul : forall (D : Domain) rho xs ys,
  eval_gvars (D := D) rho (mul_gvars xs ys) = mul (eval_gvars rho xs) (eval_gvars rho ys).
Proof.
  intros D rho xs ys. induction xs as [| x rest IH]; cbn.
  - symmetry. apply mul_one.
  - rewrite eval_gvars_insert, IH, <- mul_assoc. reflexivity.
Qed.

Fixpoint gvars_cmp (xs ys : gvars) : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: xs', y :: ys' =>
      match Nat.compare x y with
      | Lt => Lt
      | Gt => Gt
      | Eq => gvars_cmp xs' ys'
      end
  end.

Lemma gvars_cmp_eq : forall xs ys,
  gvars_cmp xs ys = Eq -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; destruct ys as [| y ys']; cbn; intro H; try discriminate.
  - reflexivity.
  - destruct (Nat.compare x y) eqn:Ec; try discriminate.
    apply Nat.compare_eq in Ec. subst y. f_equal. apply IH; exact H.
Qed.

Definition gpoly (D : Domain) := list (grade D * gvars).

Fixpoint eval_gpoly {D : Domain} (rho : nat -> grade D) (p : gpoly D) : grade D :=
  match p with
  | [] => zero
  | (c, vs) :: rest => add (mul c (eval_gvars rho vs)) (eval_gpoly rho rest)
  end.

Lemma mul_add_r : forall (D : Domain) (a b c : grade D),
  mul (add a b) c = add (mul a c) (mul b c).
Proof.
  intros D a b c. rewrite mul_comm, mul_add, (mul_comm D c a), (mul_comm D c b). reflexivity.
Qed.

Lemma add_zero_r : forall (D : Domain) (a : grade D),
  add a zero = a.
Proof.
  intros D a. rewrite add_comm. apply add_zero.
Qed.

Lemma mul_zero_r : forall (D : Domain) (a : grade D),
  mul a zero = zero.
Proof.
  intros D a. rewrite mul_comm. apply mul_zero.
Qed.

Lemma mul_one_r : forall (D : Domain) (a : grade D),
  mul a one = a.
Proof.
  intros D a. rewrite mul_comm. apply mul_one.
Qed.

Fixpoint insert_gterm {D : Domain} (c : grade D) (vs : gvars) (p : gpoly D) : gpoly D :=
  match p with
  | [] => [(c, vs)]
  | (c', vs') :: rest =>
      match gvars_cmp vs vs' with
      | Lt => (c, vs) :: p
      | Eq => (add c c', vs') :: rest
      | Gt => (c', vs') :: insert_gterm c vs rest
      end
  end.

Lemma eval_gpoly_insert_term : forall (D : Domain) rho c vs (p : gpoly D),
  eval_gpoly rho (insert_gterm c vs p) = add (mul c (eval_gvars rho vs)) (eval_gpoly rho p).
Proof.
  intros D rho c vs p. induction p as [| [c' vs'] rest IH]; cbn.
  - reflexivity.
  - destruct (gvars_cmp vs vs') eqn:Hcmp; cbn.
    + apply gvars_cmp_eq in Hcmp. subst vs'.
      rewrite mul_add_r, <- add_assoc. reflexivity.
    + reflexivity.
    + rewrite IH, add_assoc,
              (add_comm D (mul c' (eval_gvars rho vs')) (mul c (eval_gvars rho vs))),
              <- add_assoc.
      reflexivity.
Qed.

Fixpoint add_gpoly {D : Domain} (p1 p2 : gpoly D) : gpoly D :=
  match p1 with
  | [] => p2
  | (c, vs) :: rest => insert_gterm c vs (add_gpoly rest p2)
  end.

Lemma eval_gpoly_add : forall (D : Domain) rho (p1 p2 : gpoly D),
  eval_gpoly rho (add_gpoly p1 p2) = add (eval_gpoly rho p1) (eval_gpoly rho p2).
Proof.
  intros D rho p1 p2. induction p1 as [| [c vs] rest IH]; cbn.
  - symmetry. apply add_zero.
  - rewrite eval_gpoly_insert_term, IH, <- add_assoc. reflexivity.
Qed.

Fixpoint scale_gterm {D : Domain} (c : grade D) (vs : gvars) (p : gpoly D) : gpoly D :=
  match p with
  | [] => []
  | (c', vs') :: rest =>
      insert_gterm (mul c c') (mul_gvars vs vs') (scale_gterm c vs rest)
  end.

Lemma eval_gpoly_scale_term : forall (D : Domain) rho c vs (p : gpoly D),
  eval_gpoly rho (scale_gterm c vs p) = mul (mul c (eval_gvars rho vs)) (eval_gpoly rho p).
Proof.
  intros D rho c vs p. induction p as [| [c' vs'] rest IH]; cbn.
  - symmetry. apply mul_zero_r.
  - rewrite eval_gpoly_insert_term, eval_gvars_mul, IH, mul_add.
    f_equal.
    rewrite <- !mul_assoc. f_equal.
    rewrite !mul_assoc, (mul_comm D c' (eval_gvars rho vs)), <- !mul_assoc. reflexivity.
Qed.

Fixpoint mul_gpoly {D : Domain} (p1 p2 : gpoly D) : gpoly D :=
  match p1 with
  | [] => []
  | (c, vs) :: rest => add_gpoly (scale_gterm c vs p2) (mul_gpoly rest p2)
  end.

Lemma eval_gpoly_mul : forall (D : Domain) rho (p1 p2 : gpoly D),
  eval_gpoly rho (mul_gpoly p1 p2) = mul (eval_gpoly rho p1) (eval_gpoly rho p2).
Proof.
  intros D rho p1 p2. induction p1 as [| [c vs] rest IH]; cbn.
  - symmetry. apply mul_zero.
  - rewrite eval_gpoly_add, eval_gpoly_scale_term, IH, mul_add_r. reflexivity.
Qed.

Fixpoint normalize_gexpr {D : Domain} (e : GradeExpr D) : gpoly D :=
  match e with
  | GLit q => [(q, [])]
  | GVar x => [(one, [x])]
  | GAdd e1 e2 => add_gpoly (normalize_gexpr e1) (normalize_gexpr e2)
  | GMul e1 e2 => mul_gpoly (normalize_gexpr e1) (normalize_gexpr e2)
  end.

Theorem normalize_gexpr_sound : forall (D : Domain) rho (e : GradeExpr D),
  eval_gpoly rho (normalize_gexpr e) = eval_gexpr rho e.
Proof.
  intros D rho e. induction e; cbn.
  - rewrite mul_one_r, add_zero_r. reflexivity.
  - rewrite !mul_one_r, mul_one, add_zero_r. reflexivity.
  - rewrite eval_gpoly_add, IHe1, IHe2. reflexivity.
  - rewrite eval_gpoly_mul, IHe1, IHe2. reflexivity.
Qed.

Fixpoint gpoly_allowsb_empty {D : Domain} (p2 : gpoly D) : bool :=
  match p2 with
  | [] => true
  | (c2, _) :: r2 => allowsb zero c2 && gpoly_allowsb_empty r2
  end.

Fixpoint gpoly_allowsb {D : Domain} (p1 p2 : gpoly D) : bool :=
  match p1 with
  | [] => gpoly_allowsb_empty p2
  | (c1, vs1) :: r1 =>
      (fix step_right (p2 : gpoly D) : bool :=
        match p2 with
        | [] => allowsb c1 zero && gpoly_allowsb r1 []
        | (c2, vs2) :: r2 =>
            match gvars_cmp vs1 vs2 with
            | Eq => allowsb c1 c2 && gpoly_allowsb r1 r2
            | Lt => allowsb c1 zero && gpoly_allowsb r1 p2
            | Gt => allowsb zero c2 && step_right r2
            end
        end) p2
  end.

Lemma allows_zero_gpoly_right : forall (D : Domain) (p : gpoly D),
  gpoly_allowsb_empty p = true ->
  forall rho, allows zero (eval_gpoly rho p).
Proof.
  intros D p. induction p as [| [c vs] rest IH]; intros H rho; cbn in *.
  - apply allows_refl.
  - apply andb_true_iff in H as [Hc Hr].
    destruct (allows_reflect D zero c); [| discriminate].
    rewrite <- (add_zero D zero).
    apply add_monotone; [| apply IH; exact Hr].
    rewrite <- (mul_zero D (eval_gvars rho vs)).
    apply mul_monotone; [assumption | apply allows_refl].
Qed.

Lemma allows_gpoly_zero_left : forall (D : Domain) (p : gpoly D),
  gpoly_allowsb p [] = true ->
  forall rho, allows (eval_gpoly rho p) zero.
Proof.
  intros D p. induction p as [| [c vs] rest IH]; intros H rho; cbn in *.
  - apply allows_refl.
  - apply andb_true_iff in H as [Hc Hr].
    destruct (allows_reflect D c zero); [| discriminate].
    rewrite <- (add_zero D zero).
    apply add_monotone; [| apply IH; exact Hr].
    rewrite <- (mul_zero D (eval_gvars rho vs)).
    apply mul_monotone; [assumption | apply allows_refl].
Qed.

Lemma gpoly_allows_sound : forall (D : Domain) (p1 p2 : gpoly D),
  gpoly_allowsb p1 p2 = true ->
  forall rho, allows (eval_gpoly rho p1) (eval_gpoly rho p2).
Proof.
  intros D p1. induction p1 as [| [c1 vs1] r1 IH1]; intros p2 H rho.
  - apply allows_zero_gpoly_right; exact H.
  - revert H. induction p2 as [| [c2 vs2] r2 IH2]; intros H.
    + apply allows_gpoly_zero_left; exact H.
    + change (
        match gvars_cmp vs1 vs2 with
        | Eq => allowsb c1 c2 && gpoly_allowsb r1 r2
        | Lt => allowsb c1 zero && gpoly_allowsb r1 ((c2, vs2) :: r2)
        | Gt => allowsb zero c2 && gpoly_allowsb ((c1, vs1) :: r1) r2
        end = true) in H.
      destruct (gvars_cmp vs1 vs2) eqn:Hcmp.
      * apply gvars_cmp_eq in Hcmp. subst vs1.
        apply andb_true_iff in H as [Hc Hr].
        destruct (allows_reflect D c1 c2); [| discriminate].
        cbn. apply add_monotone; [| apply IH1; exact Hr].
        apply mul_monotone; [assumption | apply allows_refl].
      * apply andb_true_iff in H as [Hc Hr].
        destruct (allows_reflect D c1 zero); [| discriminate].
        cbn [eval_gpoly].
        rewrite <- (add_zero D (add (mul c2 (eval_gvars rho vs2)) (eval_gpoly rho r2))).
        apply add_monotone; [| exact (IH1 ((c2, vs2) :: r2) Hr rho)].
        rewrite <- (mul_zero D (eval_gvars rho vs1)).
        apply mul_monotone; [assumption | apply allows_refl].
      * apply andb_true_iff in H as [Hc Hr].
        destruct (allows_reflect D zero c2); [| discriminate].
        cbn [eval_gpoly].
        rewrite <- (add_zero D (add (mul c1 (eval_gvars rho vs1)) (eval_gpoly rho r1))).
        apply add_monotone; [| exact (IH2 Hr)].
        rewrite <- (mul_zero D (eval_gvars rho vs2)).
        apply mul_monotone; [assumption | apply allows_refl].
Qed.

Definition gexpr_allowsb {D : Domain} (e1 e2 : GradeExpr D) : bool :=
  gpoly_allowsb (normalize_gexpr e1) (normalize_gexpr e2).

Theorem gexpr_allows_sound : forall (D : Domain) (e1 e2 : GradeExpr D),
  gexpr_allowsb e1 e2 = true -> gexpr_allows e1 e2.
Proof.
  intros D e1 e2 H rho. unfold gexpr_allowsb in H.
  rewrite <- !normalize_gexpr_sound. apply gpoly_allows_sound; exact H.
Qed.

Fixpoint gvars_eqb (xs ys : gvars) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && gvars_eqb xs' ys'
  | _, _ => false
  end.

Lemma gvars_eqb_sound : forall xs ys, gvars_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; destruct ys as [| y ys']; cbn; intro H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [Hxy Hrest]. apply Nat.eqb_eq in Hxy. subst y.
    f_equal. apply IH; exact Hrest.
Qed.

Fixpoint gpoly_eqb {D : JoinDomain} (p1 p2 : gpoly D) : bool :=
  match p1, p2 with
  | [], [] => true
  | (c1, vs1) :: r1, (c2, vs2) :: r2 =>
      grade_eqb c1 c2 && gvars_eqb vs1 vs2 && gpoly_eqb r1 r2
  | _, _ => false
  end.

Lemma gpoly_eqb_sound : forall (D : JoinDomain) (p1 p2 : gpoly D),
  gpoly_eqb p1 p2 = true -> p1 = p2.
Proof.
  intros D p1. induction p1 as [| [c1 vs1] r1 IH]; destruct p2 as [| [c2 vs2] r2];
    cbn; intro H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [Hhead Hrest].
    apply andb_true_iff in Hhead as [Hc Hvs].
    destruct (grade_eqb_spec D c1 c2); [| discriminate].
    apply gvars_eqb_sound in Hvs. subst.
    f_equal. apply IH; exact Hrest.
Qed.

Definition gexpr_eqb {D : JoinDomain} (e1 e2 : GradeExpr D) : bool :=
  gpoly_eqb (normalize_gexpr e1) (normalize_gexpr e2).

Theorem gexpr_eqb_sound : forall (D : JoinDomain) (e1 e2 : GradeExpr D),
  gexpr_eqb e1 e2 = true -> gexpr_eq e1 e2.
Proof.
  intros D e1 e2 H rho. unfold gexpr_eqb in H.
  apply gpoly_eqb_sound in H.
  rewrite <- !normalize_gexpr_sound, H. reflexivity.
Qed.

Theorem gexpr_semiring_laws :
  forall (D : Domain) (q r s : GradeExpr D),
    gexpr_eq (GAdd q r) (GAdd r q) /\
    gexpr_eq (GAdd (GAdd q r) s) (GAdd q (GAdd r s)) /\
    gexpr_eq (GMul (GAdd q r) s) (GMul s (GAdd q r)) /\
    gexpr_eq (GMul (GMul q r) s) (GMul q (GMul r s)) /\
    gexpr_eq (GMul q (GAdd r s)) (GAdd (GMul q r) (GMul q s)) /\
    gexpr_eq (GMul (GLit zero) q) (GLit zero) /\
    gexpr_eq (GMul (GLit one) q) q /\
    gexpr_eq (GAdd (GLit zero) q) q.
Proof.
  intros D q r s. repeat split; intro rho; cbn.
  - apply add_comm.
  - symmetry. apply add_assoc.
  - apply mul_comm.
  - symmetry. apply mul_assoc.
  - apply mul_add.
  - apply mul_zero.
  - apply mul_one.
  - apply add_zero.
Qed.

Lemma gexpr_allows_refl : forall (D : Domain) (e : GradeExpr D),
  gexpr_allows e e.
Proof. intros D e rho. apply allows_refl. Qed.

Lemma gexpr_allows_trans : forall (D : Domain) (e1 e2 e3 : GradeExpr D),
  gexpr_allows e1 e2 -> gexpr_allows e2 e3 -> gexpr_allows e1 e3.
Proof. intros D e1 e2 e3 H12 H23 rho. eapply allows_trans; [apply H12 | apply H23]. Qed.

Lemma gexpr_allows_add_compat : forall (D : Domain) (a1 a2 b1 b2 : GradeExpr D),
  gexpr_allows a1 a2 -> gexpr_allows b1 b2 -> gexpr_allows (GAdd a1 b1) (GAdd a2 b2).
Proof. intros D a1 a2 b1 b2 Ha Hb rho. cbn. apply add_monotone; [apply Ha | apply Hb]. Qed.

Lemma gexpr_allows_mul_compat : forall (D : Domain) (a1 a2 b1 b2 : GradeExpr D),
  gexpr_allows a1 a2 -> gexpr_allows b1 b2 -> gexpr_allows (GMul a1 b1) (GMul a2 b2).
Proof. intros D a1 a2 b1 b2 Ha Hb rho. cbn. apply mul_monotone; [apply Ha | apply Hb]. Qed.

End GradedDomains.
