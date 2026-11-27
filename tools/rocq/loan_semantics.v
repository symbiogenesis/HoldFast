(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Import ListNotations.

Module LoanSemantics.

(* ================================================================= *)
(* 1. Identifiers, Projection Steps, and Places                      *)
(* ================================================================= *)

Definition owner_id := nat.
Definition loan_id := nat.
Definition origin_id := nat.
Definition field_id := nat.
Definition backing_id := nat.
Definition fact_id := nat.
Definition point_id := nat.
Definition tag_id := nat.

Inductive proj_step : Type :=
| SField (f : field_id)
| SElem (idx : nat)
| SSlice (off len : nat)
| SCell2D (r c : nat)
| SUnionPayload.

Definition proj_step_beq (a b : proj_step) : bool :=
  match a, b with
  | SField f1, SField f2 => Nat.eqb f1 f2
  | SElem i1, SElem i2 => Nat.eqb i1 i2
  | SSlice o1 l1, SSlice o2 l2 => Nat.eqb o1 o2 && Nat.eqb l1 l2
  | SCell2D r1 c1, SCell2D r2 c2 => Nat.eqb r1 r2 && Nat.eqb c1 c2
  | SUnionPayload, SUnionPayload => true
  | _, _ => false
  end.

Lemma proj_step_beq_eq : forall a b, proj_step_beq a b = true <-> a = b.
Proof.
  intros a b; split; intro H.
  - destruct a, b; cbn in H; try discriminate;
      repeat rewrite andb_true_iff in H;
      repeat match goal with
             | H0 : _ /\ _ |- _ => destruct H0
             | H0 : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H0; subst
             end; reflexivity.
  - subst b. destruct a; cbn; repeat rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma proj_step_beq_refl : forall a, proj_step_beq a a = true.
Proof.
  intro a. now apply proj_step_beq_eq.
Qed.

Definition proj_step_eq_dec : forall a b : proj_step, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint list_beq {A : Type} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => eqb x y && list_beq eqb xr yr
  | _, _ => false
  end.

Lemma list_beq_eq : forall {A : Type} (eqb : A -> A -> bool),
  (forall x y, eqb x y = true <-> x = y) ->
  forall xs ys, list_beq eqb xs ys = true <-> xs = ys.
Proof.
  intros A eqb Heqb xs. induction xs as [| x xr IH]; destruct ys as [| y yr];
    cbn; split; intro H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [Hxy Hrec].
    apply Heqb in Hxy. apply IH in Hrec. now subst.
  - inversion H; subst. apply andb_true_iff; split.
    + now apply Heqb.
    + now apply IH.
Qed.

Record place := {
  p_owner : owner_id;
  p_path : list proj_step;
}.

Definition PRoot (o : owner_id) : place :=
  {| p_owner := o; p_path := [] |}.

Definition PField (p : place) (f : field_id) : place :=
  {| p_owner := p_owner p; p_path := p_path p ++ [SField f] |}.

Definition PElem (p : place) (idx : nat) : place :=
  {| p_owner := p_owner p; p_path := p_path p ++ [SElem idx] |}.

Definition PSlice (p : place) (off len : nat) : place :=
  {| p_owner := p_owner p; p_path := p_path p ++ [SSlice off len] |}.

Definition PCell2D (p : place) (r c : nat) : place :=
  {| p_owner := p_owner p; p_path := p_path p ++ [SCell2D r c] |}.

Definition PUnionPayload (p : place) : place :=
  {| p_owner := p_owner p; p_path := p_path p ++ [SUnionPayload] |}.

Definition place_beq (p1 p2 : place) : bool :=
  Nat.eqb (p_owner p1) (p_owner p2) &&
  list_beq proj_step_beq (p_path p1) (p_path p2).

Lemma place_beq_eq : forall p1 p2, place_beq p1 p2 = true <-> p1 = p2.
Proof.
  intros [o1 s1] [o2 s2]; unfold place_beq; cbn.
  rewrite andb_true_iff, Nat.eqb_eq, (list_beq_eq proj_step_beq proj_step_beq_eq).
  split; intro H.
  - destruct H as [-> ->]. reflexivity.
  - inversion H; auto.
Qed.

Lemma place_beq_refl : forall p, place_beq p p = true.
Proof.
  intro p. now apply place_beq_eq.
Qed.

Definition place_eq_dec : forall p1 p2 : place, {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  destruct (place_beq p1 p2) eqn:E.
  - left. now apply place_beq_eq.
  - right. intro Heq. apply place_beq_eq in Heq. congruence.
Defined.

(* ================================================================= *)
(* 2. Containment (within) and Symbolic Disjointness                 *)
(* ================================================================= *)

Definition step_within_b (child parent : proj_step) : bool :=
  if proj_step_beq child parent then true
  else match child, parent with
       | SElem i, SSlice a m => Nat.leb a i && Nat.ltb i (a + m)
       | SSlice a m, SSlice b n => Nat.leb b a && Nat.leb (a + m) (b + n)
       | _, _ => false
       end.

Lemma step_within_refl : forall s, step_within_b s s = true.
Proof.
  intro s. unfold step_within_b. now rewrite proj_step_beq_refl.
Qed.

Lemma step_within_trans : forall a b c,
  step_within_b a b = true ->
  step_within_b b c = true ->
  step_within_b a c = true.
Proof.
  intros a b c Hab Hbc.
  unfold step_within_b in *.
  destruct (proj_step_beq a b) eqn:Eab.
  - apply proj_step_beq_eq in Eab. now subst.
  - destruct (proj_step_beq b c) eqn:Ebc.
    + apply proj_step_beq_eq in Ebc. subst.
      now rewrite Eab.
    + destruct a, b, c; try discriminate; cbn [proj_step_beq step_within_b] in *.
      * repeat rewrite andb_true_iff in *.
        repeat rewrite Nat.leb_le in *.
        repeat rewrite Nat.ltb_lt in *.
        split; lia.
      * destruct (Nat.eqb off off1 && Nat.eqb len len1); [reflexivity |].
        repeat rewrite andb_true_iff in *.
        repeat rewrite Nat.leb_le in *.
        split; lia.
Qed.

Fixpoint steps_within_b (child parent : list proj_step) {struct parent} : bool :=
  match parent with
  | [] => true
  | b :: r2 =>
      match child with
      | [] => false
      | a :: r1 =>
          if proj_step_beq a b then steps_within_b r1 r2
          else match r2 with
               | [] => step_within_b a b
               | _ => false
               end
      end
  end.

Lemma steps_within_refl : forall s, steps_within_b s s = true.
Proof.
  induction s as [| a r IH]; cbn; [reflexivity |].
  now rewrite proj_step_beq_refl.
Qed.

Lemma steps_within_trans : forall a b c,
  steps_within_b a b = true ->
  steps_within_b b c = true ->
  steps_within_b a c = true.
Proof.
  intros a b c. revert a b.
  induction c as [| xc rc IH]; intros a b Hab Hbc; [destruct a; reflexivity |].
  destruct b as [| xb rb]; [cbn in Hbc; discriminate |].
  destruct a as [| xa ra]; [cbn in Hab; discriminate |].
  cbn in Hab, Hbc. cbn.
  destruct (proj_step_beq xb xc) eqn:Exbc.
  - apply proj_step_beq_eq in Exbc; subst xc.
    destruct (proj_step_beq xa xb) eqn:Exab.
    + apply proj_step_beq_eq in Exab; subst xb.
      eapply IH; eassumption.
    + destruct rb as [| xb' rb'].
      * destruct rc as [| xc' rc']; [| cbn in Hbc; discriminate].
        exact Hab.
      * discriminate.
  - destruct rc as [| xc' rc']; [| discriminate].
    destruct (proj_step_beq xa xb) eqn:Exab.
    + apply proj_step_beq_eq in Exab; subst xb.
      rewrite Exbc. exact Hbc.
    + destruct rb as [| xb' rb']; [| discriminate].
      destruct (proj_step_beq xa xc) eqn:Exac; [reflexivity |].
      eapply step_within_trans; [exact Hab | exact Hbc].
Qed.

Definition within_b (child parent : place) : bool :=
  Nat.eqb (p_owner child) (p_owner parent) &&
  steps_within_b (p_path child) (p_path parent).

Definition within (child parent : place) : Prop :=
  within_b child parent = true.

Lemma within_refl : forall p, within p p.
Proof.
  intro p. unfold within, within_b.
  now rewrite Nat.eqb_refl, steps_within_refl.
Qed.

Lemma within_trans : forall a b c,
  within a b -> within b c -> within a c.
Proof.
  intros a b c Hab Hbc.
  unfold within, within_b in *.
  apply andb_true_iff in Hab as [Ho1 Hs1].
  apply andb_true_iff in Hbc as [Ho2 Hs2].
  apply Nat.eqb_eq in Ho1. apply Nat.eqb_eq in Ho2.
  apply andb_true_iff; split.
  - apply Nat.eqb_eq; congruence.
  - eapply steps_within_trans; eassumption.
Qed.

Lemma within_owner : forall a b, within a b -> p_owner a = p_owner b.
Proof.
  intros a b H. unfold within, within_b in H.
  apply andb_true_iff in H as [Ho _]. now apply Nat.eqb_eq in Ho.
Qed.

Definition step_disjoint_b (a b : proj_step) : bool :=
  match a, b with
  | SField f1, SField f2 => negb (Nat.eqb f1 f2)
  | SElem i, SElem j => negb (Nat.eqb i j)
  | SCell2D r1 c1, SCell2D r2 c2 => negb (Nat.eqb r1 r2) || negb (Nat.eqb c1 c2)
  | SSlice a1 m1, SSlice a2 m2 => Nat.leb (a1 + m1) a2 || Nat.leb (a2 + m2) a1
  | SElem k, SSlice a1 m1 => Nat.ltb k a1 || Nat.leb (a1 + m1) k
  | SSlice a1 m1, SElem k => Nat.ltb k a1 || Nat.leb (a1 + m1) k
  | _, _ => false
  end.

Lemma step_disjoint_sym : forall a b,
  step_disjoint_b a b = true -> step_disjoint_b b a = true.
Proof.
  intros a b H.
  destruct a, b; cbn in *; try discriminate;
    try (rewrite Nat.eqb_sym; exact H);
    try (rewrite orb_comm; exact H);
    try exact H.
  rewrite (Nat.eqb_sym r0 r), (Nat.eqb_sym c0 c); exact H.
Qed.

Lemma step_disjoint_within_left : forall a b c,
  step_disjoint_b a b = true ->
  step_within_b c a = true ->
  step_disjoint_b c b = true.
Proof.
  intros a b c Hab Hca.
  unfold step_within_b in Hca.
  destruct (proj_step_beq c a) eqn:Eca.
  - apply proj_step_beq_eq in Eca. now subst.
  - destruct c, a; cbn [step_within_b proj_step_beq] in Hca; try discriminate;
      destruct b; cbn [step_disjoint_b] in *; try discriminate;
      rewrite ?orb_true_iff, ?andb_true_iff, ?negb_true_iff,
        ?Nat.eqb_neq, ?Nat.leb_le, ?Nat.ltb_lt in *;
      lia.
Qed.

Fixpoint steps_disjoint_b (s1 s2 : list proj_step) : bool :=
  match s1, s2 with
  | [], _ => false
  | _, [] => false
  | a :: r1, b :: r2 =>
      if step_disjoint_b a b then true
      else if proj_step_beq a b then steps_disjoint_b r1 r2
      else false
  end.

Lemma steps_disjoint_sym : forall s1 s2,
  steps_disjoint_b s1 s2 = true -> steps_disjoint_b s2 s1 = true.
Proof.
  induction s1 as [| a r1 IH]; destruct s2 as [| b r2]; cbn; intro H; try discriminate.
  destruct (step_disjoint_b a b) eqn:Eab.
  - rewrite (step_disjoint_sym a b Eab). reflexivity.
  - destruct (proj_step_beq a b) eqn:Eeq.
    + apply proj_step_beq_eq in Eeq; subst b.
      rewrite proj_step_beq_refl.
      destruct (step_disjoint_b a a) eqn:Eaa; [reflexivity |].
      now apply IH.
    + discriminate.
Qed.

Definition step_nonempty (s : proj_step) : Prop :=
  match s with
  | SSlice _ len => 0 < len
  | _ => True
  end.

Lemma step_disjoint_not_eq : forall a b,
  step_nonempty a ->
  step_disjoint_b a b = true -> proj_step_beq a b = false.
Proof.
  intros a b Hne H.
  destruct (proj_step_beq a b) eqn:E; [| reflexivity].
  apply proj_step_beq_eq in E; subst b.
  destruct a; cbn in H, Hne;
    repeat rewrite Nat.eqb_refl in H;
    repeat rewrite orb_true_iff in H;
    repeat rewrite Nat.leb_le in H;
    try discriminate; lia.
Qed.

Lemma steps_disjoint_within_left : forall s1 s2 s3,
  steps_disjoint_b s1 s2 = true ->
  steps_within_b s3 s1 = true ->
  steps_disjoint_b s3 s2 = true.
Proof.
  induction s1 as [| a r1 IH]; intros [| b r2] [| c r3] Hdisj Hwith;
    cbn in *; try discriminate.
  destruct (step_disjoint_b a b) eqn:Eab.
  - destruct (proj_step_beq c a) eqn:Eca.
    + apply proj_step_beq_eq in Eca; subst c. now rewrite Eab.
    + destruct r1 as [| a' r1']; [| discriminate].
      rewrite (step_disjoint_within_left a b c Eab Hwith). reflexivity.
  - destruct (proj_step_beq a b) eqn:Eeq; [| discriminate].
    apply proj_step_beq_eq in Eeq; subst b.
    destruct (proj_step_beq c a) eqn:Eca.
    + apply proj_step_beq_eq in Eca; subst c.
      destruct (step_disjoint_b a a); [reflexivity |].
      eapply IH; eassumption.
    + destruct r1; [cbn in Hdisj; discriminate | discriminate].
Qed.

Definition places_disjoint_b (p1 p2 : place) : bool :=
  negb (Nat.eqb (p_owner p1) (p_owner p2)) ||
  steps_disjoint_b (p_path p1) (p_path p2).

Definition places_disjoint (p1 p2 : place) : Prop :=
  places_disjoint_b p1 p2 = true.

Definition places_overlap_b (p1 p2 : place) : bool :=
  negb (places_disjoint_b p1 p2).

Lemma places_disjoint_sym : forall p1 p2,
  places_disjoint p1 p2 -> places_disjoint p2 p1.
Proof.
  intros [o1 s1] [o2 s2] H. unfold places_disjoint, places_disjoint_b in *; cbn in *.
  apply orb_true_iff in H as [Ho | Hs]; apply orb_true_iff.
  - left. now rewrite Nat.eqb_sym.
  - right. now apply steps_disjoint_sym.
Qed.

Lemma places_disjoint_within : forall p1 p2 q1 q2,
  places_disjoint p1 p2 ->
  within q1 p1 ->
  within q2 p2 ->
  places_disjoint q1 q2.
Proof.
  intros p1 p2 q1 q2 Hdisj Hq1 Hq2.
  unfold places_disjoint, places_disjoint_b in *.
  unfold within, within_b in *.
  apply andb_true_iff in Hq1 as [Ho1 Hs1].
  apply andb_true_iff in Hq2 as [Ho2 Hs2].
  apply Nat.eqb_eq in Ho1. apply Nat.eqb_eq in Ho2.
  apply orb_true_iff in Hdisj as [Hneq | Hsteps]; apply orb_true_iff.
  - left. rewrite Ho1, Ho2. exact Hneq.
  - right.
    apply steps_disjoint_sym.
    eapply steps_disjoint_within_left; [| exact Hs2].
    apply steps_disjoint_sym.
    eapply steps_disjoint_within_left; [exact Hsteps | exact Hs1].
Qed.

Lemma steps_disjoint_app_prefix : forall p s1 s2,
  steps_disjoint_b s1 s2 = true ->
  steps_disjoint_b (p ++ s1) (p ++ s2) = true.
Proof.
  induction p as [| a r IH]; intros s1 s2 H; cbn; [exact H |].
  destruct (step_disjoint_b a a); [reflexivity |].
  rewrite proj_step_beq_refl. now apply IH.
Qed.

Lemma places_disjoint_elem_ne : forall p i j,
  i <> j -> places_disjoint (PElem p i) (PElem p j).
Proof.
  intros p i j Hneq.
  unfold places_disjoint, places_disjoint_b, PElem; cbn.
  apply orb_true_iff; right.
  apply steps_disjoint_app_prefix; cbn.
  destruct (Nat.eqb i j) eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma places_disjoint_cell2d : forall p r1 c1 r2 c2,
  (r1 <> r2 \/ c1 <> c2) ->
  places_disjoint (PCell2D p r1 c1) (PCell2D p r2 c2).
Proof.
  intros p r1 c1 r2 c2 Hneq.
  unfold places_disjoint, places_disjoint_b, PCell2D; cbn.
  apply orb_true_iff; right.
  apply steps_disjoint_app_prefix; cbn.
  destruct (Nat.eqb r1 r2) eqn:Er, (Nat.eqb c1 c2) eqn:Ec; cbn; try reflexivity.
  apply Nat.eqb_eq in Er; apply Nat.eqb_eq in Ec. destruct Hneq; contradiction.
Qed.

Lemma places_disjoint_slice : forall p a m b n,
  (a + m <= b \/ b + n <= a) ->
  places_disjoint (PSlice p a m) (PSlice p b n).
Proof.
  intros p a m b n Hdisj.
  unfold places_disjoint, places_disjoint_b, PSlice; cbn.
  apply orb_true_iff; right.
  apply steps_disjoint_app_prefix; cbn.
  destruct (Nat.leb (a + m) b || Nat.leb (b + n) a) eqn:E; [reflexivity |].
  exfalso. apply orb_false_iff in E as [E1 E2].
  apply Nat.leb_gt in E1; apply Nat.leb_gt in E2. lia.
Qed.

Lemma places_disjoint_elem_slice : forall p k a m,
  (k < a \/ a + m <= k) ->
  places_disjoint (PElem p k) (PSlice p a m).
Proof.
  intros p k a m Hdisj.
  unfold places_disjoint, places_disjoint_b, PElem, PSlice; cbn.
  apply orb_true_iff; right.
  apply steps_disjoint_app_prefix; cbn [steps_disjoint_b step_disjoint_b].
  destruct (Nat.ltb k a || Nat.leb (a + m) k) eqn:E; [reflexivity |].
  exfalso. apply orb_false_iff in E as [E1 E2].
  apply Nat.ltb_ge in E1; apply Nat.leb_gt in E2. lia.
Qed.

Lemma places_disjoint_field_ne : forall p f1 f2,
  f1 <> f2 -> places_disjoint (PField p f1) (PField p f2).
Proof.
  intros p f1 f2 Hneq.
  unfold places_disjoint, places_disjoint_b, PField; cbn.
  apply orb_true_iff; right.
  apply steps_disjoint_app_prefix; cbn.
  destruct (Nat.eqb f1 f2) eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma step_disjoint_not_within : forall a b,
  step_nonempty a ->
  step_disjoint_b a b = true -> step_within_b a b = false.
Proof.
  intros a b Hne Hab.
  unfold step_within_b. rewrite (step_disjoint_not_eq a b Hne Hab).
  destruct a, b; cbn [step_disjoint_b step_nonempty] in *; cbv iota; try reflexivity;
    (destruct (Nat.leb _ _ && _) eqn:Ew; [exfalso | reflexivity]);
    rewrite ?orb_true_iff, ?andb_true_iff, ?Nat.leb_le, ?Nat.ltb_lt in *;
    lia.
Qed.

Lemma steps_disjoint_not_within : forall s1 s2,
  Forall step_nonempty s1 ->
  steps_disjoint_b s1 s2 = true -> steps_within_b s1 s2 = false.
Proof.
  induction s1 as [| a r1 IH]; destruct s2 as [| b r2]; intros Hne H; cbn in *; try discriminate.
  inversion Hne; subst.
  destruct (step_disjoint_b a b) eqn:Eab.
  - rewrite (step_disjoint_not_eq a b H2 Eab).
    destruct r2; [| reflexivity].
    now apply step_disjoint_not_within.
  - destruct (proj_step_beq a b) eqn:Eeq; [| discriminate].
    now apply IH.
Qed.

Lemma places_disjoint_not_within : forall p1 p2,
  Forall step_nonempty (p_path p1) ->
  places_disjoint p1 p2 -> ~ within p1 p2.
Proof.
  intros [o1 s1] [o2 s2] Hne Hdisj Hwith.
  unfold places_disjoint, places_disjoint_b in Hdisj.
  unfold within, within_b in Hwith. cbn in *.
  apply andb_true_iff in Hwith as [Ho Hs].
  apply Nat.eqb_eq in Ho; subst o2.
  rewrite Nat.eqb_refl in Hdisj; cbn in Hdisj.
  rewrite (steps_disjoint_not_within s1 s2 Hne Hdisj) in Hs.
  discriminate.
Qed.

(* ================================================================= *)
(* 3. Operational Memory, Containers, Tagged Unions, and Addresses   *)
(* ================================================================= *)

Inductive owner_val : Type :=
| VScalar (v : nat)
| VContainer (bid : backing_id) (cap : nat) (elems : list owner_val)
| VGrid (bid : backing_id) (rows cols : nat) (cells : list ((nat * nat) * nat))
| VUnion (utag : tag_id) (pbid : backing_id) (payload : owner_val)
| VRecord (bid : backing_id) (fields : list (field_id * owner_val))
| VMoved.

Definition cell_beq (a b : nat * nat) : bool :=
  Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Lemma cell_beq_eq : forall a b, cell_beq a b = true <-> a = b.
Proof.
  intros [r1 c1] [r2 c2]; unfold cell_beq; cbn.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Fixpoint assoc_get {K V : Type} (eqb : K -> K -> bool)
    (xs : list (K * V)) (k : K) : option V :=
  match xs with
  | [] => None
  | (k', v) :: rest => if eqb k k' then Some v else assoc_get eqb rest k
  end.

Fixpoint assoc_update {K V : Type} (eqb : K -> K -> bool)
    (xs : list (K * V)) (k : K) (v : V) : option (list (K * V)) :=
  match xs with
  | [] => None
  | (k', v') :: rest =>
      if eqb k k' then Some ((k', v) :: rest)
      else option_map (cons (k', v')) (assoc_update eqb rest k v)
  end.

Fixpoint assoc_set {K V : Type} (eqb : K -> K -> bool)
    (xs : list (K * V)) (k : K) (v : V) : list (K * V) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if eqb k k' then (k', v) :: rest
      else (k', v') :: assoc_set eqb rest k v
  end.

Fixpoint list_set {A : Type} (xs : list A) (i : nat) (v : A) : option (list A) :=
  match xs, i with
  | [], _ => None
  | _ :: rest, 0 => Some (v :: rest)
  | x :: rest, S i' => option_map (cons x) (list_set rest i' v)
  end.

Lemma assoc_get_update_same : forall {K V : Type} (eqb : K -> K -> bool),
  (forall a b, eqb a b = true <-> a = b) ->
  forall (xs : list (K * V)) k v xs',
  assoc_update eqb xs k v = Some xs' -> assoc_get eqb xs' k = Some v.
Proof.
  intros K V eqb Heqb xs.
  induction xs as [| [k' v'] rest IH]; intros k v xs' Hu; cbn in Hu; [discriminate |].
  destruct (eqb k k') eqn:Ek.
  - inversion Hu; subst. cbn. rewrite Ek. reflexivity.
  - destruct (assoc_update eqb rest k v) as [rest' |] eqn:Hr; [| discriminate].
    inversion Hu; subst. cbn. rewrite Ek. eapply IH; eauto.
Qed.

Lemma assoc_get_update_other : forall {K V : Type} (eqb : K -> K -> bool),
  (forall a b, eqb a b = true <-> a = b) ->
  forall (xs : list (K * V)) k1 k2 v xs',
  k1 <> k2 ->
  assoc_update eqb xs k1 v = Some xs' ->
  assoc_get eqb xs' k2 = assoc_get eqb xs k2.
Proof.
  intros K V eqb Heqb xs.
  induction xs as [| [k' v'] rest IH]; intros k1 k2 v xs' Hneq Hu; cbn in Hu; [discriminate |].
  destruct (eqb k1 k') eqn:Ek1.
  - inversion Hu; subst. cbn.
    apply Heqb in Ek1; subst k'.
    destruct (eqb k2 k1) eqn:Ek2.
    + apply Heqb in Ek2; congruence.
    + reflexivity.
  - destruct (assoc_update eqb rest k1 v) as [rest' |] eqn:Hr; [| discriminate].
    inversion Hu; subst. cbn.
    destruct (eqb k2 k'); [reflexivity |].
    eapply IH; eauto.
Qed.

Lemma assoc_get_set_same : forall {K V : Type} (eqb : K -> K -> bool),
  (forall a b, eqb a b = true <-> a = b) ->
  forall (xs : list (K * V)) k v,
  assoc_get eqb (assoc_set eqb xs k v) k = Some v.
Proof.
  intros K V eqb Heqb xs.
  induction xs as [| [k' v'] rest IH]; intros k v; cbn.
  - destruct (eqb k k) eqn:E; [reflexivity |].
    exfalso. assert (k = k) by reflexivity. apply Heqb in H. congruence.
  - destruct (eqb k k') eqn:Ek; cbn.
    + rewrite Ek. reflexivity.
    + rewrite Ek. apply IH.
Qed.

Lemma assoc_get_set_other : forall {K V : Type} (eqb : K -> K -> bool),
  (forall a b, eqb a b = true <-> a = b) ->
  forall (xs : list (K * V)) k1 k2 v,
  k1 <> k2 ->
  assoc_get eqb (assoc_set eqb xs k1 v) k2 = assoc_get eqb xs k2.
Proof.
  intros K V eqb Heqb xs.
  induction xs as [| [k' v'] rest IH]; intros k1 k2 v Hneq; cbn.
  - destruct (eqb k2 k1) eqn:E; [apply Heqb in E; congruence | reflexivity].
  - destruct (eqb k1 k') eqn:Ek1; cbn.
    + apply Heqb in Ek1; subst k'.
      destruct (eqb k2 k1) eqn:Ek2; [apply Heqb in Ek2; congruence | reflexivity].
    + destruct (eqb k2 k'); [reflexivity | apply IH; exact Hneq].
Qed.

Lemma list_set_length : forall {A : Type} (xs : list A) i v xs',
  list_set xs i v = Some xs' -> length xs' = length xs.
Proof.
  induction xs as [| x rest IH]; intros [| i'] v xs' H; cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct (list_set rest i' v) as [rest' |] eqn:Hr; [| discriminate].
    inversion H; subst; cbn. f_equal. eapply IH; eauto.
Qed.

Lemma list_set_nth_same : forall {A : Type} (xs : list A) i v xs',
  list_set xs i v = Some xs' -> nth_error xs' i = Some v.
Proof.
  induction xs as [| x rest IH]; intros [| i'] v xs' H; cbn in H; try discriminate.
  - inversion H; reflexivity.
  - destruct (list_set rest i' v) as [rest' |] eqn:Hr; [| discriminate].
    inversion H; subst; cbn. eapply IH; eauto.
Qed.

Lemma list_set_nth_other : forall {A : Type} (xs : list A) i j v xs',
  i <> j ->
  list_set xs i v = Some xs' ->
  nth_error xs' j = nth_error xs j.
Proof.
  induction xs as [| x rest IH]; intros [| i'] [| j'] v xs' Hneq H;
    cbn in H; try discriminate.
  - exfalso; lia.
  - inversion H; reflexivity.
  - destruct (list_set rest i' v) as [rest' |] eqn:Hr; [| discriminate].
    inversion H; subst; reflexivity.
  - destruct (list_set rest i' v) as [rest' |] eqn:Hr; [| discriminate].
    inversion H; subst; cbn. apply IH with (i := i') (v := v); [lia | exact Hr].
Qed.

Fixpoint read_val (v : owner_val) (steps : list proj_step) : option owner_val :=
  match steps with
  | [] => match v with VMoved => None | _ => Some v end
  | SField f :: rest =>
      match v with
      | VRecord _ fs =>
          match assoc_get Nat.eqb fs f with
          | Some fv => read_val fv rest
          | None => None
          end
      | _ => None
      end
  | SElem i :: rest =>
      match v with
      | VContainer _ _ elems =>
          match nth_error elems i with
          | Some ev => read_val ev rest
          | None => None
          end
      | _ => None
      end
  | SSlice off len :: rest =>
      match v with
      | VContainer bid _ elems =>
          if Nat.leb (off + len) (length elems) then
            match rest with
            | [] => Some (VContainer bid len (firstn len (skipn off elems)))
            | SElem k :: rest' =>
                if Nat.ltb k len then
                  match nth_error elems (off + k) with
                  | Some ev => read_val ev rest'
                  | None => None
                  end
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  | SCell2D r c :: rest =>
      match v, rest with
      | VGrid _ rows cols cells, [] =>
          if Nat.ltb r rows && Nat.ltb c cols then
            Some (VScalar (match assoc_get cell_beq cells (r, c) with Some n => n | None => 0 end))
          else None
      | _, _ => None
      end
  | SUnionPayload :: rest =>
      match v with
      | VUnion _ _ p => read_val p rest
      | _ => None
      end
  end.

Definition read_scalar (v : owner_val) (steps : list proj_step) : option nat :=
  match read_val v steps with
  | Some (VScalar n) => Some n
  | _ => None
  end.

Fixpoint write_slice_fill (elems : list owner_val) (idx off len val : nat)
    : option (list owner_val) :=
  match elems with
  | [] => Some []
  | e :: rest =>
      if Nat.leb off idx && Nat.ltb idx (off + len) then
        match e with
        | VScalar _ =>
            option_map (cons (VScalar val)) (write_slice_fill rest (S idx) off len val)
        | _ => None
        end
      else
        option_map (cons e) (write_slice_fill rest (S idx) off len val)
  end.

Lemma write_slice_fill_length : forall elems idx off len val elems',
  write_slice_fill elems idx off len val = Some elems' ->
  length elems' = length elems.
Proof.
  induction elems as [| e rest IH]; intros idx off len val elems' H;
    cbn [write_slice_fill option_map] in H.
  - inversion H; reflexivity.
  - destruct (Nat.leb off idx && Nat.ltb idx (off + len)) eqn:Hin;
      cbn [write_slice_fill option_map] in H.
    + destruct e; cbn [write_slice_fill option_map] in H; try discriminate.
      destruct (write_slice_fill rest (S idx) off len val) as [r' |] eqn:Hr;
        cbn [write_slice_fill option_map] in H; [| discriminate].
      inversion H; subst; cbn. f_equal. eapply IH; eauto.
    + destruct (write_slice_fill rest (S idx) off len val) as [r' |] eqn:Hr;
        cbn [write_slice_fill option_map] in H; [| discriminate].
      inversion H; subst; cbn. f_equal. eapply IH; eauto.
Qed.

Lemma write_slice_fill_outside : forall elems idx off len val elems' j,
  write_slice_fill elems idx off len val = Some elems' ->
  (idx + j < off \/ off + len <= idx + j) ->
  nth_error elems' j = nth_error elems j.
Proof.
  induction elems as [| e rest IH]; intros idx off len val elems' j H Hout;
    cbn [write_slice_fill option_map] in H.
  - inversion H; reflexivity.
  - destruct (Nat.leb off idx && Nat.ltb idx (off + len)) eqn:Hin;
      cbn [write_slice_fill option_map] in H.
    + destruct e; cbn [write_slice_fill option_map] in H; try discriminate.
      destruct (write_slice_fill rest (S idx) off len val) as [r' |] eqn:Hr;
        cbn [write_slice_fill option_map] in H; [| discriminate].
      inversion H; subst; clear H.
      destruct j as [| j']; cbn.
      * exfalso. apply andb_true_iff in Hin as [H1 H2].
        apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. lia.
      * apply IH with (idx := S idx) (off := off) (len := len) (val := val); [exact Hr | lia].
    + destruct (write_slice_fill rest (S idx) off len val) as [r' |] eqn:Hr;
        cbn [write_slice_fill option_map] in H; [| discriminate].
      inversion H; subst; clear H.
      destruct j as [| j']; cbn; [reflexivity |].
      apply IH with (idx := S idx) (off := off) (len := len) (val := val); [exact Hr | lia].
Qed.

Lemma write_slice_fill_inside : forall elems cur off len val elems' idx ev0 ev',
  write_slice_fill elems cur off len val = Some elems' ->
  off <= cur + idx ->
  cur + idx < off + len ->
  nth_error elems idx = Some ev0 ->
  nth_error elems' idx = Some ev' ->
  exists m1 m2, ev0 = VScalar m1 /\ ev' = VScalar m2.
Proof.
  induction elems as [| e rs IH]; intros cur off len val elems' idx ev0 ev' Hfill H1 H2 He0 He';
    destruct idx as [| idx']; cbn [write_slice_fill option_map nth_error] in *;
    try discriminate.
  - destruct (Nat.leb off cur && Nat.ltb cur (off + len)) eqn:Hcur;
      cbn [write_slice_fill option_map] in Hfill.
    + destruct e; cbn [write_slice_fill option_map] in Hfill; try discriminate.
      destruct (write_slice_fill rs (S cur) off len val) as [r' |] eqn:Hr;
        cbn in Hfill; [| discriminate].
      inversion Hfill; subst; clear Hfill.
      cbn in He0, He'. inversion He0; inversion He'; subst. eauto.
    + apply andb_false_iff in Hcur as [Hcur | Hcur];
        [apply Nat.leb_gt in Hcur | apply Nat.ltb_ge in Hcur]; lia.
  - destruct (Nat.leb off cur && Nat.ltb cur (off + len)) eqn:Hcur;
      cbn [write_slice_fill option_map] in Hfill.
    + destruct e; cbn [write_slice_fill option_map] in Hfill; try discriminate.
      destruct (write_slice_fill rs (S cur) off len val) as [r' |] eqn:Hr;
        cbn in Hfill; [| discriminate].
      inversion Hfill; subst; clear Hfill.
      cbn in He'. eapply IH; [exact Hr | | | exact He0 | exact He']; lia.
    + destruct (write_slice_fill rs (S cur) off len val) as [r' |] eqn:Hr;
        cbn in Hfill; [| discriminate].
      inversion Hfill; subst; clear Hfill.
      cbn in He'. eapply IH; [exact Hr | | | exact He0 | exact He']; lia.
Qed.

Lemma skipn_nth_error_cons : forall {A : Type} n (xs : list A) x,
  nth_error xs n = Some x -> skipn n xs = x :: skipn (S n) xs.
Proof.
  induction n as [| n' IH]; intros [| y yr] x H; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - now apply IH.
Qed.

Lemma firstn_skipn_ext : forall {A : Type} (xs ys : list A) off len,
  length ys = length xs ->
  (forall j, off <= j -> j < off + len -> nth_error ys j = nth_error xs j) ->
  firstn len (skipn off ys) = firstn len (skipn off xs).
Proof.
  intros A xs ys off len Hlen Hext.
  revert xs ys off Hlen Hext.
  induction len as [| len' IH]; intros xs ys off Hlen Hext; [reflexivity |].
  destruct (Nat.ltb off (length xs)) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    assert (Hnth : nth_error ys off = nth_error xs off) by (apply Hext; lia).
    destruct (nth_error xs off) as [vx |] eqn:Exs.
    + assert (Eys : nth_error ys off = Some vx) by congruence.
      rewrite (skipn_nth_error_cons off ys vx Eys).
      rewrite (skipn_nth_error_cons off xs vx Exs).
      cbn [firstn]. f_equal.
      apply IH; [exact Hlen | intros j H1 H2; apply Hext; lia].
    + apply nth_error_None in Exs. lia.
  - apply Nat.ltb_ge in Hlt.
    rewrite !skipn_all2 by lia. reflexivity.
Qed.

Fixpoint write_stable_val (v : owner_val) (steps : list proj_step) (n : nat)
    : option owner_val :=
  match steps with
  | [] => match v with VScalar _ => Some (VScalar n) | _ => None end
  | SField f :: rest =>
      match v with
      | VRecord bid fs =>
          match assoc_get Nat.eqb fs f with
          | Some fv =>
              match write_stable_val fv rest n with
              | Some fv' => option_map (VRecord bid) (assoc_update Nat.eqb fs f fv')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SElem i :: rest =>
      match v with
      | VContainer bid cap elems =>
          match nth_error elems i with
          | Some ev =>
              match write_stable_val ev rest n with
              | Some ev' => option_map (VContainer bid cap) (list_set elems i ev')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SSlice off len :: rest =>
      match v with
      | VContainer bid cap elems =>
          if Nat.leb (off + len) (length elems) then
            match rest with
            | [] =>
                option_map (VContainer bid cap) (write_slice_fill elems 0 off len n)
            | SElem k :: rest' =>
                if Nat.ltb k len then
                  match nth_error elems (off + k) with
                  | Some ev =>
                      match write_stable_val ev rest' n with
                      | Some ev' => option_map (VContainer bid cap) (list_set elems (off + k) ev')
                      | None => None
                      end
                  | None => None
                  end
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  | SCell2D r c :: rest =>
      match v, rest with
      | VGrid bid rows cols cells, [] =>
          if Nat.ltb r rows && Nat.ltb c cols then
            Some (VGrid bid rows cols (assoc_set cell_beq cells (r, c) n))
          else None
      | _, _ => None
      end
  | SUnionPayload :: rest =>
      match v with
      | VUnion utag pbid p =>
          option_map (VUnion utag pbid) (write_stable_val p rest n)
      | _ => None
      end
  end.

Inductive step_stamp : Type :=
| StField (bid : backing_id) (f : field_id)
| StElem (bid : backing_id) (idx : nat)
| StSlice (bid : backing_id) (off len : nat)
| StCell2D (bid : backing_id) (r c : nat)
| StUnionPayload (utag : tag_id) (pbid : backing_id).

Definition val_bid (v : owner_val) : option backing_id :=
  match v with
  | VScalar _ => Some 0
  | VContainer b _ _ => Some b
  | VGrid b _ _ _ => Some b
  | VUnion _ b _ => Some b
  | VRecord b _ => Some b
  | VMoved => None
  end.

Fixpoint resolve_steps (v : owner_val) (steps : list proj_step) : option (list step_stamp) :=
  match steps with
  | [] => match v with VMoved => None | _ => Some [] end
  | SField f :: rest =>
      match v with
      | VRecord bid fs =>
          match assoc_get Nat.eqb fs f with
          | Some fv => option_map (cons (StField bid f)) (resolve_steps fv rest)
          | None => None
          end
      | _ => None
      end
  | SElem i :: rest =>
      match v with
      | VContainer bid _ elems =>
          match nth_error elems i with
          | Some ev => option_map (cons (StElem bid i)) (resolve_steps ev rest)
          | None => None
          end
      | _ => None
      end
  | SSlice off len :: rest =>
      match v with
      | VContainer bid _ elems =>
          if Nat.leb (off + len) (length elems) then
            match rest with
            | [] => Some [StSlice bid off len]
            | SElem k :: rest' =>
                if Nat.ltb k len then
                  match nth_error elems (off + k) with
                  | Some ev =>
                      option_map (fun st => StSlice bid off len :: StElem bid k :: st)
                        (resolve_steps ev rest')
                  | None => None
                  end
                else None
            | _ => None
            end
          else None
      | _ => None
      end
  | SCell2D r c :: rest =>
      match v, rest with
      | VGrid bid rows cols _, [] =>
          if Nat.ltb r rows && Nat.ltb c cols then Some [StCell2D bid r c] else None
      | _, _ => None
      end
  | SUnionPayload :: rest =>
      match v with
      | VUnion utag pbid p =>
          option_map (cons (StUnionPayload utag pbid)) (resolve_steps p rest)
      | _ => None
      end
  end.

Fixpoint valid_stamps (v : owner_val) (stamps : list step_stamp) : bool :=
  match stamps with
  | [] => match v with VMoved => false | _ => true end
  | StField bid f :: rest =>
      match v with
      | VRecord bid' fs =>
          if Nat.eqb bid bid' then
            match assoc_get Nat.eqb fs f with
            | Some fv => valid_stamps fv rest
            | None => false
            end
          else false
      | _ => false
      end
  | StElem bid i :: rest =>
      match v with
      | VContainer bid' _ elems =>
          if Nat.eqb bid bid' then
            match nth_error elems i with
            | Some ev => valid_stamps ev rest
            | None => false
            end
          else false
      | _ => false
      end
  | StSlice bid off len :: rest =>
      match v with
      | VContainer bid' _ elems =>
          if Nat.eqb bid bid' && Nat.leb (off + len) (length elems) then
            match rest with
            | [] => true
            | StElem bid'' k :: rest' =>
                if Nat.eqb bid bid'' && Nat.ltb k len then
                  match nth_error elems (off + k) with
                  | Some ev => valid_stamps ev rest'
                  | None => false
                  end
                else false
            | _ => false
            end
          else false
      | _ => false
      end
  | StCell2D bid r c :: rest =>
      match v, rest with
      | VGrid bid' rows cols _, [] =>
          Nat.eqb bid bid' && Nat.ltb r rows && Nat.ltb c cols
      | _, _ => false
      end
  | StUnionPayload utag pbid :: rest =>
      match v with
      | VUnion utag' pbid' p =>
          Nat.eqb utag utag' && Nat.eqb pbid pbid' && valid_stamps p rest
      | _ => false
      end
  end.

Record place_addr := {
  addr_owner : owner_id;
  addr_root_bid : backing_id;
  addr_steps : list step_stamp;
}.

Record owner_entry := {
  oe_borrowed : bool;
  oe_val : owner_val;
}.

Definition memory := list (owner_id * owner_entry).

Definition lookup_owner (m : memory) (o : owner_id) : option owner_entry :=
  assoc_get Nat.eqb m o.

Definition update_owner (m : memory) (o : owner_id) (e : owner_entry) : option memory :=
  assoc_update Nat.eqb m o e.

Definition resolve_addr (m : memory) (p : place) : option place_addr :=
  match lookup_owner m (p_owner p) with
  | Some oe =>
      match val_bid (oe_val oe), resolve_steps (oe_val oe) (p_path p) with
      | Some rbid, Some st =>
          Some {| addr_owner := p_owner p; addr_root_bid := rbid; addr_steps := st |}
      | _, _ => None
      end
  | None => None
  end.

Definition addr_valid_b (m : memory) (a : place_addr) : bool :=
  match lookup_owner m (addr_owner a) with
  | Some oe =>
      match val_bid (oe_val oe) with
      | Some rbid =>
          Nat.eqb rbid (addr_root_bid a) && valid_stamps (oe_val oe) (addr_steps a)
      | None => false
      end
  | None => false
  end.

Definition addr_valid (m : memory) (a : place_addr) : Prop :=
  addr_valid_b m a = true.

Lemma resolve_steps_valid : forall v steps st,
  resolve_steps v steps = Some st -> valid_stamps v st = true.
Proof.
  intros v steps st H.
  assert (Haux : forall k steps v st,
    length steps <= k -> resolve_steps v steps = Some st -> valid_stamps v st = true).
  { induction k as [| k' IH]; intros [| s rest] v0 st0 Hlen0 Hr0;
      cbn [resolve_steps length] in *.
    - destruct v0; inversion Hr0; reflexivity.
    - lia.
    - destruct v0; inversion Hr0; reflexivity.
    - destruct s; cbn [resolve_steps option_map] in Hr0.
      + destruct v0; try discriminate.
        destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (resolve_steps fv rest) as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
        inversion Hr0; subst; cbn [valid_stamps]. rewrite Nat.eqb_refl, Hf.
        eapply IH; [| exact Hr]; lia.
      + destruct v0; try discriminate.
        destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (resolve_steps ev rest) as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
        inversion Hr0; subst; cbn [valid_stamps]. rewrite Nat.eqb_refl, He.
        eapply IH; [| exact Hr]; lia.
      + destruct v0; try discriminate.
        destruct (Nat.leb (off + len) (length elems)) eqn:Hlen; [| discriminate].
        destruct rest as [| s' rest']; cbn [resolve_steps option_map] in Hr0.
        * inversion Hr0; subst; cbn [valid_stamps]. rewrite Nat.eqb_refl, Hlen. reflexivity.
        * destruct s'; try discriminate.
          destruct (Nat.ltb idx len) eqn:Hk; [| discriminate].
          destruct (nth_error elems (off + idx)) as [ev |] eqn:He; [| discriminate].
          destruct (resolve_steps ev rest') as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
          inversion Hr0; subst; cbn [valid_stamps].
          rewrite Nat.eqb_refl, Hlen; cbn [andb]; cbv iota.
          rewrite Hk; cbn [andb]; cbv iota.
          rewrite He; cbv iota.
          eapply IH; [| exact Hr]; cbn in Hlen0; lia.
      + destruct v0, rest; try discriminate.
        destruct (Nat.ltb r rows && Nat.ltb c cols) eqn:Hb; [| discriminate].
        inversion Hr0; subst; cbn [valid_stamps]. rewrite Nat.eqb_refl. exact Hb.
      + destruct v0; try discriminate.
        destruct (resolve_steps v0 rest) as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
        inversion Hr0; subst; cbn [valid_stamps]. rewrite !Nat.eqb_refl. cbn.
        eapply IH; [| exact Hr]; lia. }
  eapply Haux; eauto.
Qed.

Lemma resolve_addr_valid : forall m p a,
  resolve_addr m p = Some a -> addr_valid m a.
Proof.
  intros m p a H. unfold resolve_addr in H.
  destruct (lookup_owner m (p_owner p)) as [oe |] eqn:Ho; [| discriminate].
  destruct (val_bid (oe_val oe)) as [rbid |] eqn:Hb; [| discriminate].
  destruct (resolve_steps (oe_val oe) (p_path p)) as [st |] eqn:Hs; [| discriminate].
  inversion H; subst. unfold addr_valid, addr_valid_b; cbn.
  rewrite Ho, Hb, Nat.eqb_refl. cbn. eapply resolve_steps_valid; eauto.
Qed.

Lemma write_stable_preserves_bid : forall v steps n v',
  write_stable_val v steps n = Some v' -> val_bid v' = val_bid v.
Proof.
  intros v steps. revert v.
  induction steps as [| s rest IH]; intros v n v' H; cbn [write_stable_val] in H.
  - destruct v; inversion H; reflexivity.
  - destruct s; destruct v; try discriminate; cbn [write_stable_val option_map] in H.
    + destruct (assoc_get Nat.eqb fields f); [| discriminate].
      destruct (write_stable_val o rest n); [| discriminate].
      destruct (assoc_update _ _ _ _); cbn in H; inversion H; reflexivity.
    + destruct (nth_error elems idx); [| discriminate].
      destruct (write_stable_val o rest n); [| discriminate].
      destruct (list_set _ _ _); cbn in H; inversion H; reflexivity.
    + destruct (Nat.leb (off + len) (length elems)); [| discriminate].
      destruct rest as [| s' rest'].
      * destruct (write_slice_fill _ _ _ _ _); cbn in H; inversion H; reflexivity.
      * destruct s'; try discriminate.
        destruct (Nat.ltb idx len); [| discriminate].
        destruct (nth_error elems (off + idx)); [| discriminate].
        destruct (write_stable_val o rest' n); [| discriminate].
        destruct (list_set _ _ _); cbn in H; inversion H; reflexivity.
    + destruct rest; [| discriminate].
      destruct (Nat.ltb r rows && Nat.ltb c cols); inversion H; reflexivity.
    + destruct (write_stable_val v rest n); cbn in H; inversion H; reflexivity.
Qed.

Lemma write_stable_preserves_stamps : forall v steps n v' st,
  write_stable_val v steps n = Some v' ->
  valid_stamps v st = true ->
  valid_stamps v' st = true.
Proof.
  intros v steps n v' st Hw0 Hv0.
  assert (Haux : forall k steps v n v' st,
    length steps <= k ->
    write_stable_val v steps n = Some v' ->
    valid_stamps v st = true ->
    valid_stamps v' st = true).
  { induction k as [| k' IH]; intros [| s rest] v0 n0 v0' st0 Hlen0 Hw Hv;
      cbn [length] in *.
    - cbn in Hw. destruct v0; inversion Hw; subst.
      destruct st0 as [| st1 str]; [reflexivity | destruct st1; cbn in Hv; discriminate].
    - lia.
    - cbn in Hw. destruct v0; inversion Hw; subst.
      destruct st0 as [| st1 str]; [reflexivity | destruct st1; cbn in Hv; discriminate].
    - destruct st0 as [| st1 str].
      + destruct v0' eqn:Ev'; try reflexivity.
        exfalso. apply write_stable_preserves_bid in Hw.
        cbn in Hw, Hv. destruct v0; discriminate.
      + destruct s, v0; cbn [write_stable_val option_map] in Hw; try discriminate.
        * (* SField *)
          destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
          destruct (write_stable_val fv rest n0) as [fv' |] eqn:Hwfv; [| discriminate].
          destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
            cbn in Hw; [| discriminate].
          inversion Hw; subst; clear Hw.
          destruct st1; cbn [valid_stamps] in *; try discriminate.
          destruct (Nat.eqb bid0 bid) eqn:Ebid; cbv iota in Hv; [| discriminate].
          destruct (assoc_get Nat.eqb fields f0) as [fv0 |] eqn:Hf0; cbv iota in Hv; [| discriminate].
          destruct (Nat.eq_dec f f0) as [-> | Hneq].
          -- rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f0 fv' fs' Hup).
             rewrite Hf in Hf0. inversion Hf0; subst.
             eapply IH; [| exact Hwfv | exact Hv]; lia.
          -- rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 fv' fs' Hneq Hup).
             rewrite Hf0. exact Hv.
        * (* SElem *)
          destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
          destruct (write_stable_val ev rest n0) as [ev' |] eqn:Hwev; [| discriminate].
          destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
            cbn in Hw; [| discriminate].
          inversion Hw; subst; clear Hw.
          destruct st1; cbn [valid_stamps] in *; try discriminate.
          -- destruct (Nat.eqb bid0 bid) eqn:Ebid; cbv iota in Hv; [| discriminate].
             destruct (nth_error elems idx0) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
             destruct (Nat.eq_dec idx idx0) as [-> | Hneq].
             ++ rewrite (list_set_nth_same elems idx0 ev' elems' Hls).
                rewrite He in He0. inversion He0; subst.
                eapply IH; [| exact Hwev | exact Hv]; lia.
             ++ rewrite (list_set_nth_other elems idx idx0 ev' elems' Hneq Hls).
                rewrite He0. exact Hv.
          -- destruct (Nat.eqb bid0 bid && Nat.leb (off + len) (length elems)) eqn:Hb;
               cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
             apply andb_true_iff in Hb as [Hbid Hlen].
             rewrite (list_set_length elems idx ev' elems' Hls), Hbid, Hlen; cbn [andb]; cbv iota.
             destruct str as [| st2 str1]; [reflexivity |].
             destruct st2; try discriminate.
             destruct (Nat.eqb bid0 bid1 && Nat.ltb idx0 len) eqn:Hk;
               cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
             destruct (nth_error elems (off + idx0)) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
             destruct (Nat.eq_dec idx (off + idx0)) as [Heq | Hneq].
             ++ rewrite Heq in *.
                rewrite (list_set_nth_same elems (off + idx0) ev' elems' Hls).
                rewrite He in He0. inversion He0; subst.
                eapply IH; [| exact Hwev | exact Hv]; lia.
             ++ rewrite (list_set_nth_other elems idx (off + idx0) ev' elems' Hneq Hls).
                rewrite He0. exact Hv.
        * (* SSlice *)
          destruct (Nat.leb (off + len) (length elems)) eqn:Hbound; [| discriminate].
          destruct rest as [| s' rest'].
          -- destruct (write_slice_fill elems 0 off len n0) as [elems' |] eqn:Hfill;
               cbn in Hw; [| discriminate].
             inversion Hw; subst; clear Hw.
             destruct st1; cbn [valid_stamps] in *; try discriminate.
             ++ destruct (Nat.eqb bid0 bid) eqn:Ebid; cbv iota in Hv; [| discriminate].
                destruct (nth_error elems idx) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
                assert (Hlen' : length elems' = length elems) by (eapply write_slice_fill_length; eauto).
                destruct (Nat.lt_ge_cases idx off) as [Hlt | Hge];
                  [| destruct (Nat.lt_ge_cases idx (off + len)) as [Hin | Hout]].
                ** rewrite (write_slice_fill_outside elems 0 off len n0 elems' idx Hfill) by lia.
                   rewrite He0. exact Hv.
                ** destruct (nth_error elems' idx) as [ev' |] eqn:He'.
                   { clear Hlen'.
                     pose proof (write_slice_fill_inside elems 0 off len n0 elems' idx ev0 ev'
                       Hfill ltac:(lia) ltac:(lia) He0 He') as [m1 [m2 [-> ->]]].
                     destruct str as [| st2 str1]; [reflexivity | destruct st2; cbn in Hv; discriminate]. }
                   { apply nth_error_None in He'.
                     assert (idx < length elems) by (apply nth_error_Some; congruence). lia. }
                ** rewrite (write_slice_fill_outside elems 0 off len n0 elems' idx Hfill) by lia.
                   rewrite He0. exact Hv.
             ++ destruct (Nat.eqb bid0 bid && Nat.leb (off0 + len0) (length elems)) eqn:Hb;
                  cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
                apply andb_true_iff in Hb as [Hbid Hlen_sl].
                rewrite (write_slice_fill_length elems 0 off len n0 elems' Hfill), Hbid, Hlen_sl;
                  cbn [andb]; cbv iota.
                destruct str as [| st2 str1]; [reflexivity |].
                destruct st2; try discriminate.
                destruct (Nat.eqb bid0 bid1 && Nat.ltb idx len0) eqn:Hk;
                  cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
                destruct (nth_error elems (off0 + idx)) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
                destruct (Nat.lt_ge_cases (off0 + idx) off) as [Hlt | Hge];
                  [| destruct (Nat.lt_ge_cases (off0 + idx) (off + len)) as [Hin | Hout]].
                ** rewrite (write_slice_fill_outside elems 0 off len n0 elems' (off0 + idx) Hfill) by lia.
                   rewrite He0. exact Hv.
                ** destruct (nth_error elems' (off0 + idx)) as [ev' |] eqn:He'.
                   { pose proof (write_slice_fill_inside elems 0 off len n0 elems' (off0 + idx) ev0 ev'
                       Hfill ltac:(lia) ltac:(lia) He0 He') as [m1 [m2 [-> ->]]].
                     destruct str1 as [| st3 str2]; [reflexivity | destruct st3; cbn in Hv; discriminate]. }
                   { apply nth_error_None in He'.
                     assert (Hlen' : length elems' = length elems) by (eapply write_slice_fill_length; eauto).
                     assert (off0 + idx < length elems) by (apply nth_error_Some; congruence). lia. }
                ** rewrite (write_slice_fill_outside elems 0 off len n0 elems' (off0 + idx) Hfill) by lia.
                   rewrite He0. exact Hv.
          -- destruct s'; try discriminate.
             destruct (Nat.ltb idx len) eqn:Hk; [| discriminate].
             destruct (nth_error elems (off + idx)) as [ev |] eqn:He; [| discriminate].
             destruct (write_stable_val ev rest' n0) as [ev' |] eqn:Hwev; [| discriminate].
             destruct (list_set elems (off + idx) ev') as [elems' |] eqn:Hls;
               cbn in Hw; [| discriminate].
             inversion Hw; subst; clear Hw.
             destruct st1; cbn [valid_stamps] in *; try discriminate.
             ++ destruct (Nat.eqb bid0 bid) eqn:Ebid; cbv iota in Hv; [| discriminate].
                destruct (nth_error elems idx0) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
                destruct (Nat.eq_dec (off + idx) idx0) as [Heq | Hneq].
                ** rewrite <- Heq in *.
                   rewrite (list_set_nth_same elems (off + idx) ev' elems' Hls).
                   rewrite He in He0. inversion He0; subst.
                   eapply IH; [| exact Hwev | exact Hv]; cbn in Hlen0; lia.
                ** rewrite (list_set_nth_other elems (off + idx) idx0 ev' elems' Hneq Hls).
                   rewrite He0. exact Hv.
             ++ destruct (Nat.eqb bid0 bid && Nat.leb (off0 + len0) (length elems)) eqn:Hb;
                  cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
                apply andb_true_iff in Hb as [Hbid Hlen].
                rewrite (list_set_length elems (off + idx) ev' elems' Hls), Hbid, Hlen;
                  cbn [andb]; cbv iota.
                destruct str as [| st2 str1]; [reflexivity |].
                destruct st2; try discriminate.
                destruct (Nat.eqb bid0 bid1 && Nat.ltb idx0 len0) eqn:Hk0;
                  cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
                destruct (nth_error elems (off0 + idx0)) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
                destruct (Nat.eq_dec (off + idx) (off0 + idx0)) as [Heq | Hneq].
                ** rewrite <- Heq in *.
                   rewrite (list_set_nth_same elems (off + idx) ev' elems' Hls).
                   rewrite He in He0. inversion He0; subst.
                   eapply IH; [| exact Hwev | exact Hv]; cbn in Hlen0; lia.
                ** rewrite (list_set_nth_other elems (off + idx) (off0 + idx0) ev' elems' Hneq Hls).
                   rewrite He0. exact Hv.
        * (* SCell2D *)
          destruct rest; [| discriminate].
          destruct (Nat.ltb r rows && Nat.ltb c cols); [| discriminate].
          inversion Hw; subst; clear Hw.
          destruct st1, str; cbn [valid_stamps] in *; try discriminate; exact Hv.
        * (* SUnionPayload *)
          destruct (write_stable_val v0 rest n0) as [p' |] eqn:Hwp;
            cbn in Hw; [| discriminate].
          inversion Hw; subst; clear Hw.
          destruct st1; cbn [valid_stamps] in *; try discriminate.
          destruct (Nat.eqb utag0 utag && Nat.eqb pbid0 pbid);
            cbn [andb valid_stamps] in *; [| discriminate].
          eapply IH; [| exact Hwp | exact Hv]; lia. }
  eapply Haux; eauto.
Qed.

(* ================================================================= *)
(* 4. Disjoint Write Frame Preservation                              *)
(* ================================================================= *)

Lemma write_stable_val_frame : forall v s1 s2 n v',
  steps_disjoint_b s1 s2 = true ->
  write_stable_val v s1 n = Some v' ->
  read_val v' s2 = read_val v s2.
Proof.
  intros v s1 s2 n v' Hdisj0 Hw0.
  assert (Haux : forall k s1 v s2 n v',
    length s1 <= k ->
    steps_disjoint_b s1 s2 = true ->
    write_stable_val v s1 n = Some v' ->
    read_val v' s2 = read_val v s2).
  { induction k as [| k' IH]; intros [| a r1] v0 [| b r2] n0 v0' Hlen0 Hdisj Hw;
      cbn [steps_disjoint_b length] in *; try discriminate; try lia.
    destruct a, b, v0; cbn [steps_disjoint_b step_disjoint_b proj_step_beq
      write_stable_val option_map] in Hdisj, Hw; try discriminate.
    - (* SField vs SField *)
      destruct (Nat.eqb f f0) eqn:Ef.
      + cbn [negb] in Hdisj; cbv iota in Hdisj.
        apply Nat.eqb_eq in Ef; subst f0.
        destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (write_stable_val fv r1 n0) as [fv' |] eqn:Hwfv; [| discriminate].
        destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f fv' fs' Hup), Hf.
        eapply IH; [| exact Hdisj | exact Hwfv]; lia.
      + cbn in Hdisj. apply Nat.eqb_neq in Ef.
        destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (write_stable_val fv r1 n0) as [fv' |] eqn:Hwfv; [| discriminate].
        destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 fv' fs' Ef Hup).
        reflexivity.
    - (* SElem vs SElem *)
      destruct (Nat.eqb idx idx0) eqn:Ei.
      + cbn [negb] in Hdisj; cbv iota in Hdisj.
        apply Nat.eqb_eq in Ei; subst idx0.
        destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (write_stable_val ev r1 n0) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (list_set_nth_same elems idx ev' elems' Hls), He.
        eapply IH; [| exact Hdisj | exact Hwev]; lia.
      + cbn in Hdisj. apply Nat.eqb_neq in Ei.
        destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (write_stable_val ev r1 n0) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (list_set_nth_other elems idx idx0 ev' elems' Ei Hls).
        reflexivity.
    - (* SElem vs SSlice *)
      destruct (Nat.ltb idx off || Nat.leb (off + len) idx) eqn:Hsep;
        [| cbv iota in Hdisj; discriminate].
      apply orb_true_iff in Hsep.
      destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
      destruct (write_stable_val ev r1 n0) as [ev' |] eqn:Hwev; [| discriminate].
      destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
        cbn in Hw; [| discriminate].
      inversion Hw; subst; clear Hw; cbn [read_val].
      rewrite (list_set_length elems idx ev' elems' Hls).
      destruct (Nat.leb (off + len) (length elems)) eqn:Hb; [| reflexivity].
      assert (Hout : idx < off \/ off + len <= idx).
      { destruct Hsep as [H1 | H2].
        - left. now apply Nat.ltb_lt.
        - right. now apply Nat.leb_le. }
      destruct r2 as [| s2' r2'].
      + f_equal. f_equal.
        apply firstn_skipn_ext; [eapply list_set_length; eauto |].
        intros j Hj1 Hj2.
        apply list_set_nth_other with (i := idx) (v := ev'); [lia | exact Hls].
      + destruct s2'; try reflexivity.
        destruct (Nat.ltb idx0 len) eqn:Hk; [| reflexivity].
        apply Nat.ltb_lt in Hk.
        rewrite (list_set_nth_other elems idx (off + idx0) ev' elems'); [reflexivity | lia | exact Hls].
    - (* SSlice vs SElem *)
      destruct (Nat.ltb idx off || Nat.leb (off + len) idx) eqn:Hsep;
        [| cbv iota in Hdisj; discriminate].
      apply orb_true_iff in Hsep.
      assert (Hout : idx < off \/ off + len <= idx).
      { destruct Hsep as [H1 | H2]; [left; now apply Nat.ltb_lt | right; now apply Nat.leb_le]. }
      destruct (Nat.leb (off + len) (length elems)) eqn:Hb; [| discriminate].
      destruct r1 as [| s1' r1'].
      + destruct (write_slice_fill elems 0 off len n0) as [elems' |] eqn:Hfill;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (write_slice_fill_outside elems 0 off len n0 elems' idx Hfill) by lia.
        reflexivity.
      + destruct s1'; try discriminate.
        destruct (Nat.ltb idx0 len) eqn:Hk; [| discriminate].
        apply Nat.ltb_lt in Hk.
        destruct (nth_error elems (off + idx0)) as [ev |] eqn:He; [| discriminate].
        destruct (write_stable_val ev r1' n0) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems (off + idx0) ev') as [elems' |] eqn:Hls;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (list_set_nth_other elems (off + idx0) idx ev' elems'); [reflexivity | lia | exact Hls].
    - (* SSlice vs SSlice *)
      destruct (Nat.leb (off + len) off0 || Nat.leb (off0 + len0) off) eqn:Hsep.
      + apply orb_true_iff in Hsep.
        assert (Hdisj_int : off + len <= off0 \/ off0 + len0 <= off).
        { destruct Hsep as [H1 | H2]; [left; now apply Nat.leb_le | right; now apply Nat.leb_le]. }
        destruct (Nat.leb (off + len) (length elems)) eqn:Hb; [| discriminate].
        destruct r1 as [| s1' r1'].
        * destruct (write_slice_fill elems 0 off len n0) as [elems' |] eqn:Hfill;
            cbn in Hw; [| discriminate].
          inversion Hw; subst; clear Hw; cbn [read_val].
          rewrite (write_slice_fill_length elems 0 off len n0 elems' Hfill).
          destruct (Nat.leb (off0 + len0) (length elems)) eqn:Hb0; [| reflexivity].
          destruct r2 as [| s2' r2'].
          -- f_equal. f_equal.
             apply firstn_skipn_ext; [eapply write_slice_fill_length; eauto |].
             intros j Hj1 Hj2.
             eapply write_slice_fill_outside; [exact Hfill | lia].
          -- destruct s2'; try reflexivity.
             destruct (Nat.ltb idx len0) eqn:Hk; [| reflexivity].
             apply Nat.ltb_lt in Hk.
             rewrite (write_slice_fill_outside elems 0 off len n0 elems' (off0 + idx) Hfill) by lia.
             reflexivity.
        * destruct s1'; try discriminate.
          destruct (Nat.ltb idx len) eqn:Hk; [| discriminate].
          apply Nat.ltb_lt in Hk.
          destruct (nth_error elems (off + idx)) as [ev |] eqn:He; [| discriminate].
          destruct (write_stable_val ev r1' n0) as [ev' |] eqn:Hwev; [| discriminate].
          destruct (list_set elems (off + idx) ev') as [elems' |] eqn:Hls;
            cbn in Hw; [| discriminate].
          inversion Hw; subst; clear Hw; cbn [read_val].
          rewrite (list_set_length elems (off + idx) ev' elems' Hls).
          destruct (Nat.leb (off0 + len0) (length elems)) eqn:Hb0; [| reflexivity].
          destruct r2 as [| s2' r2'].
          -- f_equal. f_equal.
             apply firstn_skipn_ext; [eapply list_set_length; eauto |].
             intros j Hj1 Hj2.
             apply list_set_nth_other with (i := off + idx) (v := ev'); [lia | exact Hls].
          -- destruct s2'; try reflexivity.
             destruct (Nat.ltb idx0 len0) eqn:Hk0; [| reflexivity].
             apply Nat.ltb_lt in Hk0.
             rewrite (list_set_nth_other elems (off + idx) (off0 + idx0) ev' elems');
               [reflexivity | lia | exact Hls].
      + cbv iota in Hdisj.
        destruct (Nat.eqb off off0 && Nat.eqb len len0) eqn:Eeq; cbn [andb] in Hdisj; cbv iota in Hdisj; [| discriminate].
        apply andb_true_iff in Eeq as [Eo El].
        apply Nat.eqb_eq in Eo; apply Nat.eqb_eq in El; subst off0 len0.
        destruct (Nat.leb (off + len) (length elems)) eqn:Hb; [| discriminate].
        destruct r1 as [| s1' r1']; [discriminate |].
        destruct s1'; try discriminate.
        destruct (Nat.ltb idx len) eqn:Hk; [| discriminate].
        destruct (nth_error elems (off + idx)) as [ev |] eqn:He; [| discriminate].
        destruct (write_stable_val ev r1' n0) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems (off + idx) ev') as [elems' |] eqn:Hls;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw; cbn [read_val].
        rewrite (list_set_length elems (off + idx) ev' elems' Hls), Hb.
        destruct r2 as [| s2' r2']; [cbn in Hdisj; discriminate |].
        destruct s2'; try reflexivity.
        destruct (Nat.ltb idx0 len) eqn:Hk0; [| reflexivity].
        destruct (Nat.eq_dec idx idx0) as [-> | Hneq].
        * cbn [steps_disjoint_b step_disjoint_b proj_step_beq negb] in Hdisj.
          rewrite Nat.eqb_refl in Hdisj; cbn in Hdisj.
          rewrite (list_set_nth_same elems (off + idx0) ev' elems' Hls), He.
          eapply IH; [| exact Hdisj | exact Hwev]; cbn in Hlen0; lia.
        * rewrite (list_set_nth_other elems (off + idx) (off + idx0) ev' elems');
            [reflexivity | lia | exact Hls].
    - (* SCell2D vs SCell2D *)
      destruct r1; [| discriminate].
      destruct r2; [| destruct (Nat.ltb r rows && Nat.ltb c cols); try discriminate;
                      inversion Hw; subst; reflexivity].
      cbn in Hdisj.
      destruct (Nat.ltb r rows && Nat.ltb c cols) eqn:Hb; [| discriminate].
      inversion Hw; subst; clear Hw; cbn [read_val].
      destruct (Nat.ltb r0 rows && Nat.ltb c0 cols) eqn:Hb0; [| reflexivity].
      assert (Hrc : (r, c) <> (r0, c0)).
      { intro Heq. inversion Heq; subst r0 c0.
        rewrite !Nat.eqb_refl in Hdisj. discriminate. }
      rewrite (assoc_get_set_other cell_beq cell_beq_eq cells (r, c) (r0, c0) n0 Hrc).
      reflexivity.
    - (* SUnionPayload vs SUnionPayload *)
      cbn in Hdisj.
      destruct (write_stable_val v0 r1 n0) as [p' |] eqn:Hwp;
        cbn in Hw; [| discriminate].
      inversion Hw; subst; clear Hw; cbn [read_val].
      eapply IH; [| exact Hdisj | exact Hwp]; lia. }
  eapply Haux; eauto.
Qed.

Definition read_val_mem (m : memory) (p : place) : option owner_val :=
  match lookup_owner m (p_owner p) with
  | Some oe => read_val (oe_val oe) (p_path p)
  | None => None
  end.

Definition read_scalar_mem (m : memory) (p : place) : option nat :=
  match lookup_owner m (p_owner p) with
  | Some oe => read_scalar (oe_val oe) (p_path p)
  | None => None
  end.

Definition write_stable_mem (m : memory) (p : place) (n : nat) : option memory :=
  match lookup_owner m (p_owner p) with
  | Some oe =>
      match write_stable_val (oe_val oe) (p_path p) n with
      | Some v' => update_owner m (p_owner p) {| oe_borrowed := oe_borrowed oe; oe_val := v' |}
      | None => None
      end
  | None => None
  end.

Lemma write_stable_mem_preserves_addr : forall m p n m' a,
  write_stable_mem m p n = Some m' ->
  addr_valid m a ->
  addr_valid m' a.
Proof.
  intros m p n m' a Hw Ha.
  unfold write_stable_mem in Hw.
  destruct (lookup_owner m (p_owner p)) as [oe |] eqn:Ho; [| discriminate].
  destruct (write_stable_val (oe_val oe) (p_path p) n) as [v' |] eqn:Hv'; [| discriminate].
  unfold update_owner in Hw.
  unfold addr_valid, addr_valid_b in *.
  unfold lookup_owner in *.
  destruct (Nat.eq_dec (p_owner p) (addr_owner a)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner p)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hw).
    rewrite Ho in Ha. cbn in *.
    rewrite (write_stable_preserves_bid (oe_val oe) (p_path p) n v' Hv').
    destruct (val_bid (oe_val oe)) as [rbid |] eqn:Hrb; [| discriminate].
    apply andb_true_iff in Ha as [Hrbid Hst].
    rewrite Hrbid; cbn.
    eapply write_stable_preserves_stamps; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner p)
               (addr_owner a) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hw).
    exact Ha.
Qed.

Lemma write_stable_mem_frame : forall m p1 p2 n m',
  places_disjoint p1 p2 ->
  write_stable_mem m p1 n = Some m' ->
  read_val_mem m' p2 = read_val_mem m p2.
Proof.
  intros m p1 p2 n m' Hdisj Hw.
  unfold write_stable_mem in Hw.
  destruct (lookup_owner m (p_owner p1)) as [oe |] eqn:Ho; [| discriminate].
  destruct (write_stable_val (oe_val oe) (p_path p1) n) as [v' |] eqn:Hv'; [| discriminate].
  unfold update_owner in Hw.
  unfold read_val_mem, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner p1) (p_owner p2)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner p1)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hw).
    rewrite Ho; cbn.
    unfold places_disjoint, places_disjoint_b in Hdisj.
    rewrite <- Heq, Nat.eqb_refl in Hdisj; cbn in Hdisj.
    eapply write_stable_val_frame; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner p1)
               (p_owner p2) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hw).
    reflexivity.
Qed.

Lemma write_stable_mem_preserves_borrowed : forall m p n m' o oe,
  write_stable_mem m p n = Some m' ->
  lookup_owner m o = Some oe ->
  exists oe', lookup_owner m' o = Some oe' /\ oe_borrowed oe' = oe_borrowed oe.
Proof.
  intros m p n m' o oe Hw Ho.
  unfold write_stable_mem in Hw.
  destruct (lookup_owner m (p_owner p)) as [oe0 |] eqn:Ho0; [| discriminate].
  destruct (write_stable_val (oe_val oe0) (p_path p) n) as [v' |] eqn:Hv'; [| discriminate].
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner p) o) as [Heq | Hneq].
  - rewrite Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m o
               {| oe_borrowed := oe_borrowed oe0; oe_val := v' |} m' Hw).
    rewrite Ho in Ho0. inversion Ho0; subst. eexists; split; reflexivity.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner p)
               o {| oe_borrowed := oe_borrowed oe0; oe_val := v' |} m' Hneq Hw).
    rewrite Ho. eexists; split; reflexivity.
Qed.

(* ================================================================= *)
(* 5. Unstable Writes, Tag-Preserving Union, Capacity-Preserving Push*)
(* ================================================================= *)

Inductive unstable_kind : Type :=
| UClear
| UResize (new_cap : nat)
| URetag (new_tag : tag_id) (new_payload : owner_val)
| UDrop.

Fixpoint write_unstable_val (v : owner_val) (steps : list proj_step)
    (next_bid : backing_id) (kind : unstable_kind) : option owner_val :=
  match steps with
  | [] =>
      match kind with
      | UClear =>
          match v with
          | VContainer _ cap _ => Some (VContainer next_bid cap [])
          | _ => None
          end
      | UResize new_cap =>
          match v with
          | VContainer _ _ elems =>
              Some (VContainer next_bid new_cap (firstn new_cap elems))
          | _ => None
          end
      | URetag new_tag new_payload =>
          match v with
          | VUnion _ _ _ => Some (VUnion new_tag next_bid new_payload)
          | _ => None
          end
      | UDrop =>
          match v with
          | VMoved => None
          | _ => Some VMoved
          end
      end
  | SField f :: rest =>
      match v with
      | VRecord bid fs =>
          match assoc_get Nat.eqb fs f with
          | Some fv =>
              match write_unstable_val fv rest next_bid kind with
              | Some fv' => option_map (VRecord bid) (assoc_update Nat.eqb fs f fv')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SElem i :: rest =>
      match v with
      | VContainer bid cap elems =>
          match nth_error elems i with
          | Some ev =>
              match write_unstable_val ev rest next_bid kind with
              | Some ev' => option_map (VContainer bid cap) (list_set elems i ev')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SUnionPayload :: rest =>
      match v with
      | VUnion utag pbid p =>
          option_map (VUnion utag pbid) (write_unstable_val p rest next_bid kind)
      | _ => None
      end
  | _ => None
  end.

Fixpoint write_tag_preserving_val (v : owner_val) (steps : list proj_step)
    (expected_tag : tag_id) (new_payload : nat) : option owner_val :=
  match steps with
  | [] =>
      match v with
      | VUnion utag pbid (VScalar _) =>
          if Nat.eqb utag expected_tag then
            Some (VUnion utag pbid (VScalar new_payload))
          else None
      | _ => None
      end
  | SField f :: rest =>
      match v with
      | VRecord bid fs =>
          match assoc_get Nat.eqb fs f with
          | Some fv =>
              match write_tag_preserving_val fv rest expected_tag new_payload with
              | Some fv' => option_map (VRecord bid) (assoc_update Nat.eqb fs f fv')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SElem i :: rest =>
      match v with
      | VContainer bid cap elems =>
          match nth_error elems i with
          | Some ev =>
              match write_tag_preserving_val ev rest expected_tag new_payload with
              | Some ev' => option_map (VContainer bid cap) (list_set elems i ev')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SUnionPayload :: rest =>
      match v with
      | VUnion utag pbid p =>
          option_map (VUnion utag pbid)
            (write_tag_preserving_val p rest expected_tag new_payload)
      | _ => None
      end
  | _ => None
  end.

Lemma write_tag_preserving_bid : forall v steps tag payload v',
  write_tag_preserving_val v steps tag payload = Some v' ->
  val_bid v' = val_bid v.
Proof.
  intros v steps. revert v.
  induction steps as [| s rest IH]; intros v tag payload v' H;
    cbn [write_tag_preserving_val option_map] in H.
  - destruct v; try discriminate. destruct v; try discriminate.
    destruct (Nat.eqb utag tag); inversion H; reflexivity.
  - destruct s, v; cbn [write_tag_preserving_val option_map] in H; try discriminate.
    + destruct (assoc_get Nat.eqb fields f); [| discriminate].
      destruct (write_tag_preserving_val o rest tag payload); [| discriminate].
      destruct (assoc_update _ _ _ _); cbn in H; inversion H; reflexivity.
    + destruct (nth_error elems idx); [| discriminate].
      destruct (write_tag_preserving_val o rest tag payload); [| discriminate].
      destruct (list_set _ _ _); cbn in H; inversion H; reflexivity.
    + destruct (write_tag_preserving_val v rest tag payload); cbn in H; inversion H; reflexivity.
Qed.

Lemma write_tag_preserving_stamps : forall v steps tag payload v' st,
  write_tag_preserving_val v steps tag payload = Some v' ->
  valid_stamps v st = true ->
  valid_stamps v' st = true.
Proof.
  intros v steps. revert v.
  induction steps as [| s rest IH]; intros v tag payload v' st Hw Hv.
  - cbn [write_tag_preserving_val] in Hw. destruct v; try discriminate. destruct v; try discriminate.
    destruct (Nat.eqb utag tag); inversion Hw; subst; clear Hw.
    destruct st as [| st0 str]; [reflexivity |].
    destruct st0; cbn [valid_stamps] in *; try discriminate.
    destruct (Nat.eqb utag0 utag && Nat.eqb pbid0 pbid) eqn:Eu;
      cbn [andb valid_stamps] in *; cbv iota in *; [| discriminate].
    destruct str; [reflexivity | destruct s; cbn in Hv; discriminate].
  - destruct st as [| st0 str].
    + destruct v' eqn:Ev'; try reflexivity.
      exfalso. apply write_tag_preserving_bid in Hw.
      cbn in Hw, Hv. destruct v; discriminate.
    + destruct s, v; cbn [write_tag_preserving_val option_map] in Hw; try discriminate.
      * destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (write_tag_preserving_val fv rest tag payload) as [fv' |] eqn:Hwfv; [| discriminate].
        destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw.
        destruct st0; cbn [valid_stamps] in *; try discriminate.
        destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
        destruct (assoc_get Nat.eqb fields f0) as [fv0 |] eqn:Hf0; cbv iota in Hv; [| discriminate].
        destruct (Nat.eq_dec f f0) as [-> | Hneq].
        -- rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f0 fv' fs' Hup).
           rewrite Hf in Hf0; inversion Hf0; subst. eapply IH; eauto.
        -- rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 fv' fs' Hneq Hup).
           rewrite Hf0; exact Hv.
      * destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (write_tag_preserving_val ev rest tag payload) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw.
        destruct st0; cbn [valid_stamps] in *; try discriminate.
        -- destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
           destruct (nth_error elems idx0) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
           destruct (Nat.eq_dec idx idx0) as [-> | Hneq].
           ++ rewrite (list_set_nth_same elems idx0 ev' elems' Hls).
              rewrite He in He0; inversion He0; subst. eapply IH; eauto.
           ++ rewrite (list_set_nth_other elems idx idx0 ev' elems' Hneq Hls).
              rewrite He0; exact Hv.
        -- destruct (Nat.eqb bid0 bid && Nat.leb (off + len) (length elems)) eqn:Hb;
             cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
           apply andb_true_iff in Hb as [Hbid Hlen].
           rewrite (list_set_length elems idx ev' elems' Hls), Hbid, Hlen; cbn [andb]; cbv iota.
           destruct str as [| st1 str1]; [reflexivity |].
           destruct st1; try discriminate.
           destruct (Nat.eqb bid0 bid1 && Nat.ltb idx0 len);
             cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
           destruct (nth_error elems (off + idx0)) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
           destruct (Nat.eq_dec idx (off + idx0)) as [Heq | Hneq].
           ++ rewrite Heq in *.
              rewrite (list_set_nth_same elems (off + idx0) ev' elems' Hls).
              rewrite He in He0; inversion He0; subst. eapply IH; eauto.
           ++ rewrite (list_set_nth_other elems idx (off + idx0) ev' elems' Hneq Hls).
              rewrite He0; exact Hv.
      * destruct (write_tag_preserving_val v rest tag payload) as [p' |] eqn:Hwp;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw.
        destruct st0; cbn [valid_stamps] in *; try discriminate.
        destruct (Nat.eqb utag0 utag && Nat.eqb pbid0 pbid);
          cbn [andb valid_stamps] in *; [| discriminate].
        eapply IH; eauto.
Qed.

Fixpoint push_cap_preserving_val (v : owner_val) (steps : list proj_step)
    (new_elem : owner_val) : option owner_val :=
  match steps with
  | [] =>
      match v with
      | VContainer bid cap elems =>
          if Nat.ltb (length elems) cap then
            Some (VContainer bid cap (elems ++ [new_elem]))
          else None
      | _ => None
      end
  | SField f :: rest =>
      match v with
      | VRecord bid fs =>
          match assoc_get Nat.eqb fs f with
          | Some fv =>
              match push_cap_preserving_val fv rest new_elem with
              | Some fv' => option_map (VRecord bid) (assoc_update Nat.eqb fs f fv')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SElem i :: rest =>
      match v with
      | VContainer bid cap elems =>
          match nth_error elems i with
          | Some ev =>
              match push_cap_preserving_val ev rest new_elem with
              | Some ev' => option_map (VContainer bid cap) (list_set elems i ev')
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SUnionPayload :: rest =>
      match v with
      | VUnion utag pbid p =>
          option_map (VUnion utag pbid) (push_cap_preserving_val p rest new_elem)
      | _ => None
      end
  | _ => None
  end.

Lemma push_cap_preserving_bid : forall v steps elem v',
  push_cap_preserving_val v steps elem = Some v' ->
  val_bid v' = val_bid v.
Proof.
  intros v steps. revert v.
  induction steps as [| s rest IH]; intros v elem v' H;
    cbn [push_cap_preserving_val option_map] in H.
  - destruct v; try discriminate.
    destruct (Nat.ltb (length elems) cap); inversion H; reflexivity.
  - destruct s, v; cbn [push_cap_preserving_val option_map] in H; try discriminate.
    + destruct (assoc_get Nat.eqb fields f); [| discriminate].
      destruct (push_cap_preserving_val o rest elem); [| discriminate].
      destruct (assoc_update _ _ _ _); cbn in H; inversion H; reflexivity.
    + destruct (nth_error elems idx); [| discriminate].
      destruct (push_cap_preserving_val o rest elem); [| discriminate].
      destruct (list_set _ _ _); cbn in H; inversion H; reflexivity.
    + destruct (push_cap_preserving_val v rest elem); cbn in H; inversion H; reflexivity.
Qed.

Lemma nth_error_app_lt : forall {A : Type} (xs ys : list A) i,
  i < length xs -> nth_error (xs ++ ys) i = nth_error xs i.
Proof.
  intros A xs ys i H. now apply nth_error_app1.
Qed.

Lemma push_cap_preserving_stamps : forall v steps elem v' st,
  push_cap_preserving_val v steps elem = Some v' ->
  valid_stamps v st = true ->
  valid_stamps v' st = true.
Proof.
  intros v steps. revert v.
  induction steps as [| s rest IH]; intros v elem v' st Hw Hv.
  - cbn [push_cap_preserving_val] in Hw. destruct v; try discriminate.
    destruct (Nat.ltb (length elems) cap); inversion Hw; subst; clear Hw.
    destruct st as [| st0 str]; [reflexivity |].
    destruct st0; cbn [valid_stamps] in *; try discriminate.
    + destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
      destruct (nth_error elems idx) as [ev |] eqn:He; cbv iota in Hv; [| discriminate].
      assert (Hlt : idx < length elems) by (apply nth_error_Some; congruence).
      rewrite nth_error_app1 by exact Hlt. rewrite He. exact Hv.
    + destruct (Nat.eqb bid0 bid) eqn:Ebid;
        cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
      destruct (Nat.leb (off + len) (length elems)) eqn:Hlen;
        cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
      rewrite length_app; cbn [length].
      apply Nat.leb_le in Hlen.
      assert (Hlen' : Nat.leb (off + len) (length elems + 1) = true) by (apply Nat.leb_le; lia).
      rewrite Hlen'; cbn [andb]; cbv iota.
      destruct str as [| st1 str1]; [reflexivity |].
      destruct st1; try discriminate.
      destruct (Nat.eqb bid0 bid1 && Nat.ltb idx len) eqn:Hk;
        cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
      apply andb_true_iff in Hk as [Hbid1 Hk].
      apply Nat.ltb_lt in Hk.
      destruct (nth_error elems (off + idx)) as [ev |] eqn:He; cbv iota in Hv; [| discriminate].
      assert (Hlt : off + idx < length elems) by (apply nth_error_Some; congruence).
      rewrite nth_error_app1 by exact Hlt. rewrite He. exact Hv.
  - destruct st as [| st0 str].
    + destruct v' eqn:Ev'; try reflexivity.
      exfalso. apply push_cap_preserving_bid in Hw.
      cbn in Hw, Hv. destruct v; discriminate.
    + destruct s, v; cbn [push_cap_preserving_val option_map] in Hw; try discriminate.
      * destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (push_cap_preserving_val fv rest elem) as [fv' |] eqn:Hwfv; [| discriminate].
        destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw.
        destruct st0; cbn [valid_stamps] in *; try discriminate.
        destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
        destruct (assoc_get Nat.eqb fields f0) as [fv0 |] eqn:Hf0; cbv iota in Hv; [| discriminate].
        destruct (Nat.eq_dec f f0) as [-> | Hneq].
        -- rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f0 fv' fs' Hup).
           rewrite Hf in Hf0; inversion Hf0; subst. eapply IH; eauto.
        -- rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 fv' fs' Hneq Hup).
           rewrite Hf0; exact Hv.
      * destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (push_cap_preserving_val ev rest elem) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw.
        destruct st0; cbn [valid_stamps] in *; try discriminate.
        -- destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
           destruct (nth_error elems idx0) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
           destruct (Nat.eq_dec idx idx0) as [-> | Hneq].
           ++ rewrite (list_set_nth_same elems idx0 ev' elems' Hls).
              rewrite He in He0; inversion He0; subst. eapply IH; eauto.
           ++ rewrite (list_set_nth_other elems idx idx0 ev' elems' Hneq Hls).
              rewrite He0; exact Hv.
        -- destruct (Nat.eqb bid0 bid && Nat.leb (off + len) (length elems)) eqn:Hb;
             cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
           apply andb_true_iff in Hb as [Hbid Hlen].
           rewrite (list_set_length elems idx ev' elems' Hls), Hbid, Hlen; cbn [andb]; cbv iota.
           destruct str as [| st1 str1]; [reflexivity |].
           destruct st1; try discriminate.
           destruct (Nat.eqb bid0 bid1 && Nat.ltb idx0 len);
             cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
           destruct (nth_error elems (off + idx0)) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
           destruct (Nat.eq_dec idx (off + idx0)) as [Heq | Hneq].
           ++ rewrite Heq in *.
              rewrite (list_set_nth_same elems (off + idx0) ev' elems' Hls).
              rewrite He in He0; inversion He0; subst. eapply IH; eauto.
           ++ rewrite (list_set_nth_other elems idx (off + idx0) ev' elems' Hneq Hls).
              rewrite He0; exact Hv.
      * destruct (push_cap_preserving_val v rest elem) as [p' |] eqn:Hwp;
          cbn in Hw; [| discriminate].
        inversion Hw; subst; clear Hw.
        destruct st0; cbn [valid_stamps] in *; try discriminate.
        destruct (Nat.eqb utag0 utag && Nat.eqb pbid0 pbid);
          cbn [andb valid_stamps] in *; [| discriminate].
        eapply IH; eauto.
Qed.

(* ================================================================= *)
(* 6. Loans, Refinements, Polonius Origin Flow, and Small-Step State *)
(* ================================================================= *)

Inductive loan_mode : Type :=
| LShared
| LExclusive
| LSharedMut
| LReserved.

Definition loan_mode_beq (m1 m2 : loan_mode) : bool :=
  match m1, m2 with
  | LShared, LShared => true
  | LExclusive, LExclusive => true
  | LSharedMut, LSharedMut => true
  | LReserved, LReserved => true
  | _, _ => false
  end.

Lemma loan_mode_beq_eq : forall m1 m2, loan_mode_beq m1 m2 = true <-> m1 = m2.
Proof.
  intros m1 m2; destruct m1, m2; cbn; split; intro H; try reflexivity; discriminate.
Qed.

Record loan_entry := {
  ln_id : loan_id;
  ln_origin : origin_id;
  ln_parent : option loan_id;
  ln_root_loan : loan_id;
  ln_place : place;
  ln_addr : place_addr;
  ln_mode : loan_mode;
  ln_suspended : bool;
  ln_returned : bool;
}.

Definition loan_active (le : loan_entry) : bool :=
  negb (ln_suspended le) && negb (ln_returned le).

Definition loan_live (le : loan_entry) : bool :=
  negb (ln_returned le).

Inductive content_fact : Type :=
| FEquals (v : nat)
| FNonZero
| FInRange (lo hi : nat).

Definition fact_holds (m : memory) (p : place) (cf : content_fact) : Prop :=
  match cf with
  | FEquals v => read_scalar_mem m p = Some v
  | FNonZero => exists v, read_scalar_mem m p = Some v /\ v <> 0
  | FInRange lo hi => exists v, read_scalar_mem m p = Some v /\ lo <= v /\ v < hi
  end.

Definition fact_holds_b (m : memory) (p : place) (cf : content_fact) : bool :=
  match read_scalar_mem m p with
  | None => false
  | Some v =>
      match cf with
      | FEquals v0 => Nat.eqb v v0
      | FNonZero => negb (Nat.eqb v 0)
      | FInRange lo hi => Nat.leb lo v && Nat.ltb v hi
      end
  end.

Lemma fact_holds_b_sound : forall m p cf,
  fact_holds_b m p cf = true -> fact_holds m p cf.
Proof.
  intros m p cf H. unfold fact_holds_b, fact_holds in *.
  destruct (read_scalar_mem m p) as [v |] eqn:Hr; [| discriminate].
  destruct cf; cbn in *.
  - apply Nat.eqb_eq in H. congruence.
  - apply negb_true_iff, Nat.eqb_neq in H. eauto.
  - apply andb_true_iff in H as [Hlo Hhi].
    apply Nat.leb_le in Hlo. apply Nat.ltb_lt in Hhi. eauto.
Qed.

Definition ref_store := list (fact_id * (place * content_fact)).

Definition invalidate_overlapping_refs (wp : place) (refs : ref_store) : ref_store :=
  filter (fun entry => places_disjoint_b wp (fst (snd entry))) refs.

Record machine_state := {
  st_mem : memory;
  st_loans : list loan_entry;
  st_refs : ref_store;
  st_next_bid : backing_id;
}.

Definition lookup_loan (loans : list loan_entry) (l : loan_id) : option loan_entry :=
  find (fun le => Nat.eqb (ln_id le) l) loans.

Definition has_loan (loans : list loan_entry) (l : loan_id) : bool :=
  existsb (fun le => Nat.eqb (ln_id le) l) loans.

Definition has_live_child (loans : list loan_entry) (l : loan_id) : bool :=
  existsb (fun le =>
    loan_live le &&
    match ln_parent le with
    | Some pid => Nat.eqb pid l
    | None => false
    end) loans.

Definition set_loan_suspended (loans : list loan_entry) (l : loan_id) (susp : bool)
    : list loan_entry :=
  map (fun le =>
    if Nat.eqb (ln_id le) l then
      {| ln_id := ln_id le;
         ln_origin := ln_origin le;
         ln_parent := ln_parent le;
         ln_root_loan := ln_root_loan le;
         ln_place := ln_place le;
         ln_addr := ln_addr le;
         ln_mode := ln_mode le;
         ln_suspended := susp;
         ln_returned := ln_returned le |}
    else le) loans.

Definition set_loan_mode (loans : list loan_entry) (l : loan_id) (m : loan_mode)
    : list loan_entry :=
  map (fun le =>
    if Nat.eqb (ln_id le) l then
      {| ln_id := ln_id le;
         ln_origin := ln_origin le;
         ln_parent := ln_parent le;
         ln_root_loan := ln_root_loan le;
         ln_place := ln_place le;
         ln_addr := ln_addr le;
         ln_mode := m;
         ln_suspended := ln_suspended le;
         ln_returned := ln_returned le |}
    else le) loans.

Definition set_loan_returned (loans : list loan_entry) (l : loan_id) : list loan_entry :=
  map (fun le =>
    if Nat.eqb (ln_id le) l then
      {| ln_id := ln_id le;
         ln_origin := ln_origin le;
         ln_parent := ln_parent le;
         ln_root_loan := ln_root_loan le;
         ln_place := ln_place le;
         ln_addr := ln_addr le;
         ln_mode := ln_mode le;
         ln_suspended := ln_suspended le;
         ln_returned := true |}
    else le) loans.

Definition remove_loan (loans : list loan_entry) (l : loan_id) : list loan_entry :=
  filter (fun le => negb (Nat.eqb (ln_id le) l)) loans.

Definition option_nat_eqb (a b : option nat) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => Nat.eqb x y
  | _, _ => false
  end.

Definition borrow_compatible (new_mode : loan_mode) (parent : option loan_id)
    (p : place) (other : loan_entry) : bool :=
  if option_nat_eqb parent (Some (ln_id other)) then true
  else if negb (loan_active other) then true
  else if places_disjoint_b p (ln_place other) then true
  else match new_mode, ln_mode other with
       | LShared, LShared => true
       | LShared, LSharedMut => true
       | LShared, LReserved => true
       | LSharedMut, LShared => true
       | LSharedMut, LSharedMut => true
       | LReserved, LShared => true
       | LReserved, LSharedMut => true
       | _, _ => false
       end.

Definition can_borrow_from_parent (new_mode : loan_mode) (parent_mode : loan_mode) : bool :=
  match new_mode, parent_mode with
  | LShared, LShared => true
  | LShared, LExclusive => true
  | LShared, LSharedMut => true
  | LSharedMut, LSharedMut => true
  | LSharedMut, LExclusive => true
  | LExclusive, LExclusive => true
  | LReserved, LExclusive => true
  | _, _ => false
  end.

Definition direct_read_ok (p : place) (loans : list loan_entry) : bool :=
  forallb (fun le =>
    if negb (loan_active le) then true
    else if places_disjoint_b p (ln_place le) then true
    else match ln_mode le with
         | LShared | LSharedMut | LReserved => true
         | LExclusive => false
         end) loans.

Definition direct_write_ok (p : place) (loans : list loan_entry) : bool :=
  forallb (fun le =>
    if negb (loan_live le) then true
    else places_disjoint_b p (ln_place le)) loans.

Definition no_overlapping_exclusive_or_reserved (p : place) (except_id : option loan_id)
    (loans : list loan_entry) : bool :=
  forallb (fun le =>
    if option_nat_eqb except_id (Some (ln_id le)) then true
    else if negb (loan_active le) then true
    else if places_disjoint_b p (ln_place le) then true
    else match ln_mode le with
         | LShared | LSharedMut => true
         | LExclusive | LReserved => false
         end) loans.

Definition no_overlapping_loan_at (p : place) (loans : list loan_entry) : bool :=
  forallb (fun le =>
    if negb (loan_live le) then true
    else places_disjoint_b p (ln_place le)) loans.

(* ================================================================= *)
(* 7. Step Operations and Small-Step Semantics                       *)
(* ================================================================= *)

Inductive step_op : Type :=
| OpBorrow (l : loan_id) (orig : origin_id) (parent : option loan_id)
    (p : place) (mode : loan_mode)
| OpReserve (l : loan_id) (orig : origin_id) (parent : option loan_id) (p : place)
| OpActivate (l : loan_id)
| OpCancelReservation (l : loan_id)
| OpRead (p : place) (via : option loan_id)
| OpStableWrite (p : place) (via : option loan_id) (v : nat)
| OpUnstableWrite (p : place) (kind : unstable_kind)
| OpTagPreservingUnionWrite (pu : place) (via : option loan_id)
    (expected_tag : tag_id) (new_payload : nat)
| OpCapPreservingPush (pc : place) (via : option loan_id) (new_elem : owner_val)
| OpEndLoan (l : loan_id)
| OpReturnLoan (l : loan_id)
| OpLoopStep (cursor_id new_cursor_id : loan_id) (orig : origin_id) (sub_place : place)
| OpAssumeRefinement (fid : fact_id) (p : place) (cf : content_fact)
| OpUseRefinement (fid : fact_id)
| OpDropRefinement (fid : fact_id).

Definition write_unstable_mem (m : memory) (p : place) (next_bid : backing_id)
    (kind : unstable_kind) : option memory :=
  match lookup_owner m (p_owner p) with
  | Some oe =>
      match write_unstable_val (oe_val oe) (p_path p) next_bid kind with
      | Some v' => update_owner m (p_owner p) {| oe_borrowed := oe_borrowed oe; oe_val := v' |}
      | None => None
      end
  | None => None
  end.

Definition write_tag_preserving_mem (m : memory) (pu : place) (expected_tag : tag_id)
    (new_payload : nat) : option memory :=
  match lookup_owner m (p_owner pu) with
  | Some oe =>
      match write_tag_preserving_val (oe_val oe) (p_path pu) expected_tag new_payload with
      | Some v' => update_owner m (p_owner pu) {| oe_borrowed := oe_borrowed oe; oe_val := v' |}
      | None => None
      end
  | None => None
  end.

Definition push_cap_preserving_mem (m : memory) (pc : place) (new_elem : owner_val)
    : option (memory * nat) :=
  match lookup_owner m (p_owner pc) with
  | Some oe =>
      match read_val (oe_val oe) (p_path pc) with
      | Some (VContainer _ _ elems) =>
          match push_cap_preserving_val (oe_val oe) (p_path pc) new_elem with
          | Some v' =>
              match update_owner m (p_owner pc) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} with
              | Some m' => Some (m', length elems)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Definition exec_step (st : machine_state) (op : step_op) : option machine_state :=
  match op with
  | OpBorrow l orig parent p mode =>
      match mode with
      | LReserved => None
      | _ =>
          if has_loan (st_loans st) l then None
          else match resolve_addr (st_mem st) p with
               | None => None
               | Some addr =>
                   let parent_ok :=
                     match parent with
                     | None => Some l
                     | Some pid =>
                         match lookup_loan (st_loans st) pid with
                         | Some pe =>
                             if loan_active pe &&
                                negb (loan_mode_beq (ln_mode pe) LReserved) &&
                                within_b p (ln_place pe) &&
                                can_borrow_from_parent mode (ln_mode pe)
                             then Some (ln_root_loan pe)
                             else None
                         | None => None
                         end
                     end in
                   match parent_ok with
                   | None => None
                   | Some root_id =>
                       if forallb (borrow_compatible mode parent p) (st_loans st) then
                         let loans1 :=
                           match parent, mode with
                           | Some pid, LExclusive => set_loan_suspended (st_loans st) pid true
                           | _, _ => st_loans st
                           end in
                         let entry := {|
                           ln_id := l;
                           ln_origin := orig;
                           ln_parent := parent;
                           ln_root_loan := root_id;
                           ln_place := p;
                           ln_addr := addr;
                           ln_mode := mode;
                           ln_suspended := false;
                           ln_returned := false;
                         |} in
                         Some {| st_mem := st_mem st;
                                 st_loans := entry :: loans1;
                                 st_refs := st_refs st;
                                 st_next_bid := st_next_bid st |}
                       else None
                   end
               end
      end

  | OpReserve l orig parent p =>
      if has_loan (st_loans st) l then None
      else match resolve_addr (st_mem st) p with
           | None => None
           | Some addr =>
               let parent_ok :=
                 match parent with
                 | None => Some l
                 | Some pid =>
                     match lookup_loan (st_loans st) pid with
                     | Some pe =>
                         if loan_active pe &&
                            negb (loan_mode_beq (ln_mode pe) LReserved) &&
                            within_b p (ln_place pe) &&
                            can_borrow_from_parent LReserved (ln_mode pe)
                         then Some (ln_root_loan pe)
                         else None
                     | None => None
                     end
                 end in
               match parent_ok with
               | None => None
               | Some root_id =>
                   if forallb (borrow_compatible LReserved parent p) (st_loans st) then
                     let entry := {|
                       ln_id := l;
                       ln_origin := orig;
                       ln_parent := parent;
                       ln_root_loan := root_id;
                       ln_place := p;
                       ln_addr := addr;
                       ln_mode := LReserved;
                       ln_suspended := false;
                       ln_returned := false;
                     |} in
                     Some {| st_mem := st_mem st;
                             st_loans := entry :: st_loans st;
                             st_refs := st_refs st;
                             st_next_bid := st_next_bid st |}
                   else None
               end
           end

  | OpActivate l =>
      match lookup_loan (st_loans st) l with
      | None => None
      | Some le =>
          if loan_active le && loan_mode_beq (ln_mode le) LReserved &&
             addr_valid_b (st_mem st) (ln_addr le) then
            let compat := forallb (fun other =>
              if Nat.eqb (ln_id other) l then true
              else borrow_compatible LExclusive (ln_parent le) (ln_place le) other) (st_loans st) in
            if compat then
              let loans1 := set_loan_mode (st_loans st) l LExclusive in
              let loans2 :=
                match ln_parent le with
                | Some pid => set_loan_suspended loans1 pid true
                | None => loans1
                end in
              Some {| st_mem := st_mem st;
                      st_loans := loans2;
                      st_refs := st_refs st;
                      st_next_bid := st_next_bid st |}
            else None
          else None
      end

  | OpCancelReservation l =>
      match lookup_loan (st_loans st) l with
      | None => None
      | Some le =>
          if loan_active le && loan_mode_beq (ln_mode le) LReserved &&
             negb (has_live_child (st_loans st) l) then
            Some {| st_mem := st_mem st;
                    st_loans := remove_loan (st_loans st) l;
                    st_refs := st_refs st;
                    st_next_bid := st_next_bid st |}
          else None
      end

  | OpRead p via =>
      match via with
      | Some l =>
          match lookup_loan (st_loans st) l with
          | None => None
          | Some le =>
              if loan_active le &&
                 negb (loan_mode_beq (ln_mode le) LReserved) &&
                 within_b p (ln_place le) &&
                 addr_valid_b (st_mem st) (ln_addr le) then
                match read_scalar_mem (st_mem st) p with
                | Some _ => Some st
                | None => None
                end
              else None
          end
      | None =>
          if direct_read_ok p (st_loans st) then
            match read_scalar_mem (st_mem st) p with
            | Some _ => Some st
            | None => None
            end
          else None
      end

  | OpStableWrite p via v =>
      let perm_ok :=
        match via with
        | Some l =>
            match lookup_loan (st_loans st) l with
            | None => false
            | Some le =>
                loan_active le &&
                (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) &&
                within_b p (ln_place le) &&
                addr_valid_b (st_mem st) (ln_addr le)
            end
        | None => direct_write_ok p (st_loans st)
        end in
      if perm_ok then
        match write_stable_mem (st_mem st) p v with
        | None => None
        | Some m' =>
            Some {| st_mem := m';
                    st_loans := st_loans st;
                    st_refs := invalidate_overlapping_refs p (st_refs st);
                    st_next_bid := st_next_bid st |}
        end
      else None

  | OpUnstableWrite p kind =>
      if no_overlapping_loan_at p (st_loans st) then
        match write_unstable_mem (st_mem st) p (st_next_bid st) kind with
        | None => None
        | Some m' =>
            Some {| st_mem := m';
                    st_loans := st_loans st;
                    st_refs := invalidate_overlapping_refs p (st_refs st);
                    st_next_bid := S (st_next_bid st) |}
        end
      else None

  | OpTagPreservingUnionWrite pu via expected_tag new_payload =>
      let perm_ok :=
        match via with
        | Some l =>
            match lookup_loan (st_loans st) l with
            | None => false
            | Some le =>
                loan_active le &&
                (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) &&
                within_b pu (ln_place le) &&
                addr_valid_b (st_mem st) (ln_addr le)
            end
        | None => no_overlapping_exclusive_or_reserved pu None (st_loans st)
        end in
      if perm_ok then
        match write_tag_preserving_mem (st_mem st) pu expected_tag new_payload with
        | None => None
        | Some m' =>
            Some {| st_mem := m';
                    st_loans := st_loans st;
                    st_refs := invalidate_overlapping_refs (PUnionPayload pu) (st_refs st);
                    st_next_bid := st_next_bid st |}
        end
      else None

  | OpCapPreservingPush pc via new_elem =>
      let base_ok :=
        match via with
        | Some l =>
            match lookup_loan (st_loans st) l with
            | None => false
            | Some le =>
                loan_active le &&
                (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) &&
                within_b pc (ln_place le) &&
                addr_valid_b (st_mem st) (ln_addr le) &&
                no_overlapping_exclusive_or_reserved pc (Some l) (st_loans st)
            end
        | None => no_overlapping_exclusive_or_reserved pc None (st_loans st)
        end in
      if base_ok then
        match push_cap_preserving_mem (st_mem st) pc new_elem with
        | None => None
        | Some (m', old_len) =>
            let pushed_slot := PElem pc old_len in
            let slot_ok :=
              forallb (fun le =>
                if option_nat_eqb via (Some (ln_id le)) then true
                else if negb (loan_active le) then true
                else places_disjoint_b pushed_slot (ln_place le)) (st_loans st) in
            if slot_ok then
              Some {| st_mem := m';
                      st_loans := st_loans st;
                      st_refs := invalidate_overlapping_refs pushed_slot (st_refs st);
                      st_next_bid := st_next_bid st |}
            else None
        end
      else None

  | OpEndLoan l =>
      match lookup_loan (st_loans st) l with
      | None => None
      | Some le =>
          if loan_active le && negb (has_live_child (st_loans st) l) then
            let loans1 := remove_loan (st_loans st) l in
            let loans2 :=
              match ln_parent le, ln_mode le with
              | Some pid, LExclusive => set_loan_suspended loans1 pid false
              | _, _ => loans1
              end in
            Some {| st_mem := st_mem st;
                    st_loans := loans2;
                    st_refs := st_refs st;
                    st_next_bid := st_next_bid st |}
          else None
      end

  | OpReturnLoan l =>
      match lookup_loan (st_loans st) l with
      | None => None
      | Some le =>
          if loan_active le &&
             negb (loan_mode_beq (ln_mode le) LReserved) &&
             negb (has_live_child (st_loans st) l) &&
             addr_valid_b (st_mem st) (ln_addr le) then
            match lookup_owner (st_mem st) (p_owner (ln_place le)) with
            | Some oe =>
                if oe_borrowed oe then
                  Some {| st_mem := st_mem st;
                          st_loans := set_loan_returned (st_loans st) l;
                          st_refs := st_refs st;
                          st_next_bid := st_next_bid st |}
                else None
            | None => None
            end
          else None
      end

  | OpLoopStep cursor_id new_cursor_id orig sub_place =>
      if Nat.eqb cursor_id new_cursor_id then None
      else if has_loan (st_loans st) new_cursor_id then None
      else match lookup_loan (st_loans st) cursor_id with
           | None => None
           | Some ce =>
               if loan_active ce &&
                  loan_mode_beq (ln_mode ce) LExclusive &&
                  negb (has_live_child (st_loans st) cursor_id) &&
                  within_b sub_place (ln_place ce) &&
                  addr_valid_b (st_mem st) (ln_addr ce) then
                 match resolve_addr (st_mem st) sub_place with
                 | None => None
                 | Some addr =>
                     let loans1 := remove_loan (st_loans st) cursor_id in
                     let folded := {|
                       ln_id := new_cursor_id;
                       ln_origin := orig;
                       ln_parent := ln_parent ce;
                       ln_root_loan := ln_root_loan ce;
                       ln_place := sub_place;
                       ln_addr := addr;
                       ln_mode := LExclusive;
                       ln_suspended := false;
                       ln_returned := false;
                     |} in
                     Some {| st_mem := st_mem st;
                             st_loans := folded :: loans1;
                             st_refs := st_refs st;
                             st_next_bid := st_next_bid st |}
                 end
               else None
           end

  | OpAssumeRefinement fid p cf =>
      if fact_holds_b (st_mem st) p cf then
        Some {| st_mem := st_mem st;
                st_loans := st_loans st;
                st_refs := assoc_set Nat.eqb (st_refs st) fid (p, cf);
                st_next_bid := st_next_bid st |}
      else None

  | OpUseRefinement fid =>
      match assoc_get Nat.eqb (st_refs st) fid with
      | Some (p, cf) =>
          if fact_holds_b (st_mem st) p cf then Some st else None
      | None => None
      end

  | OpDropRefinement fid =>
      Some {| st_mem := st_mem st;
              st_loans := st_loans st;
              st_refs := filter (fun entry => negb (Nat.eqb (fst entry) fid)) (st_refs st);
              st_next_bid := st_next_bid st |}
  end.

Inductive Step : machine_state -> step_op -> machine_state -> Prop :=
| StepExec : forall st op st',
    exec_step st op = Some st' ->
    Step st op st'.

(* ================================================================= *)
(* 8. Polonius Origin Flow and Branching CFG Model                   *)
(* ================================================================= *)

Inductive cfg_instr : Type :=
| INop
| IStep (op : step_op).

Record cfg_node := {
  cn_point : point_id;
  cn_instr : cfg_instr;
  cn_succs : list point_id;
}.

Record polonius_cfg := {
  cfg_entry : point_id;
  cfg_nodes : list cfg_node;
  cfg_exits : list point_id;
  cfg_issues : list (point_id * origin_id * loan_id);
  cfg_subsets : list (point_id * origin_id * origin_id);
  cfg_live : list (point_id * origin_id);
  cfg_kills : list (point_id * loan_id);
  cfg_contains : list (point_id * origin_id * loan_id);
}.

Definition find_cfg_node (cfg : polonius_cfg) (pt : point_id) : option cfg_node :=
  find (fun n => Nat.eqb (cn_point n) pt) (cfg_nodes cfg).

Definition cfg_edge (cfg : polonius_cfg) (pt1 pt2 : point_id) : Prop :=
  exists n, find_cfg_node cfg pt1 = Some n /\ In pt2 (cn_succs n).

Definition issued_at (cfg : polonius_cfg) (pt : point_id) (o : origin_id) (l : loan_id) : Prop :=
  In (pt, o, l) (cfg_issues cfg).

Definition subset_at (cfg : polonius_cfg) (pt : point_id) (o1 o2 : origin_id) : Prop :=
  In (pt, o1, o2) (cfg_subsets cfg).

Definition origin_live_at (cfg : polonius_cfg) (pt : point_id) (o : origin_id) : Prop :=
  In (pt, o) (cfg_live cfg).

Definition loan_killed_at (cfg : polonius_cfg) (pt : point_id) (l : loan_id) : Prop :=
  In (pt, l) (cfg_kills cfg).

Definition origin_contains_loan_at (cfg : polonius_cfg) (pt : point_id)
    (o : origin_id) (l : loan_id) : Prop :=
  In (pt, o, l) (cfg_contains cfg).

Definition loan_live_at (cfg : polonius_cfg) (pt : point_id) (l : loan_id) : Prop :=
  exists o, origin_live_at cfg pt o /\ origin_contains_loan_at cfg pt o l.

Inductive polonius_flow (cfg : polonius_cfg) : point_id -> origin_id -> loan_id -> Prop :=
| PFIssue : forall pt o l,
    issued_at cfg pt o l ->
    polonius_flow cfg pt o l
| PFSubset : forall pt o1 o2 l,
    polonius_flow cfg pt o1 l ->
    subset_at cfg pt o1 o2 ->
    polonius_flow cfg pt o2 l
| PFEdge : forall pt1 pt2 o l,
    polonius_flow cfg pt1 o l ->
    cfg_edge cfg pt1 pt2 ->
    ~ loan_killed_at cfg pt2 l ->
    origin_live_at cfg pt2 o ->
    polonius_flow cfg pt2 o l.

Definition triple_beq (x y : nat * nat * nat) : bool :=
  Nat.eqb (fst (fst x)) (fst (fst y)) &&
  Nat.eqb (snd (fst x)) (snd (fst y)) &&
  Nat.eqb (snd x) (snd y).

Definition pair_beq (x y : nat * nat) : bool :=
  Nat.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

Lemma triple_beq_eq : forall x y, triple_beq x y = true <-> x = y.
Proof.
  intros [[a1 b1] c1] [[a2 b2] c2]; unfold triple_beq; cbn.
  rewrite !andb_true_iff, !Nat.eqb_eq.
  split; [intros [[-> ->] ->]; reflexivity | intro H; inversion H; auto].
Qed.

Lemma pair_beq_eq : forall x y, pair_beq x y = true <-> x = y.
Proof.
  intros [a1 b1] [a2 b2]; unfold pair_beq; cbn.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Definition mem_triple (x : nat * nat * nat) (xs : list (nat * nat * nat)) : bool :=
  existsb (triple_beq x) xs.

Definition mem_pair (x : nat * nat) (xs : list (nat * nat)) : bool :=
  existsb (pair_beq x) xs.

Lemma mem_triple_In : forall x xs, mem_triple x xs = true <-> In x xs.
Proof.
  intros x xs. unfold mem_triple. rewrite existsb_exists. split.
  - intros [y [Hin Heq]]. apply triple_beq_eq in Heq; subst; exact Hin.
  - intro Hin. exists x; split; [exact Hin | now apply triple_beq_eq].
Qed.

Lemma mem_pair_In : forall x xs, mem_pair x xs = true <-> In x xs.
Proof.
  intros x xs. unfold mem_pair. rewrite existsb_exists. split.
  - intros [y [Hin Heq]]. apply pair_beq_eq in Heq; subst; exact Hin.
  - intro Hin. exists x; split; [exact Hin | now apply pair_beq_eq].
Qed.

Definition check_polonius_closure (cfg : polonius_cfg) : bool :=
  (* 1. Issue closure *)
  forallb (fun entry => mem_triple entry (cfg_contains cfg)) (cfg_issues cfg) &&
  (* 2. Subset closure *)
  forallb (fun c =>
    let '(pt, o1, l) := c in
    forallb (fun s =>
      let '(pts, os1, os2) := s in
      if Nat.eqb pt pts && Nat.eqb o1 os1 then
        mem_triple (pt, os2, l) (cfg_contains cfg)
      else true) (cfg_subsets cfg)) (cfg_contains cfg) &&
  (* 3. Edge propagation closure *)
  forallb (fun node =>
    let pt1 := cn_point node in
    forallb (fun pt2 =>
      forallb (fun c =>
        let '(ptc, o, l) := c in
        if Nat.eqb ptc pt1 && negb (mem_pair (pt2, l) (cfg_kills cfg)) &&
           mem_pair (pt2, o) (cfg_live cfg)
        then mem_triple (pt2, o, l) (cfg_contains cfg)
        else true) (cfg_contains cfg)) (cn_succs node)) (cfg_nodes cfg).

Lemma polonius_closure_sound : forall cfg pt o l,
  check_polonius_closure cfg = true ->
  polonius_flow cfg pt o l ->
  origin_contains_loan_at cfg pt o l.
Proof.
  intros cfg pt o l Hcl Hflow.
  unfold check_polonius_closure in Hcl.
  rewrite !andb_true_iff in Hcl.
  destruct Hcl as [[Hissue Hsub] Hedge].
  induction Hflow as [pt o l Hiss | pt o1 o2 l Hfl IH Hsubs | pt1 pt2 o l Hfl IH Hed Hnkill Hlive].
  - rewrite forallb_forall in Hissue.
    apply mem_triple_In. apply Hissue. exact Hiss.
  - rewrite forallb_forall in Hsub.
    specialize (Hsub (pt, o1, l) IH). cbn in Hsub.
    rewrite forallb_forall in Hsub.
    specialize (Hsub (pt, o1, o2) Hsubs). cbn in Hsub.
    rewrite !Nat.eqb_refl in Hsub; cbn in Hsub.
    now apply mem_triple_In.
  - destruct Hed as [node [Hfind Hsucc]].
    rewrite forallb_forall in Hedge.
    assert (Hin_node : In node (cfg_nodes cfg)) by (eapply find_some; eauto).
    assert (Hpt1 : cn_point node = pt1).
    { apply find_some in Hfind as [_ Hpt]. now apply Nat.eqb_eq in Hpt. }
    specialize (Hedge node Hin_node). cbv zeta in Hedge.
    rewrite forallb_forall in Hedge.
    specialize (Hedge pt2 Hsucc).
    rewrite forallb_forall in Hedge.
    specialize (Hedge (pt1, o, l) IH). cbv beta iota in Hedge.
    rewrite Hpt1, Nat.eqb_refl in Hedge; cbn [andb] in Hedge.
    assert (Hnkill_b : mem_pair (pt2, l) (cfg_kills cfg) = false).
    { destruct (mem_pair (pt2, l) (cfg_kills cfg)) eqn:Ek; [| reflexivity].
      apply mem_pair_In in Ek. exfalso. now apply Hnkill. }
    assert (Hlive_b : mem_pair (pt2, o) (cfg_live cfg) = true) by (now apply mem_pair_In).
    unfold point_id, origin_id, loan_id in Hedge, Hnkill_b, Hlive_b.
    rewrite Hnkill_b, Hlive_b in Hedge; cbn [negb andb] in Hedge; cbv iota in Hedge.
    now apply mem_triple_In.
Qed.

End LoanSemantics.
