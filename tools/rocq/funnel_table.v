(* SPDX-License-Identifier: Apache-2.0 *)

(* Mechanized fixed-capacity Funnel Hashing (Farach-Colton, Krapivin, Kuszmaul)
   for HoldFast's zero-heap, non-relocating static storage discipline.
   All slots stay immovable in place once written (no reordering). *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Import ListNotations.

Module FunnelTable.

Record FunnelLayout : Type := mk_layout {
  levels : list nat;
  beta : nat;
  overflow_size : nat;
}.

Fixpoint level_total_slots (b : nat) (ls : list nat) : nat :=
  match ls with
  | [] => 0
  | buckets :: rest => buckets * b + level_total_slots b rest
  end.

Definition capacity (L : FunnelLayout) : nat :=
  level_total_slots (beta L) (levels L) + overflow_size L.

Fixpoint prefix_slots (b : nat) (ls : list nat) (i : nat) : nat :=
  match ls, i with
  | [], _ => 0
  | _, 0 => 0
  | buckets :: rest, S i' => buckets * b + prefix_slots b rest i'
  end.

Definition level_offset (L : FunnelLayout) (i : nat) : nat :=
  prefix_slots (beta L) (levels L) i.

Definition level_size (L : FunnelLayout) (i : nat) : nat :=
  nth i (levels L) 0 * beta L.

Fixpoint probe_levels {K : Type} (b : nat) (h : nat -> K -> nat) (k : K)
    (ls : list nat) (lvl off : nat) : list nat :=
  match ls with
  | [] => []
  | buckets :: rest =>
      let lvl_slots := buckets * b in
      let this_lvl :=
        match buckets with
        | 0 => []
        | S _ => seq (off + ((h lvl k) mod buckets) * b) b
        end in
      this_lvl ++ probe_levels b h k rest (S lvl) (off + lvl_slots)
  end.

Definition probe_sequence {K : Type} (L : FunnelLayout) (h : nat -> K -> nat) (k : K) : list nat :=
  probe_levels (beta L) h k (levels L) 0 0 ++ seq (level_total_slots (beta L) (levels L)) (overflow_size L).

Definition Table (K V : Type) : Type := list (option (K * V)).

Inductive InsertResult (K V : Type) : Type :=
| Inserted : Table K V -> InsertResult K V
| AlreadyPresent : Table K V -> InsertResult K V
| Full : Table K V -> InsertResult K V.

Arguments Inserted {K V} _.
Arguments AlreadyPresent {K V} _.
Arguments Full {K V} _.

Fixpoint set_slot {A : Type} (xs : list A) (idx : nat) (val : A) : list A :=
  match xs, idx with
  | [], _ => []
  | _ :: rest, 0 => val :: rest
  | x :: rest, S j => x :: set_slot rest j val
  end.

Fixpoint lookup_seq {K V : Type} (eqb : K -> K -> bool) (t : Table K V)
    (probes : list nat) (k : K) : option V :=
  match probes with
  | [] => None
  | idx :: rest =>
      match nth_error t idx with
      | Some (Some (k', v)) => if eqb k k' then Some v else lookup_seq eqb t rest k
      | Some None => lookup_seq eqb t rest k
      | None => None
      end
  end.

Fixpoint insert_seq {K V : Type} (eqb : K -> K -> bool) (t : Table K V)
    (probes : list nat) (k : K) (v : V) : InsertResult K V :=
  match probes with
  | [] => Full t
  | idx :: rest =>
      match nth_error t idx with
      | Some None => Inserted (set_slot t idx (Some (k, v)))
      | Some (Some (k', _)) =>
          if eqb k k' then AlreadyPresent t else insert_seq eqb t rest k v
      | None => Full t
      end
  end.

Definition funnel_lookup {K V : Type} (eqb : K -> K -> bool) (L : FunnelLayout)
    (h : nat -> K -> nat) (t : Table K V) (k : K) : option V :=
  lookup_seq eqb t (probe_sequence L h k) k.

Definition funnel_insert {K V : Type} (eqb : K -> K -> bool) (L : FunnelLayout)
    (h : nat -> K -> nat) (t : Table K V) (k : K) (v : V) : InsertResult K V :=
  insert_seq eqb t (probe_sequence L h k) k v.

(* ------------------------------------------------------------------ *)
(* Basic slot and layout lemmas                                       *)
(* ------------------------------------------------------------------ *)

Lemma set_slot_length : forall {A : Type} (xs : list A) idx val,
  length (set_slot xs idx val) = length xs.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros [|j] val; simpl; auto.
Qed.

Lemma nth_error_set_slot_same : forall {A : Type} (xs : list A) idx val,
  idx < length xs -> nth_error (set_slot xs idx val) idx = Some val.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros [|j] val Hlen; simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma nth_error_set_slot_other : forall {A : Type} (xs : list A) idx j val,
  j <> idx -> nth_error (set_slot xs idx val) j = nth_error xs j.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros [|idx'] [|j'] val Hneq; simpl in *; auto; try lia.
Qed.

Lemma nth_error_Some_lt : forall {A : Type} (xs : list A) idx (v : A),
  nth_error xs idx = Some v -> idx < length xs.
Proof.
  intros A xs idx v H. apply nth_error_Some. rewrite H. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. Probe indices stay strictly within fixed capacity               *)
(* ------------------------------------------------------------------ *)

Lemma probe_levels_in_bounds : forall {K : Type} b (h : nat -> K -> nat) k ls lvl off idx,
  In idx (probe_levels b h k ls lvl off) ->
  off <= idx /\ idx < off + level_total_slots b ls.
Proof.
  intros K b h k ls; induction ls as [|buckets rest IH]; intros lvl off idx Hin; simpl in *.
  - contradiction.
  - apply in_app_iff in Hin as [Hhere | Hrest].
    + destruct buckets as [|buckets']; simpl in Hhere; [contradiction|].
      apply in_seq in Hhere.
      assert (Hmod : h lvl k mod S buckets' < S buckets').
      { apply Nat.mod_upper_bound. discriminate. }
      assert (Hmul : (h lvl k mod S buckets' + 1) * b <= S buckets' * b).
      { apply Nat.mul_le_mono_r. lia. }
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l in Hmul. lia.
    + apply IH in Hrest. lia.
Qed.

Theorem probe_indices_in_bounds : forall {K : Type} (L : FunnelLayout) (h : nat -> K -> nat) k idx,
  In idx (probe_sequence L h k) -> idx < capacity L.
Proof.
  intros K L h k idx Hin. unfold probe_sequence, capacity in *.
  apply in_app_iff in Hin as [Hlvls | Hov].
  - apply probe_levels_in_bounds in Hlvls. lia.
  - apply in_seq in Hov. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Level index intervals are pairwise disjoint and below overflow  *)
(* ------------------------------------------------------------------ *)

Lemma prefix_slots_step_le : forall b ls i,
  prefix_slots b ls i + nth i ls 0 * b <= prefix_slots b ls (S i).
Proof.
  intros b ls; induction ls as [|buckets rest IH]; intros [|i']; simpl; try lia.
  specialize (IH i'). lia.
Qed.

Lemma prefix_slots_mono : forall b ls i j,
  i <= j -> prefix_slots b ls i <= prefix_slots b ls j.
Proof.
  intros b ls i j Hij. induction Hij as [|j' Hij' IH]; [lia|].
  pose proof (prefix_slots_step_le b ls j'). lia.
Qed.

Lemma prefix_slots_le_total : forall b ls i,
  prefix_slots b ls i <= level_total_slots b ls.
Proof.
  intros b ls; induction ls as [|buckets rest IH]; intros [|i']; simpl; try lia.
  specialize (IH i'). lia.
Qed.

Theorem level_ranges_disjoint : forall (L : FunnelLayout) i j,
  i < j ->
  level_offset L i + level_size L i <= level_offset L j /\
  level_offset L j + level_size L j <= level_total_slots (beta L) (levels L).
Proof.
  intros L i j Hij. unfold level_offset, level_size.
  split.
  - pose proof (prefix_slots_step_le (beta L) (levels L) i) as Hstep.
    pose proof (prefix_slots_mono (beta L) (levels L) (S i) j ltac:(lia)) as Hmono.
    lia.
  - pose proof (prefix_slots_step_le (beta L) (levels L) j) as Hstep.
    pose proof (prefix_slots_le_total (beta L) (levels L) (S j)) as Htot.
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Static capacity preservation & 4. Non-reordering immutability   *)
(* ------------------------------------------------------------------ *)

Lemma insert_seq_preserves_length : forall {K V : Type} (eqb : K -> K -> bool)
    t probes (k : K) (v : V) t',
  insert_seq eqb t probes k v = Inserted t' ->
  length t' = length t.
Proof.
  intros K V eqb t probes; induction probes as [|idx rest IH]; intros k v t' Hins; simpl in Hins.
  - discriminate.
  - destruct (nth_error t idx) as [[ [k' v'] | ] | ] eqn:Hslot.
    + destruct (eqb k k'); [discriminate | eapply IH; eauto].
    + inversion Hins; subst. apply set_slot_length.
    + discriminate.
Qed.

Theorem insert_preserves_length : forall {K V : Type} (eqb : K -> K -> bool)
    (L : FunnelLayout) (h : nat -> K -> nat) (t : Table K V) k v t',
  length t = capacity L ->
  funnel_insert eqb L h t k v = Inserted t' ->
  length t' = capacity L.
Proof.
  intros K V eqb L h t k v t' Hlen Hins.
  unfold funnel_insert in Hins.
  apply insert_seq_preserves_length in Hins. lia.
Qed.

Lemma insert_seq_only_writes_empty : forall {K V : Type} (eqb : K -> K -> bool)
    t probes (k : K) (v : V) t',
  insert_seq eqb t probes k v = Inserted t' ->
  exists widx, nth_error t widx = Some None /\ t' = set_slot t widx (Some (k, v)).
Proof.
  intros K V eqb t probes; induction probes as [|idx rest IH]; intros k v t' Hins; simpl in Hins.
  - discriminate.
  - destruct (nth_error t idx) as [[ [k' v'] | ] | ] eqn:Hslot.
    + destruct (eqb k k'); [discriminate | eapply IH; eauto].
    + inversion Hins; subst. exists idx. split; [exact Hslot | reflexivity].
    + discriminate.
Qed.

Theorem insert_no_reordering : forall {K V : Type} (eqb : K -> K -> bool)
    (L : FunnelLayout) (h : nat -> K -> nat) (t : Table K V) k v t' i kv,
  funnel_insert eqb L h t k v = Inserted t' ->
  nth_error t i = Some (Some kv) ->
  nth_error t' i = Some (Some kv).
Proof.
  intros K V eqb L h t k v t' i kv Hins Hocc.
  unfold funnel_insert in Hins.
  apply insert_seq_only_writes_empty in Hins as [widx [Hempty ->]].
  rewrite nth_error_set_slot_other; [exact Hocc |].
  intros Heq; subst. rewrite Hocc in Hempty. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. Lookup hit after insertion & 6. Preservation of other keys      *)
(* ------------------------------------------------------------------ *)

Lemma lookup_seq_after_insert_hit : forall {K V : Type} (eqb : K -> K -> bool)
    (eqb_refl : forall x, eqb x x = true)
    t probes (k : K) (v : V) t',
  lookup_seq eqb t probes k = None ->
  insert_seq eqb t probes k v = Inserted t' ->
  lookup_seq eqb t' probes k = Some v.
Proof.
  intros K V eqb eqb_refl t probes; induction probes as [|idx rest IH];
    intros k v t' Hmiss Hins; simpl in *.
  - discriminate.
  - destruct (nth_error t idx) as [[ [k' v'] | ] | ] eqn:Hslot; try discriminate.
    + destruct (eqb k k') eqn:Heq; [discriminate|].
      pose proof Hins as Hins_copy.
      apply insert_seq_only_writes_empty in Hins as [widx [Hempty Ht']].
      assert (Hneq : idx <> widx).
      { intros ->. rewrite Hslot in Hempty. discriminate. }
      rewrite Ht', nth_error_set_slot_other; [|exact Hneq].
      simpl in Hmiss.
      rewrite Hslot, Heq. rewrite Ht' in Hins_copy. eapply IH; [exact Hmiss | exact Hins_copy].
    + inversion Hins; subst.
      rewrite nth_error_set_slot_same.
      * rewrite eqb_refl. reflexivity.
      * eapply nth_error_Some_lt. exact Hslot.
Qed.

Theorem lookup_after_insert_hit : forall {K V : Type} (eqb : K -> K -> bool)
    (eqb_refl : forall x, eqb x x = true)
    (L : FunnelLayout) (h : nat -> K -> nat) (t : Table K V) k v t',
  funnel_lookup eqb L h t k = None ->
  funnel_insert eqb L h t k v = Inserted t' ->
  funnel_lookup eqb L h t' k = Some v.
Proof.
  intros K V eqb eqb_refl L h t k v t' Hmiss Hins.
  unfold funnel_lookup, funnel_insert in *.
  eapply lookup_seq_after_insert_hit; eauto.
Qed.

Lemma lookup_seq_preserved_at_set_empty : forall {K V : Type} (eqb : K -> K -> bool)
    t probes widx (k1 k2 : K) (v1 v2 : V),
  eqb k1 k2 = false ->
  nth_error t widx = Some None ->
  lookup_seq eqb t probes k1 = Some v1 ->
  lookup_seq eqb (set_slot t widx (Some (k2, v2))) probes k1 = Some v1.
Proof.
  intros K V eqb t probes widx k1 k2 v1 v2 Hneq Hempty.
  induction probes as [|idx rest IH]; intros Hlook; simpl in *.
  - discriminate.
  - destruct (Nat.eq_dec idx widx) as [-> | Hdiff].
    + rewrite Hempty in Hlook.
      rewrite nth_error_set_slot_same; [| eapply nth_error_Some_lt; exact Hempty].
      rewrite Hneq. exact (IH Hlook).
    + rewrite nth_error_set_slot_other; [|exact Hdiff].
      destruct (nth_error t idx) as [[ [k' v'] | ] | ] eqn:Hslot; try discriminate.
      * destruct (eqb k1 k'); [exact Hlook | exact (IH Hlook)].
      * exact (IH Hlook).
Qed.

Theorem insert_preserves_other_keys : forall {K V : Type} (eqb : K -> K -> bool)
    (L : FunnelLayout) (h : nat -> K -> nat) (t : Table K V) k1 v1 k2 v2 t',
  eqb k1 k2 = false ->
  funnel_lookup eqb L h t k1 = Some v1 ->
  funnel_insert eqb L h t k2 v2 = Inserted t' ->
  funnel_lookup eqb L h t' k1 = Some v1.
Proof.
  intros K V eqb L h t k1 v1 k2 v2 t' Hneq Hlook Hins.
  unfold funnel_lookup, funnel_insert in *.
  apply insert_seq_only_writes_empty in Hins as [widx [Hempty ->]].
  eapply lookup_seq_preserved_at_set_empty; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* 7. Fail-closed exhaustion & bounded static probe count             *)
(* ------------------------------------------------------------------ *)

Lemma insert_seq_full_unchanged : forall {K V : Type} (eqb : K -> K -> bool)
    t probes (k : K) (v : V) t',
  insert_seq eqb t probes k v = Full t' -> t' = t.
Proof.
  intros K V eqb t probes; induction probes as [|idx rest IH]; intros k v t' Hins; simpl in Hins.
  - inversion Hins; reflexivity.
  - destruct (nth_error t idx) as [[ [k' v'] | ] | ] eqn:Hslot.
    + destruct (eqb k k'); [discriminate | eapply IH; eauto].
    + discriminate.
    + inversion Hins; reflexivity.
Qed.

Theorem insert_full_fails_closed : forall {K V : Type} (eqb : K -> K -> bool)
    (L : FunnelLayout) (h : nat -> K -> nat) (t : Table K V) k v t',
  funnel_insert eqb L h t k v = Full t' -> t' = t.
Proof.
  intros K V eqb L h t k v t' Hins.
  unfold funnel_insert in Hins. eapply insert_seq_full_unchanged; eauto.
Qed.

Lemma probe_levels_length_le : forall {K : Type} b (h : nat -> K -> nat) k ls lvl off,
  length (probe_levels b h k ls lvl off) <= length ls * b.
Proof.
  intros K b h k ls; induction ls as [|buckets rest IH]; intros lvl off; simpl.
  - lia.
  - rewrite length_app.
    destruct buckets as [|buckets'].
    + simpl. specialize (IH (S lvl) (off + 0)). lia.
    + rewrite length_seq. specialize (IH (S lvl) (off + S buckets' * b)).
      simpl in IH. simpl. lia.
Qed.

Theorem probe_steps_bounded : forall {K : Type} (L : FunnelLayout) (h : nat -> K -> nat) k,
  length (probe_sequence L h k) <= length (levels L) * beta L + overflow_size L.
Proof.
  intros K L h k. unfold probe_sequence.
  rewrite length_app, length_seq.
  pose proof (probe_levels_length_le (beta L) h k (levels L) 0 0). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Concrete inhabited witness (3-level funnel + 2-slot overflow)      *)
(* ------------------------------------------------------------------ *)

Definition demo_layout : FunnelLayout := mk_layout [4; 2; 1] 2 2.
Definition demo_hash (lvl k : nat) : nat := k + lvl.
Definition empty_demo : Table nat nat := repeat None (capacity demo_layout).

Example demo_funnel_behavior :
  match funnel_insert Nat.eqb demo_layout demo_hash empty_demo 10 100 with
  | Inserted t1 =>
      match funnel_insert Nat.eqb demo_layout demo_hash t1 14 200 with
      | Inserted t2 =>
          (length t2 = capacity demo_layout) /\
          (funnel_lookup Nat.eqb demo_layout demo_hash t2 10 = Some 100) /\
          (funnel_lookup Nat.eqb demo_layout demo_hash t2 14 = Some 200)
      | _ => False
      end
  | _ => False
  end.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

End FunnelTable.
