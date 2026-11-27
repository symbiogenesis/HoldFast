(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Require Import loan_semantics.
Import ListNotations LoanSemantics.

Module LoanSoundness.

(* ================================================================= *)
(* 1. Place-to-Address Structural Correspondence and Well-Formedness *)
(* ================================================================= *)

Fixpoint steps_match_stamps (steps : list proj_step) (stamps : list step_stamp) : bool :=
  match steps, stamps with
  | [], [] => true
  | SField f :: r1, StField _ f' :: r2 =>
      Nat.eqb f f' && steps_match_stamps r1 r2
  | SElem i :: r1, StElem _ i' :: r2 =>
      Nat.eqb i i' && steps_match_stamps r1 r2
  | SSlice off len :: r1, StSlice _ off' len' :: r2 =>
      Nat.eqb off off' && Nat.eqb len len' &&
      match r1, r2 with
      | [], [] => true
      | SElem k :: r1', StElem _ k' :: r2' =>
          Nat.eqb k k' && steps_match_stamps r1' r2'
      | _, _ => false
      end
  | SCell2D r c :: [], StCell2D _ r' c' :: [] =>
      Nat.eqb r r' && Nat.eqb c c'
  | SUnionPayload :: r1, StUnionPayload _ _ :: r2 =>
      steps_match_stamps r1 r2
  | _, _ => false
  end.

Definition addr_matches_place (a : place_addr) (p : place) : bool :=
  Nat.eqb (addr_owner a) (p_owner p) &&
  steps_match_stamps (p_path p) (addr_steps a).

Lemma resolve_steps_match : forall v steps st,
  resolve_steps v steps = Some st -> steps_match_stamps steps st = true.
Proof.
  intros v steps st H.
  assert (Haux : forall k steps v st,
    length steps <= k -> resolve_steps v steps = Some st -> steps_match_stamps steps st = true).
  { induction k as [| k' IH]; intros [| s rest] v0 st0 Hlen0 Hr0;
      cbn [resolve_steps length] in *.
    - destruct v0; inversion Hr0; reflexivity.
    - lia.
    - destruct v0; inversion Hr0; reflexivity.
    - destruct s; cbn [resolve_steps option_map] in Hr0.
      + destruct v0; try discriminate.
        destruct (assoc_get Nat.eqb fields f); [| discriminate].
        destruct (resolve_steps o rest) as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
        inversion Hr0; subst; cbn [steps_match_stamps].
        rewrite Nat.eqb_refl; cbn [andb]. eapply IH; [| exact Hr]; lia.
      + destruct v0; try discriminate.
        destruct (nth_error elems idx); [| discriminate].
        destruct (resolve_steps o rest) as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
        inversion Hr0; subst; cbn [steps_match_stamps].
        rewrite Nat.eqb_refl; cbn [andb]. eapply IH; [| exact Hr]; lia.
      + destruct v0; try discriminate.
        destruct (Nat.leb (off + len) (length elems)); [| discriminate].
        destruct rest as [| s' rest']; cbn [resolve_steps option_map] in Hr0.
        * inversion Hr0; subst; cbn [steps_match_stamps].
          rewrite !Nat.eqb_refl; reflexivity.
        * destruct s'; try discriminate.
          destruct (Nat.ltb idx len); [| discriminate].
          destruct (nth_error elems (off + idx)); [| discriminate].
          destruct (resolve_steps o rest') as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
          inversion Hr0; subst; cbn [steps_match_stamps].
          rewrite !Nat.eqb_refl; cbn [andb].
          eapply IH; [| exact Hr]; cbn in Hlen0; lia.
      + destruct v0, rest; try discriminate.
        destruct (Nat.ltb r rows && Nat.ltb c cols); [| discriminate].
        inversion Hr0; subst; cbn [steps_match_stamps].
        rewrite !Nat.eqb_refl; reflexivity.
      + destruct v0; try discriminate.
        destruct (resolve_steps v0 rest) as [rs |] eqn:Hr; cbn in Hr0; [| discriminate].
        inversion Hr0; subst; cbn [steps_match_stamps].
        eapply IH; [| exact Hr]; lia. }
  eapply Haux; eauto.
Qed.

Lemma resolve_addr_matches_place : forall m p a,
  resolve_addr m p = Some a -> addr_matches_place a p = true.
Proof.
  intros m p a H. unfold resolve_addr in H.
  destruct (lookup_owner m (p_owner p)); [| discriminate].
  destruct (val_bid (oe_val o)); [| discriminate].
  destruct (resolve_steps (oe_val o) (p_path p)) as [st |] eqn:Hs; [| discriminate].
  inversion H; subst; unfold addr_matches_place; cbn.
  rewrite Nat.eqb_refl; cbn. eapply resolve_steps_match; eauto.
Qed.

Lemma write_unstable_preserves_bid : forall v steps next_bid kind v',
  steps <> [] ->
  write_unstable_val v steps next_bid kind = Some v' ->
  val_bid v' = val_bid v.
Proof.
  intros v [| s rest] next_bid kind v' Hne Hw; [contradiction |].
  destruct s, v; cbn [write_unstable_val option_map] in Hw; try discriminate.
  - destruct (assoc_get Nat.eqb fields f); [| discriminate].
    destruct (write_unstable_val o rest next_bid kind); [| discriminate].
    destruct (assoc_update _ _ _ _); cbn in Hw; inversion Hw; reflexivity.
  - destruct (nth_error elems idx); [| discriminate].
    destruct (write_unstable_val o rest next_bid kind); [| discriminate].
    destruct (list_set _ _ _); cbn in Hw; inversion Hw; reflexivity.
  - destruct (write_unstable_val v rest next_bid kind); cbn in Hw; inversion Hw; reflexivity.
Qed.

Lemma write_unstable_preserves_disjoint_stamps : forall s1 s2 v next_bid kind v' st,
  steps_disjoint_b s1 s2 = true ->
  steps_match_stamps s2 st = true ->
  write_unstable_val v s1 next_bid kind = Some v' ->
  valid_stamps v st = true ->
  valid_stamps v' st = true.
Proof.
  induction s1 as [| a r1 IH]; intros [| b r2] v next_bid kind v' st Hdisj Hmatch Hw Hv;
    cbn [steps_disjoint_b] in Hdisj; try discriminate.
  destruct a, b, v;
    cbn [steps_disjoint_b step_disjoint_b proj_step_beq write_unstable_val option_map]
      in Hdisj, Hw; try discriminate.
  - (* SField vs SField *)
    destruct st as [| st0 str]; [cbn in Hmatch; discriminate |].
    destruct st0; cbn [steps_match_stamps] in Hmatch; try discriminate.
    apply andb_true_iff in Hmatch as [Hf0 Hmr].
    apply Nat.eqb_eq in Hf0; subst f1.
    destruct (Nat.eqb f f0) eqn:Ef.
    + apply Nat.eqb_eq in Ef; subst f0.
      cbn [negb] in Hdisj; cbv iota in Hdisj.
      destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
      destruct (write_unstable_val fv r1 next_bid kind) as [fv' |] eqn:Hwfv; [| discriminate].
      destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
        cbn in Hw; [| discriminate].
      inversion Hw; subst; clear Hw.
      cbn [valid_stamps] in *.
      destruct (Nat.eqb bid0 bid); cbv iota in *; [| discriminate].
      destruct (assoc_get Nat.eqb fields f) as [fv0 |] eqn:Hfv0; cbv iota in *; [| discriminate].
      rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f fv' fs' Hup).
      assert (fv0 = fv) by congruence; subst fv0.
      eapply IH; eauto.
    + apply Nat.eqb_neq in Ef.
      destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
      destruct (write_unstable_val fv r1 next_bid kind) as [fv' |] eqn:Hwfv; [| discriminate].
      destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
        cbn in Hw; [| discriminate].
      inversion Hw; subst; clear Hw.
      cbn [valid_stamps] in *.
      destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
      destruct (assoc_get Nat.eqb fields f0) as [fv0 |] eqn:Hfv0; cbv iota in Hv; [| discriminate].
      rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 fv' fs' Ef Hup).
      rewrite Hfv0; exact Hv.
  - (* SElem vs SElem *)
    destruct st as [| st0 str]; [cbn in Hmatch; discriminate |].
    destruct st0; cbn [steps_match_stamps] in Hmatch; try discriminate.
    apply andb_true_iff in Hmatch as [Hi0 Hmr].
    apply Nat.eqb_eq in Hi0; subst idx1.
    destruct (Nat.eqb idx idx0) eqn:Ei.
    + apply Nat.eqb_eq in Ei; subst idx0.
      cbn [negb] in Hdisj; cbv iota in Hdisj.
      destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
      destruct (write_unstable_val ev r1 next_bid kind) as [ev' |] eqn:Hwev; [| discriminate].
      destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
        cbn in Hw; [| discriminate].
      inversion Hw; subst; clear Hw.
      cbn [valid_stamps] in *.
      destruct (Nat.eqb bid0 bid); cbv iota in *; [| discriminate].
      destruct (nth_error elems idx) as [ev0 |] eqn:He0; cbv iota in *; [| discriminate].
      rewrite (list_set_nth_same elems idx ev' elems' Hls).
      assert (ev0 = ev) by congruence; subst ev0.
      eapply IH; eauto.
    + apply Nat.eqb_neq in Ei.
      destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
      destruct (write_unstable_val ev r1 next_bid kind) as [ev' |] eqn:Hwev; [| discriminate].
      destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
        cbn in Hw; [| discriminate].
      inversion Hw; subst; clear Hw.
      cbn [valid_stamps] in *.
      destruct (Nat.eqb bid0 bid); cbv iota in Hv; [| discriminate].
      destruct (nth_error elems idx0) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
      rewrite (list_set_nth_other elems idx idx0 ev' elems' Ei Hls).
      rewrite He0; exact Hv.
  - (* SElem vs SSlice *)
    destruct (Nat.ltb idx off || Nat.leb (off + len) idx) eqn:Hsep;
      [| cbv iota in Hdisj; discriminate].
    apply orb_true_iff in Hsep.
    assert (Hout : idx < off \/ off + len <= idx).
    { destruct Hsep as [H1 | H2]; [left; now apply Nat.ltb_lt | right; now apply Nat.leb_le]. }
    destruct st as [| st0 str]; [cbn in Hmatch; discriminate |].
    destruct st0; cbn [steps_match_stamps] in Hmatch; try discriminate.
    apply andb_true_iff in Hmatch as [Htmp Hrest].
    apply andb_true_iff in Htmp as [Ho0 Hl0].
    apply Nat.eqb_eq in Ho0; apply Nat.eqb_eq in Hl0; subst off0 len0.
    destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
    destruct (write_unstable_val ev r1 next_bid kind) as [ev' |] eqn:Hwev; [| discriminate].
    destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
      cbn in Hw; [| discriminate].
    inversion Hw; subst; clear Hw.
    cbn [valid_stamps] in *.
    destruct (Nat.eqb bid0 bid && Nat.leb (off + len) (length elems)) eqn:Hb;
      cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
    apply andb_true_iff in Hb as [Hbid Hlen].
    rewrite (list_set_length elems idx ev' elems' Hls), Hbid, Hlen; cbn [andb]; cbv iota.
    destruct r2 as [| s2' r2']; [destruct str; [reflexivity | discriminate] |].
    destruct s2', str as [| st1 str1]; cbv iota in Hrest; try discriminate.
    destruct st1; try discriminate.
    apply andb_true_iff in Hrest as [Hk0 _].
    apply Nat.eqb_eq in Hk0; subst idx1.
    destruct (Nat.eqb bid0 bid1 && Nat.ltb idx0 len) eqn:Hk;
      cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
    apply andb_true_iff in Hk as [Hbid1 Hk].
    apply Nat.ltb_lt in Hk.
    destruct (nth_error elems (off + idx0)) as [ev0 |] eqn:He0; cbv iota in Hv; [| discriminate].
    rewrite (list_set_nth_other elems idx (off + idx0) ev' elems');
      [rewrite He0; exact Hv | lia | exact Hls].
  - (* SUnionPayload vs SUnionPayload *)
    destruct st as [| st0 str]; [cbn in Hmatch; discriminate |].
    destruct st0; cbn [steps_match_stamps] in Hmatch; try discriminate.
    cbn in Hdisj.
    destruct (write_unstable_val v r1 next_bid kind) as [p' |] eqn:Hwp;
      cbn in Hw; [| discriminate].
    inversion Hw; subst; clear Hw.
    cbn [valid_stamps] in *.
    destruct (Nat.eqb utag0 utag && Nat.eqb pbid0 pbid);
      cbn [andb] in Hv; cbv iota in Hv; [| discriminate].
    eapply IH; eauto.
Qed.

Lemma write_unstable_mem_preserves_disjoint_addr : forall m p1 p2 next_bid kind m' a,
  places_disjoint p1 p2 ->
  addr_matches_place a p2 = true ->
  write_unstable_mem m p1 next_bid kind = Some m' ->
  addr_valid m a ->
  addr_valid m' a.
Proof.
  intros m p1 p2 next_bid kind m' a Hdisj Hmatch Hw Ha.
  unfold write_unstable_mem in Hw.
  destruct (lookup_owner m (p_owner p1)) as [oe |] eqn:Ho; [| discriminate].
  destruct (write_unstable_val (oe_val oe) (p_path p1) next_bid kind) as [v' |] eqn:Hv';
    [| discriminate].
  unfold addr_matches_place in Hmatch.
  apply andb_true_iff in Hmatch as [Ho_eq Hst_m].
  apply Nat.eqb_eq in Ho_eq.
  unfold addr_valid, addr_valid_b in *.
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner p1) (addr_owner a)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner p1)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hw).
    rewrite Ho in Ha; cbn in *.
    unfold places_disjoint, places_disjoint_b in Hdisj.
    rewrite <- Ho_eq, Nat.eqb_refl in Hdisj; cbn in Hdisj.
    assert (Hne : p_path p1 <> []).
    { intro E. rewrite E in Hdisj; cbn in Hdisj; discriminate. }
    rewrite (write_unstable_preserves_bid (oe_val oe) (p_path p1) next_bid kind v' Hne Hv').
    destruct (val_bid (oe_val oe)) as [rbid |] eqn:Hrb; [| discriminate].
    apply andb_true_iff in Ha as [Hrbid Hst].
    rewrite Hrbid; cbn.
    eapply write_unstable_preserves_disjoint_stamps; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner p1)
               (addr_owner a) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hw).
    exact Ha.
Qed.

Lemma write_tag_preserving_mem_preserves_addr : forall m pu tag payload m' a,
  write_tag_preserving_mem m pu tag payload = Some m' ->
  addr_valid m a ->
  addr_valid m' a.
Proof.
  intros m pu tag payload m' a Hw Ha.
  unfold write_tag_preserving_mem in Hw.
  destruct (lookup_owner m (p_owner pu)) as [oe |] eqn:Ho; [| discriminate].
  destruct (write_tag_preserving_val (oe_val oe) (p_path pu) tag payload) as [v' |] eqn:Hv';
    [| discriminate].
  unfold addr_valid, addr_valid_b in *.
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner pu) (addr_owner a)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner pu)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hw).
    rewrite Ho in Ha; cbn in *.
    rewrite (write_tag_preserving_bid (oe_val oe) (p_path pu) tag payload v' Hv').
    destruct (val_bid (oe_val oe)); [| discriminate].
    apply andb_true_iff in Ha as [Hrbid Hst].
    rewrite Hrbid; cbn.
    eapply write_tag_preserving_stamps; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner pu)
               (addr_owner a) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hw).
    exact Ha.
Qed.

Lemma push_cap_preserving_mem_preserves_addr : forall m pc elem m' old_len a,
  push_cap_preserving_mem m pc elem = Some (m', old_len) ->
  addr_valid m a ->
  addr_valid m' a.
Proof.
  intros m pc elem m' old_len a Hw Ha.
  unfold push_cap_preserving_mem in Hw.
  destruct (lookup_owner m (p_owner pc)) as [oe |] eqn:Ho; [| discriminate].
  destruct (read_val (oe_val oe) (p_path pc)) as [vc |] eqn:Hrv; [| discriminate].
  destruct vc as [| b_c cap_c elems_c | | | |]; try discriminate.
  destruct (push_cap_preserving_val (oe_val oe) (p_path pc) elem) as [v' |] eqn:Hv';
    [| discriminate].
  destruct (update_owner m (p_owner pc) {| oe_borrowed := oe_borrowed oe; oe_val := v' |})
    as [m'' |] eqn:Hu; [| discriminate].
  inversion Hw; subst; clear Hw.
  unfold addr_valid, addr_valid_b in *.
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner pc) (addr_owner a)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner pc)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hu).
    rewrite Ho in Ha; cbn in *.
    rewrite (push_cap_preserving_bid (oe_val oe) (p_path pc) elem v' Hv').
    destruct (val_bid (oe_val oe)); [| discriminate].
    apply andb_true_iff in Ha as [Hrbid Hst].
    rewrite Hrbid; cbn.
    eapply push_cap_preserving_stamps; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner pc)
               (addr_owner a) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hu).
    exact Ha.
Qed.

Definition loan_entry_wf_b (m : memory) (le : loan_entry) : bool :=
  addr_matches_place (ln_addr le) (ln_place le) &&
  (if loan_live le then addr_valid_b m (ln_addr le) else true).

Fixpoint nodup_nat_b (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (existsb (Nat.eqb x) rest) && nodup_nat_b rest
  end.

Lemma nodup_nat_b_sound : forall xs, nodup_nat_b xs = true -> NoDup xs.
Proof.
  induction xs as [| x rest IH]; intro H; cbn in H.
  - constructor.
  - apply andb_true_iff in H as [Hnot Hrest].
    constructor.
    + intro Hin. apply negb_true_iff in Hnot.
      assert (Hex : existsb (Nat.eqb x) rest = true).
      { apply existsb_exists. exists x; split; [exact Hin | apply Nat.eqb_refl]. }
      congruence.
    + apply IH; exact Hrest.
Qed.

Definition state_wf_b (st : machine_state) : bool :=
  nodup_nat_b (map ln_id (st_loans st)) &&
  forallb (loan_entry_wf_b (st_mem st)) (st_loans st) &&
  forallb (fun entry => fact_holds_b (st_mem st) (fst (snd entry)) (snd (snd entry)))
    (st_refs st).

Definition state_wf (st : machine_state) : Prop :=
  NoDup (map ln_id (st_loans st)) /\
  (forall le, In le (st_loans st) ->
    addr_matches_place (ln_addr le) (ln_place le) = true /\
    (loan_live le = true -> addr_valid (st_mem st) (ln_addr le))) /\
  (forall fid p cf, In (fid, (p, cf)) (st_refs st) -> fact_holds (st_mem st) p cf).

Lemma state_wf_b_sound : forall st, state_wf_b st = true -> state_wf st.
Proof.
  intros st H. unfold state_wf_b in H.
  rewrite !andb_true_iff in H. destruct H as [[Hnd Hloans] Hrefs].
  split; [now apply nodup_nat_b_sound |].
  split.
  - intros le Hin. rewrite forallb_forall in Hloans.
    specialize (Hloans le Hin). unfold loan_entry_wf_b in Hloans.
    apply andb_true_iff in Hloans as [Hm Hv].
    split; [exact Hm |].
    intro Hlive. rewrite Hlive in Hv. exact Hv.
  - intros fid p cf Hin. rewrite forallb_forall in Hrefs.
    specialize (Hrefs (fid, (p, cf)) Hin). cbn in Hrefs.
    now apply fact_holds_b_sound.
Qed.

Lemma map_remove_loan : forall loans l,
  map ln_id (remove_loan loans l) = filter (fun x => negb (Nat.eqb x l)) (map ln_id loans).
Proof.
  induction loans as [| le rest IH]; intro l; cbn; [reflexivity |].
  destruct (negb (Nat.eqb (ln_id le) l)); cbn; f_equal; apply IH.
Qed.

Lemma NoDup_filter : forall {A : Type} (f : A -> bool) (xs : list A),
  NoDup xs -> NoDup (filter f xs).
Proof.
  intros A f xs H. induction H as [| x xs Hnotin Hnd IH]; cbn; [constructor |].
  destruct (f x); [| exact IH].
  constructor; [| exact IH].
  intro Hin. apply filter_In in Hin as [Hin _]. contradiction.
Qed.

Lemma set_loan_suspended_ids : forall loans l susp,
  map ln_id (set_loan_suspended loans l susp) = map ln_id loans.
Proof.
  induction loans as [| le rest IH]; intros l susp; cbn; [reflexivity |].
  destruct (Nat.eqb (ln_id le) l); cbn; f_equal; apply IH.
Qed.

Lemma set_loan_mode_ids : forall loans l m,
  map ln_id (set_loan_mode loans l m) = map ln_id loans.
Proof.
  induction loans as [| le rest IH]; intros l m; cbn; [reflexivity |].
  destruct (Nat.eqb (ln_id le) l); cbn; f_equal; apply IH.
Qed.

Lemma set_loan_returned_ids : forall loans l,
  map ln_id (set_loan_returned loans l) = map ln_id loans.
Proof.
  induction loans as [| le rest IH]; intro l; cbn; [reflexivity |].
  destruct (Nat.eqb (ln_id le) l); cbn; f_equal; apply IH.
Qed.

Lemma has_loan_false_notin : forall loans l,
  has_loan loans l = false -> ~ In l (map ln_id loans).
Proof.
  intros loans l H Hin. unfold has_loan in H.
  apply in_map_iff in Hin as [le [Heq Hin]].
  assert (Htrue : existsb (fun le0 => Nat.eqb (ln_id le0) l) loans = true).
  { apply existsb_exists. exists le; split; [exact Hin | rewrite Heq; apply Nat.eqb_refl]. }
  congruence.
Qed.

Lemma read_val_to_scalar : forall m1 m2 p,
  read_val_mem m1 p = read_val_mem m2 p ->
  read_scalar_mem m1 p = read_scalar_mem m2 p.
Proof.
  intros m1 m2 p H. unfold read_scalar_mem, read_scalar.
  unfold read_val_mem in H.
  destruct (lookup_owner m1 (p_owner p)), (lookup_owner m2 (p_owner p));
    try rewrite H; try rewrite <- H; reflexivity.
Qed.

Lemma invalidate_refs_preserves_facts : forall m wp m' refs fid p cf,
  (forall rp, places_disjoint wp rp -> read_val_mem m' rp = read_val_mem m rp) ->
  (forall fid0 rp cf0, In (fid0, (rp, cf0)) refs -> fact_holds m rp cf0) ->
  In (fid, (p, cf)) (invalidate_overlapping_refs wp refs) ->
  fact_holds m' p cf.
Proof.
  intros m wp m' refs fid p cf Hframe Hrefs Hin.
  unfold invalidate_overlapping_refs in Hin.
  apply filter_In in Hin as [Hin_orig Hdisj].
  cbn in Hdisj.
  specialize (Hrefs fid p cf Hin_orig).
  pose proof (read_val_to_scalar m' m p (Hframe p Hdisj)) as Hread.
  destruct cf; cbn in *; try rewrite Hread; exact Hrefs.
Qed.

Lemma invalidate_refs_preserves_scalar_facts : forall m wp m' refs fid p cf,
  (forall rp, places_disjoint wp rp -> read_scalar_mem m' rp = read_scalar_mem m rp) ->
  (forall fid0 rp cf0, In (fid0, (rp, cf0)) refs -> fact_holds m rp cf0) ->
  In (fid, (p, cf)) (invalidate_overlapping_refs wp refs) ->
  fact_holds m' p cf.
Proof.
  intros m wp m' refs fid p cf Hframe Hrefs Hin.
  unfold invalidate_overlapping_refs in Hin.
  apply filter_In in Hin as [Hin_orig Hdisj].
  cbn in Hdisj.
  specialize (Hrefs fid p cf Hin_orig).
  pose proof (Hframe p Hdisj) as Hread.
  destruct cf; cbn in *; try rewrite Hread; exact Hrefs.
Qed.

Lemma write_unstable_mem_frame : forall m p1 p2 next_bid kind m',
  places_disjoint p1 p2 ->
  write_unstable_mem m p1 next_bid kind = Some m' ->
  read_val_mem m' p2 = read_val_mem m p2.
Proof.
  intros m p1 p2 next_bid kind m' Hdisj Hw.
  unfold read_val_mem, write_unstable_mem in *.
  destruct (lookup_owner m (p_owner p1)) as [oe |] eqn:Ho; [| discriminate].
  destruct (write_unstable_val (oe_val oe) (p_path p1) next_bid kind) as [v' |] eqn:Hv';
    [| discriminate].
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner p1) (p_owner p2)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner p1)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hw).
    rewrite Ho; cbn.
    unfold places_disjoint, places_disjoint_b in Hdisj.
    rewrite <- Heq, Nat.eqb_refl in Hdisj; cbn in Hdisj.
    clear - Hdisj Hv'.
    revert v' Hdisj Hv'. generalize (oe_val oe) as v0. generalize (p_path p2) as s2.
    induction (p_path p1) as [| a r1 IH]; intros [| b r2] v0 v' Hdisj Hv';
      cbn [steps_disjoint_b] in Hdisj; try discriminate.
    destruct a, b, v0;
      cbn [steps_disjoint_b step_disjoint_b proj_step_beq write_unstable_val option_map]
        in Hdisj, Hv'; try discriminate.
    + destruct (Nat.eqb f f0) eqn:Ef.
      * apply Nat.eqb_eq in Ef; subst f0.
        cbn [negb] in Hdisj; cbv iota in Hdisj.
        destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (write_unstable_val fv r1 next_bid kind) as [fv' |] eqn:Hwfv; [| discriminate].
        destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup; cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f fv' fs' Hup), Hf.
        eapply IH; eauto.
      * apply Nat.eqb_neq in Ef.
        destruct (assoc_get Nat.eqb fields f); [| discriminate].
        destruct (write_unstable_val o r1 next_bid kind); [| discriminate].
        destruct (assoc_update Nat.eqb fields f o0) as [fs' |] eqn:Hup; cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 o0 fs' Ef Hup).
        reflexivity.
    + destruct (Nat.eqb idx idx0) eqn:Ei.
      * apply Nat.eqb_eq in Ei; subst idx0.
        cbn [negb] in Hdisj; cbv iota in Hdisj.
        destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (write_unstable_val ev r1 next_bid kind) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems idx ev') as [elems' |] eqn:Hls; cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        rewrite (list_set_nth_same elems idx ev' elems' Hls), He.
        eapply IH; eauto.
      * apply Nat.eqb_neq in Ei.
        destruct (nth_error elems idx); [| discriminate].
        destruct (write_unstable_val o r1 next_bid kind); [| discriminate].
        destruct (list_set elems idx o0) as [elems' |] eqn:Hls; cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        rewrite (list_set_nth_other elems idx idx0 o0 elems' Ei Hls).
        reflexivity.
    + destruct (Nat.ltb idx off || Nat.leb (off + len) idx) eqn:Hsep;
        [| cbv iota in Hdisj; discriminate].
      apply orb_true_iff in Hsep.
      assert (Hout : idx < off \/ off + len <= idx).
      { destruct Hsep as [H1 | H2]; [left; now apply Nat.ltb_lt | right; now apply Nat.leb_le]. }
      destruct (nth_error elems idx); [| discriminate].
      destruct (write_unstable_val o r1 next_bid kind); [| discriminate].
      destruct (list_set elems idx o0) as [elems' |] eqn:Hls; cbn in Hv'; [| discriminate].
      inversion Hv'; subst; cbn [read_val].
      rewrite (list_set_length elems idx o0 elems' Hls).
      destruct (Nat.leb (off + len) (length elems)); [| reflexivity].
      destruct r2 as [| s2' r2'].
      * f_equal; f_equal; apply firstn_skipn_ext; [eapply list_set_length; eauto |].
        intros j Hj1 Hj2. apply list_set_nth_other with (i := idx) (v := o0); [lia | exact Hls].
      * destruct s2'; try reflexivity.
        destruct (Nat.ltb idx0 len) eqn:Hk; [| reflexivity].
        apply Nat.ltb_lt in Hk.
        rewrite (list_set_nth_other elems idx (off + idx0) o0 elems'); [reflexivity | lia | exact Hls].
    + destruct (write_unstable_val v0 r1 next_bid kind) as [p' |] eqn:Hwp;
        cbn in Hv'; [| discriminate].
      inversion Hv'; subst; cbn [read_val]. eapply IH; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner p1)
               (p_owner p2) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hw).
    reflexivity.
Qed.

Lemma write_tag_preserving_mem_frame : forall m pu p2 tag payload m',
  places_disjoint (PUnionPayload pu) p2 ->
  write_tag_preserving_mem m pu tag payload = Some m' ->
  read_val_mem m' p2 = read_val_mem m p2.
Proof.
  intros m pu p2 tag payload m' Hdisj Hw.
  unfold read_val_mem, write_tag_preserving_mem in *.
  destruct (lookup_owner m (p_owner pu)) as [oe |] eqn:Ho; [| discriminate].
  destruct (write_tag_preserving_val (oe_val oe) (p_path pu) tag payload)
    as [v' |] eqn:Hv'; [| discriminate].
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner pu) (p_owner p2)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner pu)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hw).
    rewrite Ho; cbn.
    unfold places_disjoint, places_disjoint_b, PUnionPayload in Hdisj; cbn in Hdisj.
    rewrite <- Heq, Nat.eqb_refl in Hdisj; cbn in Hdisj.
    clear - Hdisj Hv'.
    revert v' Hdisj Hv'. generalize (oe_val oe) as v0. generalize (p_path p2) as s2.
    induction (p_path pu) as [| a r1 IH]; intros [| b r2] v0 v' Hdisj Hv'.
    + cbn in Hdisj; discriminate.
    + cbn in Hdisj. destruct b; cbn in Hdisj; try discriminate.
    + cbn in Hdisj; discriminate.
    + cbn [app] in Hdisj. destruct a, b, v0;
        cbn [steps_disjoint_b step_disjoint_b proj_step_beq write_tag_preserving_val option_map]
          in Hdisj, Hv'; try discriminate.
      * destruct (Nat.eqb f f0) eqn:Ef.
        -- apply Nat.eqb_eq in Ef; subst f0.
           cbn [negb] in Hdisj; cbv iota in Hdisj.
           destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
           destruct (write_tag_preserving_val fv r1 tag payload) as [fv' |] eqn:Hwfv; [| discriminate].
           destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f fv' fs' Hup), Hf.
           eapply IH; eauto.
        -- apply Nat.eqb_neq in Ef.
           destruct (assoc_get Nat.eqb fields f); [| discriminate].
           destruct (write_tag_preserving_val o r1 tag payload); [| discriminate].
           destruct (assoc_update Nat.eqb fields f o0) as [fs' |] eqn:Hup;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 o0 fs' Ef Hup).
           reflexivity.
      * destruct (Nat.eqb idx idx0) eqn:Ei.
        -- apply Nat.eqb_eq in Ei; subst idx0.
           cbn [negb] in Hdisj; cbv iota in Hdisj.
           destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
           destruct (write_tag_preserving_val ev r1 tag payload) as [ev' |] eqn:Hwev; [| discriminate].
           destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (list_set_nth_same elems idx ev' elems' Hls), He.
           eapply IH; eauto.
        -- apply Nat.eqb_neq in Ei.
           destruct (nth_error elems idx); [| discriminate].
           destruct (write_tag_preserving_val o r1 tag payload); [| discriminate].
           destruct (list_set elems idx o0) as [elems' |] eqn:Hls;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (list_set_nth_other elems idx idx0 o0 elems' Ei Hls).
           reflexivity.
      * destruct (Nat.ltb idx off || Nat.leb (off + len) idx) eqn:Hsep;
          [| cbv iota in Hdisj; discriminate].
        apply orb_true_iff in Hsep.
        assert (Hout : idx < off \/ off + len <= idx).
        { destruct Hsep as [H1 | H2]; [left; now apply Nat.ltb_lt | right; now apply Nat.leb_le]. }
        destruct (nth_error elems idx); [| discriminate].
        destruct (write_tag_preserving_val o r1 tag payload); [| discriminate].
        destruct (list_set elems idx o0) as [elems' |] eqn:Hls;
          cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        rewrite (list_set_length elems idx o0 elems' Hls).
        destruct (Nat.leb (off + len) (length elems)); [| reflexivity].
        destruct r2 as [| s2' r2'].
        -- f_equal; f_equal; apply firstn_skipn_ext; [eapply list_set_length; eauto |].
           intros j Hj1 Hj2. apply list_set_nth_other with (i := idx) (v := o0); [lia | exact Hls].
        -- destruct s2'; try reflexivity.
           destruct (Nat.ltb idx0 len) eqn:Hk; [| reflexivity].
           apply Nat.ltb_lt in Hk.
           rewrite (list_set_nth_other elems idx (off + idx0) o0 elems');
             [reflexivity | lia | exact Hls].
      * destruct (write_tag_preserving_val v0 r1 tag payload) as [p' |] eqn:Hwp;
          cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val]. eapply IH; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner pu)
               (p_owner p2) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hw).
    reflexivity.
Qed.

Lemma firstn_skipn_app_le : forall {A : Type} (xs ys : list A) off len,
  off + len <= length xs ->
  firstn len (skipn off (xs ++ ys)) = firstn len (skipn off xs).
Proof.
  intros A xs ys off len Hle.
  rewrite skipn_app, firstn_app, length_skipn.
  assert (H0 : len - (length xs - off) = 0) by lia.
  rewrite H0; cbn. apply app_nil_r.
Qed.

Definition step_nonempty_b (s : proj_step) : bool :=
  match s with
  | SSlice _ len => Nat.ltb 0 len
  | _ => true
  end.

Lemma step_nonempty_b_sound : forall steps,
  forallb step_nonempty_b steps = true -> Forall step_nonempty steps.
Proof.
  induction steps as [| s rest IH]; intro H; [constructor |].
  cbn in H. apply andb_true_iff in H as [Hs Hr].
  constructor; [destruct s; cbn in *; auto; now apply Nat.ltb_lt | now apply IH].
Qed.

Lemma read_scalar_empty_slice_none : forall steps v,
  forallb step_nonempty_b steps = false ->
  read_scalar v steps = None.
Proof.
  assert (Haux : forall k steps v,
    length steps <= k ->
    forallb step_nonempty_b steps = false ->
    read_scalar v steps = None).
  { induction k as [| k' IH]; intros [| s rest] v Hlen H;
      [cbn in H; discriminate | cbn in Hlen; lia | cbn in H; discriminate |].
    cbn in H. destruct (step_nonempty_b s) eqn:Hs; cbn [andb] in H; cbv iota in H.
    - destruct s, v; unfold read_scalar in *; cbn [read_val]; try reflexivity.
      + destruct (assoc_get Nat.eqb fields f); [eapply IH; [cbn in Hlen; lia | exact H] | reflexivity].
      + destruct (nth_error elems idx); [eapply IH; [cbn in Hlen; lia | exact H] | reflexivity].
      + destruct (Nat.leb (off + len) (length elems)); [| reflexivity].
        destruct rest as [| s' rest']; [reflexivity |].
        destruct s'; [reflexivity | | reflexivity | reflexivity | reflexivity].
        destruct (Nat.ltb idx len); [| reflexivity].
        destruct (nth_error elems (off + idx)); [| reflexivity].
        cbn [forallb step_nonempty_b] in H. cbn [andb] in H; cbv iota in H.
        eapply IH; [cbn in Hlen; lia | exact H].
      + destruct rest; [cbn in H; discriminate | reflexivity].
      + eapply IH; [cbn in Hlen; lia | exact H].
    - destruct s; cbn in Hs; try discriminate.
      destruct len; [| discriminate].
      destruct v; unfold read_scalar; cbn [read_val]; try reflexivity.
      destruct (Nat.leb (off + 0) (length elems)); [| reflexivity].
      destruct rest as [| s' rest']; [reflexivity |].
      destruct s'; reflexivity. }
  intros steps v H. eapply Haux; [apply le_n | exact H].
Qed.

Lemma push_cap_preserving_mem_frame : forall m pc p2 elem m' old_len,
  places_disjoint (PElem pc old_len) p2 ->
  Forall step_nonempty (p_path p2) ->
  push_cap_preserving_mem m pc elem = Some (m', old_len) ->
  read_val_mem m' p2 = read_val_mem m p2.
Proof.
  intros m pc p2 elem m' old_len Hdisj Hne Hw.
  unfold read_val_mem, push_cap_preserving_mem in *.
  destruct (lookup_owner m (p_owner pc)) as [oe |] eqn:Ho; [| discriminate].
  destruct (read_val (oe_val oe) (p_path pc)) as [vc |] eqn:Hrv; [| discriminate].
  destruct vc as [| b_c cap_c elems_c | | | |]; try discriminate.
  destruct (push_cap_preserving_val (oe_val oe) (p_path pc) elem) as [v' |] eqn:Hv';
    [| discriminate].
  destruct (update_owner m (p_owner pc) {| oe_borrowed := oe_borrowed oe; oe_val := v' |})
    as [m'' |] eqn:Hu; [| discriminate].
  inversion Hw; subst; clear Hw.
  unfold update_owner, lookup_owner in *.
  destruct (Nat.eq_dec (p_owner pc) (p_owner p2)) as [Heq | Hneq].
  - rewrite <- Heq in *.
    rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq m (p_owner pc)
               {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hu).
    rewrite Ho; cbn.
    unfold places_disjoint, places_disjoint_b, PElem in Hdisj; cbn in Hdisj.
    rewrite <- Heq, Nat.eqb_refl in Hdisj; cbn in Hdisj.
    clear - Hdisj Hne Hv' Hrv.
    revert v' Hdisj Hne Hv' Hrv. generalize (oe_val oe) as v0. generalize (p_path p2) as s2.
    induction (p_path pc) as [| a r1 IH]; intros [| b r2] v0 v' Hdisj Hne Hv' Hrv;
      cbn [app] in Hdisj; cbn [steps_disjoint_b] in Hdisj; try discriminate.
    + destruct v0; cbn [push_cap_preserving_val] in Hv'; try discriminate.
      cbn [read_val] in Hrv; inversion Hrv as [[Eb Ec Ee]]; subst b_c cap_c elems_c; clear Hrv.
      destruct (Nat.ltb (length elems) cap) eqn:Hcap; cbv iota in Hv';
        [| discriminate]; inversion Hv'; subst; clear Hv'.
      inversion Hne as [| ? ? Hb_ne Hr2_ne]; subst.
      destruct b; cbn [steps_disjoint_b step_disjoint_b proj_step_beq] in Hdisj;
        cbv iota in Hdisj; try discriminate.
      * destruct (Nat.eqb (length elems) idx) eqn:Elen; [cbn in Hdisj; discriminate |].
        apply Nat.eqb_neq in Elen.
        cbn [read_val].
        destruct (Nat.lt_ge_cases idx (length elems)) as [Hlt | Hge].
        -- rewrite nth_error_app1 by exact Hlt. reflexivity.
        -- assert (Hge1 : length (elems ++ [elem]) <= idx) by (rewrite length_app; cbn; lia).
           rewrite (proj2 (nth_error_None _ idx) Hge1), (proj2 (nth_error_None _ idx) Hge).
           reflexivity.
      * destruct (Nat.ltb (length elems) off || Nat.leb (off + len) (length elems))
          eqn:Hsep; [| cbn in Hdisj; discriminate].
        apply orb_true_iff in Hsep.
        cbn [read_val].
        destruct (Nat.leb (off + len) (length elems)) eqn:Hb1.
        -- apply Nat.leb_le in Hb1.
           assert (Hb2 : Nat.leb (off + len) (length (elems ++ [elem])) = true)
             by (rewrite length_app; cbn; apply Nat.leb_le; lia).
           rewrite Hb2.
           destruct r2 as [| s2' r2'].
           ++ f_equal; f_equal. apply firstn_skipn_app_le; exact Hb1.
           ++ destruct s2'; try reflexivity.
              destruct (Nat.ltb idx len) eqn:Hk; [| reflexivity].
              apply Nat.ltb_lt in Hk.
              rewrite nth_error_app1 by lia; reflexivity.
        -- apply Nat.leb_gt in Hb1.
           cbn in Hb_ne.
           assert (Hout : length elems < off \/ off + len <= length elems).
           { destruct Hsep as [H1 | H2]; [left; now apply Nat.ltb_lt | right; now apply Nat.leb_le]. }
           assert (Hb2 : Nat.leb (off + len) (length (elems ++ [elem])) = false)
             by (rewrite length_app; cbn; apply Nat.leb_gt; lia).
           rewrite Hb2; reflexivity.
    + inversion Hne as [| ? ? Hb_ne Hr2_ne]; subst.
      destruct a, b, v0;
        cbn [steps_disjoint_b step_disjoint_b proj_step_beq push_cap_preserving_val option_map]
          in Hdisj, Hv'; try discriminate.
      * destruct (Nat.eqb f f0) eqn:Ef.
        -- apply Nat.eqb_eq in Ef; subst f0.
           cbn [negb] in Hdisj; cbv iota in Hdisj.
           destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
           destruct (push_cap_preserving_val fv r1 elem) as [fv' |] eqn:Hwfv; [| discriminate].
           destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f fv' fs' Hup), Hf.
           cbn [read_val] in Hrv; rewrite Hf in Hrv.
           eapply IH; eauto.
        -- apply Nat.eqb_neq in Ef.
           destruct (assoc_get Nat.eqb fields f); [| discriminate].
           destruct (push_cap_preserving_val o r1 elem); [| discriminate].
           destruct (assoc_update Nat.eqb fields f o0) as [fs' |] eqn:Hup;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq fields f f0 o0 fs' Ef Hup).
           reflexivity.
      * destruct (Nat.eqb idx idx0) eqn:Ei.
        -- apply Nat.eqb_eq in Ei; subst idx0.
           cbn [negb] in Hdisj; cbv iota in Hdisj.
           destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
           destruct (push_cap_preserving_val ev r1 elem) as [ev' |] eqn:Hwev; [| discriminate].
           destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (list_set_nth_same elems idx ev' elems' Hls), He.
           cbn [read_val] in Hrv; rewrite He in Hrv.
           eapply IH; eauto.
        -- apply Nat.eqb_neq in Ei.
           destruct (nth_error elems idx); [| discriminate].
           destruct (push_cap_preserving_val o r1 elem); [| discriminate].
           destruct (list_set elems idx o0) as [elems' |] eqn:Hls;
             cbn in Hv'; [| discriminate].
           inversion Hv'; subst; cbn [read_val].
           rewrite (list_set_nth_other elems idx idx0 o0 elems' Ei Hls).
           reflexivity.
      * destruct (Nat.ltb idx off || Nat.leb (off + len) idx) eqn:Hsep;
          [| cbv iota in Hdisj; discriminate].
        apply orb_true_iff in Hsep.
        assert (Hout : idx < off \/ off + len <= idx).
        { destruct Hsep as [H1 | H2]; [left; now apply Nat.ltb_lt | right; now apply Nat.leb_le]. }
        destruct (nth_error elems idx); [| discriminate].
        destruct (push_cap_preserving_val o r1 elem); [| discriminate].
        destruct (list_set elems idx o0) as [elems' |] eqn:Hls;
          cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        rewrite (list_set_length elems idx o0 elems' Hls).
        destruct (Nat.leb (off + len) (length elems)); [| reflexivity].
        destruct r2 as [| s2' r2'].
        -- f_equal; f_equal; apply firstn_skipn_ext; [eapply list_set_length; eauto |].
           intros j Hj1 Hj2. apply list_set_nth_other with (i := idx) (v := o0); [lia | exact Hls].
        -- destruct s2'; try reflexivity.
           destruct (Nat.ltb idx0 len) eqn:Hk; [| reflexivity].
           apply Nat.ltb_lt in Hk.
           rewrite (list_set_nth_other elems idx (off + idx0) o0 elems');
             [reflexivity | lia | exact Hls].
      * destruct (push_cap_preserving_val v0 r1 elem) as [p' |] eqn:Hwp;
          cbn in Hv'; [| discriminate].
        inversion Hv'; subst; cbn [read_val].
        cbn [read_val] in Hrv. eapply IH; eauto.
  - rewrite (assoc_get_update_other Nat.eqb Nat.eqb_eq m (p_owner pc)
               (p_owner p2) {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m' Hneq Hu).
    reflexivity.
Qed.

Lemma step_preserves_state_wf : forall st op st',
  state_wf st -> Step st op st' -> state_wf st'.
Proof.
  intros st0 op0 st0' Hwf Hstep.
  inversion Hstep as [? ? ? Hexec]; subst.
  destruct Hwf as [Hnd [Hloans Hrefs]].
  destruct op0; cbn [exec_step] in Hexec.
  - (* OpBorrow *)
    destruct mode; try discriminate.
    all: destruct (has_loan (st_loans st0) l) eqn:Hhas; [discriminate |].
    all: destruct (resolve_addr (st_mem st0) p) as [addr |] eqn:Hres; [| discriminate].
    all: destruct (match parent with
                   | None => Some l
                   | Some pid => match lookup_loan (st_loans st0) pid with
                                 | Some pe => if loan_active pe && negb (loan_mode_beq (ln_mode pe) LReserved) && within_b p (ln_place pe) && can_borrow_from_parent _ (ln_mode pe) then Some (ln_root_loan pe) else None
                                 | None => None
                                 end
                   end) as [root_id |] eqn:Hpar; [| discriminate].
    all: destruct (forallb (borrow_compatible _ parent p) (st_loans st0)); [| discriminate].
    all: inversion Hexec; subst; clear Hexec.
    all: cbn [st_loans st_mem st_refs].
    all: split; [constructor; [destruct parent; rewrite ?set_loan_suspended_ids; now apply has_loan_false_notin |
                               destruct parent; rewrite ?set_loan_suspended_ids; exact Hnd]
                | split; [| exact Hrefs]].
    all: intros le [<- | Hin]; split;
      [ cbn; now apply resolve_addr_matches_place in Hres
      | intro; cbn; now apply resolve_addr_valid in Hres
      | destruct parent as [pid |];
        [ try exact (proj1 (Hloans le Hin));
          unfold set_loan_suspended in Hin;
          apply in_map_iff in Hin as [le0 [<- Hin0]];
          destruct (Nat.eqb (ln_id le0) pid); cbn; exact (proj1 (Hloans le0 Hin0))
        | exact (proj1 (Hloans le Hin)) ]
      | intro Hlive; destruct parent as [pid |];
        [ try exact (proj2 (Hloans le Hin) Hlive);
          unfold set_loan_suspended in Hin;
          apply in_map_iff in Hin as [le0 [<- Hin0]];
          destruct (Nat.eqb (ln_id le0) pid); cbn in *; exact (proj2 (Hloans le0 Hin0) Hlive)
        | exact (proj2 (Hloans le Hin) Hlive) ] ].
  - (* OpReserve *)
    destruct (has_loan (st_loans st0) l) eqn:Hhas; [discriminate |].
    destruct (resolve_addr (st_mem st0) p) as [addr |] eqn:Hres; [| discriminate].
    destruct (match parent with
              | None => Some l
              | Some pid => match lookup_loan (st_loans st0) pid with
                            | Some pe => if loan_active pe && negb (loan_mode_beq (ln_mode pe) LReserved) && within_b p (ln_place pe) && can_borrow_from_parent LReserved (ln_mode pe) then Some (ln_root_loan pe) else None
                            | None => None
                            end
              end); [| discriminate].
    destruct (forallb (borrow_compatible LReserved parent p) (st_loans st0)); [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + constructor; [now apply has_loan_false_notin | exact Hnd].
    + intros le [<- | Hin]; split; cbn.
      * now apply resolve_addr_matches_place in Hres.
      * intro; now apply resolve_addr_valid in Hres.
      * exact (proj1 (Hloans le Hin)).
      * intro Hlive; exact (proj2 (Hloans le Hin) Hlive).
    + exact Hrefs.
  - (* OpActivate *)
    destruct (lookup_loan (st_loans st0) l) as [le |] eqn:Hlk; [| discriminate].
    destruct (loan_active le && loan_mode_beq (ln_mode le) LReserved && addr_valid_b (st_mem st0) (ln_addr le)); [| discriminate].
    destruct (forallb _ (st_loans st0)); [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + destruct (ln_parent le); [rewrite set_loan_suspended_ids |];
        rewrite set_loan_mode_ids; exact Hnd.
    + intros le' Hin; split.
      * destruct (ln_parent le) as [pid |].
        -- apply in_map_iff in Hin as [le1 [<- Hin1]].
           apply in_map_iff in Hin1 as [le0 [<- Hin0]].
           destruct (Nat.eqb (ln_id le0) l); cbn;
             destruct (Nat.eqb (ln_id le0) pid); cbn; exact (proj1 (Hloans le0 Hin0)).
        -- apply in_map_iff in Hin as [le0 [<- Hin0]].
           destruct (Nat.eqb (ln_id le0) l); cbn; exact (proj1 (Hloans le0 Hin0)).
      * intro Hlive; destruct (ln_parent le) as [pid |].
        -- apply in_map_iff in Hin as [le1 [<- Hin1]].
           apply in_map_iff in Hin1 as [le0 [<- Hin0]].
           destruct (Nat.eqb (ln_id le0) l); cbn in *;
             destruct (Nat.eqb (ln_id le0) pid); cbn in *; exact (proj2 (Hloans le0 Hin0) Hlive).
        -- apply in_map_iff in Hin as [le0 [<- Hin0]].
           destruct (Nat.eqb (ln_id le0) l); cbn in *; exact (proj2 (Hloans le0 Hin0) Hlive).
    + exact Hrefs.
  - (* OpCancelReservation *)
    destruct (lookup_loan (st_loans st0) l); [| discriminate].
    destruct (loan_active l0 && loan_mode_beq (ln_mode l0) LReserved && negb (has_live_child (st_loans st0) l)); [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + rewrite map_remove_loan. now apply NoDup_filter.
    + intros le Hin. unfold remove_loan in Hin. apply filter_In in Hin as [Hin _].
      exact (Hloans le Hin).
    + exact Hrefs.
  - (* OpRead *)
    destruct via.
    + destruct (lookup_loan (st_loans st0) l); [| discriminate].
      destruct (loan_active l0 && negb (loan_mode_beq (ln_mode l0) LReserved) && within_b p (ln_place l0) && addr_valid_b (st_mem st0) (ln_addr l0)); [| discriminate].
      destruct (read_scalar_mem (st_mem st0) p); inversion Hexec; subst;
        split; [exact Hnd | split; [exact Hloans | exact Hrefs]].
    + destruct (direct_read_ok p (st_loans st0)); [| discriminate].
      destruct (read_scalar_mem (st_mem st0) p); inversion Hexec; subst;
        split; [exact Hnd | split; [exact Hloans | exact Hrefs]].
  - (* OpStableWrite *)
    destruct (match via with
              | Some l => match lookup_loan (st_loans st0) l with
                          | Some le => loan_active le && (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) && within_b p (ln_place le) && addr_valid_b (st_mem st0) (ln_addr le)
                          | None => false
                          end
              | None => direct_write_ok p (st_loans st0)
              end); [| discriminate].
    destruct (write_stable_mem (st_mem st0) p v) as [m' |] eqn:Hw; [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + exact Hnd.
    + intros le Hin; split; [exact (proj1 (Hloans le Hin)) |].
      intro Hlive. eapply write_stable_mem_preserves_addr; [exact Hw | exact (proj2 (Hloans le Hin) Hlive)].
    + intros fid rp cf Hin.
      eapply invalidate_refs_preserves_facts; [| exact Hrefs | exact Hin].
      intros rp0 Hdisj. eapply write_stable_mem_frame; [exact Hdisj | exact Hw].
  - (* OpUnstableWrite *)
    destruct (no_overlapping_loan_at p (st_loans st0)) eqn:Hno; [| discriminate].
    destruct (write_unstable_mem (st_mem st0) p (st_next_bid st0) kind) as [m' |] eqn:Hw; [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + exact Hnd.
    + intros le Hin; split; [exact (proj1 (Hloans le Hin)) |].
      intro Hlive.
      unfold no_overlapping_loan_at in Hno. rewrite forallb_forall in Hno.
      specialize (Hno le Hin). rewrite Hlive in Hno; cbn in Hno.
      destruct (Hloans le Hin) as [Hmatch Hvalid].
      eapply write_unstable_mem_preserves_disjoint_addr;
        [exact Hno | exact Hmatch | exact Hw | exact (Hvalid Hlive)].
    + intros fid rp cf Hin.
      eapply invalidate_refs_preserves_facts; [| exact Hrefs | exact Hin].
      intros rp0 Hdisj. eapply write_unstable_mem_frame; [exact Hdisj | exact Hw].
  - (* OpTagPreservingUnionWrite *)
    destruct (match via with
              | Some l => match lookup_loan (st_loans st0) l with
                          | Some le => loan_active le && (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) && within_b pu (ln_place le) && addr_valid_b (st_mem st0) (ln_addr le)
                          | None => false
                          end
              | None => no_overlapping_exclusive_or_reserved pu None (st_loans st0)
              end); [| discriminate].
    destruct (write_tag_preserving_mem (st_mem st0) pu expected_tag new_payload) as [m' |] eqn:Hw;
      [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + exact Hnd.
    + intros le Hin; split; [exact (proj1 (Hloans le Hin)) |].
      intro Hlive. eapply write_tag_preserving_mem_preserves_addr;
        [exact Hw | exact (proj2 (Hloans le Hin) Hlive)].
    + intros fid rp cf Hin.
      eapply invalidate_refs_preserves_facts; [| exact Hrefs | exact Hin].
      intros rp0 Hdisj. eapply write_tag_preserving_mem_frame; [exact Hdisj | exact Hw].
  - (* OpCapPreservingPush *)
    destruct (match via with
              | Some l => match lookup_loan (st_loans st0) l with
                          | Some le => loan_active le && (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) && within_b pc (ln_place le) && addr_valid_b (st_mem st0) (ln_addr le) && no_overlapping_exclusive_or_reserved pc (Some l) (st_loans st0)
                          | None => false
                          end
              | None => no_overlapping_exclusive_or_reserved pc None (st_loans st0)
              end); [| discriminate].
    destruct (push_cap_preserving_mem (st_mem st0) pc new_elem) as [[m' old_len] |] eqn:Hw;
      [| discriminate].
    destruct (forallb _ (st_loans st0)); [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + exact Hnd.
    + intros le Hin; split; [exact (proj1 (Hloans le Hin)) |].
      intro Hlive. eapply push_cap_preserving_mem_preserves_addr;
        [exact Hw | exact (proj2 (Hloans le Hin) Hlive)].
    + intros fid rp cf Hin.
      eapply invalidate_refs_preserves_scalar_facts; [| exact Hrefs | exact Hin].
      intros rp0 Hdisj.
      destruct (forallb step_nonempty_b (p_path rp0)) eqn:Hne.
      * apply read_val_to_scalar. eapply push_cap_preserving_mem_frame;
          [exact Hdisj | now apply step_nonempty_b_sound | exact Hw].
      * unfold read_scalar_mem.
        destruct (lookup_owner m' (p_owner rp0)), (lookup_owner (st_mem st0) (p_owner rp0));
          rewrite ?read_scalar_empty_slice_none by exact Hne; reflexivity.
  - (* OpEndLoan *)
    destruct (lookup_loan (st_loans st0) l) as [le |] eqn:Hlk; [| discriminate].
    destruct (loan_active le && negb (has_live_child (st_loans st0) l)); [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + destruct (ln_parent le), (ln_mode le);
        rewrite ?set_loan_suspended_ids, map_remove_loan; now apply NoDup_filter.
    + intros le0 Hin; split.
      * destruct (ln_parent le) as [pid |], (ln_mode le);
          try (apply in_map_iff in Hin as [le1 [<- Hin1]];
               apply filter_In in Hin1 as [Hin1 _];
               destruct (Nat.eqb (ln_id le1) pid); cbn; exact (proj1 (Hloans le1 Hin1)));
          apply filter_In in Hin as [Hin _]; exact (proj1 (Hloans le0 Hin)).
      * intro Hlive; destruct (ln_parent le) as [pid |], (ln_mode le);
          try (apply in_map_iff in Hin as [le1 [<- Hin1]];
               apply filter_In in Hin1 as [Hin1 _];
               destruct (Nat.eqb (ln_id le1) pid); cbn in *; exact (proj2 (Hloans le1 Hin1) Hlive));
          apply filter_In in Hin as [Hin _]; exact (proj2 (Hloans le0 Hin) Hlive).
    + exact Hrefs.
  - (* OpReturnLoan *)
    destruct (lookup_loan (st_loans st0) l) as [le |] eqn:Hlk; [| discriminate].
    destruct (loan_active le && negb (loan_mode_beq (ln_mode le) LReserved) &&
              negb (has_live_child (st_loans st0) l) && addr_valid_b (st_mem st0) (ln_addr le));
      [| discriminate].
    destruct (lookup_owner (st_mem st0) (p_owner (ln_place le))) as [oe |] eqn:Ho; [| discriminate].
    destruct (oe_borrowed oe); [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + rewrite set_loan_returned_ids; exact Hnd.
    + intros le0 Hin; split.
      * apply in_map_iff in Hin as [le1 [<- Hin1]].
        destruct (Nat.eqb (ln_id le1) l); cbn; exact (proj1 (Hloans le1 Hin1)).
      * intro Hlive; apply in_map_iff in Hin as [le1 [<- Hin1]].
        destruct (Nat.eqb (ln_id le1) l); cbn in *;
          [discriminate | exact (proj2 (Hloans le1 Hin1) Hlive)].
    + exact Hrefs.
  - (* OpLoopStep *)
    destruct (Nat.eqb cursor_id new_cursor_id); [discriminate |].
    destruct (has_loan (st_loans st0) new_cursor_id) eqn:Hhas; [discriminate |].
    destruct (lookup_loan (st_loans st0) cursor_id) as [ce |] eqn:Hlk; [| discriminate].
    destruct (loan_active ce && loan_mode_beq (ln_mode ce) LExclusive &&
              negb (has_live_child (st_loans st0) cursor_id) &&
              within_b sub_place (ln_place ce) && addr_valid_b (st_mem st0) (ln_addr ce));
      [| discriminate].
    destruct (resolve_addr (st_mem st0) sub_place) as [addr |] eqn:Hres; [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [| split]; cbn.
    + constructor.
      * rewrite map_remove_loan. intro Hin. apply filter_In in Hin as [Hin _].
        now apply (has_loan_false_notin _ _ Hhas).
      * rewrite map_remove_loan. now apply NoDup_filter.
    + intros le [<- | Hin]; split; cbn.
      * now apply resolve_addr_matches_place in Hres.
      * intro; now apply resolve_addr_valid in Hres.
      * apply filter_In in Hin as [Hin _]. exact (proj1 (Hloans le Hin)).
      * intro Hlive; apply filter_In in Hin as [Hin _]. exact (proj2 (Hloans le Hin) Hlive).
    + exact Hrefs.
  - (* OpAssumeRefinement *)
    destruct (fact_holds_b (st_mem st0) p cf) eqn:Hf; [| discriminate].
    inversion Hexec; subst; clear Hexec; split; [exact Hnd | split; [exact Hloans |]]; cbn.
    intros fid0 p0 cf0 Hin.
    assert (Haux : forall refs0,
      (forall f1 p1 c1, In (f1, (p1, c1)) refs0 -> fact_holds (st_mem st0) p1 c1) ->
      In (fid0, (p0, cf0)) (assoc_set Nat.eqb refs0 fid (p, cf)) ->
      fact_holds (st_mem st0) p0 cf0).
    { induction refs0 as [| [k' v'] rest IH]; intros Hold Hin0; cbn in Hin0.
      - destruct Hin0 as [Heq | []]. inversion Heq; subst. now apply fact_holds_b_sound.
      - destruct (Nat.eqb fid k'); cbn in Hin0.
        + destruct Hin0 as [Heq | Hin0].
          * inversion Heq; subst. now apply fact_holds_b_sound.
          * eapply Hold; right; exact Hin0.
        + destruct Hin0 as [Heq | Hin0].
          * eapply Hold; left; exact Heq.
          * eapply IH; [intros; eapply Hold; right; eauto | exact Hin0]. }
    eapply Haux; eauto.
  - (* OpUseRefinement *)
    destruct (assoc_get Nat.eqb (st_refs st0) fid) as [[p cf] |]; [| discriminate].
    destruct (fact_holds_b (st_mem st0) p cf); inversion Hexec; subst;
      split; [exact Hnd | split; [exact Hloans | exact Hrefs]].
  - (* OpDropRefinement *)
    inversion Hexec; subst; clear Hexec; split; [exact Hnd | split; [exact Hloans |]]; cbn.
    intros fid0 p cf Hin. apply filter_In in Hin as [Hin _]. eapply Hrefs; eauto.
Qed.

(* ================================================================= *)
(* 2. Theorem 1: Polonius Origin Flow Soundness                      *)
(* ================================================================= *)

Inductive cfg_path (cfg : polonius_cfg) : point_id -> point_id -> Prop :=
| CFGPathRefl : forall pt, cfg_path cfg pt pt
| CFGPathStep : forall pt1 pt2 pt3,
    cfg_edge cfg pt1 pt2 ->
    cfg_path cfg pt2 pt3 ->
    cfg_path cfg pt1 pt3.

Fixpoint exec_cfg_trace (st : machine_state) (cfg : polonius_cfg)
    (trace : list (point_id * step_op * point_id)) : option machine_state :=
  match trace with
  | [] => Some st
  | (pt1, op, pt2) :: rest =>
      match find_cfg_node cfg pt1 with
      | None => None
      | Some node =>
          match cn_instr node with
          | IStep op' =>
              if existsb (Nat.eqb pt2) (cn_succs node) then
                match exec_step st op with
                | Some st' => exec_cfg_trace st' cfg rest
                | None => None
                end
              else None
          | INop => None
          end
      end
  end.

Definition mem_loan_live_b (cfg : polonius_cfg) (pt : point_id) (l : loan_id) : bool :=
  existsb (fun p =>
    Nat.eqb (fst p) pt && mem_triple (pt, snd p, l) (cfg_contains cfg))
    (cfg_live cfg).

Lemma mem_loan_live_b_sound : forall cfg pt l,
  mem_loan_live_b cfg pt l = true -> loan_live_at cfg pt l.
Proof.
  intros cfg pt l H. unfold mem_loan_live_b in H.
  apply existsb_exists in H as [[pt0 o] [Hin Hcond]].
  cbn in Hcond. apply andb_true_iff in Hcond as [Hpt Htri].
  apply Nat.eqb_eq in Hpt; subst pt0.
  apply mem_triple_In in Htri.
  exists o; split; assumption.
Qed.

Definition polonius_node_consistent (cfg : polonius_cfg) (node : cfg_node) : bool :=
  let pt := cn_point node in
  match cn_instr node with
  | INop => true
  | IStep op =>
      match op with
      | OpRead _ (Some l) => mem_loan_live_b cfg pt l
      | OpStableWrite _ (Some l) _ => mem_loan_live_b cfg pt l
      | OpTagPreservingUnionWrite _ (Some l) _ _ => mem_loan_live_b cfg pt l
      | OpCapPreservingPush _ (Some l) _ => mem_loan_live_b cfg pt l
      | OpBorrow l orig _ _ _ => mem_triple (pt, orig, l) (cfg_issues cfg)
      | OpReserve l orig _ _ => mem_triple (pt, orig, l) (cfg_issues cfg)
      | _ => true
      end
  end.

Ltac split_and := repeat (lazymatch goal with |- state_wf _ => fail | |- _ /\ _ => split end).

Theorem polonius_origin_flow_sound :
  forall cfg st0 trace st_final,
    state_wf st0 ->
    check_polonius_closure cfg = true ->
    forallb (polonius_node_consistent cfg) (cfg_nodes cfg) = true ->
    exec_cfg_trace st0 cfg trace = Some st_final ->
    (forall pt o l,
      polonius_flow cfg pt o l ->
      origin_contains_loan_at cfg pt o l) /\
    (forall pt o1 o2 l,
      polonius_flow cfg pt o1 l ->
      subset_at cfg pt o1 o2 ->
      origin_live_at cfg pt o2 ->
      loan_live_at cfg pt l) /\
    (forall pt1 pt2 o1 o2 l,
      issued_at cfg pt1 o1 l ->
      subset_at cfg pt1 o1 o2 ->
      cfg_edge cfg pt1 pt2 ->
      ~ loan_killed_at cfg pt2 l ->
      origin_live_at cfg pt2 o2 ->
      loan_live_at cfg pt2 l) /\
    state_wf st_final /\
    (forall le, In le (st_loans st_final) -> loan_live le = true ->
      addr_valid (st_mem st_final) (ln_addr le)).
Proof.
  intros cfg st0 trace st_final Hwf0 Hcl Hnodes Hexec.
  assert (Htrace : forall tr st stf,
    state_wf st -> exec_cfg_trace st cfg tr = Some stf -> state_wf stf).
  { induction tr as [| [[pt1 op] pt2] rest IH]; intros st stf Hw He; cbn in He.
    - inversion He; subst; exact Hw.
    - destruct (find_cfg_node cfg pt1) as [nd |] eqn:Hfn; [| discriminate].
      destruct (cn_instr nd); try discriminate.
      destruct (existsb (Nat.eqb pt2) (cn_succs nd)); [| discriminate].
      destruct (exec_step st op) as [st' |] eqn:Hs; [| discriminate].
      eapply IH; [| exact He].
      eapply step_preserves_state_wf; [exact Hw | constructor; exact Hs]. }
  pose proof (Htrace trace st0 st_final Hwf0 Hexec) as Hwf_final.
  split; [| split; [| split; [| split]]].
  - intros pt o l Hfl. eapply polonius_closure_sound; eauto.
  - intros pt o1 o2 l Hfl Hsub Hlive.
    exists o2; split; [exact Hlive |].
    eapply polonius_closure_sound; [exact Hcl |].
    eapply PFSubset; eassumption.
  - intros pt1 pt2 o1 o2 l Hiss Hsub Hedge Hnkill Hlive.
    exists o2; split; [exact Hlive |].
    eapply polonius_closure_sound; [exact Hcl |].
    eapply PFEdge; [| exact Hedge | exact Hnkill | exact Hlive].
    eapply PFSubset; [apply PFIssue; exact Hiss | exact Hsub].
  - exact Hwf_final.
  - destruct Hwf_final as [_ [Hl _]].
    intros le Hin Hlive. now apply Hl.
Qed.

(* ================================================================= *)
(* 3. Theorem 2: Exclusive `ref` Return Restoration (NLL #3)         *)
(* ================================================================= *)

Definition apply_prophecy_restore (m : memory) (le : loan_entry) (v_prophecy : nat)
    : option memory :=
  write_stable_mem m (ln_place le) v_prophecy.

Lemma find_none_iff : forall {A : Type} (f : A -> bool) (xs : list A),
  find f xs = None <-> (forall x, In x xs -> f x = false).
Proof.
  intros A f xs; induction xs as [| y ys IH]; cbn; split; intro H.
  - intros x [].
  - reflexivity.
  - intros x [<- | Hin]; destruct (f y) eqn:Ey; try discriminate;
      [reflexivity | exact (proj1 IH H x Hin)].
  - destruct (f y) eqn:Ey.
    + specialize (H y (or_introl eq_refl)). congruence.
    + apply (proj2 IH); intros x Hin. apply H; right; exact Hin.
Qed.

Lemma existsb_false : forall {A : Type} (f : A -> bool) (xs : list A),
  (forall x, In x xs -> f x = false) -> existsb f xs = false.
Proof.
  intros A f xs H; induction xs as [| y ys IH]; cbn; [reflexivity |].
  rewrite (H y (or_introl eq_refl)). apply IH; intros x Hin; apply H; right; exact Hin.
Qed.

Lemma write_stable_val_reads_back : forall v steps n v' old_n,
  write_stable_val v steps n = Some v' ->
  read_scalar v steps = Some old_n ->
  read_scalar v' steps = Some n.
Proof.
  intros v steps n v' old_n Hw Hr.
  assert (Haux : forall k steps v v' old_n,
    length steps <= k ->
    write_stable_val v steps n = Some v' ->
    read_scalar v steps = Some old_n ->
    read_scalar v' steps = Some n).
  { induction k as [| k' IH]; intros [| s rest] v0 v0' old0 Hlen0 Hw0 Hr0;
      cbn [length] in *.
    - cbn in Hw0. destruct v0; inversion Hw0; reflexivity.
    - lia.
    - cbn in Hw0. destruct v0; inversion Hw0; reflexivity.
    - destruct s, v0; cbn [write_stable_val option_map] in Hw0; try discriminate.
      + destruct (assoc_get Nat.eqb fields f) as [fv |] eqn:Hf; [| discriminate].
        destruct (write_stable_val fv rest n) as [fv' |] eqn:Hwfv; [| discriminate].
        destruct (assoc_update Nat.eqb fields f fv') as [fs' |] eqn:Hup;
          cbn in Hw0; [| discriminate].
        inversion Hw0; subst; clear Hw0.
        unfold read_scalar in Hr0 |- *; cbn [read_val] in Hr0 |- *.
        rewrite Hf in Hr0.
        rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq fields f fv' fs' Hup).
        eapply IH; [| exact Hwfv | exact Hr0]; lia.
      + destruct (nth_error elems idx) as [ev |] eqn:He; [| discriminate].
        destruct (write_stable_val ev rest n) as [ev' |] eqn:Hwev; [| discriminate].
        destruct (list_set elems idx ev') as [elems' |] eqn:Hls;
          cbn in Hw0; [| discriminate].
        inversion Hw0; subst; clear Hw0.
        unfold read_scalar in Hr0 |- *; cbn [read_val] in Hr0 |- *.
        rewrite He in Hr0.
        rewrite (list_set_nth_same elems idx ev' elems' Hls).
        eapply IH; [| exact Hwev | exact Hr0]; lia.
      + destruct (Nat.leb (off + len) (length elems)) eqn:Hb; [| discriminate].
        destruct rest as [| s' rest'].
        * destruct (write_slice_fill elems 0 off len n); inversion Hw0; subst.
          unfold read_scalar in Hr0; cbn [read_val] in Hr0; rewrite Hb in Hr0; discriminate.
        * destruct s'; try discriminate.
          destruct (Nat.ltb idx len) eqn:Hk; [| discriminate].
          destruct (nth_error elems (off + idx)) as [ev |] eqn:He; [| discriminate].
          destruct (write_stable_val ev rest' n) as [ev' |] eqn:Hwev; [| discriminate].
          destruct (list_set elems (off + idx) ev') as [elems' |] eqn:Hls;
            cbn in Hw0; [| discriminate].
          inversion Hw0; subst; clear Hw0.
          unfold read_scalar in Hr0 |- *; cbn [read_val] in Hr0 |- *.
          rewrite Hb, Hk, He in Hr0.
          rewrite (list_set_length elems (off + idx) ev' elems' Hls), Hb, Hk.
          rewrite (list_set_nth_same elems (off + idx) ev' elems' Hls).
          eapply IH; [| exact Hwev | exact Hr0]; cbn in Hlen0; lia.
      + destruct rest; [| discriminate].
        destruct (Nat.ltb r rows && Nat.ltb c cols) eqn:Hb; [| discriminate].
        inversion Hw0; subst; clear Hw0.
        unfold read_scalar; cbn [read_val]. rewrite Hb.
        rewrite (assoc_get_set_same cell_beq cell_beq_eq cells (r, c) n). reflexivity.
      + destruct (write_stable_val v0 rest n) as [p' |] eqn:Hwp;
          cbn in Hw0; [| discriminate].
        inversion Hw0; subst; clear Hw0.
        unfold read_scalar in Hr0 |- *; cbn [read_val] in Hr0 |- *.
        eapply IH; [| exact Hwp | exact Hr0]; lia. }
  eapply Haux; eauto.
Qed.

Theorem exclusive_return_restoration_sound :
  forall st l le,
    state_wf st ->
    lookup_loan (st_loans st) l = Some le ->
    ln_mode le = LExclusive ->
    loan_active le = true ->
    has_live_child (st_loans st) l = false ->
    (* Part A: Local EndLoan restores parent and preserves disjoint frame *)
    (exists st_end,
      Step st (OpEndLoan l) st_end /\
      lookup_loan (st_loans st_end) l = None /\
      st_mem st_end = st_mem st /\
      (forall pid pe,
        ln_parent le = Some pid ->
        lookup_loan (st_loans st) pid = Some pe ->
        exists pe', lookup_loan (st_loans st_end) pid = Some pe' /\
          ln_suspended pe' = false)) /\
    (* Part B: ReturnLoan requires borrowed parameter root and restores owner via prophecy *)
    (forall st_ret,
      Step st (OpReturnLoan l) st_ret ->
      (exists oe, lookup_owner (st_mem st) (p_owner (ln_place le)) = Some oe /\
                  oe_borrowed oe = true) /\
      (forall v_prophecy m_final,
        apply_prophecy_restore (st_mem st_ret) le v_prophecy = Some m_final ->
        (forall old_v, read_scalar_mem (st_mem st) (ln_place le) = Some old_v ->
          read_scalar_mem m_final (ln_place le) = Some v_prophecy) /\
        (forall q, places_disjoint (ln_place le) q ->
          read_val_mem m_final q = read_val_mem (st_mem st) q) /\
        (forall le', In le' (st_loans st) -> loan_live le' = true ->
          addr_valid m_final (ln_addr le')))).
Proof.
  intros st l le Hwf Hlk Hmode Hact Hnoch.
  split.
  - (* Part A: Local EndLoan *)
    assert (Hexec : exists st_end, exec_step st (OpEndLoan l) = Some st_end).
    { unfold exec_step. rewrite Hlk, Hact, Hnoch; cbn. eauto. }
    destruct Hexec as [st_end Hexec].
    exists st_end; split; [constructor; exact Hexec |].
    unfold exec_step in Hexec. rewrite Hlk, Hact, Hnoch in Hexec; cbn in Hexec.
    inversion Hexec; subst; clear Hexec; cbn.
    destruct Hwf as [Hnd [Hloans _]].
    split.
    + unfold lookup_loan.
      rewrite Hmode; destruct (ln_parent le) as [pid |].
      * rewrite find_none_iff. intros x Hin.
        apply in_map_iff in Hin as [y [<- Hy]].
        apply filter_In in Hy as [_ Hneq].
        apply negb_true_iff in Hneq.
        destruct (Nat.eqb (ln_id y) pid); cbn; exact Hneq.
      * rewrite find_none_iff. intros x Hin.
        apply filter_In in Hin as [_ Hneq].
        apply negb_true_iff in Hneq; exact Hneq.
    + split; [reflexivity |].
      intros pid pe Hpar Hpe. rewrite Hpar, Hmode.
      destruct (Nat.eq_dec (ln_id pe) l) as [Heq_id | Hneq_id].
      * assert (Hpid_eq : pid = ln_id pe).
        { apply find_some in Hpe as [_ Heq]. now apply Nat.eqb_eq in Heq. }
        rewrite Hpid_eq, Heq_id in Hpe.
        rewrite Hlk in Hpe; inversion Hpe; subst pe.
        exfalso.
        unfold has_live_child in Hnoch.
        assert (Htrue : existsb (fun le0 => loan_live le0 &&
          match ln_parent le0 with Some p0 => Nat.eqb p0 l | None => false end) (st_loans st) = true).
        { apply existsb_exists. exists le; split; [eapply find_some; exact Hlk |].
          unfold loan_active in Hact. apply andb_true_iff in Hact as [_ Hlive].
          unfold loan_live; rewrite Hlive, Hpar, Hpid_eq, Heq_id, Nat.eqb_refl; reflexivity. }
        congruence.
      * assert (Hin_pe : In pe (st_loans st)) by (eapply find_some; exact Hpe).
        assert (Hpid_eq : ln_id pe = pid).
        { apply find_some in Hpe as [_ Heq]. now apply Nat.eqb_eq in Heq. }
        assert (Hin_rem : In pe (remove_loan (st_loans st) l)).
        { apply filter_In; split; [exact Hin_pe |].
          apply negb_true_iff, Nat.eqb_neq; congruence. }
        assert (Hnd_rem : NoDup (map ln_id (remove_loan (st_loans st) l))).
        { rewrite map_remove_loan. now apply NoDup_filter. }
        unfold lookup_loan.
        assert (Hex : exists pe',
          In pe' (set_loan_suspended (remove_loan (st_loans st) l) pid false) /\
          ln_id pe' = pid /\ ln_suspended pe' = false).
        { exists {| ln_id := ln_id pe; ln_origin := ln_origin pe; ln_parent := ln_parent pe;
                    ln_root_loan := ln_root_loan pe; ln_place := ln_place pe;
                    ln_addr := ln_addr pe; ln_mode := ln_mode pe;
                    ln_suspended := false; ln_returned := ln_returned pe |}.
          repeat split; [| exact Hpid_eq].
          unfold set_loan_suspended. apply in_map_iff. exists pe; split; [| exact Hin_rem].
          rewrite Hpid_eq, Nat.eqb_refl; reflexivity. }
        destruct Hex as [pe' [Hin' [Hid' Hsusp']]].
        assert (Hnd_set : NoDup (map ln_id (set_loan_suspended (remove_loan (st_loans st) l) pid false)))
          by (rewrite set_loan_suspended_ids; exact Hnd_rem).
        assert (Hfind : find (fun x => Nat.eqb (ln_id x) pid)
                          (set_loan_suspended (remove_loan (st_loans st) l) pid false) = Some pe').
        { clear - Hin' Hid' Hnd_set.
          induction (set_loan_suspended (remove_loan (st_loans st) l) pid false) as [| x xs IH];
            [contradiction |].
          cbn in *. inversion Hnd_set as [| ? ? H1 Hnd_rest]; clear Hnd_set.
          destruct Hin' as [-> | Hin'].
          - rewrite Hid', Nat.eqb_refl; reflexivity.
          - destruct (Nat.eqb (ln_id x) pid) eqn:Ex.
            + apply Nat.eqb_eq in Ex; subst pid.
              exfalso. apply H1. apply in_map_iff; exists pe'; auto.
            + apply IH; auto. }
        rewrite Hfind; eauto.
  - (* Part B: ReturnLoan *)
    intros st_ret Hstep. inversion Hstep as [? ? ? Hexec]; subst.
    cbn [exec_step] in Hexec.
    rewrite Hlk, Hact, Hmode in Hexec; cbn in Hexec.
    rewrite Hnoch in Hexec; cbn in Hexec.
    destruct (addr_valid_b (st_mem st) (ln_addr le)) eqn:Had; [| discriminate].
    destruct (lookup_owner (st_mem st) (p_owner (ln_place le))) as [oe |] eqn:Ho; [| discriminate].
    destruct (oe_borrowed oe) eqn:Hbor; [| discriminate].
    inversion Hexec; subst; clear Hexec; cbn.
    split; [exists oe; split; [exact Ho || reflexivity | exact Hbor] |].
    intros v_prophecy m_final Hprop.
    unfold apply_prophecy_restore in Hprop.
    split_and.
    + intros old_v Hold.
      unfold write_stable_mem in Hprop.
      rewrite Ho in Hprop.
      destruct (write_stable_val (oe_val oe) (p_path (ln_place le)) v_prophecy) as [v' |] eqn:Hv';
        [| discriminate].
      unfold update_owner, read_scalar_mem, lookup_owner in *.
      rewrite Ho in Hold.
      rewrite (assoc_get_update_same Nat.eqb Nat.eqb_eq (st_mem st) (p_owner (ln_place le))
                 {| oe_borrowed := oe_borrowed oe; oe_val := v' |} m_final Hprop).
      cbn. eapply write_stable_val_reads_back; eauto.
    + intros q Hdisj. eapply write_stable_mem_frame; [exact Hdisj | exact Hprop].
    + intros le' Hin' Hlive'.
      destruct Hwf as [_ [Hloans _]].
      eapply write_stable_mem_preserves_addr; [exact Hprop | exact (proj2 (Hloans le' Hin') Hlive')].
Qed.

(* ================================================================= *)
(* 4. Theorem 3: Two-Phase Borrow Soundness                          *)
(* ================================================================= *)

Lemma place_nonempty_not_disjoint_self : forall p,
  Forall step_nonempty (p_path p) ->
  places_disjoint_b p p = false.
Proof.
  intros p Hne.
  destruct (places_disjoint_b p p) eqn:E; [| reflexivity].
  exfalso. eapply places_disjoint_not_within; [exact Hne | exact E | apply within_refl].
Qed.

Theorem two_phase_borrow_sound :
  forall st l orig parent p st_res,
    state_wf st ->
    Forall step_nonempty (p_path p) ->
    has_live_child (st_loans st) l = false ->
    Step st (OpReserve l orig parent p) st_res ->
    (exists le_res,
      lookup_loan (st_loans st_res) l = Some le_res /\
      ln_mode le_res = LReserved /\
      loan_active le_res = true) /\
    (* 1. Reserve admits non-mutating Read when place holds scalar and no active exclusive overlaps *)
    (forall n,
      read_scalar_mem (st_mem st) p = Some n ->
      direct_read_ok p (st_loans st) = true ->
      Step st_res (OpRead p None) st_res) /\
    (* 2. Reserve rejects conflicting writes, unstable drops, and exclusive borrows *)
    (forall v, exec_step st_res (OpStableWrite p None v) = None) /\
    (exec_step st_res (OpUnstableWrite p UDrop) = None) /\
    (forall l2 orig2, exec_step st_res (OpBorrow l2 orig2 None p LExclusive) = None) /\
    (* 3. Activate succeeds cleanly when no overlapping active loan conflicts *)
    (forallb (fun other =>
      if Nat.eqb (ln_id other) l then true
      else borrow_compatible LExclusive parent p other) (st_loans st_res) = true ->
      exists st_act,
        Step st_res (OpActivate l) st_act /\
        exists le_act,
          lookup_loan (st_loans st_act) l = Some le_act /\
          ln_mode le_act = LExclusive /\
          loan_active le_act = true) /\
    (* 4. CancelReservation succeeds cleanly on early exit *)
    (exists st_can,
      Step st_res (OpCancelReservation l) st_can /\
      lookup_loan (st_loans st_can) l = None /\
      st_mem st_can = st_mem st).
Proof.
  intros st l orig parent p st_res Hwf Hne Hnochild Hstep.
  inversion Hstep as [? ? ? Hexec]; subst.
  cbn [exec_step] in Hexec.
  destruct (has_loan (st_loans st) l) eqn:Hhas; [discriminate |].
  destruct (resolve_addr (st_mem st) p) as [addr |] eqn:Hres; [| discriminate].
  destruct (match parent with
            | None => Some l
            | Some pid => match lookup_loan (st_loans st) pid with
                          | Some pe => if loan_active pe && negb (loan_mode_beq (ln_mode pe) LReserved) && within_b p (ln_place pe) && can_borrow_from_parent LReserved (ln_mode pe) then Some (ln_root_loan pe) else None
                          | None => None
                          end
            end) as [root_id |] eqn:Hpar; [| discriminate].
  destruct (forallb (borrow_compatible LReserved parent p) (st_loans st)) eqn:Hcompat;
    [| discriminate].
  inversion Hexec; subst; clear Hexec.
  set (le_res := {|
    ln_id := l; ln_origin := orig; ln_parent := parent; ln_root_loan := root_id;
    ln_place := p; ln_addr := addr; ln_mode := LReserved;
    ln_suspended := false; ln_returned := false
  |}).
  assert (Hfind_l : lookup_loan (le_res :: st_loans st) l = Some le_res).
  { unfold lookup_loan; cbn. rewrite Nat.eqb_refl; reflexivity. }
  assert (Hself : places_disjoint_b p p = false) by (now apply place_nonempty_not_disjoint_self).
  split_and.
  - exists le_res; split; [exact Hfind_l | split; reflexivity].
  - (* 1. Reserve admits non-mutating Read *)
    intros nv Hread Hdrok. constructor. cbn [exec_step st_loans st_mem].
    assert (Hdrok' : direct_read_ok p (le_res :: st_loans st) = true).
    { unfold direct_read_ok in *; cbn. rewrite Hdrok.
      destruct (places_disjoint_b p p); reflexivity. }
    rewrite Hdrok', Hread; reflexivity.
  - (* 2a. Reserve rejects StableWrite *)
    intro v. cbn [exec_step st_loans].
    unfold direct_write_ok; cbn. rewrite Hself; cbn. reflexivity.
  - (* 2b. Reserve rejects UnstableWrite UDrop *)
    cbn [exec_step st_loans].
    unfold no_overlapping_loan_at; cbn. rewrite Hself; cbn. reflexivity.
  - (* 2c. Reserve rejects conflicting LExclusive borrow *)
    intros l2 orig2. cbn [exec_step st_loans st_mem].
    destruct (has_loan (le_res :: st_loans st) l2); [reflexivity |].
    rewrite Hres.
    unfold borrow_compatible at 1; cbn. rewrite Hself; cbn. reflexivity.
  - (* 3. Activate succeeds cleanly *)
    intro Hact_compat.
    cbn [st_loans forallb] in Hact_compat. unfold le_res at 1 in Hact_compat.
    cbn [ln_id] in Hact_compat. rewrite Nat.eqb_refl in Hact_compat.
    cbn [andb] in Hact_compat. cbv iota in Hact_compat.
    assert (Had : addr_valid_b (st_mem st) addr = true) by (eapply resolve_addr_valid; eauto).
    assert (Hex_act : exists st_act, exec_step {| st_mem := st_mem st; st_loans := le_res :: st_loans st; st_refs := st_refs st; st_next_bid := st_next_bid st |} (OpActivate l) = Some st_act).
    { cbn [exec_step st_loans st_mem]. rewrite Hfind_l; cbn.
      rewrite Had; cbn. rewrite Hact_compat, Nat.eqb_refl. eexists; reflexivity. }
    destruct Hex_act as [st_act Hact_exec].
    exists st_act; split; [constructor; exact Hact_exec |].
    cbn [exec_step st_loans st_mem] in Hact_exec.
    rewrite Hfind_l in Hact_exec; cbn in Hact_exec.
    rewrite Had in Hact_exec; cbn in Hact_exec.
    rewrite Hact_compat, Nat.eqb_refl in Hact_exec.
    inversion Hact_exec; subst; clear Hact_exec.
    set (le_act := {|
      ln_id := l; ln_origin := orig; ln_parent := parent; ln_root_loan := root_id;
      ln_place := p; ln_addr := addr; ln_mode := LExclusive;
      ln_suspended := false; ln_returned := false
    |}).
    destruct parent as [pid |]; cbn.
    + assert (Hpid_ne : pid <> l).
      { intro E; subst pid.
        destruct (lookup_loan (st_loans st) l) as [pe0 |] eqn:Elk; [| discriminate].
        apply find_some in Elk as [Hin Heq]. apply Nat.eqb_eq in Heq.
        apply (has_loan_false_notin (st_loans st) l Hhas).
        apply in_map_iff; exists pe0; auto. }
      assert (Hpid_beq : Nat.eqb l pid = false) by (apply Nat.eqb_neq; congruence).
      exists le_act; split; [| split; reflexivity].
      unfold lookup_loan; cbn. rewrite Hpid_beq.
      unfold le_act at 1; cbn [ln_id]; rewrite Nat.eqb_refl; reflexivity.
    + exists le_act; split; [| split; reflexivity].
      unfold lookup_loan; cbn.
      unfold le_act at 1; cbn [ln_id]; rewrite Nat.eqb_refl; reflexivity.
  - (* 4. CancelReservation succeeds cleanly *)
    assert (Hnoch' : has_live_child (le_res :: st_loans st) l = false).
    { unfold has_live_child in *; cbn.
      destruct parent as [pid |]; [| exact Hnochild].
      destruct (lookup_loan (st_loans st) pid) as [pe0 |] eqn:Elk; [| discriminate].
      assert (Hpid_beq : Nat.eqb pid l = false).
      { apply Nat.eqb_neq; intro E; subst pid.
        apply find_some in Elk as [Hin Heq]; apply Nat.eqb_eq in Heq.
        apply (has_loan_false_notin (st_loans st) l Hhas).
        apply in_map_iff; exists pe0; auto. }
      rewrite Hpid_beq; exact Hnochild. }
    assert (Hex_can : exists st_can,
      exec_step {| st_mem := st_mem st; st_loans := le_res :: st_loans st; st_refs := st_refs st; st_next_bid := st_next_bid st |}
        (OpCancelReservation l) = Some st_can).
    { cbn [exec_step st_loans st_mem]. rewrite Hfind_l, Hnoch'.
      cbn [loan_active loan_mode_beq ln_suspended ln_returned ln_mode negb andb].
      cbv iota. eexists; reflexivity. }
    destruct Hex_can as [st_can Hcan_exec].
    exists st_can; split; [constructor; exact Hcan_exec |].
    cbn [exec_step st_loans st_mem] in Hcan_exec.
    rewrite Hfind_l, Hnoch' in Hcan_exec.
    cbn [loan_active loan_mode_beq ln_suspended ln_returned ln_mode negb andb] in Hcan_exec.
    cbv iota in Hcan_exec.
    inversion Hcan_exec; subst; clear Hcan_exec; cbn.
    split; [| reflexivity].
    unfold lookup_loan, remove_loan; cbn. rewrite Nat.eqb_refl; cbn.
    rewrite find_none_iff. intros le0 Hin0.
    apply filter_In in Hin0 as [_ Hneq].
    apply negb_true_iff in Hneq; exact Hneq.
Qed.

(* ================================================================= *)
(* 5. Theorem 4: Loop Cursor Folding Soundness                       *)
(* ================================================================= *)

Fixpoint exec_cursor_loop (st : machine_state) (cur_id : loan_id)
    (iters : list (loan_id * origin_id * place * option nat))
    : option (machine_state * loan_id) :=
  match iters with
  | [] => Some (st, cur_id)
  | (next_id, orig, sub_p, opt_w) :: rest =>
      match exec_step st (OpLoopStep cur_id next_id orig sub_p) with
      | None => None
      | Some st1 =>
          match opt_w with
          | None => exec_cursor_loop st1 next_id rest
          | Some v =>
              match exec_step st1 (OpStableWrite sub_p (Some next_id) v) with
              | None => None
              | Some st2 => exec_cursor_loop st2 next_id rest
              end
          end
      end
  end.

Lemma lookup_loan_In : forall loans l le,
  NoDup (map ln_id loans) ->
  In le loans ->
  ln_id le = l ->
  lookup_loan loans l = Some le.
Proof.
  induction loans as [| x xs IH]; intros l le Hnd Hin Hid; [contradiction |].
  cbn in *. inversion Hnd as [| ? ? H1 Hnd_rest]; clear Hnd.
  destruct Hin as [-> | Hin].
  - rewrite Hid, Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb (ln_id x) l) eqn:Ex.
    + apply Nat.eqb_eq in Ex; subst l.
      exfalso. apply H1. apply in_map_iff; exists le; auto.
    + apply IH; auto.
Qed.

Definition live_parents_exist (loans : list loan_entry) : Prop :=
  forall x pid,
    In x loans ->
    loan_live x = true ->
    ln_parent x = Some pid ->
    exists p, In p loans /\ ln_id p = pid.

Theorem loop_cursor_folding_sound :
  forall st0 root_id root_le cid0 ce0 iters st_k cid_k,
    state_wf st0 ->
    live_parents_exist (st_loans st0) ->
    lookup_loan (st_loans st0) root_id = Some root_le ->
    ln_mode root_le = LExclusive ->
    ln_suspended root_le = true ->
    ln_returned root_le = false ->
    lookup_loan (st_loans st0) cid0 = Some ce0 ->
    ln_parent ce0 = Some root_id ->
    ln_root_loan ce0 = ln_root_loan root_le ->
    ln_mode ce0 = LExclusive ->
    loan_active ce0 = true ->
    has_live_child (st_loans st0) cid0 = false ->
    within (ln_place ce0) (ln_place root_le) ->
    exec_cursor_loop st0 cid0 iters = Some (st_k, cid_k) ->
    state_wf st_k /\
    (* 1. Parent root stays suspended across arbitrary loop iterations *)
    (exists root_k,
      lookup_loan (st_loans st_k) root_id = Some root_k /\
      ln_suspended root_k = true /\
      ln_place root_k = ln_place root_le /\
      ln_root_loan root_k = ln_root_loan root_le /\
      ln_mode root_k = LExclusive /\
      ln_returned root_k = false) /\
    (* 2. Folded cursor preserves ancestor containment and address validity *)
    (exists ce_k,
      lookup_loan (st_loans st_k) cid_k = Some ce_k /\
      ln_parent ce_k = Some root_id /\
      ln_root_loan ce_k = ln_root_loan root_le /\
      ln_mode ce_k = LExclusive /\
      loan_active ce_k = true /\
      has_live_child (st_loans st_k) cid_k = false /\
      within (ln_place ce_k) (ln_place root_le) /\
      addr_valid (st_mem st_k) (ln_addr ce_k)) /\
    (* 3. Disjoint frame outside root is preserved across loop body writes *)
    (forall q, places_disjoint (ln_place root_le) q ->
      read_val_mem (st_mem st_k) q = read_val_mem (st_mem st0) q) /\
    (* 4. Exit restoration unsuspends root cleanly *)
    (exists st_exit,
      Step st_k (OpEndLoan cid_k) st_exit /\
      lookup_loan (st_loans st_exit) cid_k = None /\
      (exists root_exit,
        lookup_loan (st_loans st_exit) root_id = Some root_exit /\
        ln_suspended root_exit = false) /\
      (forall q, places_disjoint (ln_place root_le) q ->
        read_val_mem (st_mem st_exit) q = read_val_mem (st_mem st0) q)).
Proof.
  intros st0 root_id root_le cid0 ce0 iters.
  revert st0 root_le cid0 ce0.
  induction iters as [| [[[next_id orig] sub_p] opt_w] rest IH];
    intros st0 root_le cid0 ce0 st_k cid_k
      Hwf Hlp Hroot Hrmode Hrsusp Hrret Hcur Hcpar Hcroot Hcmode Hcact Hcnoc Hcwith Hloop.
  - (* Base case: 0 iterations *)
    cbn in Hloop. inversion Hloop as [[Est Ecid]]; subst st_k cid_k; clear Hloop.
    destruct Hwf as [Hnd [Hloans Hrefs]].
    assert (Hwf0 : state_wf st0) by (split; [exact Hnd | split; [exact Hloans | exact Hrefs]]).
    assert (Hce_valid : addr_valid (st_mem st0) (ln_addr ce0)).
    { apply (proj2 (Hloans ce0 ltac:(eapply find_some; exact Hcur))).
      unfold loan_active in Hcact. apply andb_true_iff in Hcact as [_ Hl]; exact Hl. }
    assert (Hex_end : exists st_exit, exec_step st0 (OpEndLoan cid0) = Some st_exit).
    { cbn [exec_step]. rewrite Hcur, Hcact, Hcnoc; cbn. eexists; reflexivity. }
    destruct Hex_end as [st_exit Hexit].
    split_and; try assumption.
    + exists root_le; split_and; try assumption; reflexivity.
    + exists ce0; split_and; try assumption; reflexivity.
    + intros q _; reflexivity.
    + exists st_exit; split_and.
      * constructor; exact Hexit.
      * cbn [exec_step] in Hexit. rewrite Hcur, Hcact, Hcnoc in Hexit; cbn in Hexit.
        inversion Hexit; subst; clear Hexit; cbn.
        unfold lookup_loan. rewrite Hcpar, Hcmode.
        rewrite find_none_iff. intros x Hin.
        apply in_map_iff in Hin as [y [<- Hy]].
        apply filter_In in Hy as [_ Hneq].
        apply negb_true_iff in Hneq.
        destruct (Nat.eqb (ln_id y) root_id); cbn; exact Hneq.
      * cbn [exec_step] in Hexit. rewrite Hcur, Hcact, Hcnoc in Hexit; cbn in Hexit.
        inversion Hexit; subst; clear Hexit; cbn.
        rewrite Hcpar, Hcmode.
        assert (Hroot_ne : root_id <> cid0).
        { intro E; subst root_id.
          rewrite Hroot in Hcur; inversion Hcur; subst.
          unfold loan_active in Hcact; rewrite Hrsusp in Hcact; discriminate. }
        assert (Hin_root : In root_le (st_loans st0)) by (eapply find_some; exact Hroot).
        assert (Hid_root : ln_id root_le = root_id).
        { apply find_some in Hroot as [_ E]. now apply Nat.eqb_eq in E. }
        assert (Hin_rem : In root_le (remove_loan (st_loans st0) cid0)).
        { apply filter_In; split; [exact Hin_root |].
          apply negb_true_iff, Nat.eqb_neq; congruence. }
        set (root_exit := {|
          ln_id := ln_id root_le; ln_origin := ln_origin root_le;
          ln_parent := ln_parent root_le; ln_root_loan := ln_root_loan root_le;
          ln_place := ln_place root_le; ln_addr := ln_addr root_le;
          ln_mode := ln_mode root_le; ln_suspended := false;
          ln_returned := ln_returned root_le
        |}).
        exists root_exit; split; [| reflexivity].
        apply lookup_loan_In.
        -- rewrite set_loan_suspended_ids, map_remove_loan. now apply NoDup_filter.
        -- unfold set_loan_suspended. apply in_map_iff. exists root_le; split; [| exact Hin_rem].
           unfold root_exit; rewrite Hid_root, Nat.eqb_refl; reflexivity.
        -- exact Hid_root.
      * intros q Hdisj.
        cbn [exec_step] in Hexit. rewrite Hcur, Hcact, Hcnoc in Hexit; cbn in Hexit.
        inversion Hexit; subst; reflexivity.
  - (* Inductive step: OpLoopStep + optional OpStableWrite + rest *)
    cbn [exec_cursor_loop] in Hloop.
    destruct (exec_step st0 (OpLoopStep cid0 next_id orig sub_p)) as [st1 |] eqn:Hstep1;
      [| discriminate].
    assert (Hwf1 : state_wf st1) by (eapply step_preserves_state_wf; [exact Hwf | constructor; exact Hstep1]).
    cbn [exec_step] in Hstep1.
    destruct (Nat.eqb cid0 next_id) eqn:Ene; [discriminate |].
    destruct (has_loan (st_loans st0) next_id) eqn:Hhas; [discriminate |].
    rewrite Hcur, Hcact, Hcmode, Hcnoc in Hstep1; cbn in Hstep1.
    destruct (within_b sub_p (ln_place ce0)) eqn:Hsub; [| discriminate].
    destruct (addr_valid_b (st_mem st0) (ln_addr ce0)); [| discriminate].
    destruct (resolve_addr (st_mem st0) sub_p) as [addr1 |] eqn:Hres1; [| discriminate].
    inversion Hstep1; subst; clear Hstep1.
    set (ce1 := {|
      ln_id := next_id; ln_origin := orig; ln_parent := Some root_id;
      ln_root_loan := ln_root_loan root_le; ln_place := sub_p;
      ln_addr := addr1; ln_mode := LExclusive;
      ln_suspended := false; ln_returned := false
    |}).
    assert (Hroot_ne : root_id <> cid0).
    { intro E; subst root_id. rewrite Hroot in Hcur; inversion Hcur; subst.
      unfold loan_active in Hcact; rewrite Hrsusp in Hcact; discriminate. }
    assert (Hroot_ne_next : root_id <> next_id).
    { intro E; subst next_id. apply (has_loan_false_notin _ _ Hhas).
      apply in_map_iff. exists root_le; split.
      - apply find_some in Hroot as [_ E]. now apply Nat.eqb_eq in E.
      - eapply find_some; exact Hroot. }
    assert (Hin_root : In root_le (st_loans st0)) by (eapply find_some; exact Hroot).
    assert (Hid_root : ln_id root_le = root_id).
    { apply find_some in Hroot as [_ E]. now apply Nat.eqb_eq in E. }
    assert (Hst1_loans : st_loans {|
        st_mem := st_mem st0;
        st_loans := {|
          ln_id := next_id; ln_origin := orig; ln_parent := ln_parent ce0;
          ln_root_loan := ln_root_loan ce0; ln_place := sub_p;
          ln_addr := addr1; ln_mode := LExclusive;
          ln_suspended := false; ln_returned := false |} :: remove_loan (st_loans st0) cid0;
        st_refs := st_refs st0; st_next_bid := st_next_bid st0 |} = ce1 :: remove_loan (st_loans st0) cid0).
    { unfold ce1; rewrite Hcpar, Hcroot; reflexivity. }
    assert (Hroot1 : lookup_loan (ce1 :: remove_loan (st_loans st0) cid0) root_id = Some root_le).
    { apply lookup_loan_In.
      - destruct Hwf1 as [Hnd1 _]. rewrite <- Hst1_loans. exact Hnd1.
      - right. apply filter_In; split; [exact Hin_root |].
        apply negb_true_iff, Nat.eqb_neq; congruence.
      - exact Hid_root. }
    assert (Hcur1 : lookup_loan (ce1 :: remove_loan (st_loans st0) cid0) next_id = Some ce1).
    { unfold lookup_loan; cbn. rewrite Nat.eqb_refl; reflexivity. }
    assert (Hlp1 : live_parents_exist (ce1 :: remove_loan (st_loans st0) cid0)).
    { intros x pid [<- | Hin] Hlive Hpar.
      - cbn in Hpar. inversion Hpar; subst pid.
        exists root_le; split; [| exact Hid_root].
        right. apply filter_In; split; [exact Hin_root |].
        apply negb_true_iff, Nat.eqb_neq; congruence.
      - apply filter_In in Hin as [Hin0 _].
        destruct (Hlp x pid Hin0 Hlive Hpar) as [p [Hp0 Hpid]].
        exists p; split; [| exact Hpid].
        right. apply filter_In; split; [exact Hp0 |].
        apply negb_true_iff, Nat.eqb_neq; intro Ecid.
        subst pid. unfold has_live_child in Hcnoc.
        assert (Htrue : existsb (fun le0 =>
          loan_live le0 &&
          match ln_parent le0 with
          | Some p0 => Nat.eqb p0 cid0
          | None => false
          end) (st_loans st0) = true).
        { apply existsb_exists. exists x; split; [exact Hin0 |].
          rewrite Hlive, Hpar, Ecid, Nat.eqb_refl; reflexivity. }
        congruence. }
    assert (Hnoch1 : has_live_child (ce1 :: remove_loan (st_loans st0) cid0) next_id = false).
    { unfold has_live_child.
      apply existsb_false; intros le0 [<- | Hin0].
      - unfold ce1; cbn [loan_live ln_parent].
        rewrite (proj2 (Nat.eqb_neq root_id next_id) Hroot_ne_next). reflexivity.
      - apply filter_In in Hin0 as [Hin0 _].
        destruct (loan_live le0) eqn:Elive; cbn; [| reflexivity].
        destruct (ln_parent le0) as [p0 |] eqn:Ep0; [| reflexivity].
        destruct (Nat.eqb p0 next_id) eqn:Epn; [| reflexivity].
        apply Nat.eqb_eq in Epn; subst p0.
        destruct (Hlp le0 next_id Hin0 Elive Ep0) as [p [Hp0 Hpid]].
        exfalso. apply (has_loan_false_notin _ _ Hhas).
        apply in_map_iff; exists p; auto. }
    assert (Hwith1 : within sub_p (ln_place root_le)) by (eapply within_trans; [exact Hsub | exact Hcwith]).
    destruct opt_w as [v |].
    + destruct (exec_step _ (OpStableWrite sub_p (Some next_id) v)) as [st2 |] eqn:Hstep2;
        [| discriminate].
      assert (Hwf2 : state_wf st2)
        by (eapply step_preserves_state_wf; [exact Hwf1 | constructor; exact Hstep2]).
      cbn [exec_step] in Hstep2.
      rewrite Hst1_loans in *.
      cbn [st_mem] in Hstep2.
      rewrite Hcur1 in Hstep2. unfold ce1 in Hstep2.
      cbn [loan_active loan_mode_beq ln_mode ln_suspended ln_returned ln_place ln_addr orb andb] in Hstep2.
      rewrite within_refl in Hstep2; cbn [negb andb] in Hstep2; cbv iota in Hstep2.
      destruct (addr_valid_b (st_mem st0) addr1) eqn:Hva1; cbv iota in Hstep2; [| discriminate].
      destruct (write_stable_mem (st_mem st0) sub_p v) as [m2 |] eqn:Hwm2; cbv iota in Hstep2; [| discriminate].
      inversion Hstep2; subst; clear Hstep2.
      specialize (IH _ root_le next_id ce1 st_k cid_k
        Hwf2 Hlp1 Hroot1 Hrmode Hrsusp Hrret Hcur1 eq_refl eq_refl eq_refl eq_refl Hnoch1 Hwith1 Hloop).
      destruct IH as [Hwf_k [Hroot_k [Hce_k [Hframe Hexit]]]].
      split_and; try assumption.
      * intros q Hdisj. rewrite Hframe by exact Hdisj. cbn [st_mem].
        eapply write_stable_mem_frame; [| exact Hwm2].
        eapply places_disjoint_within; [exact Hdisj | exact Hwith1 | apply within_refl].
      * destruct Hexit as [st_exit [Hstex [Hnone [Hrex Hexframe]]]].
        exists st_exit; split_and; try assumption.
        intros q Hdisj. rewrite Hexframe by exact Hdisj. cbn [st_mem].
        eapply write_stable_mem_frame; [| exact Hwm2].
        eapply places_disjoint_within; [exact Hdisj | exact Hwith1 | apply within_refl].
    + rewrite Hcpar, Hcroot in Hwf1, Hloop.
      exact (IH _ root_le next_id ce1 st_k cid_k
        Hwf1 Hlp1 Hroot1 Hrmode Hrsusp Hrret Hcur1 eq_refl eq_refl eq_refl eq_refl Hnoch1 Hwith1 Hloop).
Qed.

(* ================================================================= *)
(* 6. Theorem 5: Symbolic Disjoint Write Frame                       *)
(* ================================================================= *)

Theorem symbolic_disjoint_write_frame :
  forall st wp via val st' le,
    state_wf st ->
    Step st (OpStableWrite wp via val) st' ->
    In le (st_loans st) ->
    loan_live le = true ->
    ((exists p i j, wp = PElem p i /\ ln_place le = PElem p j /\ i <> j) \/
     (exists p r1 c1 r2 c2, wp = PCell2D p r1 c1 /\ ln_place le = PCell2D p r2 c2 /\ (r1 <> r2 \/ c1 <> c2)) \/
     (exists p a m b n, wp = PSlice p a m /\ ln_place le = PSlice p b n /\ (a + m <= b \/ b + n <= a)) \/
     (exists p k a m, wp = PElem p k /\ ln_place le = PSlice p a m /\ (k < a \/ a + m <= k)) \/
     (exists p k a m, wp = PSlice p a m /\ ln_place le = PElem p k /\ (k < a \/ a + m <= k)) \/
     places_disjoint wp (ln_place le)) ->
    state_wf st' /\
    In le (st_loans st') /\
    addr_valid (st_mem st') (ln_addr le) /\
    read_val_mem (st_mem st') (ln_place le) = read_val_mem (st_mem st) (ln_place le).
Proof.
  intros st wp via val st' le Hwf Hstep Hin Hlive Hsym.
  assert (Hwf' : state_wf st') by (eapply step_preserves_state_wf; eassumption).
  assert (Hdisj : places_disjoint wp (ln_place le)).
  { destruct Hsym as [[p [i [j [-> [-> Hne]]]]]
                  | [[p [r1 [c1 [r2 [c2 [-> [-> Hne]]]]]]]
                  | [[p [a [m [b [n [-> [-> Hsep]]]]]]]
                  | [[p [k [a [m [-> [-> Hsep]]]]]]
                  | [[p [k [a [m [-> [-> Hsep]]]]]]
                  | Hdisj]]]]];
      try exact Hdisj.
    - now apply places_disjoint_elem_ne.
    - now apply places_disjoint_cell2d.
    - now apply places_disjoint_slice.
    - now apply places_disjoint_elem_slice.
    - apply places_disjoint_sym. now apply places_disjoint_elem_slice. }
  inversion Hstep as [? ? ? Hexec]; subst.
  cbn [exec_step] in Hexec.
  destruct (match via with
            | Some l =>
                match lookup_loan (st_loans st) l with
                | Some le0 =>
                    loan_active le0 &&
                    (loan_mode_beq (ln_mode le0) LExclusive || loan_mode_beq (ln_mode le0) LSharedMut) &&
                    within_b wp (ln_place le0) &&
                    addr_valid_b (st_mem st) (ln_addr le0)
                | None => false
                end
            | None => direct_write_ok wp (st_loans st)
            end) eqn:Hperm; [| discriminate].
  destruct (write_stable_mem (st_mem st) wp val) as [m' |] eqn:Hwm; [| discriminate].
  inversion Hexec; subst; clear Hexec.
  pose proof Hwf' as [_ [Hloans' _]].
  cbn [st_loans st_mem] in Hloans'.
  split_and; try assumption.
  - cbn [st_mem]. exact (proj2 (Hloans' le Hin) Hlive).
  - cbn [st_mem]. eapply write_stable_mem_frame; eassumption.
Qed.

(* ================================================================= *)
(* 7. Theorems 6 & 7: Safe Shared Mutability & Refinement Soundness  *)
(* ================================================================= *)

Theorem stable_shared_mut_preserves_address :
  forall st wp w_id w_le val st',
    state_wf st ->
    lookup_loan (st_loans st) w_id = Some w_le ->
    ln_mode w_le = LSharedMut ->
    Step st (OpStableWrite wp (Some w_id) val) st' ->
    state_wf st' /\
    st_loans st' = st_loans st /\
    (forall other,
      In other (st_loans st) ->
      loan_live other = true ->
      (ln_mode other = LShared \/ ln_mode other = LSharedMut \/ ln_mode other = LReserved \/ ln_mode other = LExclusive) /\
      In other (st_loans st') /\
      addr_valid (st_mem st') (ln_addr other)).
Proof.
  intros st wp w_id w_le val st' Hwf Hw Hmode Hstep.
  assert (Hwf' : state_wf st') by (eapply step_preserves_state_wf; eassumption).
  inversion Hstep as [? ? ? Hexec]; subst.
  cbn [exec_step] in Hexec. rewrite Hw in Hexec.
  destruct (loan_active w_le &&
            (loan_mode_beq (ln_mode w_le) LExclusive || loan_mode_beq (ln_mode w_le) LSharedMut) &&
            within_b wp (ln_place w_le) &&
            addr_valid_b (st_mem st) (ln_addr w_le)); [| discriminate].
  destruct (write_stable_mem (st_mem st) wp val) as [m' |] eqn:Hwm; [| discriminate].
  inversion Hexec; subst; clear Hexec.
  pose proof Hwf' as [_ [Hloans' _]].
  cbn [st_loans st_mem] in Hloans'.
  split_and; try assumption; [reflexivity |].
  - intros other Hother Hlive. split_and.
    + destruct (ln_mode other); auto.
    + cbn; exact Hother.
    + cbn [st_mem]. exact (proj2 (Hloans' other Hother) Hlive).
Qed.

Lemma assoc_get_In : forall {V : Type} (xs : list (nat * V)) k v,
  assoc_get Nat.eqb xs k = Some v -> In (k, v) xs.
Proof.
  induction xs as [| [k' v'] rest IH]; intros k v H; cbn in H; [discriminate |].
  destruct (Nat.eqb k k') eqn:Ek;
    [apply Nat.eqb_eq in Ek; inversion H; subst; left; reflexivity | right; exact (IH k v H)].
Qed.

Lemma assoc_get_filter_keep : forall {V : Type} (P : fact_id * V -> bool) xs k v,
  assoc_get Nat.eqb xs k = Some v ->
  P (k, v) = true ->
  assoc_get Nat.eqb (filter P xs) k = Some v.
Proof.
  induction xs as [| [k' v'] rest IH]; intros k v Hget Hp; cbn in *; [discriminate |].
  destruct (Nat.eqb k k') eqn:Ek.
  - apply Nat.eqb_eq in Ek; subst k'. inversion Hget; subst.
    rewrite Hp; cbn. rewrite Nat.eqb_refl; reflexivity.
  - destruct (P (k', v')); cbn; [rewrite Ek |]; now apply IH.
Qed.

Theorem shared_mut_refinement_invalidation_sound :
  forall st wp w_id w_le val st',
    state_wf st ->
    lookup_loan (st_loans st) w_id = Some w_le ->
    ln_mode w_le = LSharedMut ->
    Step st (OpStableWrite wp (Some w_id) val) st' ->
    state_wf st' /\
    (* 1. Every surviving refinement fact is disjoint from wp and still holds semantically *)
    (forall fid rp cf,
      assoc_get Nat.eqb (st_refs st') fid = Some (rp, cf) ->
      places_disjoint wp rp /\ fact_holds (st_mem st') rp cf) /\
    (* 2. Any overlapping refinement fact from st was invalidated (evicted) from st_refs st' *)
    (forall fid rp cf,
      In (fid, (rp, cf)) (st_refs st') <->
      (In (fid, (rp, cf)) (st_refs st) /\ places_disjoint wp rp)) /\
    (* 3. Proved-disjoint refinement facts survive both in store and in memory *)
    (forall fid rp cf,
      assoc_get Nat.eqb (st_refs st) fid = Some (rp, cf) ->
      places_disjoint wp rp ->
      assoc_get Nat.eqb (st_refs st') fid = Some (rp, cf) /\
      fact_holds (st_mem st') rp cf).
Proof.
  intros st wp w_id w_le val st' Hwf Hw Hmode Hstep.
  assert (Hwf' : state_wf st') by (eapply step_preserves_state_wf; eassumption).
  inversion Hstep as [? ? ? Hexec]; subst.
  cbn [exec_step] in Hexec. rewrite Hw in Hexec.
  destruct (loan_active w_le &&
            (loan_mode_beq (ln_mode w_le) LExclusive || loan_mode_beq (ln_mode w_le) LSharedMut) &&
            within_b wp (ln_place w_le) &&
            addr_valid_b (st_mem st) (ln_addr w_le)); [| discriminate].
  destruct (write_stable_mem (st_mem st) wp val) as [m' |] eqn:Hwm; [| discriminate].
  inversion Hexec; subst; clear Hexec.
  pose proof Hwf' as [_ [_ Hrefs']].
  cbn [st_refs st_mem] in Hrefs'.
  split_and; try assumption.
  - intros fid rp cf Hget.
    cbn [st_refs] in Hget. apply assoc_get_In in Hget as Hin.
    unfold invalidate_overlapping_refs in Hin.
    apply filter_In in Hin as [Hin0 Hdisj]. cbn in Hdisj.
    split; [exact Hdisj |].
    cbn [st_mem]. apply Hrefs' with (fid := fid).
    unfold invalidate_overlapping_refs. apply filter_In; split; [exact Hin0 | exact Hdisj].
  - intros fid rp cf. cbn [st_refs]. unfold invalidate_overlapping_refs.
    rewrite filter_In. cbn. reflexivity.
  - intros fid rp cf Hget Hdisj.
    assert (Hget' : assoc_get Nat.eqb (invalidate_overlapping_refs wp (st_refs st)) fid = Some (rp, cf)).
    { unfold invalidate_overlapping_refs. apply assoc_get_filter_keep; [exact Hget | exact Hdisj]. }
    cbn [st_refs st_mem]. split; [exact Hget' |].
    apply assoc_get_In in Hget' as Hin'.
    eapply Hrefs'; exact Hin'.
Qed.

(* ================================================================= *)
(* 8. Theorems 8 & 9: Tag-Preserving Union & Cap-Preserving Push     *)
(* ================================================================= *)

Theorem tag_preserving_union_mutation_sound :
  forall st pu via expected_tag new_payload st',
    state_wf st ->
    Step st (OpTagPreservingUnionWrite pu via expected_tag new_payload) st' ->
    state_wf st' /\
    st_loans st' = st_loans st /\
    (* 1. All live interior union-payload and sibling loans remain valid in st' *)
    (forall other,
      In other (st_loans st) ->
      loan_live other = true ->
      addr_valid (st_mem st') (ln_addr other)) /\
    (* 2. Disjoint reads and unrelated refinements are preserved *)
    (forall q,
      places_disjoint (PUnionPayload pu) q ->
      read_val_mem (st_mem st') q = read_val_mem (st_mem st) q) /\
    (forall fid rp cf,
      assoc_get Nat.eqb (st_refs st) fid = Some (rp, cf) ->
      places_disjoint (PUnionPayload pu) rp ->
      assoc_get Nat.eqb (st_refs st') fid = Some (rp, cf) /\
      fact_holds (st_mem st') rp cf).
Proof.
  intros st pu via expected_tag new_payload st' Hwf Hstep.
  assert (Hwf' : state_wf st') by (eapply step_preserves_state_wf; eassumption).
  inversion Hstep as [? ? ? Hexec]; subst.
  cbn [exec_step] in Hexec.
  destruct (match via with
            | Some l =>
                match lookup_loan (st_loans st) l with
                | Some le =>
                    loan_active le &&
                    (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) &&
                    within_b pu (ln_place le) &&
                    addr_valid_b (st_mem st) (ln_addr le)
                | None => false
                end
            | None => no_overlapping_exclusive_or_reserved pu None (st_loans st)
            end); [| discriminate].
  destruct (write_tag_preserving_mem (st_mem st) pu expected_tag new_payload) as [m' |] eqn:Hwt;
    [| discriminate].
  inversion Hexec; subst; clear Hexec.
  pose proof Hwf' as [_ [Hloans' Hrefs']].
  cbn [st_loans st_mem st_refs] in Hloans', Hrefs'.
  split_and; try assumption; [reflexivity | | |].
  - intros other Hin Hlive. cbn [st_mem]. exact (proj2 (Hloans' other Hin) Hlive).
  - intros q Hdisj. cbn [st_mem].
    eapply write_tag_preserving_mem_frame; eassumption.
  - intros fid rp cf Hget Hdisj.
    assert (Hget' : assoc_get Nat.eqb (invalidate_overlapping_refs (PUnionPayload pu) (st_refs st)) fid = Some (rp, cf)).
    { unfold invalidate_overlapping_refs. apply assoc_get_filter_keep; [exact Hget | exact Hdisj]. }
    cbn [st_refs st_mem]. split; [exact Hget' |].
    apply assoc_get_In in Hget' as Hin'.
    eapply Hrefs'; exact Hin'.
Qed.

Theorem capacity_preserving_push_sound :
  forall st pc via new_elem st',
    state_wf st ->
    Step st (OpCapPreservingPush pc via new_elem) st' ->
    state_wf st' /\
    st_loans st' = st_loans st /\
    (* 1. All existing live element/slice/container loans keep valid addresses without reallocation *)
    (forall other,
      In other (st_loans st) ->
      loan_live other = true ->
      addr_valid (st_mem st') (ln_addr other)) /\
    (* 2. Any slot < old_len and any slice within old_len keeps its exact prior contents *)
    (exists old_len m',
      push_cap_preserving_mem (st_mem st) pc new_elem = Some (m', old_len) /\
      st_mem st' = m' /\
      (forall q,
        places_disjoint (PElem pc old_len) q ->
        Forall step_nonempty (p_path q) ->
        read_val_mem (st_mem st') q = read_val_mem (st_mem st) q) /\
      (forall q,
        places_disjoint (PElem pc old_len) q ->
        read_scalar_mem (st_mem st') q = read_scalar_mem (st_mem st) q) /\
      (forall fid rp cf,
        assoc_get Nat.eqb (st_refs st) fid = Some (rp, cf) ->
        places_disjoint (PElem pc old_len) rp ->
        assoc_get Nat.eqb (st_refs st') fid = Some (rp, cf) /\
        fact_holds (st_mem st') rp cf)).
Proof.
  intros st pc via new_elem st' Hwf Hstep.
  assert (Hwf' : state_wf st') by (eapply step_preserves_state_wf; eassumption).
  inversion Hstep as [? ? ? Hexec]; subst.
  cbn [exec_step] in Hexec.
  destruct (match via with
            | Some l =>
                match lookup_loan (st_loans st) l with
                | Some le =>
                    loan_active le &&
                    (loan_mode_beq (ln_mode le) LExclusive || loan_mode_beq (ln_mode le) LSharedMut) &&
                    within_b pc (ln_place le) &&
                    addr_valid_b (st_mem st) (ln_addr le) &&
                    no_overlapping_exclusive_or_reserved pc (Some l) (st_loans st)
                | None => false
                end
            | None => no_overlapping_exclusive_or_reserved pc None (st_loans st)
            end); [| discriminate].
  destruct (push_cap_preserving_mem (st_mem st) pc new_elem) as [[m' old_len] |] eqn:Hp;
    [| discriminate].
  destruct (forallb (fun le =>
    if option_nat_eqb via (Some (ln_id le)) then true
    else if negb (loan_active le) then true
    else places_disjoint_b (PElem pc old_len) (ln_place le)) (st_loans st)); [| discriminate].
  inversion Hexec; subst; clear Hexec.
  pose proof Hwf' as [_ [Hloans' Hrefs']].
  cbn [st_loans st_mem st_refs] in Hloans', Hrefs'.
  split_and; try assumption; [reflexivity | |].
  - intros other Hin Hlive. cbn [st_mem]. exact (proj2 (Hloans' other Hin) Hlive).
  - exists old_len, m'; split_and; [reflexivity | reflexivity | | |].
    + intros q Hdisj Hne. cbn [st_mem].
      eapply push_cap_preserving_mem_frame; eassumption.
    + intros q Hdisj. cbn [st_mem].
      destruct (forallb step_nonempty_b (p_path q)) eqn:Hne.
      * apply read_val_to_scalar.
        eapply push_cap_preserving_mem_frame; [exact Hdisj | now apply step_nonempty_b_sound | exact Hp].
      * unfold read_scalar_mem.
        destruct (lookup_owner m' (p_owner q)), (lookup_owner (st_mem st) (p_owner q));
          rewrite ?read_scalar_empty_slice_none by exact Hne; reflexivity.
    + intros fid rp cf Hget Hdisj.
      assert (Hget' : assoc_get Nat.eqb (invalidate_overlapping_refs (PElem pc old_len) (st_refs st)) fid = Some (rp, cf)).
      { unfold invalidate_overlapping_refs. apply assoc_get_filter_keep; [exact Hget | exact Hdisj]. }
      cbn [st_refs st_mem]. split; [exact Hget' |].
      apply assoc_get_In in Hget' as Hin'.
      eapply Hrefs'; exact Hin'.
Qed.

(* ================================================================= *)
(* 9. Computable Certificate Checker & Soundness Theorem             *)
(* ================================================================= *)

Record loan_cert := {
  lc_init_state : machine_state;
  lc_cfg : polonius_cfg;
  lc_trace : list (point_id * step_op * point_id);
  lc_observed_loans : list loan_id;
  lc_checked_facts : list fact_id;
}.

Definition check_observed_loan_b (st : machine_state) (l : loan_id) : bool :=
  match lookup_loan (st_loans st) l with
  | None => true
  | Some le => if loan_live le then addr_valid_b (st_mem st) (ln_addr le) else true
  end.

Definition check_fact_b (st : machine_state) (fid : fact_id) : bool :=
  match assoc_get Nat.eqb (st_refs st) fid with
  | None => false
  | Some (p, cf) => fact_holds_b (st_mem st) p cf
  end.

Definition check_loan_certificate (cert : loan_cert) : bool :=
  state_wf_b (lc_init_state cert) &&
  check_polonius_closure (lc_cfg cert) &&
  forallb (polonius_node_consistent (lc_cfg cert)) (cfg_nodes (lc_cfg cert)) &&
  match exec_cfg_trace (lc_init_state cert) (lc_cfg cert) (lc_trace cert) with
  | None => false
  | Some st_final =>
      forallb (check_observed_loan_b st_final) (lc_observed_loans cert) &&
      forallb (check_fact_b st_final) (lc_checked_facts cert)
  end.

Theorem check_loan_certificate_sound :
  forall cert,
    check_loan_certificate cert = true ->
    exists st_final,
      exec_cfg_trace (lc_init_state cert) (lc_cfg cert) (lc_trace cert) = Some st_final /\
      state_wf st_final /\
      (forall pt o l,
        polonius_flow (lc_cfg cert) pt o l ->
        origin_contains_loan_at (lc_cfg cert) pt o l) /\
      (forall pt o1 o2 l,
        polonius_flow (lc_cfg cert) pt o1 l ->
        subset_at (lc_cfg cert) pt o1 o2 ->
        origin_live_at (lc_cfg cert) pt o2 ->
        loan_live_at (lc_cfg cert) pt l) /\
      (forall l le,
        In l (lc_observed_loans cert) ->
        lookup_loan (st_loans st_final) l = Some le ->
        loan_live le = true ->
        addr_valid (st_mem st_final) (ln_addr le)) /\
      (forall fid,
        In fid (lc_checked_facts cert) ->
        exists p cf,
          assoc_get Nat.eqb (st_refs st_final) fid = Some (p, cf) /\
          fact_holds (st_mem st_final) p cf).
Proof.
  intros cert Hcheck.
  unfold check_loan_certificate in Hcheck.
  rewrite !andb_true_iff in Hcheck.
  destruct Hcheck as [[[Hwf0 Hpol] Hnodes] Htrace].
  destruct (exec_cfg_trace (lc_init_state cert) (lc_cfg cert) (lc_trace cert))
    as [st_final |] eqn:Hexec; [| discriminate].
  rewrite andb_true_iff in Htrace. destruct Htrace as [Hobs Hfacts].
  exists st_final.
  pose proof (state_wf_b_sound _ Hwf0) as Hwf_init.
  pose proof (polonius_origin_flow_sound _ _ _ _ Hwf_init Hpol Hnodes Hexec)
    as [Hpol_flow [Hpol_sub [_ [Hwf_final _]]]].
  split_and; [reflexivity | exact Hwf_final | exact Hpol_flow | exact Hpol_sub | |].
  - intros l le Hin Hlu Hlive.
    rewrite forallb_forall in Hobs. specialize (Hobs l Hin).
    unfold check_observed_loan_b in Hobs. rewrite Hlu, Hlive in Hobs. exact Hobs.
  - intros fid Hin.
    rewrite forallb_forall in Hfacts. specialize (Hfacts fid Hin).
    unfold check_fact_b in Hfacts.
    destruct (assoc_get Nat.eqb (st_refs st_final) fid) as [[p cf] |] eqn:Hget;
      [| discriminate].
    exists p, cf; split; [reflexivity | now apply fact_holds_b_sound].
Qed.

(* Concrete positive and negative certificate sanity examples *)

Definition ex_union_init_mem : memory :=
  [(1, {| oe_borrowed := false; oe_val := VUnion 2 10 (VScalar 42) |})].

Definition ex_vec_init_mem : memory :=
  [(1, {| oe_borrowed := false; oe_val := VContainer 20 4 [VScalar 10; VScalar 20] |})].

Definition ex_shared_mut_init_mem : memory :=
  [(1, {| oe_borrowed := false;
          oe_val := VContainer 30 4 [VScalar 5; VScalar 9] |})].

Example cert_pos_tag_preserving_union :
  check_loan_certificate
    {| lc_init_state := {| st_mem := ex_union_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg := {| cfg_entry := 0;
                    cfg_nodes :=
                      [{| cn_point := 0;
                          cn_instr := IStep (OpBorrow 1 1 None (PUnionPayload (PRoot 1)) LShared);
                          cn_succs := [1] |};
                       {| cn_point := 1;
                          cn_instr := IStep (OpTagPreservingUnionWrite (PRoot 1) None 2 99);
                          cn_succs := [2] |}];
                    cfg_exits := [2];
                    cfg_issues := [(0, 1, 1)];
                    cfg_subsets := [];
                    cfg_live := [(0, 1); (1, 1)];
                    cfg_kills := [];
                    cfg_contains := [(0, 1, 1); (1, 1, 1)] |};
       lc_trace := [(0, OpBorrow 1 1 None (PUnionPayload (PRoot 1)) LShared, 1);
                    (1, OpTagPreservingUnionWrite (PRoot 1) None 2 99, 2)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = true.
Proof. vm_compute. reflexivity. Qed.

Example cert_pos_cap_preserving_push :
  check_loan_certificate
    {| lc_init_state := {| st_mem := ex_vec_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg := {| cfg_entry := 0;
                    cfg_nodes :=
                      [{| cn_point := 0;
                          cn_instr := IStep (OpBorrow 1 1 None (PElem (PRoot 1) 0) LShared);
                          cn_succs := [1] |};
                       {| cn_point := 1;
                          cn_instr := IStep (OpCapPreservingPush (PRoot 1) None (VScalar 30));
                          cn_succs := [2] |};
                       {| cn_point := 2;
                          cn_instr := IStep (OpRead (PElem (PRoot 1) 0) (Some 1));
                          cn_succs := [3] |}];
                    cfg_exits := [3];
                    cfg_issues := [(0, 1, 1)];
                    cfg_subsets := [];
                    cfg_live := [(0, 1); (1, 1); (2, 1)];
                    cfg_kills := [];
                    cfg_contains := [(0, 1, 1); (1, 1, 1); (2, 1, 1)] |};
       lc_trace := [(0, OpBorrow 1 1 None (PElem (PRoot 1) 0) LShared, 1);
                    (1, OpCapPreservingPush (PRoot 1) None (VScalar 30), 2);
                    (2, OpRead (PElem (PRoot 1) 0) (Some 1), 3)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = true.
Proof. vm_compute. reflexivity. Qed.

Example cert_pos_shared_mut_disjoint_refinement :
  check_loan_certificate
    {| lc_init_state := {| st_mem := ex_shared_mut_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg := {| cfg_entry := 0;
                    cfg_nodes :=
                      [{| cn_point := 0;
                          cn_instr := IStep (OpBorrow 1 1 None (PRoot 1) LSharedMut);
                          cn_succs := [1] |};
                       {| cn_point := 1;
                          cn_instr := IStep (OpAssumeRefinement 10 (PElem (PRoot 1) 1) (FEquals 9));
                          cn_succs := [2] |};
                       {| cn_point := 2;
                          cn_instr := IStep (OpStableWrite (PElem (PRoot 1) 0) (Some 1) 77);
                          cn_succs := [3] |};
                       {| cn_point := 3;
                          cn_instr := IStep (OpUseRefinement 10);
                          cn_succs := [4] |}];
                    cfg_exits := [4];
                    cfg_issues := [(0, 1, 1)];
                    cfg_subsets := [];
                    cfg_live := [(0, 1); (1, 1); (2, 1); (3, 1)];
                    cfg_kills := [];
                    cfg_contains := [(0, 1, 1); (1, 1, 1); (2, 1, 1); (3, 1, 1)] |};
       lc_trace := [(0, OpBorrow 1 1 None (PRoot 1) LSharedMut, 1);
                    (1, OpAssumeRefinement 10 (PElem (PRoot 1) 1) (FEquals 9), 2);
                    (2, OpStableWrite (PElem (PRoot 1) 0) (Some 1) 77, 3);
                    (3, OpUseRefinement 10, 4)];
       lc_observed_loans := [1];
       lc_checked_facts := [10] |} = true.
Proof. vm_compute. reflexivity. Qed.

Example cert_neg_overlapping_refinement_invalidated :
  check_loan_certificate
    {| lc_init_state := {| st_mem := ex_shared_mut_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg := {| cfg_entry := 0;
                    cfg_nodes :=
                      [{| cn_point := 0;
                          cn_instr := IStep (OpBorrow 1 1 None (PRoot 1) LSharedMut);
                          cn_succs := [1] |};
                       {| cn_point := 1;
                          cn_instr := IStep (OpAssumeRefinement 10 (PElem (PRoot 1) 0) (FEquals 5));
                          cn_succs := [2] |};
                       {| cn_point := 2;
                          cn_instr := IStep (OpStableWrite (PElem (PRoot 1) 0) (Some 1) 77);
                          cn_succs := [3] |};
                       {| cn_point := 3;
                          cn_instr := IStep (OpUseRefinement 10);
                          cn_succs := [4] |}];
                    cfg_exits := [4];
                    cfg_issues := [(0, 1, 1)];
                    cfg_subsets := [];
                    cfg_live := [(0, 1); (1, 1); (2, 1); (3, 1)];
                    cfg_kills := [];
                    cfg_contains := [(0, 1, 1); (1, 1, 1); (2, 1, 1); (3, 1, 1)] |};
       lc_trace := [(0, OpBorrow 1 1 None (PRoot 1) LSharedMut, 1);
                    (1, OpAssumeRefinement 10 (PElem (PRoot 1) 0) (FEquals 5), 2);
                    (2, OpStableWrite (PElem (PRoot 1) 0) (Some 1) 77, 3);
                    (3, OpUseRefinement 10, 4)];
       lc_observed_loans := [1];
       lc_checked_facts := [10] |} = false.
Proof. vm_compute. reflexivity. Qed.

Example cert_neg_two_phase_write_while_reserved :
  check_loan_certificate
    {| lc_init_state := {| st_mem := ex_shared_mut_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg := {| cfg_entry := 0;
                    cfg_nodes :=
                      [{| cn_point := 0;
                          cn_instr := IStep (OpReserve 1 1 None (PElem (PRoot 1) 0));
                          cn_succs := [1] |};
                       {| cn_point := 1;
                          cn_instr := IStep (OpStableWrite (PElem (PRoot 1) 0) None 99);
                          cn_succs := [2] |}];
                    cfg_exits := [2];
                    cfg_issues := [(0, 1, 1)];
                    cfg_subsets := [];
                    cfg_live := [(0, 1); (1, 1)];
                    cfg_kills := [];
                    cfg_contains := [(0, 1, 1); (1, 1, 1)] |};
       lc_trace := [(0, OpReserve 1 1 None (PElem (PRoot 1) 0), 1);
                    (1, OpStableWrite (PElem (PRoot 1) 0) None 99, 2)];
       lc_observed_loans := [1];
       lc_checked_facts := [] |} = false.
Proof. vm_compute. reflexivity. Qed.

Example cert_neg_dangling_read_after_retag :
  check_loan_certificate
    {| lc_init_state := {| st_mem := ex_union_init_mem; st_loans := []; st_refs := []; st_next_bid := 50 |};
       lc_cfg := {| cfg_entry := 0;
                    cfg_nodes :=
                      [{| cn_point := 0;
                          cn_instr := IStep (OpUnstableWrite (PRoot 1) (URetag 9 (VScalar 0)));
                          cn_succs := [1] |};
                       {| cn_point := 1;
                          cn_instr := IStep (OpTagPreservingUnionWrite (PRoot 1) None 2 99);
                          cn_succs := [2] |}];
                    cfg_exits := [2];
                    cfg_issues := [];
                    cfg_subsets := [];
                    cfg_live := [];
                    cfg_kills := [];
                    cfg_contains := [] |};
       lc_trace := [(0, OpUnstableWrite (PRoot 1) (URetag 9 (VScalar 0)), 1);
                    (1, OpTagPreservingUnionWrite (PRoot 1) None 2 99, 2)];
       lc_observed_loans := [];
       lc_checked_facts := [] |} = false.
Proof. vm_compute. reflexivity. Qed.

End LoanSoundness.
