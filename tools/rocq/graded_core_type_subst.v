(* SPDX-License-Identifier: Apache-2.0 *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Arith.Compare_dec.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

Require Import graded_domains graded_core graded_core_metatheory.
Import GradedDomains GradedCore GradedCoreMetatheory.


Module GradedCoreTypeSubst.

Local Arguments Nat.ltb !_ !_ : simpl nomatch.
Local Arguments Nat.eqb !_ !_ : simpl nomatch.

Lemma vec_zero_app : forall (D : JoinDomain) n m,
  vec_zero (D := D) n ++ vec_zero m = vec_zero (n + m).
Proof. intros D n m. unfold vec_zero. rewrite repeat_app. reflexivity. Qed.

Lemma vec_scale_app : forall (D : JoinDomain) (q : grade D) u v,
  vec_scale q (u ++ v) = vec_scale q u ++ vec_scale q v.
Proof. intros D q u v. unfold vec_scale. apply map_app. Qed.

Lemma lift_cty_1_S : forall (D : JoinDomain) n (T : cty D),
  lift_cty 0 (S n) T = lift_cty 0 1 (lift_cty 0 n T).
Proof. intros D n T. symmetry. exact (lift_cty_add D 1 n T). Qed.

Lemma lift_cty_2_SS : forall (D : JoinDomain) n (T : cty D),
  lift_cty 0 (S (S n)) T = lift_cty 0 2 (lift_cty 0 n T).
Proof. intros D n T. symmetry. exact (lift_cty_add D 2 n T). Qed.

Lemma nth_grade_0_cons : forall (D : JoinDomain) x (xs : list (grade D)),
  nth_grade (x :: xs) 0 = x.
Proof. reflexivity. Qed.

Lemma tl_vec_add : forall (D : JoinDomain) (u v : list (grade D)),
  tl (vec_add u v) = vec_add (tl u) (tl v).
Proof.
  intros D [| a [| a' u]] [| b [| b' v]]; reflexivity.
Qed.

(* ================================================================= *)
(* Part A4: Type Substitution                                        *)
(* ================================================================= *)

Fixpoint subst_tvar_cenv {D : JoinDomain} (U : cty D) (z : list (grade D)) (env_a : cenv D) : cenv D :=
  match env_a with
  | [] => []
  | e :: rest =>
      {| cbinder := cbinder e;
         cannotation := subst_tvar_in_cty (length rest) (lift_cty 0 (length rest) U) (cannotation e);
         ctype_uses := vec_subst (length rest) z (ctype_uses e) |} :: subst_tvar_cenv U z rest
  end.

Lemma subst_tvar_cenv_length : forall (D : JoinDomain) (U : cty D) z env_a,
  length (subst_tvar_cenv U z env_a) = length env_a.
Proof.
  intros D U z env_a. induction env_a as [| e rest IH]; cbn; [reflexivity | congruence].
Qed.

Fixpoint subst_tvar_in_cterm {D : JoinDomain} (k : nat) (U : cty D) (t : cterm D) : cterm D :=
  match t with
  | CVar x =>
      if x =? k then CTypeVal U
      else if x <? k then CVar x
      else CVar (x - 1)
  | CNatVal i => CNatVal (subst_tvar_in_cidx k i)
  | CBoolVal b => CBoolVal b
  | CTypeVal T => CTypeVal (subst_tvar_in_cty k U T)
  | CLam x s r dom body =>
      CLam x s r (subst_tvar_in_cty k U dom) (subst_tvar_in_cterm (S k) (lift_cty 0 1 U) body)
  | CApp fn arg => CApp (subst_tvar_in_cterm k U fn) (subst_tvar_in_cterm k U arg)
  | CLet x s r ann rhs body =>
      CLet x s r (subst_tvar_in_cty k U ann)
        (subst_tvar_in_cterm k U rhs) (subst_tvar_in_cterm (S k) (lift_cty 0 1 U) body)
  | CPair x r fst_ty snd_ty fst_val snd_val =>
      CPair x r (subst_tvar_in_cty k U fst_ty) (subst_tvar_in_cty (S k) (lift_cty 0 1 U) snd_ty)
        (subst_tvar_in_cterm k U fst_val) (subst_tvar_in_cterm k U snd_val)
  | CLetPair x y s kappa mot pr body =>
      CLetPair x y s kappa (subst_tvar_in_cty (S k) (lift_cty 0 1 U) mot)
        (subst_tvar_in_cterm k U pr) (subst_tvar_in_cterm (S (S k)) (lift_cty 0 2 U) body)
  | CPromote q v => CPromote q (subst_tvar_in_cterm k U v)
  | CLetBox x kappa mot bx body =>
      CLetBox x kappa (subst_tvar_in_cty (S k) (lift_cty 0 1 U) mot)
        (subst_tvar_in_cterm k U bx) (subst_tvar_in_cterm (S k) (lift_cty 0 1 U) body)
  | CInl rt v => CInl (subst_tvar_in_cty k U rt) (subst_tvar_in_cterm k U v)
  | CInr lt v => CInr (subst_tvar_in_cty k U lt) (subst_tvar_in_cterm k U v)
  | CMatchSum x y s kappa mot scrut lb rb =>
      CMatchSum x y s kappa (subst_tvar_in_cty (S k) (lift_cty 0 1 U) mot)
        (subst_tvar_in_cterm k U scrut)
        (subst_tvar_in_cterm (S k) (lift_cty 0 1 U) lb)
        (subst_tvar_in_cterm (S k) (lift_cty 0 1 U) rb)
  | CIf c th el =>
      CIf (subst_tvar_in_cterm k U c) (subst_tvar_in_cterm k U th) (subst_tvar_in_cterm k U el)
  | CRecordMk id fields =>
      CRecordMk id (map (fun '(fn, fg, ft, fv) =>
        (fn, fg, subst_tvar_in_cty k U ft, subst_tvar_in_cterm k U fv)) fields)
  | CMatchRecord id s mot scrut bs body =>
      CMatchRecord id s (subst_tvar_in_cty k U mot) (subst_tvar_in_cterm k U scrut) bs
        (subst_tvar_in_cterm (length bs + k) (lift_cty 0 (length bs) U) body)
  | CSubgrade target body => CSubgrade (subst_tvar_in_cty k U target) (subst_tvar_in_cterm k U body)
  | CFix xn xr sr mot scrut base step =>
      CFix xn xr sr (subst_tvar_in_cty (S k) (lift_cty 0 1 U) mot)
        (subst_tvar_in_cterm k U scrut)
        (subst_tvar_in_cterm k U base)
        (subst_tvar_in_cterm (S (S k)) (lift_cty 0 2 U) step)
  end.

Definition cenv_tvar_safe {D : JoinDomain} (env_a : cenv D) (k : nat) : Prop :=
  forall x e, x < length env_a -> clookup env_a x = Some e ->
    cty_uses_kinds false true false false false false false (k - S x) (cannotation e) = false.

Lemma cenv_tvar_safe_cons : forall (D : JoinDomain) e0 (env_a : cenv D),
  cty_uses_kinds false true false false false false false (length env_a) (cannotation e0) = false ->
  cenv_tvar_safe env_a (length env_a) ->
  cenv_tvar_safe (e0 :: env_a) (S (length env_a)).
Proof.
  intros D e0 env_a He0 Hsafe [| x'] e Hlt Hl; cbn in *.
  - inversion Hl; subst. rewrite Nat.sub_0_r. exact He0.
  - apply (Hsafe x' e ltac:(lia) Hl).
Qed.

Lemma cenv_tvar_safe_tl : forall (D : JoinDomain) e0 (env_a : cenv D),
  cenv_tvar_safe (e0 :: env_a) (S (length env_a)) ->
  cenv_tvar_safe env_a (length env_a).
Proof.
  intros D e0 env_a Hsafe x e Hlt Hl.
  exact (Hsafe (S x) e ltac:(cbn; lia) Hl).
Qed.

Lemma cenv_tvar_safe_skipn : forall (D : JoinDomain) n (env_a : cenv D),
  cenv_tvar_safe env_a (length env_a) ->
  cenv_tvar_safe (skipn n env_a) (length (skipn n env_a)).
Proof.
  intros D n. induction n as [| n IH]; intros [| e rest] Hsafe; cbn; try exact Hsafe.
  apply IH. apply cenv_tvar_safe_tl in Hsafe. exact Hsafe.
Qed.

Lemma cdemand_tvar_safe_erase : forall (D : JoinDomain) (b : cbinding D) env_b lvl_b,
  erase_hints (cannotation b) = CUniv lvl_b ->
  (forall env i d, CIdxDemand env i d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cidx_uses_kinds false false false false false (length env_a) i = false) /\
  (forall env T d, CTypeDemand env T d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cty_uses_kinds false true false false false false false (length env_a) T = false).
Proof.
  intros D b env_b lvl_b Hb.
  assert (Hlk_b : forall (env_a : cenv D), clookup (env_a ++ b :: env_b) (length env_a) = Some b).
  { intro env_a. unfold clookup. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
  assert (Hfl_b : flags_allow (ren_cty (plus (S (length (@nil (cbinding D))))) (cannotation b)) false true false false false false false) by
    (unfold flags_allow; rewrite erase_hints_ren, Hb; reflexivity).
  split.
  - intros env i d H env_a ->.
    eapply cidx_demand_uses_kinds; [exact H | apply Hlk_b |].
    eapply flags_allow_ren_plus; exact Hfl_b.
  - intros env T d H env_a ->.
    eapply ctype_demand_uses_kinds; [exact H | apply Hlk_b |].
    eapply flags_allow_ren_plus; exact Hfl_b.
Qed.

Lemma cdemand_tvar_safe : forall (D : JoinDomain) (b : cbinding D) env_b lvl_b,
  cannotation b = CUniv lvl_b ->
  (forall env i d, CIdxDemand env i d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cidx_uses_kinds false false false false false (length env_a) i = false) /\
  (forall env T d, CTypeDemand env T d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cty_uses_kinds false true false false false false false (length env_a) T = false).
Proof.
  intros D b env_b lvl_b Hb. eapply cdemand_tvar_safe_erase. rewrite Hb. reflexivity.
Qed.

Lemma cidx_uses_kinds_ren_tvar_gen : forall (D : JoinDomain) (i : cidx D) rn c k,
  (forall x, x <> k -> rn x <> c) ->
  cidx_uses_kinds false false false false false k i = false ->
  cidx_uses_kinds false false false false false c (ren_cidx rn i) = false.
Proof.
  intros D i. induction i; intros rn c k Hr Hk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hk as [H1 H2]; rewrite (IHi1 _ _ _ Hr H1), (IHi2 _ _ _ Hr H2); reflexivity);
    try (apply (IHi _ _ _ Hr Hk));
    try (apply Nat.eqb_neq, Hr; apply Nat.eqb_neq; exact Hk).
  apply orb_false_iff in Hk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
  rewrite (proj2 (Nat.eqb_neq (rn s) c) (Hr s (proj1 (Nat.eqb_neq s k) H1))).
  assert (Hrs : forall x, x <> S k -> ren_shift rn x <> S c) by
    (intros [| x'] Hne; cbn; [lia | pose proof (Hr x' ltac:(lia)); lia]).
  rewrite (IHi1 _ _ _ Hrs H2), (IHi2 _ _ _ Hrs H3). reflexivity.
Qed.

Lemma cty_uses_kinds_tvar_ren_gen : forall (D : JoinDomain) (T : cty D) rn c k,
  (forall x, x <> k -> rn x <> c) ->
  cty_uses_kinds false true false false false false false k T = false ->
  cty_uses_kinds false true false false false false false c (ren_cty rn T) = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros rn c k Hr Hk; cbn in *; try reflexivity;
    try (apply (IHT _ _ _ Hr Hk));
    try (apply orb_false_iff in Hk as [H1 H2]; rewrite (IHT1 _ _ _ Hr H1), (IHT2 _ _ _ Hr H2); reflexivity).
  - apply orb_false_iff in Hk as [H1 H2].
    rewrite (IHT _ _ _ Hr H1), (cidx_uses_kinds_ren_tvar_gen D len rn c k Hr H2). reflexivity.
  - apply Nat.eqb_neq, Hr; apply Nat.eqb_neq; exact Hk.
  - apply orb_false_iff in Hk as [H1 H2].
    assert (Hrs : forall x, x <> S k -> ren_shift rn x <> S c) by
      (intros [| x'] Hne; cbn; [lia | pose proof (Hr x' ltac:(lia)); lia]).
    rewrite (IHT1 _ _ _ Hr H1), (IHT2 _ _ _ Hrs H2). reflexivity.
  - apply orb_false_iff in Hk as [H1 H2].
    assert (Hrs : forall x, x <> S k -> ren_shift rn x <> S c) by
      (intros [| x'] Hne; cbn; [lia | pose proof (Hr x' ltac:(lia)); lia]).
    rewrite (IHT1 _ _ _ Hr H1), (IHT2 _ _ _ Hrs H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hk as [H1 Hk2].
    rewrite (H2 _ _ _ Hr H1), (IHf H3 Hk2). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hk as [H1 H2].
    rewrite (cidx_uses_kinds_ren_tvar_gen D idx rn c k Hr H1), (IH H2). reflexivity.
Qed.

Lemma cty_uses_kinds_tvar_ren_plus : forall (D : JoinDomain) (T : cty D) d k,
  cty_uses_kinds false true false false false false false k T = false ->
  cty_uses_kinds false true false false false false false (d + k) (ren_cty (plus d) T) = false.
Proof.
  intros D T d k Hk. eapply cty_uses_kinds_tvar_ren_gen; [| exact Hk].
  intros x Hne; lia.
Qed.

Lemma cty_uses_kinds_tvar_ren_avoid : forall (D : JoinDomain) (T : cty D) rn c,
  (forall x, rn x <> c) ->
  cty_uses_kinds false true false false false false false c (ren_cty rn T) = false.
Proof.
  intros D T.
  assert (Hi : forall (i : cidx D) rn c, (forall x, rn x <> c) ->
    cidx_uses_kinds false false false false false c (ren_cidx rn i) = false).
  { induction i; intros rn c Hr; cbn; try reflexivity;
      try (rewrite (IHi1 _ _ Hr), (IHi2 _ _ Hr); reflexivity);
      try (apply IHi; exact Hr);
      try (apply Nat.eqb_neq, Hr).
    rewrite (proj2 (Nat.eqb_neq (rn s) c) (Hr s)).
    assert (Hrs : forall x, ren_shift rn x <> S c) by (intros [| x']; cbn; [lia | pose proof (Hr x'); lia]).
    rewrite (IHi1 _ _ Hrs), (IHi2 _ _ Hrs). reflexivity. }
  induction T using cty_ind_nested; intros rn c Hr; cbn; try reflexivity;
    try (apply IHT; exact Hr);
    try (rewrite (IHT1 _ _ Hr), (IHT2 _ _ Hr); reflexivity).
  - rewrite (IHT _ _ Hr), (Hi len _ _ Hr). reflexivity.
  - apply Nat.eqb_neq, Hr.
  - assert (Hrs : forall x, ren_shift rn x <> S c) by (intros [| x']; cbn; [lia | pose proof (Hr x'); lia]).
    rewrite (IHT1 _ _ Hr), (IHT2 _ _ Hrs). reflexivity.
  - assert (Hrs : forall x, ren_shift rn x <> S c) by (intros [| x']; cbn; [lia | pose proof (Hr x'); lia]).
    rewrite (IHT1 _ _ Hr), (IHT2 _ _ Hrs). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ Hr), (IHf H3). reflexivity.
  - induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite (Hi idx _ _ Hr), IH. reflexivity.
Qed.

Lemma cty_uses_kinds_tvar_ren_gt : forall (D : JoinDomain) (T : cty D) d k,
  k < d ->
  cty_uses_kinds false true false false false false false k (ren_cty (plus d) T) = false.
Proof.
  intros D T d k Hkd. apply cty_uses_kinds_tvar_ren_avoid. intro x; lia.
Qed.

Lemma tvar_shift_lift_var : forall v c k,
  c <= k -> v <> k ->
  (let r := if v <? k then v else if v =? k then 0 else v - 1 in
   if r <? c then r else r + 1) =
  (let l := if v <? c then v else v + 1 in
   if l <? S k then l else if l =? S k then 0 else l - 1).
Proof.
  intros v c k Hck Hne.
  destruct (lt_eq_lt_dec v k) as [[Hlt | Heq] | Hgt]; [| contradiction |];
    destruct (Nat.ltb_spec v c); cbv zeta; repeat (rw_nat_bool; cbv iota); lia.
Qed.

Lemma subst_tvar_in_cidx_lift_ge : forall (D : JoinDomain) (i : cidx D) c k,
  c <= k ->
  cidx_uses_kinds false false false false false k i = false ->
  lift_cidx c 1 (subst_tvar_in_cidx k i) = subst_tvar_in_cidx (S k) (lift_cidx c 1 i).
Proof.
  intros D i.
  induction i; intros c k Hck Hk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hk as [H1 H2]; rewrite (IHi1 _ _ Hck H1), (IHi2 _ _ Hck H2); reflexivity);
    try (rewrite (IHi _ _ Hck Hk); reflexivity);
    nat_bool_hyps.
  - f_equal. apply tvar_shift_lift_var; assumption.
  - f_equal. apply tvar_shift_lift_var; assumption.
  - f_equal. apply tvar_shift_lift_var; assumption.
  - f_equal. apply tvar_shift_lift_var; assumption.
  - apply orb_false_iff in Hk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hrl : forall (j : cidx D), ren_cidx (ren_shift (ren_lift c 1)) j = lift_cidx (S c) 1 j) by
      (intro j; apply ren_cidx_ext; intros [| m]; unfold ren_shift, ren_lift; cbn; try reflexivity; destruct (m <? c) eqn:Em; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); reflexivity).
    f_equal; [apply tvar_shift_lift_var; assumption
             | rewrite !Hrl; apply (IHi1 (S c) (S k) ltac:(lia) H2)
             | rewrite !Hrl; apply (IHi2 (S c) (S k) ltac:(lia) H3)].
Qed.

Lemma subst_tvar_in_cty_lift_ge : forall (D : JoinDomain) (T U : cty D) c k,
  c <= k ->
  cty_uses_kinds false true false false false false false k T = false ->
  lift_cty c 1 (subst_tvar_in_cty k U T) = subst_tvar_in_cty (S k) (lift_cty c 1 U) (lift_cty c 1 T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U c k Hck Hk; cbn in *; try reflexivity;
    try (f_equal; apply IHT; assumption);
    try (apply orb_false_iff in Hk as [H1 H2]; f_equal; [apply IHT1 | apply IHT2]; assumption).
  - apply orb_false_iff in Hk as [H1 H2]. f_equal; [apply IHT; assumption | apply subst_tvar_in_cidx_lift_ge; assumption].
  - destruct (Nat.eq_dec x k) as [-> | Hne].
    + rewrite Nat.eqb_refl. unfold lift_cty, ren_lift.
      rewrite (proj2 (Nat.ltb_ge k c) Hck). replace (k + 1) with (S k) by lia.
      rewrite Nat.eqb_refl. reflexivity.
    + destruct (lt_eq_lt_dec x k) as [[Hlt | Heq] | Hgt]; [| contradiction |].
      * repeat (rw_nat_bool; cbv iota). unfold lift_cty, ren_lift.
        destruct (x <? c) eqn:Exc; nat_bool_hyps; cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
      * repeat (rw_nat_bool; cbv iota). unfold lift_cty, ren_lift.
        destruct (x <? c) eqn:Exc; nat_bool_hyps; [lia |].
        destruct (x - 1 <? c) eqn:Exc1; nat_bool_hyps; [lia |].
        cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - nat_bool_hyps. unfold ren_lift. f_equal. apply tvar_shift_lift_var; assumption.
  - apply orb_false_iff in Hk as [H1 H2].
    assert (Hrl : forall (T0 : cty D), ren_cty (ren_shift (ren_lift c 1)) T0 = lift_cty (S c) 1 T0) by
      (intro T0; apply ren_cty_ext; intros [| m]; unfold ren_shift, ren_lift; cbn; try reflexivity; destruct (m <? c) eqn:Em; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); reflexivity).
    f_equal; [apply IHT1; assumption |].
    rewrite !Hrl, (IHT2 (lift_cty 0 1 U) (S c) (S k) ltac:(lia) H2).
    rewrite (lift_cty_comm_01 c U). reflexivity.
  - apply orb_false_iff in Hk as [H1 H2].
    assert (Hrl : forall (T0 : cty D), ren_cty (ren_shift (ren_lift c 1)) T0 = lift_cty (S c) 1 T0) by
      (intro T0; apply ren_cty_ext; intros [| m]; unfold ren_shift, ren_lift; cbn; try reflexivity; destruct (m <? c) eqn:Em; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); reflexivity).
    f_equal; [apply IHT1; assumption |].
    rewrite !Hrl, (IHT2 (lift_cty 0 1 U) (S c) (S k) ltac:(lia) H2).
    rewrite (lift_cty_comm_01 c U). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hk as [H1 Hk2].
    f_equal; [f_equal; apply (H2 _ _ _ Hck H1) | apply (IHf H3 Hk2)].
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hk as [H1 H2].
    f_equal; [apply subst_tvar_in_cidx_lift_ge; assumption | apply (IH H2)].
Qed.

Lemma subst_tvar_in_cty_alpha_eq : forall (D : JoinDomain) k (U1 U2 T1 T2 : cty D),
  cty_alpha_eq U1 U2 ->
  cty_alpha_eq T1 T2 ->
  cty_alpha_eq (subst_tvar_in_cty k U1 T1) (subst_tvar_in_cty k U2 T2).
Proof.
  intros D k U1 U2 T1 T2. apply cty_alpha_eq_subst_tvar.
Qed.

Lemma subst_tvar_in_cidx_eqb : forall (D : JoinDomain) k (i1 i2 : cidx D),
  cidx_eqb i1 i2 = true ->
  cidx_eqb (subst_tvar_in_cidx k i1) (subst_tvar_in_cidx k i2) = true.
Proof.
  intros D k i1 i2 H. apply cidx_eqb_sound in H as ->. apply cidx_eqb_refl.
Qed.

Lemma subst_tvar_in_cty_ren_skip_gen : forall (D : JoinDomain) (T U : cty D) k r1 r2,
  (forall x, (r1 x < k /\ r2 x = r1 x) \/ (r1 x > k /\ r2 x = r1 x - 1)) ->
  subst_tvar_in_cty k U (ren_cty r1 T) = ren_cty r2 T.
Proof.
  assert (Hi : forall (D : JoinDomain) (i : cidx D) k r1 r2,
    (forall x, (r1 x < k /\ r2 x = r1 x) \/ (r1 x > k /\ r2 x = r1 x - 1)) ->
    subst_tvar_in_cidx k (ren_cidx r1 i) = ren_cidx r2 i).
  { intros D i. induction i; intros k r1 r2 Hr; cbn; try reflexivity;
      try (rewrite (IHi1 _ _ _ Hr), (IHi2 _ _ _ Hr); reflexivity);
      try (rewrite (IHi _ _ _ Hr); reflexivity);
      try (destruct (Hr x) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (Hr b) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (Hr p) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia).
    - f_equal.
      + destruct (Hr s) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); lia.
      + apply (IHi1 (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
      + apply (IHi2 (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]]. }
  intros D T. induction T using cty_ind_nested; intros U k r1 r2 Hr; cbn; try reflexivity;
    try (f_equal; apply IHT; exact Hr);
    try (f_equal; [apply IHT1 | apply IHT2]; exact Hr).
  - f_equal; [apply IHT; exact Hr | apply Hi; exact Hr].
  - destruct (Hr x) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Hr b) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - f_equal; [apply IHT1; exact Hr |].
    apply (IHT2 (lift_cty 0 1 U) (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
  - f_equal; [apply IHT1; exact Hr |].
    apply (IHT2 (lift_cty 0 1 U) (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ _ _ Hr), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply Hi; exact Hr | exact IH].
Qed.

Lemma subst_tvar_lookup_lt : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b x e,
  x < length env_a ->
  cenv_tvar_safe env_a (length env_a) ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_tvar_cenv U z env_a ++ env_b) x = Some e' /\
    ren_cty (plus (S x)) (cannotation e') =
      subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) (ren_cty (plus (S x)) (cannotation e)) /\
    vec_zero (S x) ++ ctype_uses e' = vec_subst (length env_a) z (vec_zero (S x) ++ ctype_uses e) /\
    skipn (S x) (subst_tvar_cenv U z env_a ++ env_b) =
      subst_tvar_cenv U z (skipn (S x) env_a) ++ env_b /\
    skipn (S x) (env_a ++ b :: env_b) = skipn (S x) env_a ++ b :: env_b.
Proof.
  intros D U z env_a. induction env_a as [| e0 rest IH]; intros b env_b [| x'] e Hlt Hsafe Hl; cbn in *; try lia.
  - inversion Hl; subst; cbn.
    exists {| cbinder := cbinder e;
              cannotation := subst_tvar_in_cty (length rest) (lift_cty 0 (length rest) U) (cannotation e);
              ctype_uses := vec_subst (length rest) z (ctype_uses e) |}.
    repeat split; try reflexivity.
    cbn [cannotation].
    pose proof (Hsafe 0 e ltac:(cbn; lia) eq_refl) as He_safe.
    cbn [length] in He_safe. replace (S (length rest) - 1) with (length rest) in He_safe by lia.
    rewrite ren_plus_1_as_lift, (subst_tvar_in_cty_lift_ge D (cannotation e) (lift_cty 0 (length rest) U) 0 (length rest) ltac:(lia) He_safe).
    rewrite lift_cty_add, <- ren_plus_1_as_lift. reflexivity.
  - assert (Hsafe_r : cenv_tvar_safe rest (length rest)) by (intros y ey Hy Hly; exact (Hsafe (S y) ey ltac:(cbn; lia) Hly)).
    destruct (IH b env_b x' e ltac:(lia) Hsafe_r Hl) as [e' [Hl' [Heq [Hvec [Hsk1 Hsk2]]]]].
    exists e'. repeat split; [exact Hl' | | | exact Hsk1 | exact Hsk2].
    + assert (He_safe : cty_uses_kinds false true false false false false false (length rest - S x') (cannotation e) = false).
      { apply (Hsafe (S x') e ltac:(cbn; lia)).
        clear -Hlt Hl. unfold clookup in *. rewrite nth_error_app1 in Hl by lia. exact Hl. }
      assert (He_safe_ren : cty_uses_kinds false true false false false false false (length rest) (ren_cty (fun m => S (x' + m)) (cannotation e)) = false) by
        (replace (length rest) with (S x' + (length rest - S x')) by lia; apply cty_uses_kinds_tvar_ren_plus; exact He_safe).
      transitivity (ren_cty S (ren_cty (fun m => S (x' + m)) (cannotation e')));
        [rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
        | rewrite Heq, !ren_plus_1_as_lift, (subst_tvar_in_cty_lift_ge D _ _ 0 (length rest) ltac:(lia) He_safe_ren), lift_cty_add;
          cbn [Nat.add]; rewrite <- ren_plus_1_as_lift, ren_cty_comp; f_equal; apply ren_cty_ext; intro y; cbn; reflexivity ].
    + cbn [vec_zero vec_subst repeat app]; f_equal; exact Hvec.
Qed.

Lemma subst_tvar_lookup_lt_ann_raw : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b x e,
  x < length env_a ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_tvar_cenv U z env_a ++ env_b) x = Some e' /\
    cannotation e' = subst_tvar_in_cty (length env_a - S x) (lift_cty 0 (length env_a - S x) U) (cannotation e) /\
    ctype_uses e' = vec_subst (length env_a - S x) z (ctype_uses e) /\
    skipn (S x) (subst_tvar_cenv U z env_a ++ env_b) = subst_tvar_cenv U z (skipn (S x) env_a) ++ env_b /\
    skipn (S x) (env_a ++ b :: env_b) = skipn (S x) env_a ++ b :: env_b.
Proof.
  intros D U z env_a. induction env_a as [| e0 rest IH]; intros b env_b [| x'] e Hlt Hl; cbn in *; try lia.
  - inversion Hl; subst; cbn.
    eexists; repeat split; try reflexivity; rewrite !Nat.sub_0_r; reflexivity.
  - destruct (IH b env_b x' e ltac:(lia) Hl) as [e' [Hl' [Ha [Hu [Hs1 Hs2]]]]].
    exists e'; repeat split; assumption.
Qed.

Lemma subst_tvar_lookup_gt_ann : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b x e,
  x > length env_a ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_tvar_cenv U z env_a ++ env_b) (x - 1) = Some e' /\
    e' = e /\
    ren_cty (plus (S (x - 1))) (cannotation e') =
      subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) (ren_cty (plus (S x)) (cannotation e)) /\
    skipn (S (x - 1)) (subst_tvar_cenv U z env_a ++ env_b) = skipn (S x) (env_a ++ b :: env_b).
Proof.
  intros D U z env_a b env_b x e Hgt Hl.
  assert (Hx_ge : S (length env_a) <= x) by lia.
  assert (Hl_b : clookup env_b (x - S (length env_a)) = Some e).
  { unfold clookup in Hl. rewrite nth_error_app2 in Hl by lia.
    replace (x - length env_a) with (S (x - S (length env_a))) in Hl by lia. exact Hl. }
  exists e. split; [| split; [| split]].
  - unfold clookup. rewrite nth_error_app2 by (rewrite subst_tvar_cenv_length; lia).
    rewrite subst_tvar_cenv_length.
    replace (x - 1 - length env_a) with (x - S (length env_a)) by lia. exact Hl_b.
  - reflexivity.
  - symmetry. apply subst_tvar_in_cty_ren_skip_gen. intro y; right; lia.
  - rewrite !skipn_app, !subst_tvar_cenv_length.
    rewrite (skipn_all2 (subst_tvar_cenv U z env_a)) by (rewrite subst_tvar_cenv_length; lia).
    rewrite (skipn_all2 env_a) by lia.
    replace (S (x - 1) - length env_a) with (x - length env_a) by lia.
    replace (S x - length env_a) with (S (x - length env_a)) by lia.
    cbn [skipn app]. reflexivity.
Qed.

Lemma subst_tvar_lookup_gt : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b x e,
  x > length env_a ->
  length z = length env_b ->
  length (vec_zero (S x) ++ ctype_uses e) = S (length env_a + length env_b) ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_tvar_cenv U z env_a ++ env_b) (x - 1) = Some e' /\
    ren_cty (plus (S (x - 1))) (cannotation e') =
      subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) (ren_cty (plus (S x)) (cannotation e)) /\
    vec_zero (S (x - 1)) ++ ctype_uses e' = vec_subst (length env_a) z (vec_zero (S x) ++ ctype_uses e) /\
    skipn (S (x - 1)) (subst_tvar_cenv U z env_a ++ env_b) = skipn (S x) (env_a ++ b :: env_b).
Proof.
  intros D U z env_a b env_b x e Hgt Hz Hlen Hl.
  destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b x e Hgt Hl) as [e' [Hl' [Ha [Hren Hsk]]]].
  exists e'. repeat split; try assumption.
  subst e'. rewrite length_app, vec_zero_length in Hlen.
  replace (vec_zero (D := D) (S x) ++ ctype_uses e)
     with (vec_zero (D := D) (S (length env_a)) ++ (vec_zero (D := D) (x - length env_a) ++ ctype_uses e))
    by (rewrite app_assoc; unfold vec_zero; rewrite <- repeat_app; f_equal; f_equal; lia).
  rewrite vec_subst_zero_prefix by (rewrite length_app, vec_zero_length; lia).
  rewrite app_assoc. unfold vec_zero; rewrite <- repeat_app. f_equal; f_equal; lia.
Qed.

Lemma subst_tvar_idx_demand : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b lvl_b i d,
  cannotation b = CUniv lvl_b ->
  cenv_tvar_safe env_a (length env_a) ->
  CTypeDemand env_b U z ->
  CIdxDemand (env_a ++ b :: env_b) i d ->
  exists d',
    CIdxDemand (subst_tvar_cenv U z env_a ++ env_b) (subst_tvar_in_cidx (length env_a) i) d' /\
    branch_rel d' (vec_subst (length env_a) z d).
Proof.
  intros D U z env_a b env_b lvl_b i d Hb Hsafe HU H.
  assert (Hz_len : length z = length env_b) by (eapply ctype_demand_length; exact HU).
  assert (Hvz_len : forall k (u : list (grade D)),
    length u = S (k + length env_b) ->
    length (vec_subst k z u) = k + length env_b) by
    (intros kk uu Hlu; exact (vec_subst_length D kk z uu (length env_b) Hz_len Hlu)).
  assert (Hv0_len : forall k (u : list (grade D)),
    length u = S (k + length env_b) ->
    length (vec_subst k (vec_zero (length env_b)) u) = k + length env_b) by
    (intros kk uu Hlu; exact (vec_subst_length D kk (vec_zero (length env_b)) uu (length env_b) (vec_zero_length D (length env_b)) Hlu)).
  remember (env_a ++ b :: env_b) as env1 eqn:Eenv.
  revert env_a Eenv Hsafe.
  induction H; intros env_a Eenv Hsafe; subst env; cbn.
  - destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt].
    + destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b x e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandVar; [exact Hl' |].
        rewrite Heq. exact (subst_tvar_in_cty_alpha_eq D (length env_a - S x) (lift_cty 0 (length env_a - S x) U) (lift_cty 0 (length env_a - S x) U) _ _ (cty_alpha_eq_refl D _) H0).
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | exact Hz_len | exact Hlt].
    + subst x. assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b x e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hx_len; cbn in Hx_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandVar; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
          [apply branch_rel_refl | exact Hz_len | lia | lia].
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero;
      [eexists; split; [constructor | rewrite !length_app, subst_tvar_cenv_length; apply branch_rel_refl] | exact Hz_len].
  - destruct (IHCIdxDemand1 env_a eq_refl Hsafe) as [dl' [Hdl' Hbrl]].
    destruct (IHCIdxDemand2 env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]].
    pose proof (cidx_demand_length D _ _ _ H) as Hlen1.
    pose proof (cidx_demand_length D _ _ _ H0) as Hlen2.
    rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2.
    exists (vec_add dl' dr'); split; [constructor; assumption |].
    rewrite (vec_subst_add D (length env_a) z dl dr (length env_b)); [apply branch_rel_add; assumption | exact Hz_len | lia | lia].
  - destruct (IHCIdxDemand env_a eq_refl Hsafe) as [d' [Hd' Hbr]].
    exists (vec_scale q d'); split; [constructor; assumption |].
    rewrite vec_subst_scale; apply branch_rel_scale; exact Hbr.
  - destruct (lt_eq_lt_dec b0 (length env_a)) as [[Hlt | Heq_b] | Hgt].
    + destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b b0 e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandUnbox; [exact Hl' |].
        rewrite Heq. exact (subst_tvar_in_cty_alpha_eq D (length env_a - S b0) (lift_cty 0 (length env_a - S b0) U) (lift_cty 0 (length env_a - S b0) U) _ _ (cty_alpha_eq_refl D _) H0).
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | exact Hz_len | exact Hlt].
    + subst b0. assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b b0 e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hb_len : b0 < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hb_len; cbn in Hb_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandUnbox; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
          [apply branch_rel_refl | exact Hz_len | lia | lia].
  - destruct (lt_eq_lt_dec p (length env_a)) as [[Hlt | Heq_p] | Hgt].
    + destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b p e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandFst; [exact Hl' |].
        rewrite Heq. exact (subst_tvar_in_cty_alpha_eq D (length env_a - S p) (lift_cty 0 (length env_a - S p) U) (lift_cty 0 (length env_a - S p) U) _ _ (cty_alpha_eq_refl D _) H0).
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | exact Hz_len | exact Hlt].
    + subst p. assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b p e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hp_len : p < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hp_len; cbn in Hp_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandFst; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
          [apply branch_rel_refl | exact Hz_len | lia | lia].
  - destruct (lt_eq_lt_dec p (length env_a)) as [[Hlt | Heq_p] | Hgt].
    + destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b p e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandSnd; [exact Hl' |].
        rewrite Heq. exact (subst_tvar_in_cty_alpha_eq D (length env_a - S p) (lift_cty 0 (length env_a - S p) U) (lift_cty 0 (length env_a - S p) U) _ _ (cty_alpha_eq_refl D _) H0).
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | exact Hz_len | exact Hlt].
    + subst p. assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b p e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hp_len : p < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hp_len; cbn in Hp_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandSnd; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
          [apply branch_rel_refl | exact Hz_len | lia | lia].
  - destruct (lt_eq_lt_dec s (length env_a)) as [[Hlt | Heq_s] | Hgt].
    + destruct (subst_tvar_lookup_lt D U z env_a b env_b s e Hlt Hsafe H) as [e' [Hl' [Hren [Hvec _]]]].
      repeat (rw_nat_bool; cbv iota).
      assert (He_safe_raw : cty_uses_kinds false true false false false false false (length env_a - S s) (cannotation e) = false) by
        (apply (Hsafe s e Hlt); unfold clookup in H; rewrite nth_error_app1 in H by exact Hlt; exact H).
      assert (HSum_safe : cty_uses_kinds false true false false false false false (length env_a) (CSum A B) = false) by
        (rewrite <- (cty_uses_kinds_alpha D _ _ _ _ _ _ _ _ _ _ H0);
         replace (length env_a) with (S s + (length env_a - S s)) by lia;
         apply cty_uses_kinds_tvar_ren_plus; exact He_safe_raw).
      cbn in HSum_safe; apply orb_false_iff in HSum_safe as [HA_safe HB_safe].
      assert (Hsafe_A : cenv_tvar_safe ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) (S (length env_a))) by
        (apply cenv_tvar_safe_cons; [exact HA_safe | exact Hsafe]).
      assert (Hsafe_B : cenv_tvar_safe ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) (S (length env_a))) by
        (apply cenv_tvar_safe_cons; [exact HB_safe | exact Hsafe]).
      destruct (IHCIdxDemand1 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl Hsafe_A) as [dl' [Hdl' Hbrl]].
      destruct (IHCIdxDemand2 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl Hsafe_B) as [dr' [Hdr' Hbrr]].
      cbn [subst_tvar_cenv length] in Hdl', Hdr', Hbrl, Hbrr.
      pose proof (cidx_demand_length D _ _ _ H1) as Hlen1.
      pose proof (cidx_demand_length D _ _ _ H2) as Hlen2.
      cbn [length] in Hlen1, Hlen2; rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2.
      destruct (BranchVec_subst D (length env_a) z (tl dl) (tl dr) d_br (tl dl') (tl dr') (length env_b) Hz_len
                  ltac:(destruct dl; cbn in *; lia) ltac:(destruct dr; cbn in *; lia) H3
                  (eq_ind_r (fun v => branch_rel (tl dl') v) (branch_rel_tl D _ _ Hbrl) (vec_subst_tl D _ _ _))
                  (eq_ind_r (fun v => branch_rel (tl dr') v) (branch_rel_tl D _ _ Hbrr) (vec_subst_tl D _ _ _)))
        as [dbr' [Hdbr' Hbr_d]].
      assert (Hlen_br : length d_br = length env_a + S (length env_b)) by
        (erewrite BranchVec_length; [| | exact H3]; destruct dl, dr; cbn in *; lia).
      eexists; split.
      * eapply CIdxDemandCase with (A := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A)
                                   (B := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) B).
        -- exact Hl'.
        -- rewrite Hren. exact (subst_tvar_in_cty_alpha_eq D (length env_a) (lift_cty 0 (length env_a) U) (lift_cty 0 (length env_a) U) _ _ (cty_alpha_eq_refl D _) H0).
        -- eapply CIdxDemand_alpha_env; [| exact Hdl'].
           constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl].
        -- eapply CIdxDemand_alpha_env; [| exact Hdr'].
           constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl].
        -- exact Hdbr'.
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r.
        rewrite (vec_subst_add D (length env_a) z (vec_single (S (length env_a + length env_b)) s one) d_br (length env_b))
          by (try exact Hz_len; try rewrite vec_single_length; lia).
        rewrite vec_subst_single_lt by (try exact Hz_len; lia).
        apply branch_rel_add; [apply branch_rel_refl | exact Hbr_d].
    + subst s. assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite erase_hints_ren, Hb in H0. cbn in H0. discriminate.
    + destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b s e Hgt H) as [e' [Hl' [Heq [Hren _]]]].
      assert (Hs_len : s < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hs_len; cbn in Hs_len. repeat (rw_nat_bool; cbv iota).
      assert (HSum_safe : cty_uses_kinds false true false false false false false (length env_a) (CSum A B) = false) by
        (rewrite <- (cty_uses_kinds_alpha D _ _ _ _ _ _ _ _ _ _ H0); apply cty_uses_kinds_tvar_ren_gt; lia).
      cbn in HSum_safe; apply orb_false_iff in HSum_safe as [HA_safe HB_safe].
      assert (Hsafe_A : cenv_tvar_safe ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) (S (length env_a))) by
        (apply cenv_tvar_safe_cons; [exact HA_safe | exact Hsafe]).
      assert (Hsafe_B : cenv_tvar_safe ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) (S (length env_a))) by
        (apply cenv_tvar_safe_cons; [exact HB_safe | exact Hsafe]).
      destruct (IHCIdxDemand1 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl Hsafe_A) as [dl' [Hdl' Hbrl]].
      destruct (IHCIdxDemand2 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl Hsafe_B) as [dr' [Hdr' Hbrr]].
      cbn [subst_tvar_cenv length] in Hdl', Hdr', Hbrl, Hbrr.
      pose proof (cidx_demand_length D _ _ _ H1) as Hlen1.
      pose proof (cidx_demand_length D _ _ _ H2) as Hlen2.
      cbn [length] in Hlen1, Hlen2; rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2.
      destruct (BranchVec_subst D (length env_a) z (tl dl) (tl dr) d_br (tl dl') (tl dr') (length env_b) Hz_len
                  ltac:(destruct dl; cbn in *; lia) ltac:(destruct dr; cbn in *; lia) H3
                  (eq_ind_r (fun v => branch_rel (tl dl') v) (branch_rel_tl D _ _ Hbrl) (vec_subst_tl D _ _ _))
                  (eq_ind_r (fun v => branch_rel (tl dr') v) (branch_rel_tl D _ _ Hbrr) (vec_subst_tl D _ _ _)))
        as [dbr' [Hdbr' Hbr_d]].
      assert (Hlen_br : length d_br = length env_a + S (length env_b)) by
        (erewrite BranchVec_length; [| | exact H3]; destruct dl, dr; cbn in *; lia).
      eexists; split.
      * eapply CIdxDemandCase with (A := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A)
                                   (B := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) B).
        -- exact Hl'.
        -- rewrite Hren. exact (subst_tvar_in_cty_alpha_eq D (length env_a) (lift_cty 0 (length env_a) U) (lift_cty 0 (length env_a) U) _ _ (cty_alpha_eq_refl D _) H0).
        -- eapply CIdxDemand_alpha_env; [| exact Hdl'].
           constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl].
        -- eapply CIdxDemand_alpha_env; [| exact Hdr'].
           constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl].
        -- exact Hdbr'.
      * rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r.
        rewrite (vec_subst_add D (length env_a) z (vec_single (S (length env_a + length env_b)) s one) d_br (length env_b))
          by (try exact Hz_len; try rewrite vec_single_length; lia).
        rewrite vec_subst_single_gt by (try exact Hz_len; lia).
        apply branch_rel_add; [apply branch_rel_refl | exact Hbr_d].
Qed.

Lemma crecord_field_demand_length_t : forall (D : JoinDomain) (env : cenv D) fs df,
  CRecordFieldDemand env fs df -> length df = length env.
Proof.
  intros D env fs df H. induction H; [apply vec_zero_length | rewrite vec_add_length; [eapply ctype_demand_length; eassumption |]].
  erewrite ctype_demand_length by eassumption. symmetry; exact IHCRecordFieldDemand.
Qed.

Lemma subst_tvar_type_demand : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b lvl_b T d,
  cannotation b = CUniv lvl_b ->
  cenv_tvar_safe env_a (length env_a) ->
  CTypeDemand env_b U z ->
  CTypeDemand (env_a ++ b :: env_b) T d ->
  exists d',
    CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) T) d' /\
    branch_rel d' (vec_subst (length env_a) z d).
Proof.
  intros D U z env_a b env_b lvl_b T d Hb Hsafe HU H.
  assert (Hz_len : length z = length env_b) by (eapply ctype_demand_length; exact HU).
  assert (Hvz_len : forall k (u : list (grade D)),
    length u = S (k + length env_b) ->
    length (vec_subst k z u) = k + length env_b) by
    (intros kk uu Hlu; exact (vec_subst_length D kk z uu (length env_b) Hz_len Hlu)).
  assert (Hv0_len : forall k (u : list (grade D)),
    length u = S (k + length env_b) ->
    length (vec_subst k (vec_zero (length env_b)) u) = k + length env_b) by
    (intros kk uu Hlu; exact (vec_subst_length D kk (vec_zero (length env_b)) uu (length env_b) (vec_zero_length D (length env_b)) Hlu)).
  remember (env_a ++ b :: env_b) as env1 eqn:Henv1.
  revert env_a Henv1 Hsafe.
  induction H using CTypeDemand_ind_mut with
    (P := fun env1 T d _ => forall env_a, env1 = env_a ++ b :: env_b ->
            cenv_tvar_safe env_a (length env_a) ->
            exists d', CTypeDemand (subst_tvar_cenv U z env_a ++ env_b)
                         (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) T) d' /\
                       branch_rel d' (vec_subst (length env_a) z d))
    (P0 := fun env1 fs df _ => forall env_a, env1 = env_a ++ b :: env_b ->
             cenv_tvar_safe env_a (length env_a) ->
             exists df', CRecordFieldDemand (subst_tvar_cenv U z env_a ++ env_b)
                           (map (fun '(fn, fg, ft) => (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft)) fs) df' /\
                         branch_rel df' (vec_subst (length env_a) z df))
    (P1 := fun env1 ls dl _ => forall env_a, env1 = env_a ++ b :: env_b ->
             cenv_tvar_safe env_a (length env_a) ->
             exists dl', CIdxListDemand (subst_tvar_cenv U z env_a ++ env_b)
                           (map (subst_tvar_in_cidx (length env_a)) ls) dl' /\
                         branch_rel dl' (vec_subst (length env_a) z dl));
    intros env_a Henv1 Hsafe; subst env; cbn.
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero;
      [eexists; split; [constructor | rewrite !length_app, subst_tvar_cenv_length; apply branch_rel_refl] | exact Hz_len].
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero;
      [eexists; split; [constructor | rewrite !length_app, subst_tvar_cenv_length; apply branch_rel_refl] | exact Hz_len].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [de' [Hde' Hbre]].
    lazymatch goal with
    | Htd : CTypeDemand _ _ de, Hci : CIdxDemand _ _ dl |- _ =>
        destruct (subst_tvar_idx_demand D U z env_a b env_b lvl_b len dl Hb Hsafe HU Hci) as [dl' [Hdl' Hbrl]];
        pose proof (ctype_demand_length D _ _ _ Htd) as Hlen1;
        pose proof (cidx_demand_length D _ _ _ Hci) as Hlen2;
        rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2;
        exists (vec_add de' dl'); split; [constructor; assumption |];
        rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hz_len | lia | lia]
    end.
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero;
      [eexists; split; [constructor | rewrite !length_app, subst_tvar_cenv_length; apply branch_rel_refl] | exact Hz_len].
  - lazymatch goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt];
        [ destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b x e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [ eapply CTypeTVar; [exact Hl' | rewrite Heq; exact (subst_tvar_in_cty_alpha_eq D (length env_a - S x) _ _ _ _ (cty_alpha_eq_refl D _) Hc)]
          | rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
              [apply branch_rel_refl | exact Hz_len | exact Hlt] ]
        | subst x; repeat (rw_nat_bool; cbv iota);
          destruct (weaken_ctype_demand_app_left D env_b U z HU (subst_tvar_cenv U z env_a)) as [z' [Hz' Hbr]];
          rewrite subst_tvar_cenv_length in Hz', Hbr;
          eexists; split; [exact Hz' |];
          rewrite length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_eq by exact Hz_len;
          rewrite vec_scale_one; exact Hbr
        | destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b x e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hx_len; cbn in Hx_len; repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [ eapply CTypeTVar; [exact Hl' | rewrite Heq; exact Hc]
          | rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
              [apply branch_rel_refl | exact Hz_len | lia | lia] ] ]
    end.
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [di' [Hdi' Hbr]].
    exists (vec_scale q di'); split; [constructor; assumption |].
    rewrite vec_subst_scale; apply branch_rel_scale; exact Hbr.
  - lazymatch goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec b0 (length env_a)) as [[Hlt | Heq_b] | Hgt];
        [ destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b b0 e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [ eapply CTypeTUnbox; [exact Hl' | rewrite Heq; exact (subst_tvar_in_cty_alpha_eq D (length env_a - S b0) _ _ _ _ (cty_alpha_eq_refl D _) Hc)]
          | rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
              [apply branch_rel_refl | exact Hz_len | exact Hlt] ]
        | subst b0;
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia; inversion Hl; reflexivity);
          subst e; exfalso; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; discriminate
        | destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b b0 e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hb_len : b0 < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hb_len; cbn in Hb_len; repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [ eapply CTypeTUnbox; [exact Hl' | rewrite Heq; exact Hc]
          | rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
              [apply branch_rel_refl | exact Hz_len | lia | lia] ] ]
    end.
  - destruct (IHCTypeDemand1 env_a eq_refl Hsafe) as [a' [Ha' Hbra]].
    assert (Hdom_safe : cty_uses_kinds false true false false false false false (length env_a) dom = false).
    { lazymatch goal with
      | Htd1 : CTypeDemand _ dom a |- _ =>
          eapply ctype_demand_uses_kinds; [exact Htd1 | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity |];
          unfold flags_allow; rewrite erase_hints_ren, Hb; reflexivity
      end. }
    destruct (IHCTypeDemand2 ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) eq_refl (cenv_tvar_safe_cons D {| cbinder := x; cannotation := dom; ctype_uses := a |} env_a Hdom_safe Hsafe)) as [b' [Hb' Hbrb]].
    cbn [length] in Hb', Hbrb.
    assert (Hb'' : CTypeDemand ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) dom; ctype_uses := a' |} :: subst_tvar_cenv U z env_a ++ env_b)
                               (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) cod) b').
    { rewrite lift_cty_add. eapply CTypeDemand_alpha_env; [| exact Hb']. constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    pose proof (ctype_demand_length D _ _ _ H) as Hlena.
    pose proof (ctype_demand_length D _ _ _ H0) as Hlenb.
    cbn [length] in Hlena, Hlenb; rewrite length_app in Hlena, Hlenb; cbn [length] in Hlena, Hlenb.
    exists (vec_add a' (tl b')); split;
      [ eapply CTypePi; [exact Ha' | exact Hb'' | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | rewrite vec_subst_nth_lt by lia; assumption]] |].
    rewrite (vec_subst_add D (length env_a) z a (tl b0) (length env_b));
      [apply branch_rel_add; [exact Hbra | rewrite vec_subst_tl; apply branch_rel_tl; exact Hbrb] | exact Hz_len | lia | destruct b0; cbn in *; lia].
  - lazymatch goal with
    | Htd1 : CTypeDemand _ ?ff a,
      Htd2 : CTypeDemand ({| cbinder := x; cannotation := ?ff; ctype_uses := a |} :: _) ?ss ?b_row |- _ =>
      destruct (IHCTypeDemand1 env_a eq_refl Hsafe) as [a' [Ha' Hbra]];
      assert (Hfst_safe : cty_uses_kinds false true false false false false false (length env_a) ff = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd1 | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity |];
         unfold flags_allow; rewrite erase_hints_ren, Hb; reflexivity);
      destruct (IHCTypeDemand2 ({| cbinder := x; cannotation := ff; ctype_uses := a |} :: env_a) eq_refl (cenv_tvar_safe_cons D {| cbinder := x; cannotation := ff; ctype_uses := a |} env_a Hfst_safe Hsafe)) as [b' [Hb' Hbrb]];
      cbn [length] in Hb', Hbrb;
      assert (Hb'' : CTypeDemand ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ff; ctype_uses := a' |} :: subst_tvar_cenv U z env_a ++ env_b)
                                 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) ss) b') by
        (rewrite lift_cty_add; eapply CTypeDemand_alpha_env; [| exact Hb']; constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]);
      pose proof (ctype_demand_length D _ _ _ Htd1) as Hlena;
      pose proof (ctype_demand_length D _ _ _ Htd2) as Hlenb;
      cbn [length] in Hlena, Hlenb; rewrite length_app in Hlena, Hlenb; cbn [length] in Hlena, Hlenb;
      exists (vec_add a' (tl b')); split;
        [ eapply CTypeSigma; [exact Ha' | exact Hb'' | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | rewrite vec_subst_nth_lt by lia; assumption]] |];
      rewrite (vec_subst_add D (length env_a) z a (tl b_row) (length env_b));
        [apply branch_rel_add; [exact Hbra | rewrite vec_subst_tl; apply branch_rel_tl; exact Hbrb] | exact Hz_len | lia | destruct b_row; cbn in *; lia]
    end.
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [d' [Hd' Hbr]]. exists d'; split; [constructor; exact Hd' | exact Hbr].
  - destruct (IHCTypeDemand1 env_a eq_refl Hsafe) as [dl' [Hdl' Hbrl]].
    destruct (IHCTypeDemand2 env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]].
    pose proof (ctype_demand_length D _ _ _ H) as Hlen1.
    pose proof (ctype_demand_length D _ _ _ H0) as Hlen2.
    rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2.
    exists (vec_add dl' dr'); split; [constructor; assumption |].
    rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hz_len | lia | lia].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [df' [Hdf' Hbr]].
    exists df'; split; [constructor; exact Hdf' | exact Hbr].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [dl' [Hdl' Hbr]].
    exists dl'; split; [constructor; exact Hdl' | exact Hbr].
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero;
      [eexists; split; [constructor | rewrite !length_app, subst_tvar_cenv_length; apply branch_rel_refl] | exact Hz_len].
  - lazymatch goal with
    | Htd : CTypeDemand _ ft dt,
      Hfs : CRecordFieldDemand _ rest drest,
      IHft : forall env_a0, _ = env_a0 ++ _ -> _ -> exists dt', CTypeDemand _ _ dt' /\ _,
      IHfs : forall env_a0, _ = env_a0 ++ _ -> _ -> exists dr', CRecordFieldDemand _ _ dr' /\ _ |- _ =>
      destruct (IHft env_a eq_refl Hsafe) as [dt' [Hdt' Hbrt]];
      destruct (IHfs env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]];
      pose proof (ctype_demand_length D _ _ _ Htd) as Hlen1;
      pose proof (crecord_field_demand_length_t D _ _ _ Hfs) as Hlen2;
      rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2;
      exists (vec_add dt' dr'); split; [constructor; assumption |];
      rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hz_len | lia | lia]
    end.
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero;
      [eexists; split; [constructor | rewrite !length_app, subst_tvar_cenv_length; apply branch_rel_refl] | exact Hz_len].
  - lazymatch goal with
    | Hci : CIdxDemand _ ?ii di,
      Hls : CIdxListDemand _ _ drest,
      IHls : forall env_a0, _ = env_a0 ++ _ -> _ -> exists dr', CIdxListDemand _ _ dr' /\ _ |- _ =>
        destruct (subst_tvar_idx_demand D U z env_a b env_b lvl_b ii di Hb Hsafe HU Hci) as [di' [Hdi' Hbri]];
        destruct (IHls env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]];
        pose proof (cidx_demand_length D _ _ _ Hci) as Hlen1;
        pose proof (cidx_list_demand_length D _ _ _ Hls) as Hlen2;
        rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2;
        exists (vec_add di' dr'); split; [constructor; assumption |];
        rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hz_len | lia | lia]
    end.
Qed.

Lemma subst_tvar_cuniverse_level : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b lvl_b T lvl,
  cannotation b = CUniv lvl_b ->
  CUniverseLevel env_b U lvl_b ->
  CUniverseLevel (env_a ++ b :: env_b) T lvl ->
  CUniverseLevel (subst_tvar_cenv U z env_a ++ env_b)
    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) T) lvl.
Proof.
  intros D U z env_a b env_b lvl_b T lvl Hb HU H.
  remember (env_a ++ b :: env_b) as env1 eqn:Eenv.
  revert env_a Eenv.
  induction H using CUniverseLevel_ind_mut with
    (P := fun env1 T lvl _ => forall env_a, env1 = env_a ++ b :: env_b ->
            CUniverseLevel (subst_tvar_cenv U z env_a ++ env_b)
              (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) T) lvl)
    (P0 := fun env1 fs lvl _ => forall env_a, env1 = env_a ++ b :: env_b ->
             CRecordFieldLevel (subst_tvar_cenv U z env_a ++ env_b)
               (map (fun '(fn, fg, ft) => (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft)) fs) lvl);
    intros env_a Eenv; subst env; cbn; try solve [constructor; auto].
  - lazymatch goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt];
        [ destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b x e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eapply CLevelTVar; [exact Hl' | rewrite Heq; exact (subst_tvar_in_cty_alpha_eq D (length env_a - S x) _ _ _ _ (cty_alpha_eq_refl D _) Hc)]
        | subst x; repeat (rw_nat_bool; cbv iota);
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia; inversion Hl; reflexivity);
          subst e; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; inversion Hc; subst lvl_b;
          pose proof (weaken_cuniverse_level_app_left D env_b U lvl HU (subst_tvar_cenv U z env_a)) as Hwk;
          rewrite subst_tvar_cenv_length in Hwk; exact Hwk
        | destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b x e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hx_len; cbn in Hx_len; repeat (rw_nat_bool; cbv iota);
          eapply CLevelTVar; [exact Hl' | rewrite Heq; exact Hc] ]
    end.
  - lazymatch goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec b0 (length env_a)) as [[Hlt | Heq_b] | Hgt];
        [ destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b b0 e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eapply CLevelTUnbox; [exact Hl' | rewrite Heq; exact (subst_tvar_in_cty_alpha_eq D (length env_a - S b0) _ _ _ _ (cty_alpha_eq_refl D _) Hc)]
        | subst b0;
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia; inversion Hl; reflexivity);
          subst e; exfalso; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; discriminate
        | destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b b0 e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hb_len : b0 < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hb_len; cbn in Hb_len; repeat (rw_nat_bool; cbv iota);
          eapply CLevelTUnbox; [exact Hl' | rewrite Heq; exact Hc] ]
    end.
  - eapply CLevelPi; [apply IHCUniverseLevel1; reflexivity |].
    lazymatch type of IHCUniverseLevel2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHCUniverseLevel2 (hd :: env_a) eq_refl);
        cbn [length subst_tvar_cenv] in IHCUniverseLevel2;
        rewrite (lift_cty_add D 1 (length env_a));
        eapply CUniverseLevel_alpha_env; [| exact IHCUniverseLevel2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
  - eapply CLevelSigma; [apply IHCUniverseLevel1; reflexivity |].
    lazymatch type of IHCUniverseLevel2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHCUniverseLevel2 (hd :: env_a) eq_refl);
        cbn [length subst_tvar_cenv] in IHCUniverseLevel2;
        rewrite (lift_cty_add D 1 (length env_a));
        eapply CUniverseLevel_alpha_env; [| exact IHCUniverseLevel2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
Qed.

Lemma subst_tvar_subty : forall (D : JoinDomain) (U : cty D) z env_a (b : cbinding D) env_b A B,
  Subty (env_a ++ b :: env_b) A B ->
  Subty (subst_tvar_cenv U z env_a ++ env_b)
    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A)
    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) B).
Proof.
  intros D U z env_a b env_b A B H.
  remember (env_a ++ b :: env_b) as env1 eqn:Eenv.
  revert env_a Eenv.
  induction H; intros env_a Eenv; subst env; cbn.
  - apply SubRefl. apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact H].
  - apply SubBox; [exact H | apply IHSubty; reflexivity].
  - eapply SubPi; [exact H | exact H0 | apply IHSubty1; reflexivity |].
    lazymatch type of IHSubty2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHSubty2 (hd :: env_a) eq_refl);
        cbn [length subst_tvar_cenv] in IHSubty2;
        rewrite (lift_cty_add D 1 (length env_a));
        eapply Subty_alpha_env; [| exact IHSubty2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
  - eapply SubSigma; [exact H | apply IHSubty1; reflexivity |].
    lazymatch type of IHSubty2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHSubty2 (hd :: env_a) eq_refl);
        cbn [length subst_tvar_cenv] in IHSubty2;
        rewrite (lift_cty_add D 1 (length env_a));
        eapply Subty_alpha_env; [| exact IHSubty2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
  - apply SubSum; [apply IHSubty1 | apply IHSubty2]; reflexivity.
  - apply SubVec; [apply subst_tvar_in_cidx_eqb; exact H | apply IHSubty; reflexivity].
Qed.

Lemma cty_uses_kinds_tvar_lift_n_false : forall (D : JoinDomain) (T : cty D) n k,
  cty_uses_kinds false true false false false false false k T = false ->
  cty_uses_kinds false true false false false false false (n + k) (lift_cty 0 n T) = false.
Proof.
  intros D T n k H. apply cty_uses_kinds_tvar_ren_gen with (k := k); [| exact H].
  intros x Hne. unfold ren_lift. destruct (x <? 0) eqn:Ex; nat_bool_hyps; lia.
Qed.

Lemma cidx_uses_kinds_tvar_lift_drop : forall (D : JoinDomain) (j : cidx D) k c0,
  c0 <= k ->
  cidx_uses_kinds false false false false false (S k) (ren_cidx (ren_lift c0 1) j) = false ->
  cidx_uses_kinds false false false false false k j = false.
Proof.
  intros D j. induction j; intros k c0 Hle Hk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hk as [H1 H2]; rewrite (IHj1 _ _ Hle H1), (IHj2 _ _ Hle H2); reflexivity);
    try (apply (IHj _ _ Hle Hk)).
  - apply Nat.eqb_neq in Hk; unfold ren_lift in Hk; destruct (x <? c0) eqn:Ec; nat_bool_hyps; apply Nat.eqb_neq; lia.
  - apply Nat.eqb_neq in Hk; unfold ren_lift in Hk; destruct (b <? c0) eqn:Ec; nat_bool_hyps; apply Nat.eqb_neq; lia.
  - apply Nat.eqb_neq in Hk; unfold ren_lift in Hk; destruct (p <? c0) eqn:Ec; nat_bool_hyps; apply Nat.eqb_neq; lia.
  - apply Nat.eqb_neq in Hk; unfold ren_lift in Hk; destruct (p <? c0) eqn:Ec; nat_bool_hyps; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Hk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps;
    unfold ren_lift in H1; destruct (s <? c0) eqn:Ec; nat_bool_hyps;
    [ rewrite (proj2 (Nat.eqb_neq s k) ltac:(lia)) | rewrite (proj2 (Nat.eqb_neq s k) ltac:(lia)) ];
    assert (Hsh2 : forall (i0 : cidx D), ren_cidx (ren_shift (ren_lift c0 1)) i0 = ren_cidx (ren_lift (S c0) 1) i0) by
      (intro i0; apply ren_cidx_ext; intros [| m]; unfold ren_shift, ren_lift; cbn; try reflexivity; destruct (m <? c0) eqn:Em; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); reflexivity);
    rewrite !Hsh2 in H2, H3;
    rewrite (IHj1 (S k) (S c0) ltac:(lia) H2), (IHj2 (S k) (S c0) ltac:(lia) H3); reflexivity.
Qed.

Lemma cty_uses_kinds_tvar_lift_drop : forall (D : JoinDomain) (T : cty D) k c0,
  c0 <= k ->
  cty_uses_kinds false true false false false false false (S k) (ren_cty (ren_lift c0 1) T) = false ->
  cty_uses_kinds false true false false false false false k T = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros k c0 Hle Hk; cbn in *; try reflexivity;
    try (apply (IHT _ _ Hle Hk));
    try (apply orb_false_iff in Hk as [H1 H2]; rewrite (IHT1 _ _ Hle H1), (IHT2 _ _ Hle H2); reflexivity).
  - apply orb_false_iff in Hk as [H1 H2].
    rewrite (IHT _ _ Hle H1), (cidx_uses_kinds_tvar_lift_drop D len _ _ Hle H2). reflexivity.
  - apply Nat.eqb_neq in Hk; unfold ren_lift in Hk; destruct (b <? c0) eqn:Ec; nat_bool_hyps; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Hk as [H1 H2].
    assert (Hsh2 : forall (U0 : cty D), ren_cty (ren_shift (ren_lift c0 1)) U0 = ren_cty (ren_lift (S c0) 1) U0) by
      (intro U0; apply ren_cty_ext; intros [| m]; unfold ren_shift, ren_lift; cbn; try reflexivity; destruct (m <? c0) eqn:Em; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); reflexivity).
    rewrite Hsh2 in H2.
    rewrite (IHT1 _ _ Hle H1), (IHT2 (S k) (S c0) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in Hk as [H1 H2].
    assert (Hsh2 : forall (U0 : cty D), ren_cty (ren_shift (ren_lift c0 1)) U0 = ren_cty (ren_lift (S c0) 1) U0) by
      (intro U0; apply ren_cty_ext; intros [| m]; unfold ren_shift, ren_lift; cbn; try reflexivity; destruct (m <? c0) eqn:Em; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); reflexivity).
    rewrite Hsh2 in H2.
    rewrite (IHT1 _ _ Hle H1), (IHT2 (S k) (S c0) ltac:(lia) H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest0 IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hk as [H1 Hk2].
    rewrite (H2 _ _ Hle H1), (IHf H3 Hk2). reflexivity.
  - induction indices as [| idx0 rest0 IH0]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hk as [H1 H2].
    rewrite (cidx_uses_kinds_tvar_lift_drop D idx0 _ _ Hle H1), (IH0 H2). reflexivity.
Qed.

Lemma CRecordExtendEnv_tvar_safe : forall (D : JoinDomain) (b : cbinding D) env_b lvl_b,
  cannotation b = CUniv lvl_b ->
  forall env1 bs fs body_env,
    CRecordExtendEnv env1 bs fs body_env ->
    forall env_a, env1 = env_a ++ b :: env_b ->
      Forall (fun '(_, _, ft) =>
        cty_uses_kinds false true false false false false false (length env_a) ft = false) fs.
Proof.
  intros D b env_b lvl_b Hb env1 bs fs body_env Hext.
  induction Hext; intros env_a Henv; subst; [constructor |].
  constructor.
  - exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ H env_a eq_refl).
  - specialize (IHHext ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a) eq_refl).
    cbn [length] in IHHext.
    clear - IHHext. induction rest as [| [[n0 g0] t0] rs IH]; cbn in *; inversion IHHext; subst; constructor; [| apply IH; exact H2].
    exact (cty_uses_kinds_tvar_lift_drop D t0 (length env_a) 0 ltac:(lia) H1).
Qed.

Lemma record_extend_subst_tvar : forall (D : JoinDomain) (U : cty D) z env_b (b : cbinding D) lvl_b,
  cannotation b = CUniv lvl_b ->
  CTypeDemand env_b U z ->
  forall env1 bs fields body_env env_a fields',
  env1 = env_a ++ b :: env_b ->
  cenv_tvar_safe env_a (length env_a) ->
  CRecordExtendEnv env1 bs fields body_env ->
  Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) =>
    n1 = n2 /\ g1 = g2 /\
    cty_alpha_eq t1 (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) t2)) fields' fields ->
  exists ext_a body_env',
    body_env = ext_a ++ b :: env_b /\
    length ext_a = length fields + length env_a /\
    cenv_tvar_safe ext_a (length ext_a) /\
    CRecordExtendEnv (subst_tvar_cenv U z env_a ++ env_b) bs fields' body_env' /\
    cenv_demand_rel body_env' (subst_tvar_cenv U z ext_a ++ env_b).
Proof.
  intros D U z env_b b lvl_b Hb HU env1 bs fields body_env env_a fields' Henv Hsafe Hext Hfs.
  pose proof (CRecordExtendEnv_tvar_safe D b env_b lvl_b Hb _ _ _ _ Hext env_a Henv) as Htv_fs.
  revert env_a fields' Henv Hsafe Hfs Htv_fs.
  induction Hext; intros env_a fields' Henv Hsafe Hfs Htv_fs; subst env.
  - inversion Hfs; subst.
    exists env_a, (subst_tvar_cenv U z env_a ++ env_b).
    split; [reflexivity | split; [reflexivity | split; [exact Hsafe | split; [constructor | apply cenv_demand_rel_refl]]]].
  - inversion Hfs as [| [[fn1 fg1] ft1] [[fn2 fg2] ft2] fs1' fs2' [Hn [Hg Hft]] Hrest]; subst.
    inversion Htv_fs as [| ? ? Hft_safe Hrest_safe]; subst.
    destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b ft row Hb Hsafe HU H) as [row' [Hrow' Hbr]].
    assert (Hrow1 : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) ft1 row') by
      (eapply CTypeDemand_alpha_ty; [exact Hrow' | apply cty_alpha_eq_sym; exact Hft]).
    assert (Hsafe1 : cenv_tvar_safe ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a) (S (length env_a))) by
      (apply cenv_tvar_safe_cons; [exact Hft_safe | exact Hsafe]).
    assert (Hfs1 : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) =>
      n1 = n2 /\ g1 = g2 /\
      cty_alpha_eq t1 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) t2))
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
    { clear - Hrest Hrest_safe.
      induction Hrest; inversion Hrest_safe; subst; constructor; [| apply IHHrest; exact H3].
      destruct x as [[n1 g1] t1], y as [[n2 g2] t2], H as [-> [-> Ht]].
      split; [reflexivity | split; [reflexivity |]].
      cbn [length] in *.
      eapply cty_alpha_eq_trans; [apply (ren_cty_alpha_eq D (ren_lift 0 1)); exact Ht |].
      replace (lift_cty 0 (S (length env_a)) U) with (lift_cty 0 1 (lift_cty 0 (length env_a) U)) by (rewrite lift_cty_add; reflexivity).
      change (ren_cty (ren_lift 0 1) (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) t2))
        with (lift_cty 0 1 (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) t2)).
      rewrite (subst_tvar_in_cty_lift_ge D t2 (lift_cty 0 (length env_a) U) 0 (length env_a) ltac:(lia) H2).
      apply cty_alpha_eq_refl. }
    assert (Htv_rest : Forall (fun '(_, _, ft0) =>
      cty_uses_kinds false true false false false false false (S (length env_a)) ft0 = false)
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
    { clear - Hrest_safe. induction rest as [| [[n0 g0] t0] rs IH]; inversion Hrest_safe; subst; constructor; [| apply IH; exact H2].
      replace (S (length env_a)) with (1 + length env_a) by lia. apply cty_uses_kinds_tvar_lift_n_false; exact H1. }
    destruct (IHHext ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a)
                (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1') eq_refl Hsafe1 Hfs1 Htv_rest)
      as [ext_a [body_env_0 [Hbody [Hlen_ext [Hsafe_ext [Hext0 Hrel0]]]]]].
    assert (Hfs_id : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2)
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')).
    { clear. induction fs1' as [| [[n0 g0] t0] rs IH]; constructor; [split; [reflexivity | split; [reflexivity | apply cty_alpha_eq_refl]] | exact IH]. }
    assert (Hrel_head : cenv_demand_rel
      ({| cbinder := b0; cannotation := ft1; ctype_uses := row' |} :: subst_tvar_cenv U z env_a ++ env_b)
      (subst_tvar_cenv U z ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a) ++ env_b)).
    { cbn [subst_tvar_cenv app]. apply cenv_demand_rel_cons;
        [apply cenv_demand_rel_refl | exact Hft | exact Hrow1 | exact Hbr]. }
    destruct (record_extend_demand_rel D _ bs _ body_env_0 _ _ Hext0 Hrel_head Hfs_id) as [body_env' [Hext_rest Hrel_rest]].
    exists ext_a, body_env'.
    split; [exact Hbody | split; [rewrite length_map in Hlen_ext; cbn [length] in *; lia | split; [exact Hsafe_ext | split]]].
    + eapply CRecordExtCons; [exact Hrow1 | exact Hext_rest].
    + eapply cenv_demand_rel_trans; [exact Hrel_rest | exact Hrel0].
Qed.

Lemma subst_tvar_in_cty_lift_cancel : forall (D : JoinDomain) (T V : cty D) c,
  subst_tvar_in_cty c V (lift_cty c 1 T) = T.
Proof.
  intros D T V c. unfold lift_cty.
  rewrite (subst_tvar_in_cty_ren_skip_gen D T V c (ren_lift c 1) (fun x => x)).
  - apply ren_cty_id.
  - intro x. unfold ren_lift. destruct (x <? c) eqn:Ex; nat_bool_hyps; [left | right]; lia.
Qed.

Lemma subst_tvar_in_cty_lift_n_comm : forall (D : JoinDomain) n k (T V : cty D),
  cty_uses_kinds false true false false false false false k T = false ->
  lift_cty 0 n (subst_tvar_in_cty k V T) = subst_tvar_in_cty (n + k) (lift_cty 0 n V) (lift_cty 0 n T).
Proof.
  intros D n. induction n as [| n IH]; intros k T V Hk; cbn [Nat.add].
  - rewrite !lift_cty_0_0. reflexivity.
  - replace (lift_cty 0 (S n) (subst_tvar_in_cty k V T))
       with (lift_cty 0 1 (lift_cty 0 n (subst_tvar_in_cty k V T))) by (rewrite lift_cty_add; reflexivity).
    rewrite (IH k T V Hk).
    rewrite (subst_tvar_in_cty_lift_ge D (lift_cty 0 n T) (lift_cty 0 n V) 0 (n + k) ltac:(lia) (cty_uses_kinds_tvar_lift_n_false D T n k Hk)).
    rewrite !lift_cty_add. reflexivity.
Qed.

Lemma cidx_uses_kinds_tvar_unshift_cidx : forall (D : JoinDomain) (i : cidx D) c k,
  c <= k ->
  cidx_uses_var c i = false ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  subst_tvar_in_cidx k (unshift_cidx c i) = unshift_cidx c (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Huv : forall v c k, c <= k -> v <> c -> v <> S k ->
    (let p := if v <? S c then v else v - 1 in
     if p <? k then p else if p =? k then 0 else p - 1) =
    (let s := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if s <? S c then s else s - 1)) by
    (intros v c k Hck Hnc Hne;
     destruct (lt_eq_lt_dec v (S k)) as [[H1 | H1] | H1]; [| contradiction |];
     destruct (lt_eq_lt_dec v c) as [[H2 | H2] | H2]; try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  assert (Hiter : forall c' m,
    Nat.iter c' ren_shift (fun x => match x with 0 => 0 | S x' => x' end) m =
    if m <? S c' then m else m - 1).
  { induction c' as [| c' IHc]; intro m; [destruct m; [reflexivity | cbn; lia] |].
    destruct m; [reflexivity |].
    change (Nat.iter (S c') ren_shift (fun x => match x with 0 => 0 | S x' => x' end) (S m))
      with (S (Nat.iter c' ren_shift (fun x => match x with 0 => 0 | S x' => x' end) m)).
    rewrite IHc; destruct (lt_eq_lt_dec m (S c')) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia. }
  induction i; intros c k Hck Hc Hk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hk as [H1 H2];
         rewrite (IHi1 _ _ Hck Hc1 H1), (IHi2 _ _ Hck Hc2 H2); reflexivity);
    try (f_equal; apply (IHi _ _ Hck Hc Hk));
    nat_bool_hyps; unfold unshift_cidx in *; cbn in *;
    try (rewrite !Hiter; f_equal; apply Huv; assumption).
  - apply orb_false_iff in Hc as [Hc12 Hc3]; apply orb_false_iff in Hc12 as [Hc1 Hc2].
    apply orb_false_iff in Hk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    f_equal.
    + rewrite !Hiter. apply Huv; assumption.
    + change (ren_cidx (ren_shift (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end))) i1)
        with (ren_cidx (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) i1).
      change (ren_cidx (ren_shift (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end))) (subst_tvar_in_cidx (S k) i1))
        with (ren_cidx (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) (subst_tvar_in_cidx (S k) i1)).
      apply (IHi1 (S c) (S k) ltac:(lia) Hc2 H2).
    + change (ren_cidx (ren_shift (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end))) i2)
        with (ren_cidx (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) i2).
      change (ren_cidx (ren_shift (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end))) (subst_tvar_in_cidx (S k) i2))
        with (ren_cidx (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) (subst_tvar_in_cidx (S k) i2)).
      apply (IHi2 (S c) (S k) ltac:(lia) Hc3 H3).
Qed.

Lemma subst_tvar_in_cty_unshift_gen : forall (D : JoinDomain) (T V : cty D) c k,
  c <= k ->
  cty_uses_var c T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  subst_tvar_in_cty k (unshift_cty c (lift_cty 0 1 V)) (unshift_cty c T) =
  unshift_cty c (subst_tvar_in_cty (S k) (lift_cty 0 1 V) T).
Proof.
  assert (Hiter : forall c' m,
    Nat.iter c' ren_shift (fun x => match x with 0 => 0 | S x' => x' end) m =
    if m <? S c' then m else m - 1).
  { induction c' as [| c' IHc]; intro m; [destruct m; [reflexivity | cbn; lia] |].
    destruct m; [reflexivity |].
    change (Nat.iter (S c') ren_shift (fun x => match x with 0 => 0 | S x' => x' end) (S m))
      with (S (Nat.iter c' ren_shift (fun x => match x with 0 => 0 | S x' => x' end) m)).
    rewrite IHc; destruct (lt_eq_lt_dec m (S c')) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia. }
  assert (Huv : forall v c k, c <= k -> v <> c -> v <> S k ->
    (let p := if v <? S c then v else v - 1 in
     if p <? k then p else if p =? k then 0 else p - 1) =
    (let s := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if s <? S c then s else s - 1)) by
    (intros v c k Hck Hnc Hne;
     destruct (lt_eq_lt_dec v (S k)) as [[H1 | H1] | H1]; [| contradiction |];
     destruct (lt_eq_lt_dec v c) as [[H2 | H2] | H2]; try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  intros D T. induction T using cty_ind_nested; intros V c k Hck Hu Hk; cbn in *; try reflexivity;
    try (f_equal; apply IHT; assumption);
    try (apply orb_false_iff in Hu as [Hu1 Hu2]; apply orb_false_iff in Hk as [Hk1 Hk2];
         f_equal; [apply IHT1 | apply IHT2]; assumption).
  - apply orb_false_iff in Hu as [Hu1 Hu2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    f_equal; [apply IHT; assumption | apply cidx_uses_kinds_tvar_unshift_cidx; assumption].
  - unfold unshift_cty; cbn; rewrite !Hiter. nat_bool_hyps.
    destruct (lt_eq_lt_dec x (S k)) as [[Hlt | ->] | Hgt].
    + destruct (lt_eq_lt_dec x c) as [[? | ->] | ?]; [| contradiction |].
      * rewrite (proj2 (Nat.ltb_lt x (S c)) ltac:(lia)), (proj2 (Nat.eqb_neq x (S k)) ltac:(lia)), (proj2 (Nat.ltb_lt x (S k)) ltac:(lia)).
        cbn. rewrite !Hiter, (proj2 (Nat.eqb_neq x k) ltac:(lia)), (proj2 (Nat.ltb_lt x k) ltac:(lia)),
                     (proj2 (Nat.ltb_lt x (S c)) ltac:(lia)). reflexivity.
      * rewrite (proj2 (Nat.ltb_ge x (S c)) ltac:(lia)), (proj2 (Nat.eqb_neq x (S k)) ltac:(lia)), (proj2 (Nat.ltb_lt x (S k)) ltac:(lia)).
        cbn. rewrite !Hiter, (proj2 (Nat.eqb_neq (x - 1) k) ltac:(lia)), (proj2 (Nat.ltb_lt (x - 1) k) ltac:(lia)),
                     (proj2 (Nat.ltb_ge x (S c)) ltac:(lia)). reflexivity.
    + rewrite (proj2 (Nat.ltb_ge (S k) (S c)) ltac:(lia)). replace (S k - 1) with k by lia.
      cbn. rewrite !Nat.eqb_refl. reflexivity.
    + rewrite (proj2 (Nat.ltb_ge x (S c)) ltac:(lia)), (proj2 (Nat.eqb_neq x (S k)) ltac:(lia)), (proj2 (Nat.ltb_ge x (S k)) ltac:(lia)).
      cbn. rewrite !Hiter, (proj2 (Nat.eqb_neq (x - 1) k) ltac:(lia)), (proj2 (Nat.ltb_ge (x - 1) k) ltac:(lia)), (proj2 (Nat.ltb_ge (x - 1) (S c)) ltac:(lia)).
      f_equal; lia.
  - unfold unshift_cty; cbn; rewrite !Hiter. nat_bool_hyps. f_equal. apply Huv; assumption.
  - apply orb_false_iff in Hu as [Hu1 Hu2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    f_equal; [apply IHT1; assumption |].
    unfold unshift_cty in *. cbn [ren_cty].
    change (ren_shift (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end)))
      with (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)).
    pose proof (IHT2 (lift_cty 0 1 V) (S c) (S k) ltac:(lia) Hu2 Hk2) as Hrec.
    (* Check unshift (S c) (lift 0 1 (lift 0 1 V)) vs lift 0 1 (unshift c (lift 0 1 V)) *)
    assert (Hul : ren_cty (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) (lift_cty 0 1 (lift_cty 0 1 V)) =
                  lift_cty 0 1 (ren_cty (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) (lift_cty 0 1 V))).
    { unfold lift_cty. rewrite !ren_cty_comp. apply ren_cty_ext; intro y.
      rewrite !Hiter. unfold ren_lift; destruct (lt_eq_lt_dec y c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia. }
    rewrite Hul in Hrec. exact Hrec.
  - apply orb_false_iff in Hu as [Hu1 Hu2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    f_equal; [apply IHT1; assumption |].
    unfold unshift_cty in *. cbn [ren_cty].
    change (ren_shift (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end)))
      with (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)).
    pose proof (IHT2 (lift_cty 0 1 V) (S c) (S k) ltac:(lia) Hu2 Hk2) as Hrec.
    assert (Hul : ren_cty (Nat.iter (S c) ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) (lift_cty 0 1 (lift_cty 0 1 V)) =
                  lift_cty 0 1 (ren_cty (Nat.iter c ren_shift (fun x => match x with 0 => 0 | S x' => x' end)) (lift_cty 0 1 V))).
    { unfold lift_cty. rewrite !ren_cty_comp. apply ren_cty_ext; intro y.
      rewrite !Hiter. unfold ren_lift; destruct (lt_eq_lt_dec y c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia. }
    rewrite Hul in Hrec. exact Hrec.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [Hu1 Hu2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    f_equal; [f_equal; apply (H2 _ _ _ Hck Hu1 Hk1) | apply (IHf H3 Hu2 Hk2)].
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hu as [Hu1 Hu2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    f_equal; [apply cidx_uses_kinds_tvar_unshift_cidx; assumption | apply (IH Hu2 Hk2)].
Qed.

Lemma subst_tvar_in_cty_unshift_0 : forall (D : JoinDomain) (T V : cty D) k,
  cty_uses_var 0 T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  subst_tvar_in_cty k V (unshift_cty 0 T) = unshift_cty 0 (subst_tvar_in_cty (S k) (lift_cty 0 1 V) T).
Proof.
  intros D T V k Hu Hk.
  pose proof (subst_tvar_in_cty_unshift_gen D T V 0 k ltac:(lia) Hu Hk) as H.
  replace (unshift_cty 0 (lift_cty 0 1 V)) with V in H; [exact H |].
  unfold unshift_cty, lift_cty. rewrite ren_cty_comp. symmetry.
  transitivity (ren_cty (fun x => x) V); [apply ren_cty_ext; intro y; unfold ren_lift; destruct y; cbn; lia | apply ren_cty_id].
Qed.

Lemma subst_tvar_in_cidx_comm : forall (D : JoinDomain) (i : cidx D) c k,
  c <= k ->
  cidx_uses_kinds false false false false false c i = false ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  subst_tvar_in_cidx k (subst_tvar_in_cidx c i) = subst_tvar_in_cidx c (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Hvc : forall v c k, c <= k -> v <> c -> v <> S k ->
    (let a := if v <? c then v else if v =? c then 0 else v - 1 in
     if a <? k then a else if a =? k then 0 else a - 1) =
    (let b := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if b <? c then b else if b =? c then 0 else b - 1)) by
    (intros v c k Hck Hc Hsk; destruct (lt_eq_lt_dec v c) as [[H1 | H1] | H1]; [| contradiction |];
     (destruct (lt_eq_lt_dec v (S k)) as [[H2 | H2] | H2]; [| contradiction |]); cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros c k Hck Hc Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
         rewrite (IHi1 _ _ Hck Hc1 Hk1), (IHi2 _ _ Hck Hc2 Hk2); reflexivity);
    try (f_equal; apply (IHi _ _ Hck Hc Hsk));
    nat_bool_hyps; try (f_equal; apply Hvc; assumption).
  - apply orb_false_iff in Hc as [Hc12 Hc3]; apply orb_false_iff in Hc12 as [Hc1 Hc2].
    apply orb_false_iff in Hsk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2].
    nat_bool_hyps.
    f_equal; [apply Hvc; assumption | apply (IHi1 (S c) (S k) ltac:(lia) Hc2 Hk2) | apply (IHi2 (S c) (S k) ltac:(lia) Hc3 Hk3)].
Qed.

Lemma subst_tvar_in_cty_subst_tvar_0 : forall (D : JoinDomain) (T W V : cty D) k,
  cty_uses_kinds false true false false false false false 0 T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k W = false ->
  subst_tvar_in_cty k V (subst_tvar_in_cty 0 W T) =
  subst_tvar_in_cty 0 (subst_tvar_in_cty k V W) (subst_tvar_in_cty (S k) (lift_cty 0 1 V) T).
Proof.
  assert (Hgen : forall (D : JoinDomain) (T W V : cty D) c k,
    cty_uses_kinds false true false false false false false c T = false ->
    cty_uses_kinds false true false false false false false (S (c + k)) T = false ->
    cty_uses_kinds false true false false false false false (c + k) W = false ->
    subst_tvar_in_cty (c + k) (lift_cty 0 c V) (subst_tvar_in_cty c W T) =
    subst_tvar_in_cty c (subst_tvar_in_cty (c + k) (lift_cty 0 c V) W) (subst_tvar_in_cty (S (c + k)) (lift_cty 0 (S c) V) T)).
  { intros D T. induction T using cty_ind_nested; intros W V c k Hc Hsk HW; cbn in *; try reflexivity;
      try (f_equal; apply IHT; assumption);
      try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
           f_equal; [apply IHT1 | apply IHT2]; assumption).
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply IHT; assumption | apply subst_tvar_in_cidx_comm; [lia | assumption | assumption]].
    - destruct (Nat.eq_dec x c) as [-> | Hne_c].
      + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S (c + k))) ltac:(lia)), (proj2 (Nat.eqb_neq c (S (c + k))) ltac:(lia)).
        cbn. rewrite Nat.eqb_refl. reflexivity.
      + destruct (Nat.eq_dec x (S (c + k))) as [-> | Hne_sk].
        * rewrite (proj2 (Nat.eqb_neq (S (c + k)) c) Hne_c), (proj2 (Nat.ltb_ge (S (c + k)) c) ltac:(lia)), Nat.eqb_refl.
          replace (S (c + k) - 1) with (c + k) by lia. cbn. rewrite Nat.eqb_refl.
          replace (lift_cty 0 (S c) V) with (lift_cty c 1 (lift_cty 0 c V)) by
            (unfold lift_cty; rewrite ren_cty_comp; apply ren_cty_ext; intro y; unfold ren_lift; repeat (rw_nat_bool; cbv iota); lia).
          rewrite subst_tvar_in_cty_lift_cancel. reflexivity.
        * destruct (lt_eq_lt_dec x c) as [[Hxc | ?] | Hxc]; [| contradiction |];
            destruct (lt_eq_lt_dec x (S (c + k))) as [[Hxk | ?] | Hxk]; [| contradiction | | | contradiction |];
            cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
    - nat_bool_hyps. f_equal.
      destruct (lt_eq_lt_dec b c) as [[Hbc | ?] | Hbc]; [| contradiction |];
        destruct (lt_eq_lt_dec b (S (c + k))) as [[Hbk | ?] | Hbk]; [| contradiction | | | contradiction |];
        repeat (rw_nat_bool; cbv iota); lia.
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply IHT1; assumption |].
      assert (HW1 : cty_uses_kinds false true false false false false false (S c + k) (lift_cty 0 1 W) = false) by
        (replace (S c + k) with (1 + (c + k)) by lia; apply cty_uses_kinds_tvar_lift_n_false; exact HW).
      pose proof (IHT2 (lift_cty 0 1 W) V (S c) k Hc2 Hk2 HW1) as Hrec.
      cbn [Nat.add] in Hrec.
      replace (lift_cty 0 (S c) V) with (lift_cty 0 1 (lift_cty 0 c V)) in Hrec by (rewrite lift_cty_add; reflexivity).
      rewrite <- (subst_tvar_in_cty_lift_ge D W (lift_cty 0 c V) 0 (c + k) ltac:(lia) HW) in Hrec.
      rewrite (lift_cty_add D 1 c V) in Hrec.
      rewrite (lift_cty_add D 1 c V), (lift_cty_add D 1 (S c) V). cbn [Nat.add] in Hrec |- *. exact Hrec.
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply IHT1; assumption |].
      assert (HW1 : cty_uses_kinds false true false false false false false (S c + k) (lift_cty 0 1 W) = false) by
        (replace (S c + k) with (1 + (c + k)) by lia; apply cty_uses_kinds_tvar_lift_n_false; exact HW).
      pose proof (IHT2 (lift_cty 0 1 W) V (S c) k Hc2 Hk2 HW1) as Hrec.
      cbn [Nat.add] in Hrec.
      replace (lift_cty 0 (S c) V) with (lift_cty 0 1 (lift_cty 0 c V)) in Hrec by (rewrite lift_cty_add; reflexivity).
      rewrite <- (subst_tvar_in_cty_lift_ge D W (lift_cty 0 c V) 0 (c + k) ltac:(lia) HW) in Hrec.
      rewrite (lift_cty_add D 1 c V) in Hrec.
      rewrite (lift_cty_add D 1 c V), (lift_cty_add D 1 (S c) V). cbn [Nat.add] in Hrec |- *. exact Hrec.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [f_equal; apply (H2 _ _ _ _ Hc1 Hk1 HW) | apply (IHf H3 Hc2 Hk2)].
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply subst_tvar_in_cidx_comm; [lia | assumption | assumption] | apply (IH Hc2 Hk2)]. }
  intros D T W V k H0 Hsk HW.
  pose proof (Hgen D T W V 0 k H0 Hsk HW) as H.
  cbn [Nat.add] in H. rewrite lift_cty_0_0 in H. exact H.
Qed.

Lemma subst_tvar_in_cidx_subst_cidx : forall (D : JoinDomain) (i val : cidx D) c k,
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false (c + k) val = false ->
  subst_tvar_in_cidx (c + k) (subst_cidx c val i) =
  subst_cidx c (subst_tvar_in_cidx (c + k) val) (subst_tvar_in_cidx (S (c + k)) i).
Proof.
  intros D i.
  assert (Hvc : forall v c k, v <> S (c + k) ->
    (let a := if v <? c then v else if v =? c then 0 else v - 1 in
     if a <? c + k then a else if a =? c + k then 0 else a - 1) =
    (let b := if v <? S (c + k) then v else if v =? S (c + k) then 0 else v - 1 in
     if b <? c then b else if b =? c then 0 else b - 1)) by
    (intros v c k Hne; destruct (lt_eq_lt_dec v c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec v (S (c + k))) as [[? | ?] | ?]; destruct (Nat.eq_dec (c + k) 0); try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros val c k Hsk Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [Hk1 Hk2];
         rewrite (IHi1 _ _ _ Hk1 Hval), (IHi2 _ _ _ Hk2 Hval); reflexivity);
    try (f_equal; apply (IHi _ _ _ Hsk Hval));
    nat_bool_hyps.
  - destruct (Nat.eq_dec x c) as [-> | Hne].
    + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S (c + k))) ltac:(lia)).
      cbn. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eq_dec x (S (c + k))) as [-> | Hne2].
      * exfalso; lia.
      * destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; [| contradiction |];
          destruct (lt_eq_lt_dec x (S (c + k))) as [[? | ?] | ?]; [| contradiction | | | contradiction |];
          cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
  - f_equal. apply Hvc; assumption.
  - f_equal. apply Hvc; assumption.
  - f_equal. apply Hvc; assumption.
  - apply orb_false_iff in Hsk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2].
    nat_bool_hyps.
    assert (Hval1 : cidx_uses_kinds false false false false false (S c + k) (lift_cidx 0 1 val) = false) by
      (eapply cidx_uses_kinds_ren_tvar_gen; [| exact Hval]; intros y Hy; unfold ren_lift; repeat (rw_nat_bool; cbv iota); lia).
    pose proof (IHi1 (lift_cidx 0 1 val) (S c) k Hk2 Hval1) as H1r.
    pose proof (IHi2 (lift_cidx 0 1 val) (S c) k Hk3 Hval1) as H2r.
    cbn [Nat.add] in H1r, H2r.
    rewrite <- (subst_tvar_in_cidx_lift_ge D val 0 (c + k) ltac:(lia) Hval) in H1r, H2r.
    f_equal; [apply Hvc; assumption | exact H1r | exact H2r].
Qed.

Lemma subst_cidx_in_cty_lift_cancel : forall (D : JoinDomain) (T : cty D) (val : cidx D) c,
  subst_cidx_in_cty c val (lift_cty c 1 T) = T.
Proof.
  intros D T val c. unfold lift_cty.
  rewrite (subst_cidx_in_cty_ren_skip_gen D T val c (ren_lift c 1) (fun x => x)).
  - apply ren_cty_id.
  - intro x. unfold ren_lift. destruct (x <? c) eqn:Ex; nat_bool_hyps; [left | right]; lia.
Qed.

Lemma subst_tvar_in_cty_subst_cidx_0 : forall (D : JoinDomain) (T V : cty D) (val : cidx D) k,
  cty_uses_kinds true false true true true true true 0 T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cidx_uses_kinds false false false false false k val = false ->
  subst_tvar_in_cty k V (subst_cidx_in_cty 0 val T) =
  subst_cidx_in_cty 0 (subst_tvar_in_cidx k val) (subst_tvar_in_cty (S k) (lift_cty 0 1 V) T).
Proof.
  assert (Hgen : forall (D : JoinDomain) (T V : cty D) (val : cidx D) c k,
    cty_uses_kinds true false true true true true true c T = false ->
    cty_uses_kinds false true false false false false false (S (c + k)) T = false ->
    cidx_uses_kinds false false false false false (c + k) val = false ->
    subst_tvar_in_cty (c + k) (lift_cty 0 c V) (subst_cidx_in_cty c val T) =
    subst_cidx_in_cty c (subst_tvar_in_cidx (c + k) val) (subst_tvar_in_cty (S (c + k)) (lift_cty 0 (S c) V) T)).
  { intros D T. induction T using cty_ind_nested; intros V val c k Hc Hsk Hval; cbn in *; try reflexivity;
      try (f_equal; apply IHT; assumption);
      try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
           f_equal; [apply IHT1 | apply IHT2]; assumption).
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply IHT; assumption | apply subst_tvar_in_cidx_subst_cidx; assumption].
    - nat_bool_hyps.
      destruct (Nat.eq_dec x (S (c + k))) as [-> | Hne_sk].
      + rewrite (proj2 (Nat.ltb_ge (S (c + k)) c) ltac:(lia)), (proj2 (Nat.eqb_neq (S (c + k)) c) ltac:(lia)), Nat.eqb_refl.
        replace (S (c + k) - 1) with (c + k) by lia. cbn. rewrite Nat.eqb_refl.
        replace (lift_cty 0 (S c) V) with (lift_cty c 1 (lift_cty 0 c V)) by
          (unfold lift_cty; rewrite ren_cty_comp; apply ren_cty_ext; intro y; unfold ren_lift; repeat (rw_nat_bool; cbv iota); lia).
        rewrite subst_cidx_in_cty_lift_cancel. reflexivity.
      + destruct (lt_eq_lt_dec x c) as [[Hxc | ?] | Hxc]; [| contradiction |];
          destruct (lt_eq_lt_dec x (S (c + k))) as [[Hxk | ?] | Hxk];
          try contradiction; destruct (Nat.eq_dec (c + k) 0);
          cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
    - nat_bool_hyps. f_equal.
      destruct (lt_eq_lt_dec b c) as [[Hbc | Heqc] | Hbc];
        destruct (lt_eq_lt_dec b (S (c + k))) as [[Hbk | ?] | Hbk];
        try contradiction; try subst b; destruct (Nat.eq_dec (c + k) 0);
        repeat (rw_nat_bool; cbv iota); lia.
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply IHT1; assumption |].
      assert (Hval1 : cidx_uses_kinds false false false false false (S c + k) (lift_cidx 0 1 val) = false) by
        (eapply cidx_uses_kinds_ren_tvar_gen; [| exact Hval]; intros y Hy; unfold ren_lift; repeat (rw_nat_bool; cbv iota); lia).
      pose proof (IHT2 V (lift_cidx 0 1 val) (S c) k Hc2 Hk2 Hval1) as Hrec.
      cbn [Nat.add] in Hrec.
      rewrite <- (subst_tvar_in_cidx_lift_ge D val 0 (c + k) ltac:(lia) Hval) in Hrec.
      rewrite (lift_cty_add D 1 c V), (lift_cty_add D 1 (S c) V).
      cbn [Nat.add] in Hrec |- *. exact Hrec.
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply IHT1; assumption |].
      assert (Hval1 : cidx_uses_kinds false false false false false (S c + k) (lift_cidx 0 1 val) = false) by
        (eapply cidx_uses_kinds_ren_tvar_gen; [| exact Hval]; intros y Hy; unfold ren_lift; repeat (rw_nat_bool; cbv iota); lia).
      pose proof (IHT2 V (lift_cidx 0 1 val) (S c) k Hc2 Hk2 Hval1) as Hrec.
      cbn [Nat.add] in Hrec.
      rewrite <- (subst_tvar_in_cidx_lift_ge D val 0 (c + k) ltac:(lia) Hval) in Hrec.
      rewrite (lift_cty_add D 1 c V), (lift_cty_add D 1 (S c) V).
      cbn [Nat.add] in Hrec |- *. exact Hrec.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [f_equal; apply (H2 _ _ _ _ Hc1 Hk1 Hval) | apply (IHf H3 Hc2 Hk2)].
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      f_equal; [apply subst_tvar_in_cidx_subst_cidx; assumption | apply (IH Hc2 Hk2)]. }
  intros D T V val k H0 Hsk Hval.
  pose proof (Hgen D T V val 0 k H0 Hsk Hval) as H.
  cbn [Nat.add] in H. rewrite lift_cty_0_0 in H. exact H.
Qed.

Lemma cty_uses_var_ren_avoid : forall (D : JoinDomain) (T : cty D) rn c,
  (forall x, rn x <> c) ->
  cty_uses_var c (ren_cty rn T) = false.
Proof.
  assert (Hi : forall (D : JoinDomain) (i : cidx D) rn c, (forall x, rn x <> c) -> cidx_uses_var c (ren_cidx rn i) = false).
  { intros D i. induction i; intros rn c Hr; cbn; try reflexivity;
      try (rewrite (IHi1 _ _ Hr), (IHi2 _ _ Hr); reflexivity);
      try (apply IHi; exact Hr);
      try (apply Nat.eqb_neq, Hr).
    rewrite (proj2 (Nat.eqb_neq (rn s) c) (Hr s)).
    assert (Hrs : forall x, ren_shift rn x <> S c) by (intros [| x']; cbn; [lia | pose proof (Hr x'); lia]).
    rewrite (IHi1 _ _ Hrs), (IHi2 _ _ Hrs). reflexivity. }
  intros D T. induction T using cty_ind_nested; intros rn c Hr; cbn; try reflexivity;
    try (apply IHT; exact Hr);
    try (rewrite (IHT1 _ _ Hr), (IHT2 _ _ Hr); reflexivity).
  - rewrite (IHT _ _ Hr), (Hi D len _ _ Hr). reflexivity.
  - apply Nat.eqb_neq, Hr.
  - apply Nat.eqb_neq, Hr.
  - assert (Hrs : forall x, ren_shift rn x <> S c) by (intros [| x']; cbn; [lia | pose proof (Hr x'); lia]).
    rewrite (IHT1 _ _ Hr), (IHT2 _ _ Hrs). reflexivity.
  - assert (Hrs : forall x, ren_shift rn x <> S c) by (intros [| x']; cbn; [lia | pose proof (Hr x'); lia]).
    rewrite (IHT1 _ _ Hr), (IHT2 _ _ Hrs). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ Hr), (IHf H3). reflexivity.
  - induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite (Hi D idx _ _ Hr), IH. reflexivity.
Qed.

Lemma subst_tvar_in_cty_uses_var_0 : forall (D : JoinDomain) (T V : cty D) k,
  cty_uses_var 0 T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_var 0 (subst_tvar_in_cty (S k) (lift_cty 0 1 V) T) = false.
Proof.
  assert (Hgen : forall (D : JoinDomain) (T V : cty D) c k,
    c <= k ->
    cty_uses_var c T = false ->
    cty_uses_kinds false true false false false false false (S k) T = false ->
    cty_uses_var c (subst_tvar_in_cty (S k) (lift_cty 0 (S c) V) T) = false).
  { assert (Hci : forall (D : JoinDomain) (i : cidx D) c k,
      c <= k -> cidx_uses_var c i = false ->
      cidx_uses_kinds false false false false false (S k) i = false ->
      cidx_uses_var c (subst_tvar_in_cidx (S k) i) = false).
    { intros D i. induction i; intros c k Hck Hi Hsk; cbn in *; try reflexivity;
        try (apply orb_false_iff in Hi as [H1 H2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
             rewrite (IHi1 _ _ Hck H1 Hk1), (IHi2 _ _ Hck H2 Hk2); reflexivity);
        try (apply (IHi _ _ Hck Hi Hsk));
        nat_bool_hyps.
      - destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; [| contradiction |];
          repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia).
      - destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; [| contradiction |];
          repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia).
      - destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; [| contradiction |];
          repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia).
      - destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; [| contradiction |];
          repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia).
      - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2];
          apply orb_false_iff in Hsk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2];
          nat_bool_hyps.
        assert (Hs : ((if s <? S k then s else if s =? S k then 0 else s - 1) =? c) = false) by
          (destruct (lt_eq_lt_dec s (S k)) as [[? | ?] | ?]; [| contradiction |];
           repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia)).
        rewrite Hs, (IHi1 (S c) (S k) ltac:(lia) H2 Hk2), (IHi2 (S c) (S k) ltac:(lia) H3 Hk3). reflexivity. }
    intros D T. induction T using cty_ind_nested; intros V c k Hck HT Hsk; cbn in *; try reflexivity;
      try (apply (IHT _ _ _ Hck HT Hsk));
      try (apply orb_false_iff in HT as [H1 H2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT1 _ _ _ Hck H1 Hk1), (IHT2 _ _ _ Hck H2 Hk2); reflexivity).
    - apply orb_false_iff in HT as [H1 H2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT _ _ _ Hck H1 Hk1), (Hci D len _ _ Hck H2 Hk2). reflexivity.
    - nat_bool_hyps. destruct (Nat.eq_dec x (S k)) as [-> | Hne].
      + rewrite Nat.eqb_refl. apply cty_uses_var_ren_avoid. intro y; unfold ren_lift; repeat (rw_nat_bool; cbv iota); lia.
      + destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; [| contradiction |];
          repeat (rw_nat_bool; cbv iota); cbn; reflexivity || (apply Nat.eqb_neq; lia).
    - nat_bool_hyps. destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia).
    - apply orb_false_iff in HT as [H1 H2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT1 _ _ _ Hck H1 Hk1).
      rewrite (lift_cty_add D 1 (S c) V). exact (IHT2 V (S c) (S k) ltac:(lia) H2 Hk2).
    - apply orb_false_iff in HT as [H1 H2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT1 _ _ _ Hck H1 Hk1).
      rewrite (lift_cty_add D 1 (S c) V). exact (IHT2 V (S c) (S k) ltac:(lia) H2 Hk2).
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2]; apply orb_false_iff in Hsk as [Hk1 Hsk2].
      rewrite (H2 _ _ _ Hck H1 Hk1), (IHf H3 HT2 Hsk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT as [H1 HT2]; apply orb_false_iff in Hsk as [Hk1 Hsk2].
      rewrite (Hci D idx _ _ Hck H1 Hk1), (IH HT2 Hsk2). reflexivity. }
  intros D T V k HT Hsk. exact (Hgen D T V 0 k ltac:(lia) HT Hsk).
Qed.

Lemma subst_tvar_in_cidx_spec_pair_body : forall (D : JoinDomain) (i : cidx D) c k,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  subst_tvar_in_cidx (S (S k)) (spec_pair_body_cidx c i) =
  spec_pair_body_cidx c (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Hv_pair : forall v c k, c <= k -> v <> S k ->
    (let p := if v <? c then v else S v in
     if p <? S (S k) then p else if p =? S (S k) then 0 else p - 1) =
    (let q := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if q <? c then q else S q)) by
    (intros v c k Hck Hsk; destruct (lt_eq_lt_dec v c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec v (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros c k Hck Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [Hk1 Hk2];
         rewrite (IHi1 _ _ Hck Hk1), (IHi2 _ _ Hck Hk2); reflexivity);
    try (f_equal; apply (IHi _ _ Hck Hsk));
    nat_bool_hyps.
  - f_equal. apply Hv_pair; assumption.
  - f_equal. apply Hv_pair; assumption.
  - destruct (Nat.eq_dec p c) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn.
      rewrite (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl.
      destruct (Nat.leb_spec c k); [reflexivity | lia].
    + rw_nat_bool. cbn.
      destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Nat.eq_dec p c) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn.
      rewrite (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), (proj2 (Nat.ltb_lt c (S (S k))) ltac:(lia)), Nat.eqb_refl.
      destruct (Nat.leb_spec c k); [reflexivity | lia].
    + rw_nat_bool. cbn.
      destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite (Hv_pair s c k Hck H1), (IHi1 (S c) (S k) ltac:(lia) H2), (IHi2 (S c) (S k) ltac:(lia) H3).
  reflexivity.
Qed.

Lemma ren_shift_lift_S_cidx : forall (D : JoinDomain) c0 m (i : cidx D),
  ren_cidx (ren_shift (ren_lift c0 m)) i = lift_cidx (S c0) m i.
Proof.
  intros D c0 m i. apply ren_cidx_ext. intros [| x]; unfold ren_shift, ren_lift;
    [destruct (Nat.ltb_spec 0 (S c0)); repeat (rw_nat_bool; cbv iota); lia |].
  destruct (Nat.ltb_spec x c0); repeat (rw_nat_bool; cbv iota); lia.
Qed.

Lemma ren_shift_lift_S_cty : forall (D : JoinDomain) c0 m (T : cty D),
  ren_cty (ren_shift (ren_lift c0 m)) T = lift_cty (S c0) m T.
Proof.
  intros D c0 m T. apply ren_cty_ext. intros [| x]; unfold ren_shift, ren_lift;
    [destruct (Nat.ltb_spec 0 (S c0)); repeat (rw_nat_bool; cbv iota); lia |].
  destruct (Nat.ltb_spec x c0); repeat (rw_nat_bool; cbv iota); lia.
Qed.

Lemma spec_pair_body_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) c c0 m,
  c0 <= c -> c < c0 + m ->
  spec_pair_body_cidx c (lift_cidx c0 m i) = lift_cidx c0 (S m) i.
Proof.
  intros D i. induction i; intros c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ _ _ Hle Hlt), (IHi2 _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ _ _ Hle Hlt); reflexivity).
  - f_equal. unfold ren_lift. destruct (lt_eq_lt_dec x c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia.
  - f_equal. unfold ren_lift. destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia.
  - unfold ren_lift. destruct (lt_eq_lt_dec p c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); try (f_equal; lia).
  - unfold ren_lift. destruct (lt_eq_lt_dec p c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); try (f_equal; lia).
  - rewrite !ren_shift_lift_S_cidx. unfold ren_lift. destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHi1 (S c) (S c0) m ltac:(lia) ltac:(lia)), (IHi2 (S c) (S c0) m ltac:(lia) ltac:(lia)); f_equal; lia.
Qed.

Ltac fold_lift_cidx :=
  repeat match goal with
  | |- context [ren_cidx (ren_lift ?a ?b) ?x] => change (ren_cidx (ren_lift a b) x) with (lift_cidx a b x)
  end.

Lemma spec_pair_body_cty_lift_above : forall (D : JoinDomain) (T : cty D) c c0 m,
  c0 <= c -> c < c0 + m ->
  spec_pair_body_cty c (lift_cty c0 m T) = lift_cty c0 (S m) T.
Proof.
  intros D T. induction T using cty_ind_nested; intros c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ _ _ Hle Hlt), (IHT2 _ _ _ Hle Hlt); reflexivity).
  - fold_lift_cidx. rewrite (IHT _ _ _ Hle Hlt), (spec_pair_body_cidx_lift_above D len _ _ _ Hle Hlt). reflexivity.
  - f_equal. unfold ren_lift. destruct (lt_eq_lt_dec x c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia.
  - f_equal. unfold ren_lift. destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia.
  - rewrite (IHT1 _ _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (spec_pair_body_cidx_lift_above D idx _ _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_spec_pair_body : forall (D : JoinDomain) (T U : cty D) c k,
  c <= k ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  subst_tvar_in_cty (S (S k)) (lift_cty 0 (S (S k)) U) (spec_pair_body_cty c T) =
  spec_pair_body_cty c (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U c k Hck HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hck HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ _ _ Hck H1), (IHT2 _ _ _ Hck H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ Hck H1), (subst_tvar_in_cidx_spec_pair_body D len _ _ Hck H2). reflexivity.
  - destruct (lt_eq_lt_dec x c) as [[? | ?] | ?];
      destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
      try (cbn; repeat (rw_nat_bool; cbv iota)); try (f_equal; lia).
    + subst x. rewrite (spec_pair_body_cty_lift_above D U c 0 (S k) ltac:(lia) ltac:(lia)). reflexivity.
  - nat_bool_hyps.
    destruct (lt_eq_lt_dec b c) as [[? | ?] | ?];
      destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); try (f_equal; lia).
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ _ Hck H1).
    rewrite (lift_cty_add D 1 (S (S k)) U), (lift_cty_add D 1 (S k) U).
    replace (1 + S (S k)) with (S (S (S k))) by lia.
    replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ (S c) (S k) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ _ Hck H1).
    rewrite (lift_cty_add D 1 (S (S k)) U), (lift_cty_add D 1 (S k) U).
    replace (1 + S (S k)) with (S (S (S k))) by lia.
    replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ (S c) (S k) ltac:(lia) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ Hck H1), (IHf H3 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_spec_pair_body D idx _ _ Hck H1), (IH HT2). reflexivity.
Qed.

Lemma spec_box_body_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) q c c0 m,
  c0 <= c -> c < c0 + m ->
  spec_box_body_cidx q c (lift_cidx c0 m i) = lift_cidx c0 m i.
Proof.
  intros D i. induction i; intros qb c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ _ _ _ Hle Hlt), (IHi2 _ _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ _ _ _ Hle Hlt); reflexivity).
  - unfold ren_lift. destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity.
  - rewrite !ren_shift_lift_S_cidx, (IHi1 _ (S c) (S c0) m ltac:(lia) ltac:(lia)), (IHi2 _ (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma spec_box_body_cty_lift_above : forall (D : JoinDomain) (T : cty D) q c c0 m,
  c0 <= c -> c < c0 + m ->
  spec_box_body_cty q c (lift_cty c0 m T) = lift_cty c0 m T.
Proof.
  intros D T. induction T using cty_ind_nested; intros qb c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ _ _ _ Hle Hlt), (IHT2 _ _ _ _ Hle Hlt); reflexivity).
  - fold_lift_cidx. rewrite (IHT _ _ _ _ Hle Hlt), (spec_box_body_cidx_lift_above D len _ _ _ _ Hle Hlt). reflexivity.
  - unfold ren_lift. destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity.
  - rewrite (IHT1 _ _ _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 _ (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ _ _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 _ (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (spec_box_body_cidx_lift_above D idx _ _ _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_in_cidx_spec_box_body : forall (D : JoinDomain) (i : cidx D) q c k,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  subst_tvar_in_cidx (S k) (spec_box_body_cidx q c i) =
  spec_box_body_cidx q c (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i. induction i; intros qb c k Hck Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ _ Hck H1), (IHi2 _ _ _ Hck H2); reflexivity);
    try (f_equal; apply (IHi _ _ _ Hck Hsk));
    nat_bool_hyps.
  - destruct (Nat.eq_dec b c) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn. rewrite (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl. reflexivity.
    + rw_nat_bool. cbn. destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); reflexivity.
  - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite (IHi1 _ (S c) (S k) ltac:(lia) H2), (IHi2 _ (S c) (S k) ltac:(lia) H3). reflexivity.
Qed.

Lemma subst_tvar_spec_box_body : forall (D : JoinDomain) (T U : cty D) q c k,
  c <= k ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) (spec_box_body_cty q c T) =
  spec_box_body_cty q c (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U qb c k Hck HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ Hck HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ _ _ _ Hck H1), (IHT2 _ _ _ _ Hck H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ _ Hck H1), (subst_tvar_in_cidx_spec_box_body D len _ _ _ Hck H2). reflexivity.
  - destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); cbn; try reflexivity.
    subst x. rewrite (spec_box_body_cty_lift_above D U qb c 0 (S k) ltac:(lia) ltac:(lia)). reflexivity.
  - nat_bool_hyps. destruct (Nat.eq_dec b c) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn. rewrite (proj2 (Nat.eqb_neq c (S k)) ltac:(lia)), !(proj2 (Nat.ltb_lt c (S k)) ltac:(lia)). cbn. rewrite Nat.eqb_refl. reflexivity.
    + rw_nat_bool. cbn. destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ _ _ Hck H1).
    rewrite (lift_cty_add D 1 (S k) U). replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ _ (S c) (S k) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ _ _ Hck H1).
    rewrite (lift_cty_add D 1 (S k) U). replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ _ (S c) (S k) ltac:(lia) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ _ Hck H1), (IHf H3 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_spec_box_body D idx _ _ _ Hck H1), (IH HT2). reflexivity.
Qed.

Lemma cidx_uses_kinds_lift_0_1 : forall (D : JoinDomain) (i : cidx D) k,
  cidx_uses_kinds false false false false false k i = false ->
  cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 i) = false.
Proof.
  intros D i k Hk.
  eapply cidx_uses_kinds_ren_tvar_gen; [| exact Hk].
  intros y Hy. unfold ren_lift. repeat (rw_nat_bool; cbv iota); lia.
Qed.

Lemma cidx_uses_kinds_subst_sum : forall (D : JoinDomain) (i : cidx D) is_left c k val,
  0 < k -> c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  cidx_uses_kinds false false false false false k val = false ->
  cidx_uses_kinds false false false false false k (subst_sum_cidx is_left c val i) = false.
Proof.
  intros D i.
  assert (Hcidx_lift0 : forall (v : cidx D) m,
    cidx_uses_kinds false false false false false m v = false ->
    cidx_uses_kinds false false false false false (S m) (lift_cidx 0 1 v) = false) by
    (intros v m Hm; apply cidx_uses_kinds_lift_0_1; exact Hm).
  induction i; intros is_left c k val Hk0 Hck Hi Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ _ _ val Hk0 Hck H1 Hval), (IHi2 _ _ _ val Hk0 Hck H2 Hval); reflexivity);
    try (apply (IHi _ _ _ val Hk0 Hck Hi Hval));
    nat_bool_hyps;
    try (destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia));
    try (destruct (lt_eq_lt_dec b c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia));
    try (destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia)).
  apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
  destruct (Nat.eq_dec s c) as [-> | Hne].
  - assert (Hsubst_cidx_lt : forall (j v : cidx D) c0 k0,
      c0 < k0 ->
      cidx_uses_kinds false false false false false k0 v = false ->
      cidx_uses_kinds false false false false false (S k0) j = false ->
      cidx_uses_kinds false false false false false k0 (subst_cidx c0 v j) = false).
    { clear - Hcidx_lift0. intro j. induction j; intros v c0 k0 Hlt Hv Hj; cbn in *; try reflexivity;
        try (apply orb_false_iff in Hj as [H1 H2]; rewrite (IHj1 _ _ _ Hlt Hv H1), (IHj2 _ _ _ Hlt Hv H2); reflexivity);
        try (apply (IHj _ _ _ Hlt Hv Hj));
        nat_bool_hyps;
        try (destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia));
        try (destruct (lt_eq_lt_dec p c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); reflexivity || (apply Nat.eqb_neq; lia)).
      - destruct (lt_eq_lt_dec x c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); try exact Hv; reflexivity || (apply Nat.eqb_neq; lia).
      - apply orb_false_iff in Hj as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
        rewrite (proj2 (Nat.eqb_neq (if s <? c0 then s else if s =? c0 then 0 else s - 1) k0)
                  ltac:(destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia)).
        rewrite (IHj1 (lift_cidx 0 1 v) (S c0) (S k0) ltac:(lia) (Hcidx_lift0 v k0 Hv) H2).
        rewrite (IHj2 (lift_cidx 0 1 v) (S c0) (S k0) ltac:(lia) (Hcidx_lift0 v k0 Hv) H3).
        reflexivity. }
    rewrite Nat.eqb_refl. apply (Hsubst_cidx_lt _ val 0 k Hk0 Hval).
    destruct is_left;
      [apply (IHi1 true (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) ltac:(lia) H2 (Hcidx_lift0 val k Hval)) |
       apply (IHi2 false (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) ltac:(lia) H3 (Hcidx_lift0 val k Hval))].
  - rw_nat_bool. cbn.
    rewrite (proj2 (Nat.eqb_neq (if s <? c then s else s - 1) k) ltac:(destruct (lt_eq_lt_dec s c) as [[? | ?] | ?]; [| contradiction |]; repeat (rw_nat_bool; cbv iota); lia)).
    rewrite (IHi1 is_left (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) ltac:(lia) H2 (Hcidx_lift0 val k Hval)).
    rewrite (IHi2 is_left (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) ltac:(lia) H3 (Hcidx_lift0 val k Hval)).
  reflexivity.
Qed.

Lemma subst_tvar_in_cidx_subst_sum : forall (D : JoinDomain) (i : cidx D) is_left c k val,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  cidx_uses_kinds false false false false false k val = false ->
  subst_tvar_in_cidx k (subst_sum_cidx is_left c val i) =
  subst_sum_cidx is_left c (subst_tvar_in_cidx k val) (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Hv : forall v c k, c <= k -> v <> S k ->
    (let p := if v <? c then v else if v =? c then 0 else v - 1 in
     if p <? k then p else if p =? k then 0 else p - 1) =
    (let q := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if q <? c then q else if q =? c then 0 else q - 1)) by
    (intros v c k Hck Hsk; destruct (lt_eq_lt_dec v c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec v (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros is_left c k val Hck Hsk Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ _ val Hck H1 Hval), (IHi2 _ _ _ val Hck H2 Hval); reflexivity);
    try (f_equal; apply (IHi _ _ _ val Hck Hsk Hval));
    nat_bool_hyps.
  - f_equal. apply Hv; assumption.
  - f_equal. apply Hv; assumption.
  - f_equal. apply Hv; assumption.
  - f_equal. apply Hv; assumption.
  - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hval1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 val) = false) by
      (apply cidx_uses_kinds_lift_0_1; exact Hval).
    destruct (Nat.eq_dec s c) as [-> | Hne].
    + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl.
      destruct is_left.
      * replace k with (0 + k) by lia.
        rewrite (subst_tvar_in_cidx_subst_cidx D (subst_sum_cidx true (S c) (lift_cidx 0 1 val) i1) val 0 k).
        -- cbn [Nat.add]. rewrite (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
           rewrite (IHi1 true (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) H2 Hval1). reflexivity.
        -- cbn [Nat.add]. apply (cidx_uses_kinds_subst_sum D i1 true (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) ltac:(lia) H2 Hval1).
        -- exact Hval.
      * replace k with (0 + k) by lia.
        rewrite (subst_tvar_in_cidx_subst_cidx D (subst_sum_cidx false (S c) (lift_cidx 0 1 val) i2) val 0 k).
        -- cbn [Nat.add]. rewrite (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
           rewrite (IHi2 false (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) H3 Hval1). reflexivity.
        -- cbn [Nat.add]. apply (cidx_uses_kinds_subst_sum D i2 false (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) ltac:(lia) H3 Hval1).
        -- exact Hval.
    + rw_nat_bool. cbn [subst_tvar_in_cidx].
      destruct (lt_eq_lt_dec s (S k)) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec s c) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota);
        rewrite (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval),
                (IHi1 is_left (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) H2 Hval1),
                (IHi2 is_left (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) H3 Hval1); f_equal; lia.
Qed.

Lemma ren_subst_tvar_in_cidx_01 : forall (D : JoinDomain) (i : cidx D) k r,
  (forall x, x < k -> r x < k) ->
  r k = k ->
  (forall x, x > k -> r x > k /\ r (x - 1) = r x - 1) ->
  cidx_uses_kinds false false false false false k i = false ->
  subst_tvar_in_cidx k (ren_cidx r i) = ren_cidx r (subst_tvar_in_cidx k i).
Proof.
  intros D i k r Hlt Heq Hgt Hi.
  symmetry. apply (ren_subst_tvar_in_cidx_gen D i k r r Hi); [| exact Heq | exact Hgt].
  intro x; intro Hx; split; [reflexivity | apply Hlt; exact Hx].
Qed.

Lemma subst_tvar_in_cidx_spec_sum_branch : forall (D : JoinDomain) (i : cidx D) is_left c k,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  subst_tvar_in_cidx (S k) (spec_sum_branch_cidx is_left c i) =
  spec_sum_branch_cidx is_left c (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  induction i; intros is_left c k Hck Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ _ Hck H1), (IHi2 _ _ _ Hck H2); reflexivity);
    try (f_equal; apply (IHi _ _ _ Hck Hsk));
    nat_bool_hyps.
  apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
  destruct (Nat.eq_dec s c) as [-> | Hne].
  - rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl.
    assert (Hsub : cidx_uses_kinds false false false false false (S k)
      (subst_sum_cidx is_left (S c) (CIdxVar 0) (if is_left then i1 else i2)) = false).
    { apply (cidx_uses_kinds_subst_sum D _ is_left (S c) (S k) (CIdxVar 0) ltac:(lia) ltac:(lia)).
      - destruct is_left; assumption.
      - reflexivity. }
    rewrite (ren_subst_tvar_in_cidx_01 D _ (S k) (sum_branch_rot c)).
    + f_equal.
      destruct is_left;
        [rewrite (subst_tvar_in_cidx_subst_sum D i1 true (S c) (S k) (CIdxVar 0) ltac:(lia) H2 ltac:(reflexivity)) |
         rewrite (subst_tvar_in_cidx_subst_sum D i2 false (S c) (S k) (CIdxVar 0) ltac:(lia) H3 ltac:(reflexivity))];
        cbn; rw_nat_bool; reflexivity.
    + intros x Hx. unfold sum_branch_rot.
      destruct (Nat.eqb_spec x 0); [lia | destruct (Nat.leb_spec x c); lia].
    + unfold sum_branch_rot. destruct (Nat.eqb_spec (S k) 0); [lia | destruct (Nat.leb_spec (S k) c); lia].
    + intros x Hx. unfold sum_branch_rot.
      destruct (Nat.eqb_spec x 0); [lia |].
      destruct (Nat.eqb_spec (x - 1) 0); destruct (Nat.leb_spec x c); destruct (Nat.leb_spec (x - 1) c); split; lia.
    + exact Hsub.
  - rw_nat_bool. cbn.
    destruct (lt_eq_lt_dec s (S k)) as [[? | ?] | ?]; [| contradiction |];
      repeat (rw_nat_bool; cbv iota);
      rewrite (IHi1 is_left (S c) (S k) ltac:(lia) H2), (IHi2 is_left (S c) (S k) ltac:(lia) H3); reflexivity.
Qed.

Lemma spec_sum_branch_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) is_left c c0 m,
  c0 <= c -> c < c0 + m ->
  spec_sum_branch_cidx is_left c (lift_cidx c0 m i) = lift_cidx c0 m i.
Proof.
  intros D i. induction i; intros is_left c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ _ _ _ Hle Hlt), (IHi2 _ _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ _ _ _ Hle Hlt); reflexivity).
  rewrite !ren_shift_lift_S_cidx. unfold ren_lift. destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
    rewrite (IHi1 _ (S c) (S c0) m ltac:(lia) ltac:(lia)), (IHi2 _ (S c) (S c0) m ltac:(lia) ltac:(lia)); reflexivity.
Qed.

Lemma spec_sum_branch_cty_lift_above : forall (D : JoinDomain) (T : cty D) is_left c c0 m,
  c0 <= c -> c < c0 + m ->
  spec_sum_branch_cty is_left c (lift_cty c0 m T) = lift_cty c0 m T.
Proof.
  intros D T. induction T using cty_ind_nested; intros is_left c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ _ _ _ Hle Hlt), (IHT2 _ _ _ _ Hle Hlt); reflexivity).
  - fold_lift_cidx. rewrite (IHT _ _ _ _ Hle Hlt), (spec_sum_branch_cidx_lift_above D len _ _ _ _ Hle Hlt). reflexivity.
  - rewrite (IHT1 _ _ _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 _ (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ _ _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 _ (S c) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (spec_sum_branch_cidx_lift_above D idx _ _ _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_spec_sum_branch : forall (D : JoinDomain) (T U : cty D) is_left c k,
  c <= k ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) (spec_sum_branch_cty is_left c T) =
  spec_sum_branch_cty is_left c (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U is_left c k Hck HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ Hck HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ _ _ _ Hck H1), (IHT2 _ _ _ _ Hck H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ _ Hck H1), (subst_tvar_in_cidx_spec_sum_branch D len _ _ _ Hck H2). reflexivity.
  - destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); cbn; try reflexivity.
    subst x. rewrite (spec_sum_branch_cty_lift_above D U is_left c 0 (S k) ltac:(lia) ltac:(lia)). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ _ _ Hck H1).
    rewrite (lift_cty_add D 1 (S k) U). replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ _ (S c) (S k) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ _ _ Hck H1).
    rewrite (lift_cty_add D 1 (S k) U). replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ _ (S c) (S k) ltac:(lia) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ _ Hck H1), (IHf H3 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_spec_sum_branch D idx _ _ _ Hck H1), (IH HT2). reflexivity.
Qed.

Lemma subst_tvar_in_cidx_subst_pair : forall (D : JoinDomain) (i : cidx D) c k fst_i snd_i,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  cidx_uses_kinds false false false false false k fst_i = false ->
  cidx_uses_kinds false false false false false k snd_i = false ->
  subst_tvar_in_cidx k (subst_pair_cidx c fst_i snd_i i) =
  subst_pair_cidx c (subst_tvar_in_cidx k fst_i) (subst_tvar_in_cidx k snd_i) (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Hv : forall v c k, c <= k -> v <> S k ->
    (let p := if v <? c then v else if v =? c then 0 else v - 1 in
     if p <? k then p else if p =? k then 0 else p - 1) =
    (let q := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if q <? c then q else if q =? c then 0 else q - 1)) by
    (intros v c k Hck Hsk; destruct (lt_eq_lt_dec v c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec v (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  assert (Hv_fs : forall p c k, c <= k -> p <> c -> p <> S k ->
    (let q := if p <? c then p else p - 1 in if q <? k then q else if q =? k then 0 else q - 1) =
    (let q' := if p <? S k then p else p - 1 in if q' <? c then q' else q' - 1)) by
    (intros p c k Hck Hc Hsk; destruct (lt_eq_lt_dec p c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros c k fst_i snd_i Hck Hsk Hfst Hsnd; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ fst_i snd_i Hck H1 Hfst Hsnd), (IHi2 _ _ fst_i snd_i Hck H2 Hfst Hsnd); reflexivity);
    try (f_equal; apply (IHi _ _ fst_i snd_i Hck Hsk Hfst Hsnd));
    nat_bool_hyps.
  - f_equal. apply Hv; assumption.
  - f_equal. apply Hv; assumption.
  - destruct (Nat.eq_dec p c) as [-> | Hne].
    + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl. reflexivity.
    + rw_nat_bool. cbn.
      destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Nat.eq_dec p c) as [-> | Hne].
    + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl. reflexivity.
    + rw_nat_bool. cbn.
      destruct (lt_eq_lt_dec p (S k)) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hf1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 fst_i) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hfst).
    assert (Hs1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 snd_i) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hsnd).
    rewrite (Hv s c k Hck H1), (subst_tvar_in_cidx_lift_ge D fst_i 0 k ltac:(lia) Hfst), (subst_tvar_in_cidx_lift_ge D snd_i 0 k ltac:(lia) Hsnd).
    rewrite (IHi1 (S c) (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) ltac:(lia) H2 Hf1 Hs1).
    rewrite (IHi2 (S c) (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) ltac:(lia) H3 Hf1 Hs1).
  reflexivity.
Qed.

Lemma subst_pair_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) c fst_i snd_i c0 m,
  c0 <= c -> c < c0 + m ->
  subst_pair_cidx c fst_i snd_i (lift_cidx c0 m i) = lift_cidx c0 (m - 1) i.
Proof.
  intros D i. induction i; intros c fst_i snd_i c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ fst_i snd_i _ _ Hle Hlt), (IHi2 _ fst_i snd_i _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ fst_i snd_i _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  - unfold ren_lift. destruct (lt_eq_lt_dec p c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - unfold ren_lift. destruct (lt_eq_lt_dec p c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - rewrite !ren_shift_lift_S_cidx. unfold ren_lift. destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHi1 (S c) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) (S c0) m ltac:(lia) ltac:(lia)),
              (IHi2 (S c) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) (S c0) m ltac:(lia) ltac:(lia));
      f_equal; lia.
Qed.

Lemma subst_pair_cty_lift_above : forall (D : JoinDomain) (T : cty D) c fst_i snd_i c0 m,
  c0 <= c -> c < c0 + m ->
  subst_pair_cty c fst_i snd_i (lift_cty c0 m T) = lift_cty c0 (m - 1) T.
Proof.
  intros D T. induction T using cty_ind_nested; intros c fst_i snd_i c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ fst_i snd_i _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ fst_i snd_i _ _ Hle Hlt), (IHT2 _ fst_i snd_i _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  - fold_lift_cidx. rewrite (IHT _ fst_i snd_i _ _ Hle Hlt), (subst_pair_cidx_lift_above D len _ fst_i snd_i _ _ Hle Hlt). reflexivity.
  - rewrite (IHT1 _ fst_i snd_i _ _ Hle Hlt), !ren_shift_lift_S_cty,
            (IHT2 (S c) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ fst_i snd_i _ _ Hle Hlt), !ren_shift_lift_S_cty,
            (IHT2 (S c) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ fst_i snd_i _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (subst_pair_cidx_lift_above D idx _ fst_i snd_i _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_in_cty_subst_pair : forall (D : JoinDomain) (T U : cty D) c k fst_i snd_i,
  c <= k ->
  cty_uses_kinds true false true true true true true c T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cidx_uses_kinds false false false false false k fst_i = false ->
  cidx_uses_kinds false false false false false k snd_i = false ->
  subst_tvar_in_cty k (lift_cty 0 k U) (subst_pair_cty c fst_i snd_i T) =
  subst_pair_cty c (subst_tvar_in_cidx k fst_i) (subst_tvar_in_cidx k snd_i)
    (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U c k fst_i snd_i Hck HTc HT Hfst Hsnd; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ fst_i snd_i Hck HTc HT Hfst Hsnd));
    try (apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2];
         rewrite (IHT1 _ _ _ fst_i snd_i Hck Hc1 H1 Hfst Hsnd), (IHT2 _ _ _ fst_i snd_i Hck Hc2 H2 Hfst Hsnd); reflexivity).
  - apply orb_false_iff in HTc as [Hc1 _]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ fst_i snd_i Hck Hc1 H1 Hfst Hsnd), (subst_tvar_in_cidx_subst_pair D len _ _ fst_i snd_i Hck H2 Hfst Hsnd). reflexivity.
  - nat_bool_hyps. destruct (Nat.eq_dec x (S k)) as [-> | Hne].
    + rewrite (proj2 (Nat.ltb_ge (S k) c) ltac:(lia)), (proj2 (Nat.eqb_neq (S k) c) HTc), Nat.eqb_refl.
      replace (S k - 1) with k by lia. cbn. rewrite Nat.eqb_refl.
      rewrite (subst_pair_cty_lift_above D U c _ _ 0 (S k) ltac:(lia) ltac:(lia)). f_equal; lia.
    + destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; [| contradiction | | | contradiction |];
        cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
  - nat_bool_hyps.
    destruct (lt_eq_lt_dec b c) as [[? | ?] | ?];
      destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); repeat (rw_nat_bool; cbv iota); try (f_equal; lia).
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ fst_i snd_i Hck Hc1 H1 Hfst Hsnd).
    assert (Hf1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 fst_i) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hfst).
    assert (Hs1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 snd_i) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hsnd).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U),
            (subst_tvar_in_cidx_lift_ge D fst_i 0 k ltac:(lia) Hfst),
            (subst_tvar_in_cidx_lift_ge D snd_i 0 k ltac:(lia) Hsnd).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ (S c) (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) ltac:(lia) Hc2 H2 Hf1 Hs1). reflexivity.
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ fst_i snd_i Hck Hc1 H1 Hfst Hsnd).
    assert (Hf1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 fst_i) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hfst).
    assert (Hs1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 snd_i) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hsnd).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U),
            (subst_tvar_in_cidx_lift_ge D fst_i 0 k ltac:(lia) Hfst),
            (subst_tvar_in_cidx_lift_ge D snd_i 0 k ltac:(lia) Hsnd).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ (S c) (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) ltac:(lia) Hc2 H2 Hf1 Hs1). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HTc as [Hc1 HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ fst_i snd_i Hck Hc1 H1 Hfst Hsnd), (IHf H3 HTc2 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HTc as [_ HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_subst_pair D idx _ _ fst_i snd_i Hck H1 Hfst Hsnd), (IH HTc2 HT2). reflexivity.
Qed.

Lemma subst_tvar_in_cidx_subst_box_nat : forall (D : JoinDomain) (i : cidx D) c k q val,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  cidx_uses_kinds false false false false false k val = false ->
  subst_tvar_in_cidx k (subst_box_nat_cidx c q val i) =
  subst_box_nat_cidx c q (subst_tvar_in_cidx k val) (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Hv : forall v c k, c <= k -> v <> S k ->
    (let p := if v <? c then v else if v =? c then 0 else v - 1 in
     if p <? k then p else if p =? k then 0 else p - 1) =
    (let q0 := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if q0 <? c then q0 else if q0 =? c then 0 else q0 - 1)) by
    (intros v c k Hck Hsk; destruct (lt_eq_lt_dec v c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec v (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros c k qb val Hck Hsk Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ qb val Hck H1 Hval), (IHi2 _ _ qb val Hck H2 Hval); reflexivity);
    try (f_equal; apply (IHi _ _ qb val Hck Hsk Hval));
    nat_bool_hyps.
  - f_equal. apply Hv; assumption.
  - destruct (Nat.eq_dec b c) as [-> | Hne].
    + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl. reflexivity.
    + rw_nat_bool. cbn.
      destruct (lt_eq_lt_dec b c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - f_equal. apply Hv; assumption.
  - f_equal. apply Hv; assumption.
  - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hval1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 val) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hval).
    rewrite (Hv s c k Hck H1), (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
    rewrite (IHi1 (S c) (S k) qb (lift_cidx 0 1 val) ltac:(lia) H2 Hval1).
    rewrite (IHi2 (S c) (S k) qb (lift_cidx 0 1 val) ltac:(lia) H3 Hval1).
  reflexivity.
Qed.

Lemma subst_box_nat_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) c q val c0 m,
  c0 <= c -> c < c0 + m ->
  subst_box_nat_cidx c q val (lift_cidx c0 m i) = lift_cidx c0 (m - 1) i.
Proof.
  intros D i. induction i; intros c qb val c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ qb val _ _ Hle Hlt), (IHi2 _ qb val _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ qb val _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  - unfold ren_lift. destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - rewrite !ren_shift_lift_S_cidx. unfold ren_lift. destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHi1 (S c) qb (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia)),
              (IHi2 (S c) qb (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia));
      f_equal; lia.
Qed.

Lemma subst_box_nat_cty_lift_above : forall (D : JoinDomain) (T : cty D) c q val c0 m,
  c0 <= c -> c < c0 + m ->
  subst_box_nat_cty c q val (lift_cty c0 m T) = lift_cty c0 (m - 1) T.
Proof.
  intros D T. induction T using cty_ind_nested; intros c qb val c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ qb val _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ qb val _ _ Hle Hlt), (IHT2 _ qb val _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  - fold_lift_cidx. rewrite (IHT _ qb val _ _ Hle Hlt), (subst_box_nat_cidx_lift_above D len _ qb val _ _ Hle Hlt). reflexivity.
  - rewrite (IHT1 _ qb val _ _ Hle Hlt), !ren_shift_lift_S_cty,
            (IHT2 (S c) qb (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ qb val _ _ Hle Hlt), !ren_shift_lift_S_cty,
            (IHT2 (S c) qb (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ qb val _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (subst_box_nat_cidx_lift_above D idx _ qb val _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_in_cty_subst_box_nat : forall (D : JoinDomain) (T U : cty D) c k q val,
  c <= k ->
  cty_uses_kinds true false true true true true true c T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cidx_uses_kinds false false false false false k val = false ->
  subst_tvar_in_cty k (lift_cty 0 k U) (subst_box_nat_cty c q val T) =
  subst_box_nat_cty c q (subst_tvar_in_cidx k val) (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U c k qb val Hck HTc HT Hval; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ qb val Hck HTc HT Hval));
    try (apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2];
         rewrite (IHT1 _ _ _ qb val Hck Hc1 H1 Hval), (IHT2 _ _ _ qb val Hck Hc2 H2 Hval); reflexivity).
  - apply orb_false_iff in HTc as [Hc1 _]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ qb val Hck Hc1 H1 Hval), (subst_tvar_in_cidx_subst_box_nat D len _ _ qb val Hck H2 Hval). reflexivity.
  - nat_bool_hyps. destruct (Nat.eq_dec x (S k)) as [-> | Hne].
    + rewrite (proj2 (Nat.ltb_ge (S k) c) ltac:(lia)), (proj2 (Nat.eqb_neq (S k) c) HTc), Nat.eqb_refl.
      replace (S k - 1) with k by lia. cbn. rewrite Nat.eqb_refl.
      rewrite (subst_box_nat_cty_lift_above D U c qb _ 0 (S k) ltac:(lia) ltac:(lia)). f_equal; lia.
    + destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; [| contradiction | | | contradiction |];
        cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
  - nat_bool_hyps.
    destruct (lt_eq_lt_dec b c) as [[? | ?] | ?];
      destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); repeat (rw_nat_bool; cbv iota); try (f_equal; lia).
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ qb val Hck Hc1 H1 Hval).
    assert (Hval1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 val) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hval).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U), (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ (S c) (S k) qb (lift_cidx 0 1 val) ltac:(lia) Hc2 H2 Hval1). reflexivity.
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ qb val Hck Hc1 H1 Hval).
    assert (Hval1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 val) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hval).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U), (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ (S c) (S k) qb (lift_cidx 0 1 val) ltac:(lia) Hc2 H2 Hval1). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HTc as [Hc1 HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ qb val Hck Hc1 H1 Hval), (IHf H3 HTc2 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HTc as [_ HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_subst_box_nat D idx _ _ qb val Hck H1 Hval), (IH HTc2 HT2). reflexivity.
Qed.

Lemma subst_tvar_in_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) c c0 m,
  c0 <= c -> c < c0 + m ->
  subst_tvar_in_cidx c (lift_cidx c0 m i) = lift_cidx c0 (m - 1) i.
Proof.
  intros D i. induction i; intros c c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ _ _ Hle Hlt), (IHi2 _ _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  rewrite !ren_shift_lift_S_cidx. unfold ren_lift. destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
    rewrite (IHi1 (S c) (S c0) m ltac:(lia) ltac:(lia)), (IHi2 (S c) (S c0) m ltac:(lia) ltac:(lia)); f_equal; lia.
Qed.

Lemma subst_box_ty_cty_lift_above : forall (D : JoinDomain) (T : cty D) c q T0 c0 m,
  c0 <= c -> c < c0 + m ->
  subst_box_ty_cty c q T0 (lift_cty c0 m T) = lift_cty c0 (m - 1) T.
Proof.
  intros D T. induction T using cty_ind_nested; intros c qb T0 c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ qb T0 _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ qb T0 _ _ Hle Hlt), (IHT2 _ qb T0 _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  - fold_lift_cidx. rewrite (IHT _ qb T0 _ _ Hle Hlt), (subst_tvar_in_cidx_lift_above D len _ _ _ Hle Hlt). reflexivity.
  - unfold ren_lift. destruct (lt_eq_lt_dec b c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - rewrite (IHT1 _ qb T0 _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 (S c) qb (lift_cty 0 1 T0) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ qb T0 _ _ Hle Hlt), !ren_shift_lift_S_cty, (IHT2 (S c) qb (lift_cty 0 1 T0) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ qb T0 _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (subst_tvar_in_cidx_lift_above D idx _ _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_in_cidx_comm_lt : forall (D : JoinDomain) (i : cidx D) c k,
  c <= k ->
  cidx_uses_kinds false false false false false (S k) i = false ->
  subst_tvar_in_cidx k (subst_tvar_in_cidx c i) =
  subst_tvar_in_cidx c (subst_tvar_in_cidx (S k) i).
Proof.
  intros D i.
  assert (Hv : forall v c k, c <= k -> v <> S k ->
    (let p := if v <? c then v else if v =? c then 0 else v - 1 in
     if p <? k then p else if p =? k then 0 else p - 1) =
    (let q := if v <? S k then v else if v =? S k then 0 else v - 1 in
     if q <? c then q else if q =? c then 0 else q - 1)) by
    (intros v c k Hck Hsk; destruct (lt_eq_lt_dec v c) as [[? | ?] | ?];
     destruct (lt_eq_lt_dec v (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); try contradiction;
     cbv zeta; repeat (rw_nat_bool; cbv iota); lia).
  induction i; intros c k Hck Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ Hck H1), (IHi2 _ _ Hck H2); reflexivity);
    try (f_equal; apply (IHi _ _ Hck Hsk));
    nat_bool_hyps; try (f_equal; apply Hv; assumption).
  apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
  rewrite (Hv s c k Hck H1), (IHi1 (S c) (S k) ltac:(lia) H2), (IHi2 (S c) (S k) ltac:(lia) H3).
  reflexivity.
Qed.

Lemma subst_tvar_in_cty_subst_box_ty : forall (D : JoinDomain) (T U T0 : cty D) c k q,
  c <= k ->
  cty_uses_kinds true false true true true true true c T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k T0 = false ->
  subst_tvar_in_cty k (lift_cty 0 k U) (subst_box_ty_cty c q T0 T) =
  subst_box_ty_cty c q (subst_tvar_in_cty k (lift_cty 0 k U) T0)
    (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U T0 c k qb Hck HTc HT HT0; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ qb Hck HTc HT HT0));
    try (apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2];
         rewrite (IHT1 _ _ _ _ qb Hck Hc1 H1 HT0), (IHT2 _ _ _ _ qb Hck Hc2 H2 HT0); reflexivity).
  - apply orb_false_iff in HTc as [Hc1 _]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ _ qb Hck Hc1 H1 HT0), (subst_tvar_in_cidx_comm_lt D len c k Hck H2). reflexivity.
  - nat_bool_hyps. destruct (Nat.eq_dec x (S k)) as [-> | Hne].
    + rewrite (proj2 (Nat.ltb_ge (S k) c) ltac:(lia)), (proj2 (Nat.eqb_neq (S k) c) HTc), Nat.eqb_refl.
      replace (S k - 1) with k by lia. cbn. rewrite Nat.eqb_refl.
      rewrite (subst_box_ty_cty_lift_above D U c qb _ 0 (S k) ltac:(lia) ltac:(lia)). f_equal; lia.
    + destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; [| contradiction | | | contradiction |];
        cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
  - nat_bool_hyps. destruct (Nat.eq_dec b c) as [-> | Hne].
    + rewrite Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)), Nat.eqb_refl. reflexivity.
    + rw_nat_bool. cbn.
      destruct (lt_eq_lt_dec b c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); try contradiction;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ _ qb Hck Hc1 H1 HT0).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    change (ren_cty (ren_lift 0 1) (subst_tvar_in_cty k (lift_cty 0 k U) T0))
      with (lift_cty 0 1 (subst_tvar_in_cty k (lift_cty 0 k U) T0)).
    rewrite (subst_tvar_in_cty_lift_ge D T0 (lift_cty 0 k U) 0 k ltac:(lia) HT0).
    rewrite (lift_cty_add D 1 k U). replace (1 + k) with (S k) by lia.
    assert (HT0' : cty_uses_kinds false true false false false false false (S k) (lift_cty 0 1 T0) = false) by
      (replace (S k) with (1 + k) by lia; apply cty_uses_kinds_tvar_lift_n_false; exact HT0).
    f_equal. exact (IHT2 U (lift_cty 0 1 T0) (S c) (S k) qb ltac:(lia) Hc2 H2 HT0').
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ _ qb Hck Hc1 H1 HT0).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    change (ren_cty (ren_lift 0 1) (subst_tvar_in_cty k (lift_cty 0 k U) T0))
      with (lift_cty 0 1 (subst_tvar_in_cty k (lift_cty 0 k U) T0)).
    rewrite (subst_tvar_in_cty_lift_ge D T0 (lift_cty 0 k U) 0 k ltac:(lia) HT0).
    rewrite (lift_cty_add D 1 k U). replace (1 + k) with (S k) by lia.
    assert (HT0' : cty_uses_kinds false true false false false false false (S k) (lift_cty 0 1 T0) = false) by
      (replace (S k) with (1 + k) by lia; apply cty_uses_kinds_tvar_lift_n_false; exact HT0).
    f_equal. exact (IHT2 U (lift_cty 0 1 T0) (S c) (S k) qb ltac:(lia) Hc2 H2 HT0').
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HTc as [Hc1 HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ _ qb Hck Hc1 H1 HT0), (IHf H3 HTc2 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HTc as [_ HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_comm_lt D idx c k Hck H1), (IH HTc2 HT2). reflexivity.
Qed.

Lemma subst_sum_cidx_lift_above : forall (D : JoinDomain) (i : cidx D) is_left c val c0 m,
  c0 <= c -> c < c0 + m ->
  subst_sum_cidx is_left c val (lift_cidx c0 m i) = lift_cidx c0 (m - 1) i.
Proof.
  intros D i. induction i; intros is_left c val c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHi1 _ _ val _ _ Hle Hlt), (IHi2 _ _ val _ _ Hle Hlt); reflexivity);
    try (rewrite (IHi _ _ val _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  rewrite !ren_shift_lift_S_cidx. unfold ren_lift. destruct (lt_eq_lt_dec s c0) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota);
    rewrite (IHi1 _ (S c) (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia)),
            (IHi2 _ (S c) (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia));
    f_equal; lia.
Qed.

Lemma subst_sum_cty_lift_above : forall (D : JoinDomain) (T : cty D) is_left c val c0 m,
  c0 <= c -> c < c0 + m ->
  subst_sum_cty is_left c val (lift_cty c0 m T) = lift_cty c0 (m - 1) T.
Proof.
  intros D T. induction T using cty_ind_nested; intros is_left c val c0 m Hle Hlt; cbn in *; try reflexivity;
    try (rewrite (IHT _ _ val _ _ Hle Hlt); reflexivity);
    try (rewrite (IHT1 _ _ val _ _ Hle Hlt), (IHT2 _ _ val _ _ Hle Hlt); reflexivity);
    try (f_equal; unfold ren_lift; match goal with |- context [Nat.ltb ?v c0] => destruct (lt_eq_lt_dec v c0) as [[? | ?] | ?] end; repeat (rw_nat_bool; cbv iota); lia).
  - fold_lift_cidx. rewrite (IHT _ _ val _ _ Hle Hlt), (subst_sum_cidx_lift_above D len _ _ val _ _ Hle Hlt). reflexivity.
  - rewrite (IHT1 _ _ val _ _ Hle Hlt), !ren_shift_lift_S_cty,
            (IHT2 _ (S c) (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite (IHT1 _ _ val _ _ Hle Hlt), !ren_shift_lift_S_cty,
            (IHT2 _ (S c) (lift_cidx 0 1 val) (S c0) m ltac:(lia) ltac:(lia)). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ val _ _ Hle Hlt), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    fold_lift_cidx. rewrite (subst_sum_cidx_lift_above D idx _ _ val _ _ Hle Hlt), IH. reflexivity.
Qed.

Lemma subst_tvar_in_cty_subst_sum : forall (D : JoinDomain) (T U : cty D) is_left c k val,
  c <= k ->
  cty_uses_kinds true false true true true true true c T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cidx_uses_kinds false false false false false k val = false ->
  subst_tvar_in_cty k (lift_cty 0 k U) (subst_sum_cty is_left c val T) =
  subst_sum_cty is_left c (subst_tvar_in_cidx k val) (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U is_left c k val Hck HTc HT Hval; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ val Hck HTc HT Hval));
    try (apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2];
         rewrite (IHT1 _ _ _ _ val Hck Hc1 H1 Hval), (IHT2 _ _ _ _ val Hck Hc2 H2 Hval); reflexivity).
  - apply orb_false_iff in HTc as [Hc1 _]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ _ val Hck Hc1 H1 Hval), (subst_tvar_in_cidx_subst_sum D len _ _ _ val Hck H2 Hval). reflexivity.
  - nat_bool_hyps. destruct (Nat.eq_dec x (S k)) as [-> | Hne].
    + rewrite (proj2 (Nat.ltb_ge (S k) c) ltac:(lia)), (proj2 (Nat.eqb_neq (S k) c) HTc), Nat.eqb_refl.
      replace (S k - 1) with k by lia. cbn. rewrite Nat.eqb_refl.
      rewrite (subst_sum_cty_lift_above D U is_left c _ 0 (S k) ltac:(lia) ltac:(lia)). f_equal; lia.
    + destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec x (S k)) as [[? | ?] | ?]; [| contradiction | | | contradiction |];
        cbn; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; f_equal; lia.
  - nat_bool_hyps.
    destruct (lt_eq_lt_dec b c) as [[? | ?] | ?];
      destruct (lt_eq_lt_dec b (S k)) as [[? | ?] | ?]; destruct (Nat.eq_dec k 0); repeat (rw_nat_bool; cbv iota); try (f_equal; lia).
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ _ val Hck Hc1 H1 Hval).
    assert (Hval1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 val) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hval).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U), (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ _ (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) Hc2 H2 Hval1). reflexivity.
  - apply orb_false_iff in HTc as [Hc1 Hc2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ _ val Hck Hc1 H1 Hval).
    assert (Hval1 : cidx_uses_kinds false false false false false (S k) (lift_cidx 0 1 val) = false) by (apply cidx_uses_kinds_lift_0_1; exact Hval).
    rewrite (lift_cty_add D 1 k U), (lift_cty_add D 1 (S k) U), (subst_tvar_in_cidx_lift_ge D val 0 k ltac:(lia) Hval).
    replace (1 + k) with (S k) by lia. replace (1 + S k) with (S (S k)) by lia.
    rewrite (IHT2 _ _ (S c) (S k) (lift_cidx 0 1 val) ltac:(lia) Hc2 H2 Hval1). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HTc as [Hc1 HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ _ _ _ val Hck Hc1 H1 Hval), (IHf H3 HTc2 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HTc as [_ HTc2]; apply orb_false_iff in HT as [H1 HT2].
    rewrite (subst_tvar_in_cidx_subst_sum D idx _ _ _ val Hck H1 Hval), (IH HTc2 HT2). reflexivity.
Qed.

Lemma ren_cty_above_drop1 : forall (D : JoinDomain) (T : cty D) m r,
  0 < m ->
  (forall i, m <= i -> r i = i - 1) ->
  ren_cty r (lift_cty 0 m T) = lift_cty 0 (m - 1) T.
Proof.
  intros D T m r Hm Hr. unfold lift_cty. rewrite ren_cty_comp.
  apply ren_cty_ext. intro x. unfold ren_lift.
  destruct (Nat.ltb_spec x 0) as [Hx | Hx]; [lia |].
  rewrite Hr by lia. lia.
Qed.

Lemma subst_tvar_in_cty_subst_var_0 : forall (D : JoinDomain) (T U : cty D) k0 y,
  y <> k0 ->
  cty_uses_kinds false true false false false false false (S k0) T = false ->
  subst_tvar_in_cty k0 (lift_cty 0 k0 U) (subst_var_in_cty 0 y T) =
  subst_var_in_cty 0 (if y <? k0 then y else y - 1) (subst_tvar_in_cty (S k0) (lift_cty 0 (S k0) U) T).
Proof.
  intros D T.
  assert (Hr : forall c x y,
    Nat.iter c ren_shift (fun i => match i with 0 => y | S i' => i' end) x =
    if x <? c then x else if x =? c then c + y else x - 1).
  { clear. intro c. induction c as [| c IHc]; intros x y.
    - change (Nat.iter 0 ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)
        with (match x with 0 => y | S i' => i' end).
      destruct x.
      + rewrite Nat.ltb_irrefl, Nat.eqb_refl. cbn. lia.
      + destruct (Nat.ltb_spec (S x) 0); [lia |].
        destruct (Nat.eqb_spec (S x) 0); [lia | cbn; lia].
    - change (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)
        with (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)) x).
      destruct x; [reflexivity |].
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)) (S x))
        with (S (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)).
      rewrite IHc.
      destruct (Nat.ltb_spec x c); destruct (Nat.eqb_spec x c);
        destruct (Nat.ltb_spec (S x) (S c)); destruct (Nat.eqb_spec (S x) (S c)); cbn; lia. }
  assert (Hcidx : forall (i : cidx D) c k0 y,
    y <> k0 ->
    cidx_uses_kinds false false false false false (S (c + k0)) i = false ->
    subst_tvar_in_cidx (c + k0) (subst_var_in_cidx c y i) =
    subst_var_in_cidx c (if y <? k0 then y else y - 1) (subst_tvar_in_cidx (S (c + k0)) i)).
  { assert (Hv : forall x c k0 y, y <> k0 -> x <> S (c + k0) ->
      (let r1 := Nat.iter c ren_shift (fun i => match i with 0 => y | S i' => i' end) x in
       if r1 <? c + k0 then r1 else if r1 =? c + k0 then 0 else r1 - 1) =
      Nat.iter c ren_shift (fun i => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)
        (if x <? S (c + k0) then x else if x =? S (c + k0) then 0 else x - 1)).
    { clear - Hr. intros x c k0 y Hy Hsk. rewrite !Hr. cbv zeta.
      destruct (lt_eq_lt_dec x c) as [[? | ?] | ?];
        destruct (lt_eq_lt_dec x (S (c + k0))) as [[? | ?] | ?];
        destruct (lt_eq_lt_dec y k0) as [[? | ?] | ?]; try contradiction;
        repeat (rw_nat_bool; cbv iota);
        repeat match goal with
        | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
        | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
        end; cbn; lia. }
    intro i. induction i; intros c k0 y Hy Hsk; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hsk as [H1 H2]; rewrite (IHi1 _ _ _ Hy H1), (IHi2 _ _ _ Hy H2); reflexivity);
      try (f_equal; apply (IHi _ _ _ Hy Hsk));
      nat_bool_hyps; try (f_equal; apply Hv; assumption).
    apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    f_equal; [apply Hv; assumption | |].
    - change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)).
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)).
      exact (IHi1 (S c) k0 y Hy H2).
    - change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)).
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)).
      exact (IHi2 (S c) k0 y Hy H3). }
  assert (Hgen : forall (T : cty D) U c k0 y,
    y <> k0 ->
    cty_uses_kinds false true false false false false false (S (c + k0)) T = false ->
    subst_tvar_in_cty (c + k0) (lift_cty 0 (c + k0) U) (subst_var_in_cty c y T) =
    subst_var_in_cty c (if y <? k0 then y else y - 1) (subst_tvar_in_cty (S (c + k0)) (lift_cty 0 (S (c + k0)) U) T)).
  { clear - Hr Hcidx. intros T. induction T using cty_ind_nested; intros U c k0 y Hy HT; cbn in *; try reflexivity;
      try (f_equal; apply (IHT _ _ _ _ Hy HT));
      try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ _ _ _ Hy H1), (IHT2 _ _ _ _ Hy H2); reflexivity).
    - apply orb_false_iff in HT as [H1 H2].
      rewrite (IHT _ _ _ _ Hy H1). f_equal. exact (Hcidx len _ _ _ Hy H2).
    - destruct (Nat.eq_dec x (S (c + k0))) as [-> | Hne].
      + rewrite Hr.
        destruct (Nat.ltb_spec (S (c + k0)) c); [lia |].
        destruct (Nat.eqb_spec (S (c + k0)) c); [lia |].
        cbn iota. replace (S (c + k0) - 1) with (c + k0) by lia.
        cbn [subst_tvar_in_cty]. rewrite !Nat.eqb_refl. unfold subst_var_in_cty.
        replace (lift_cty 0 (c + k0) U) with (lift_cty 0 (S (c + k0) - 1) U) at 1 by (f_equal; lia).
        symmetry. apply ren_cty_above_drop1; [lia |].
        intros i Hi. rewrite Hr.
        destruct (Nat.ltb_spec i c); [lia |]; destruct (Nat.eqb_spec i c); cbn; lia.
      + rewrite Hr.
        destruct (Nat.ltb_spec x c); destruct (Nat.eqb_spec x c);
          destruct (Nat.ltb_spec x (S (c + k0))); destruct (Nat.eqb_spec x (S (c + k0)));
          destruct (Nat.ltb_spec y k0); cbn; try lia;
          try rewrite Hr;
          repeat (cbn; match goal with
                        | |- context [Nat.iter _ ren_shift _ _] => rewrite Hr
                        | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                        | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                        end);
          try lia; f_equal; lia.
    - nat_bool_hyps. rewrite Hr.
      destruct (Nat.ltb_spec b c); destruct (Nat.eqb_spec b c);
        destruct (Nat.ltb_spec b (S (c + k0))); destruct (Nat.eqb_spec b (S (c + k0)));
        destruct (Nat.ltb_spec y k0); cbn; try lia;
        try rewrite Hr;
        repeat (cbn; match goal with
                      | |- context [Nat.iter _ ren_shift _ _] => rewrite Hr
                      | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                      | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                      end);
        try lia; f_equal; lia.
    - apply orb_false_iff in HT as [H1 H2]. f_equal; [exact (IHT1 _ _ _ _ Hy H1) |].
      rewrite (lift_cty_add D 1 (c + k0) U), (lift_cty_add D 1 (S (c + k0)) U).
      replace (1 + (c + k0)) with (S c + k0) by lia.
      replace (1 + S (c + k0)) with (S (S c + k0)) by lia.
      unfold subst_var_in_cty.
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)).
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)).
      exact (IHT2 U (S c) k0 y Hy H2).
    - apply orb_false_iff in HT as [H1 H2]. f_equal; [exact (IHT1 _ _ _ _ Hy H1) |].
      rewrite (lift_cty_add D 1 (c + k0) U), (lift_cty_add D 1 (S (c + k0)) U).
      replace (1 + (c + k0)) with (S c + k0) by lia.
      replace (1 + S (c + k0)) with (S (S c + k0)) by lia.
      unfold subst_var_in_cty.
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)).
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)))
        with (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => if y <? k0 then y else y - 1 | S i' => i' end)).
      exact (IHT2 U (S c) k0 y Hy H2).
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
      rewrite (H2 _ _ _ _ Hy H1), (IHf H3 HT2). reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT as [H1 HT2].
      unfold subst_var_in_cidx in Hcidx.
      rewrite (Hcidx idx _ _ _ Hy H1), (IH HT2). reflexivity. }
  intros U k0 y Hy HT. exact (Hgen T U 0 k0 y Hy HT).
Qed.

Lemma lift_cty_1_2_split : forall (D : JoinDomain) (T : cty D),
  ren_cty (ren_lift 1 2) T = lift_cty 1 1 (lift_cty 1 1 T).
Proof.
  intros D T. unfold lift_cty. rewrite ren_cty_comp.
  apply ren_cty_ext. intro x. unfold ren_lift.
  destruct (Nat.eq_dec x 0) as [-> | Hnz]; [reflexivity |].
  rw_nat_bool. lia.
Qed.

Lemma subst_tvar_spec_fix_step : forall (D : JoinDomain) (mot U : cty D) k,
  cty_uses_kinds true false true true true true true 0 mot = false ->
  cty_uses_kinds false true false false false false false (S k) mot = false ->
  subst_tvar_in_cty (S (S k)) (lift_cty 0 (S (S k)) U) (spec_fix_step_cty mot) =
  spec_fix_step_cty (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) mot).
Proof.
  intros D mot U k Hmot0 Hmot. unfold spec_fix_step_cty.
  rewrite lift_cty_1_2_split.
  assert (Hidx_true : forall (i : cidx D) c, cidx_uses_kinds true true true true true c i = false) by
    (clear; intro i; induction i; intro c; cbn; try reflexivity; try (rewrite IHi1, IHi2; reflexivity); apply IHi).
  assert (Hren_no_tvar0 : forall (T : cty D) c (r : nat -> nat),
    (forall x, r x = c -> x = c) ->
    cty_uses_kinds true false true true true true true c T = false ->
    cty_uses_kinds true false true true true true true c (ren_cty r T) = false).
  { clear - Hidx_true. intro T. induction T using cty_ind_nested; intros c rn Hrn HT; cbn in *; try reflexivity;
      try (apply (IHT _ _ Hrn HT));
      try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ _ Hrn H1), (IHT2 _ _ Hrn H2); reflexivity).
    - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT _ _ Hrn H1), Hidx_true. reflexivity.
    - nat_bool_hyps. apply Nat.eqb_neq. intro Heq. apply Hrn in Heq. lia.
    - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ Hrn H1).
      rewrite (IHT2 (S c) (ren_shift rn)); [reflexivity | | exact H2].
      intros [| vx] Hx; unfold ren_shift in *; [discriminate | injection Hx as Hx'; rewrite (Hrn _ Hx'); reflexivity].
    - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ Hrn H1).
      rewrite (IHT2 (S c) (ren_shift rn)); [reflexivity | | exact H2].
      intros [| vx] Hx; unfold ren_shift in *; [discriminate | injection Hx as Hx'; rewrite (Hrn _ Hx'); reflexivity].
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
      rewrite (H2 _ _ Hrn H1), (IHf H3 HT2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      rewrite Hidx_true, IH; [reflexivity | apply orb_false_iff in HT; exact (proj2 HT)]. }
  assert (Hm01 : cty_uses_kinds true false true true true true true 0 (lift_cty 1 1 mot) = false).
  { unfold lift_cty. apply Hren_no_tvar0; [| exact Hmot0].
    intros [| x] Hx; [reflexivity | unfold ren_lift in Hx; destruct (Nat.ltb_spec (S x) 1) in Hx; cbn in Hx; lia]. }
  assert (Hm02 : cty_uses_kinds true false true true true true true 0 (lift_cty 1 1 (lift_cty 1 1 mot)) = false).
  { unfold lift_cty. apply Hren_no_tvar0; [| exact Hm01].
    intros [| x] Hx; [reflexivity | unfold ren_lift in Hx; destruct (Nat.ltb_spec (S x) 1) in Hx; cbn in Hx; lia]. }
  assert (Hm1 : cty_uses_kinds false true false false false false false (S (S k)) (lift_cty 1 1 mot) = false).
  { unfold lift_cty. eapply cty_uses_kinds_tvar_ren_gen; [| exact Hmot].
    intros x Hx. unfold ren_lift. destruct (Nat.ltb_spec x 1); cbn; lia. }
  assert (Hm2 : cty_uses_kinds false true false false false false false (S (S (S k))) (lift_cty 1 1 (lift_cty 1 1 mot)) = false).
  { unfold lift_cty. eapply cty_uses_kinds_tvar_ren_gen; [| exact Hm1].
    intros x Hx. unfold ren_lift. destruct (Nat.ltb_spec x 1); cbn; lia. }
  assert (Hidx1 : cidx_uses_kinds (D := D) false false false false false (S (S k)) (CIdxAdd (CIdxVar 1) (CIdxLit 1)) = false) by
    (cbn; reflexivity).
  rewrite (subst_tvar_in_cty_subst_cidx_0 D (lift_cty 1 1 (lift_cty 1 1 mot))
             (lift_cty 0 (S (S k)) U) (CIdxAdd (CIdxVar 1) (CIdxLit 1)) (S (S k)) Hm02 Hm2 Hidx1).
  cbn [subst_tvar_in_cidx]. rewrite (proj2 (Nat.ltb_lt 1 (S (S k))) ltac:(lia)).
  rewrite (lift_cty_add D 1 (S (S k)) U). replace (1 + S (S k)) with (S (S (S k))) by lia.
  f_equal.
  assert (Hlift_U1 : lift_cty 1 1 (lift_cty 0 (S k) U) = lift_cty 0 (S (S k)) U).
  { unfold lift_cty. rewrite ren_cty_comp. apply ren_cty_ext. intro x. unfold ren_lift.
    destruct (Nat.ltb_spec x 0); [lia |]; destruct (Nat.ltb_spec (x + S k) 1); cbn; lia. }
  assert (Hlift_U2 : lift_cty 1 1 (lift_cty 0 (S (S k)) U) = lift_cty 0 (S (S (S k))) U).
  { unfold lift_cty. rewrite ren_cty_comp. apply ren_cty_ext. intro x. unfold ren_lift.
    destruct (Nat.ltb_spec x 0); [lia |]; destruct (Nat.ltb_spec (x + S (S k)) 1); cbn; lia. }
  rewrite <- Hlift_U2, <- (subst_tvar_in_cty_lift_ge D (lift_cty 1 1 mot) (lift_cty 0 (S (S k)) U) 1 (S (S k)) ltac:(lia) Hm1).
  rewrite <- Hlift_U1, <- (subst_tvar_in_cty_lift_ge D mot (lift_cty 0 (S k) U) 1 (S k) ltac:(lia) Hmot).
  rewrite lift_cty_1_2_split. reflexivity.
Qed.

Lemma cty_uses_var_subst_cidx_unshift : forall (D : JoinDomain) (T : cty D) k val,
  cty_uses_var k T = false ->
  subst_cidx_in_cty k val T = unshift_cty k T.
Proof.
  intros D T.
  assert (Hidx : forall (i : cidx D) k val, cidx_uses_var k i = false -> subst_cidx k val i = unshift_cidx k i).
  { assert (Hr : forall c x,
      Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x =
      if x <? S c then x else x - 1).
    { clear. intro c. induction c; intro x; [destruct x; [reflexivity | cbn; lia] |].
      destruct x; [reflexivity |].
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => 0 | S i' => i' end) (S x))
        with (S (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x)).
      rewrite IHc. destruct (Nat.ltb_spec x (S c)); destruct (Nat.ltb_spec (S x) (S (S c))); cbn; lia. }
    intro i. induction i; intros k val Hi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ val H1), (IHi2 _ val H2); reflexivity);
      try (f_equal; apply (IHi _ val Hi));
      nat_bool_hyps;
      try (try rewrite Hr; unfold unshift_cidx, unshift_var;
           repeat (cbn; match goal with
                         | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                         | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                         end); try lia; f_equal; lia).
    apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    unfold unshift_cidx in *; unfold unshift_var in *; cbn.
    try rewrite Hr. rewrite (IHi1 (S k) (lift_cidx 0 1 val) H2), (IHi2 (S k) (lift_cidx 0 1 val) H3).
    f_equal.
    repeat (cbn; match goal with
                  | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                  end); lia. }
  assert (Hr : forall c x,
    Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x =
    if x <? S c then x else x - 1).
  { clear. intro c. induction c; intro x; [destruct x; [reflexivity | cbn; lia] |].
    destruct x; [reflexivity |].
    change (Nat.iter (S c) ren_shift (fun i => match i with 0 => 0 | S i' => i' end) (S x))
      with (S (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x)).
    rewrite IHc. destruct (Nat.ltb_spec x (S c)); destruct (Nat.ltb_spec (S x) (S (S c))); cbn; lia. }
  induction T using cty_ind_nested; intros k val HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ val HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ val H1), (IHT2 _ val H2); reflexivity);
    nat_bool_hyps.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT _ val H1), (Hidx len _ val H2). reflexivity.
  - try rewrite Hr. unfold unshift_var.
    repeat (cbn; match goal with
                  | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                  end); try lia; f_equal; lia.
  - try rewrite Hr. unfold unshift_var.
    repeat (cbn; match goal with
                  | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                  end); try lia; f_equal; lia.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ val H1), (IHT2 (S k) (lift_cidx 0 1 val) H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ val H1), (IHT2 (S k) (lift_cidx 0 1 val) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 _ val H1), (IHf H3 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 HT2].
    rewrite (Hidx idx _ val H1), (IH HT2). reflexivity.
Qed.

Lemma cty_uses_var_subst_tvar_unshift : forall (D : JoinDomain) (T V : cty D) k,
  cty_uses_var k T = false ->
  subst_tvar_in_cty k V T = unshift_cty k T.
Proof.
  intros D T V k HT.
  assert (Hidx : forall (i : cidx D) k, cidx_uses_var k i = false -> subst_tvar_in_cidx k i = unshift_cidx k i).
  { assert (Hr : forall c x,
      Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x =
      if x <? S c then x else x - 1).
    { clear. intro c. induction c; intro x; [destruct x; [reflexivity | cbn; lia] |].
      destruct x; [reflexivity |].
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => 0 | S i' => i' end) (S x))
        with (S (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x)).
      rewrite IHc. destruct (Nat.ltb_spec x (S c)); destruct (Nat.ltb_spec (S x) (S (S c))); cbn; lia. }
    intro i. induction i; intros k0 Hi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ H1), (IHi2 _ H2); reflexivity);
      try (f_equal; apply (IHi _ Hi));
      nat_bool_hyps;
      try (try rewrite Hr; unfold unshift_cidx, unshift_var;
           repeat (cbn; match goal with
                         | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                         | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                         end); try lia; f_equal; lia).
    apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    unfold unshift_cidx in *; unfold unshift_var in *; cbn.
    try rewrite Hr. rewrite (IHi1 (S k0) H2), (IHi2 (S k0) H3).
    f_equal.
    repeat (cbn; match goal with
                  | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                  end); lia. }
  assert (Hr : forall c x,
    Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x =
    if x <? S c then x else x - 1).
  { clear. intro c. induction c; intro x; [destruct x; [reflexivity | cbn; lia] |].
    destruct x; [reflexivity |].
    change (Nat.iter (S c) ren_shift (fun i => match i with 0 => 0 | S i' => i' end) (S x))
      with (S (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x)).
    rewrite IHc. destruct (Nat.ltb_spec x (S c)); destruct (Nat.ltb_spec (S x) (S (S c))); cbn; lia. }
  revert V k HT.
  induction T using cty_ind_nested; intros V k HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT V k HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 V k H1), (IHT2 V k H2); reflexivity);
    nat_bool_hyps.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT V k H1), (Hidx len k H2). reflexivity.
  - try rewrite Hr. unfold unshift_var.
    repeat (cbn; match goal with
                  | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                  end); try lia; f_equal; lia.
  - try rewrite Hr. unfold unshift_var.
    repeat (cbn; match goal with
                  | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                  | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                  end); try lia; f_equal; lia.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 V k H1), (IHT2 (lift_cty 0 1 V) (S k) H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 V k H1), (IHT2 (lift_cty 0 1 V) (S k) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 HT2].
    rewrite (H2 V k H1), (IHf H3 HT2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 HT2].
    rewrite (Hidx idx k H1), (IH HT2). reflexivity.
Qed.

Lemma app_result_ty_subst_tvar : forall (D : JoinDomain) (dom dom' cod cod' U : cty D) arg k res_ty,
  cty_alpha_eq dom' (subst_tvar_in_cty k (lift_cty 0 k U) dom) ->
  cty_alpha_eq cod' (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) cod) ->
  cty_uses_kinds false true false false false false false (S k) cod = false ->
  (match dom with
   | CNat => cty_uses_kinds true false true true true true true 0 cod = false
   | CUniv _ => cty_uses_kinds false true false false false false false 0 cod = false
   | _ => True
   end) ->
  (match arg with
   | CNatVal i => cidx_uses_kinds false false false false false k i = false
   | CTypeVal T0 => cty_uses_kinds false true false false false false false k T0 = false
   | CVar x => match dom with CUniv _ => True | _ => x <> k end
   | _ => True
   end) ->
  app_result_ty dom cod arg = Some res_ty ->
  exists res_ty',
    app_result_ty dom' cod' (subst_tvar_in_cterm k (lift_cty 0 k U) arg) = Some res_ty' /\
    cty_alpha_eq res_ty' (subst_tvar_in_cty k (lift_cty 0 k U) res_ty).
Proof.
  intros D dom dom' cod cod' U arg k res_ty Hdom Hcod Hcod_k Hcod0 Harg Happ.
  assert (Hnondep : cty_uses_var 0 cod = false ->
    exists res_ty',
      app_result_ty dom' cod' (subst_tvar_in_cterm k (lift_cty 0 k U) arg) = Some res_ty' /\
      cty_alpha_eq res_ty' (subst_tvar_in_cty k (lift_cty 0 k U) (unshift_cty 0 cod))).
  { intro Huv.
    assert (Huv' : cty_uses_var 0 cod' = false).
    { rewrite (cty_uses_var_alpha_eq D 0 cod' _ Hcod).
      replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
        (rewrite lift_cty_add; f_equal; lia).
      exact (subst_tvar_in_cty_uses_var_0 D cod (lift_cty 0 k U) k Huv Hcod_k). }
    assert (Hres : app_result_ty dom' cod' (subst_tvar_in_cterm k (lift_cty 0 k U) arg) = Some (unshift_cty 0 cod')).
    { unfold app_result_ty.
      destruct dom';
        try (rewrite Huv'; reflexivity);
        [destruct (term_as_cidx (subst_tvar_in_cterm k (lift_cty 0 k U) arg));
         [f_equal; apply cty_uses_var_subst_cidx_unshift; exact Huv' | rewrite Huv'; reflexivity] |
         destruct (subst_tvar_in_cterm k (lift_cty 0 k U) arg);
         try (f_equal; apply cty_uses_var_subst_tvar_unshift; exact Huv');
         rewrite Huv'; reflexivity]. }
    exists (unshift_cty 0 cod'). split; [exact Hres |].
    eapply cty_alpha_eq_trans; [apply cty_alpha_eq_unshift; exact Hcod |].
    replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
      (rewrite lift_cty_add; f_equal; lia).
    rewrite <- (subst_tvar_in_cty_unshift_0 D cod (lift_cty 0 k U) k Huv Hcod_k).
    apply cty_alpha_eq_refl. }
  destruct dom;
    try (cbn [app_result_ty] in Happ; destruct (cty_uses_var 0 cod) eqn:Hu in Happ; [discriminate |];
         inversion Happ; subst; apply Hnondep; exact Hu).
  - cbn [subst_tvar_in_cty] in Hdom.
    apply cty_alpha_eq_CNat_inv in Hdom; subst dom'.
    destruct arg; cbn [app_result_ty term_as_cidx] in Happ;
      try (destruct (cty_uses_var 0 cod) eqn:Hu in Happ; [discriminate |];
           inversion Happ; subst; apply Hnondep; exact Hu).
    + inversion Happ; subst.
      assert (Hx : x <> k) by exact Harg.
      cbn [subst_tvar_in_cterm app_result_ty].
      destruct (Nat.eqb_spec x k); [lia |].
      destruct (Nat.ltb_spec x k); cbn [term_as_cidx];
        (eexists; split;
         [ reflexivity
         | eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hcod |];
           replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
             (rewrite lift_cty_add; f_equal; lia);
           pose proof (subst_tvar_in_cty_subst_cidx_0 D cod (lift_cty 0 k U) (CIdxVar x) k Hcod0 Hcod_k ltac:(cbn; apply Nat.eqb_neq; exact Hx)) as Hcm;
           cbn [subst_tvar_in_cidx] in Hcm; rw_nat_bool_in Hcm; rewrite <- Hcm; apply cty_alpha_eq_refl ]).
    + inversion Happ; subst. cbn [subst_tvar_in_cterm app_result_ty term_as_cidx].
      eexists; split; [reflexivity |].
      eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hcod |].
      replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
        (rewrite lift_cty_add; f_equal; lia).
      rewrite <- (subst_tvar_in_cty_subst_cidx_0 D cod (lift_cty 0 k U) i k Hcod0 Hcod_k Harg).
      apply cty_alpha_eq_refl.
  - cbn [subst_tvar_in_cty] in Hdom.
    apply cty_alpha_eq_CUniv_inv in Hdom; subst dom'.
    destruct arg; cbn [app_result_ty] in Happ;
      try (destruct (cty_uses_var 0 cod) eqn:Hu in Happ; [discriminate |];
           inversion Happ; subst; apply Hnondep; exact Hu).
    + inversion Happ; subst. cbn [subst_tvar_in_cterm app_result_ty].
      destruct (Nat.eq_dec x k) as [-> | Hne'].
      * rewrite Nat.eqb_refl. cbn [app_result_ty].
        eexists; split; [reflexivity |].
        eapply cty_alpha_eq_trans; [apply (subst_tvar_in_cty_alpha_eq D 0 _ _ _ _ (cty_alpha_eq_refl _ _) Hcod) |].
        replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
          (rewrite lift_cty_add; f_equal; lia).
        assert (Hsubst_k : forall (T V : cty D) c k0,
          cty_uses_kinds false true false false false false false c T = false ->
          cty_uses_kinds false true false false false false false (S (c + k0)) T = false ->
          subst_tvar_in_cty (c + k0) (lift_cty 0 c V) (subst_tvar_in_cty c (CTVar (c + k0)) T) =
          subst_tvar_in_cty c (lift_cty 0 c V) (subst_tvar_in_cty (S (c + k0)) (lift_cty 0 (S c) V) T)).
        { clear. intro T. induction T using cty_ind_nested; intros V c k0 Hc Hsk; cbn in *; try reflexivity;
            try (f_equal; apply IHT; assumption);
            try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
                 f_equal; [apply IHT1 | apply IHT2]; assumption).
          - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
            f_equal; [apply IHT; assumption | apply subst_tvar_in_cidx_comm; [lia | assumption | assumption]].
          - destruct (Nat.eq_dec x c) as [-> | Hne_c].
            + rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq c (S (c + k0))) ltac:(lia)), (proj2 (Nat.ltb_lt c (S (c + k0))) ltac:(lia)).
              cbn. rewrite !Nat.eqb_refl. reflexivity.
            + destruct (Nat.eq_dec x (S (c + k0))) as [-> | Hne_sk].
              * rewrite (proj2 (Nat.eqb_neq (S (c + k0)) c) Hne_c), (proj2 (Nat.ltb_ge (S (c + k0)) c) ltac:(lia)), Nat.eqb_refl.
                replace (S (c + k0) - 1) with (c + k0) by lia. cbn. rewrite Nat.eqb_refl.
                replace (lift_cty 0 (S c) V) with (lift_cty c 1 (lift_cty 0 c V)) by
                  (unfold lift_cty; rewrite ren_cty_comp; apply ren_cty_ext; intro y; unfold ren_lift;
                   destruct (Nat.ltb_spec y 0); [lia |]; destruct (Nat.ltb_spec (y + c) c); cbn; lia).
                rewrite subst_tvar_in_cty_lift_cancel. reflexivity.
              * destruct (Nat.eqb_spec x c); destruct (Nat.ltb_spec x c);
                  destruct (Nat.eqb_spec x (S (c + k0))); destruct (Nat.ltb_spec x (S (c + k0)));
                  cbn; try lia;
                  repeat (cbn; match goal with
                                | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                                | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                                end); try lia; f_equal; lia.
          - nat_bool_hyps. f_equal.
            destruct (Nat.eqb_spec b c); destruct (Nat.ltb_spec b c);
              destruct (Nat.eqb_spec b (S (c + k0))); destruct (Nat.ltb_spec b (S (c + k0)));
              cbn; try lia;
              repeat (cbn; match goal with
                            | |- context [?a =? ?b] => destruct (Nat.eqb_spec a b)
                            | |- context [?a <? ?b] => destruct (Nat.ltb_spec a b)
                            end); lia.
          - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
            f_equal; [apply IHT1; assumption |].
            pose proof (IHT2 V (S c) k0 Hc2 Hk2) as Hrec.
            rewrite (lift_cty_add D 1 c V), (lift_cty_add D 1 (S c) V). cbn [Nat.add] in Hrec |- *.
            replace (ren_lift 0 1 (c + k0)) with (S (c + k0)) by (unfold ren_lift; destruct (Nat.ltb_spec (c + k0) 0); lia).
            exact Hrec.
          - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
            f_equal; [apply IHT1; assumption |].
            pose proof (IHT2 V (S c) k0 Hc2 Hk2) as Hrec.
            rewrite (lift_cty_add D 1 c V), (lift_cty_add D 1 (S c) V). cbn [Nat.add] in Hrec |- *.
            replace (ren_lift 0 1 (c + k0)) with (S (c + k0)) by (unfold ren_lift; destruct (Nat.ltb_spec (c + k0) 0); lia).
            exact Hrec.
          - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
            inversion H; subst; cbn in H2. apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
            f_equal; [f_equal; apply (H2 V c k0 Hc1 Hk1) | apply (IHf H3 Hc2 Hk2)].
          - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
            apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
            f_equal; [apply subst_tvar_in_cidx_comm; [lia | assumption | assumption] | apply (IH Hc2 Hk2)]. }
        pose proof (Hsubst_k cod (lift_cty 0 k U) 0 k Hcod0 Hcod_k) as Hk_eq.
        cbn [Nat.add] in Hk_eq. rewrite lift_cty_0_0 in Hk_eq. rewrite <- Hk_eq. apply cty_alpha_eq_refl.
      * destruct (Nat.eqb_spec x k); [lia |].
        destruct (Nat.ltb_spec x k); cbn [app_result_ty];
          (eexists; split;
           [ reflexivity
           | eapply cty_alpha_eq_trans; [apply (subst_tvar_in_cty_alpha_eq D 0 _ _ _ _ (cty_alpha_eq_refl _ _) Hcod) |];
             replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
               (rewrite lift_cty_add; f_equal; lia);
             pose proof (subst_tvar_in_cty_subst_tvar_0 D cod (CTVar x) (lift_cty 0 k U) k Hcod0 Hcod_k ltac:(cbn; reflexivity)) as Hcm;
             cbn [subst_tvar_in_cty] in Hcm; rw_nat_bool_in Hcm; rewrite <- Hcm; apply cty_alpha_eq_refl ]).
    + inversion Happ; subst. cbn [subst_tvar_in_cterm app_result_ty].
      eexists; split; [reflexivity |].
      eapply cty_alpha_eq_trans; [apply (subst_tvar_in_cty_alpha_eq D 0 _ _ _ _ (cty_alpha_eq_refl _ _) Hcod) |].
      replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
        (rewrite lift_cty_add; f_equal; lia).
      lazymatch type of Harg with
      | cty_uses_kinds _ _ _ _ _ _ _ _ ?tt = false =>
          rewrite <- (subst_tvar_in_cty_subst_tvar_0 D cod tt (lift_cty 0 k U) k Hcod0 Hcod_k Harg)
      end.
      apply cty_alpha_eq_refl.
Qed.

Lemma branch_rel_vec_zero_any : forall (D : JoinDomain) j (v : list (grade D)),
  grade_join D = Some j ->
  (forall g, @allows D zero g) ->
  branch_rel (vec_zero (length v)) v.
Proof.
  intros D j v Hj H0. unfold branch_rel. rewrite Hj.
  induction v as [| g gs IH]; cbn; constructor; [apply H0 | exact IH].
Qed.

Lemma branch_rel_vec_scale_mono : forall (D : JoinDomain) (q1 q2 : grade D) (v : list (grade D)),
  (grade_join D = None -> forall a b, @allows D a b -> a = b) ->
  allows q1 q2 ->
  branch_rel (vec_scale q1 v) (vec_scale q2 v).
Proof.
  intros D q1 q2 v Hnone Hq. unfold branch_rel. destruct (grade_join D) eqn:Hj.
  - induction v as [| x xs IH]; cbn; constructor; [| exact IH].
    apply mul_monotone; [exact Hq | apply allows_refl].
  - rewrite (Hnone eq_refl _ _ Hq). reflexivity.
Qed.

Lemma branch_rel_vec_scale_r : forall (D : JoinDomain) (q : grade D) (v1 v2 : list (grade D)),
  branch_rel v1 v2 ->
  branch_rel (vec_scale q v1) (vec_scale q v2).
Proof.
  intros D q v1 v2 H. apply branch_rel_scale. exact H.
Qed.

Lemma branch_rel_subst_zero_z : forall (D : JoinDomain) (z u : list (grade D)) k m,
  (grade_join D = None -> z = vec_zero m) ->
  (forall j, grade_join D = Some j -> forall g, @allows D zero g) ->
  length z = m ->
  branch_rel (vec_subst k (vec_zero m) u) (vec_subst k z u).
Proof.
  intros D z u k m Hnone Hsome Hlen.
  destruct (grade_join D) eqn:Hj.
  - assert (Hz : vec_allows (vec_zero m) z).
    { rewrite <- Hlen. pose proof (branch_rel_vec_zero_any D g z Hj (Hsome g eq_refl)) as Hb.
      unfold branch_rel in Hb. rewrite Hj in Hb. exact Hb. }
    unfold branch_rel. rewrite Hj.
    induction k as [| k' IH] in u |- *; destruct u as [| a u']; cbn; try constructor.
    + apply vec_allows_add; [apply vec_allows_refl | apply vec_allows_scale; [apply allows_refl | exact Hz]].
    + apply allows_refl.
    + exact (IH u').
  - rewrite (Hnone eq_refl). apply branch_rel_refl.
Qed.

Lemma vec_subst_branch_rel_l : forall (D : JoinDomain) (v1 v2 u1 u2 : list (grade D)) k,
  branch_rel v1 v2 ->
  branch_rel u1 u2 ->
  branch_rel (vec_subst k v1 u1) (vec_subst k v2 u2).
Proof.
  intros D v1 v2 u1 u2 k Hv Hu. unfold branch_rel in *. destruct (grade_join D) eqn:Hj.
  - induction k as [| k' IH] in u1, u2, Hu |- *; destruct u1 as [| a1 u1']; destruct u2 as [| a2 u2'];
      inversion Hu; subst; cbn; try constructor.
    + apply vec_allows_add; [exact H4 | apply vec_allows_scale; [exact H2 | exact Hv]].
    + exact H2.
    + exact (IH _ _ H4).
  - subst. reflexivity.
Qed.

Lemma vec_scale_zero_vec : forall (D : JoinDomain) (q : grade D) n,
  vec_scale q (vec_zero n) = vec_zero n.
Proof.
  intros D q n. unfold vec_scale, vec_zero. rewrite map_repeat, mul_zero_r. reflexivity.
Qed.

Lemma vec_add_app_same : forall (D : JoinDomain) (u1 u2 v1 v2 : list (grade D)),
  length u1 = length v1 ->
  vec_add (u1 ++ u2) (v1 ++ v2) = vec_add u1 v1 ++ vec_add u2 v2.
Proof.
  intros D u1. induction u1 as [| a u1 IH]; intros u2 [| b v1] v2 Hlen; cbn in *; try discriminate;
    [reflexivity | f_equal; apply IH; lia].
Qed.

Lemma branch_rel_add_zero_tail : forall (D : JoinDomain) (v z : list (grade D)) k (q : grade D),
  (grade_join D = None -> z = vec_zero (length z)) ->
  (forall j, grade_join D = Some j -> forall g, @allows D zero g) ->
  length v = k + length z ->
  branch_rel v (vec_add v (vec_zero k ++ vec_scale q z)).
Proof.
  intros D v z k q Hnone Hsome Hlen.
  destruct (grade_join D) eqn:Hj.
  - assert (H0 : branch_rel (vec_zero (length v)) (vec_zero k ++ vec_scale q z)).
    { rewrite Hlen.
      replace (vec_zero (D := D) (k + length z)) with (vec_zero (D := D) k ++ vec_zero (D := D) (length z))
        by (unfold vec_zero; rewrite repeat_app; reflexivity).
      apply branch_rel_app; [apply branch_rel_refl |].
      rewrite <- (vec_scale_length D q z). eapply branch_rel_vec_zero_any; [exact Hj | apply (Hsome g eq_refl)]. }
    rewrite <- (vec_add_zero_r D v) at 1. apply branch_rel_add; [apply branch_rel_refl | exact H0].
  - rewrite (Hnone eq_refl), vec_scale_zero_vec.
    replace (vec_zero (D := D) k ++ vec_zero (D := D) (length z)) with (vec_zero (D := D) (length v))
      by (rewrite Hlen; unfold vec_zero; rewrite repeat_app; reflexivity).
    rewrite vec_add_zero_r. apply branch_rel_refl.
Qed.

Lemma branch_rel_scale_add_tail : forall (D : JoinDomain) (z : list (grade D)) k (a b : grade D),
  vec_add (vec_zero k ++ vec_scale a z) (vec_zero k ++ vec_scale b z) =
  vec_zero k ++ vec_scale (add a b) z.
Proof.
  intros D z k a b.
  rewrite vec_add_app_same by (rewrite !vec_zero_length; reflexivity).
  replace (vec_zero (D := D) k) with (vec_zero (D := D) (length (vec_zero (D := D) k))) at 1
    by (rewrite vec_zero_length; reflexivity).
  rewrite vec_add_zero_l.
  f_equal. symmetry. apply vec_scale_add_l.
Qed.

Lemma vec_scale_zero_tail_assoc : forall (D : JoinDomain) (z : list (grade D)) k (q a : grade D),
  vec_scale q (vec_zero k ++ vec_scale a z) = vec_zero k ++ vec_scale (mul q a) z.
Proof.
  intros D z k q a. unfold vec_scale at 1. rewrite map_app.
  change (map (mul q) (vec_zero k)) with (vec_scale q (vec_zero k)).
  change (map (mul q) (vec_scale a z)) with (vec_scale q (vec_scale a z)).
  rewrite vec_scale_zero_vec, vec_scale_mul. reflexivity.
Qed.

Lemma branch_rel_vec_join_upper : forall (D : JoinDomain) j (v1 v2 v1' v2' w : list (grade D)),
  grade_join D = Some j ->
  BranchVec v1 v2 (vec_join j v1 v2) ->
  branch_rel v1' w ->
  branch_rel v2' w ->
  length v1' = length w ->
  length v2' = length w ->
  branch_rel (vec_join j v1' v2') w.
Proof.
  intros D j v1 v2 v1' v2' w Hj _ H1 H2 Hl1 Hl2.
  unfold branch_rel in *. rewrite Hj in *.
  induction H1 in v2', H2, Hl1, Hl2 |- *; inversion H2; subst; cbn in *; try discriminate; constructor.
  - eapply (join_least D j Hj); assumption.
  - eapply IHForall2; [eassumption | lia | lia].
Qed.





Lemma cidx_uses_kinds_tvar_subst_cidx : forall (D : JoinDomain) (i val : cidx D) c k,
  (c + k = 0 -> cidx_uses_kinds true false false false false 0 i = false) ->
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false k val = false ->
  cidx_uses_kinds false false false false false (c + k) (subst_cidx c (lift_cidx 0 c val) i) = false.
Proof.
  intros D i. induction i; intros val c k H0 Hi Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hi as [H1 H2];
         rewrite (IHi1 _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) H1 Hval),
                 (IHi2 _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) H2 Hval); reflexivity);
    try (apply (IHi _ _ _ H0 Hi Hval));
    nat_bool_hyps.
  - destruct (Nat.eqb_spec x c); [subst x; unfold lift_cidx; eapply cidx_uses_kinds_ren_tvar_gen with (k := k); [intros y Hy; unfold ren_lift; destruct (Nat.ltb_spec y 0); cbn; lia | exact Hval] |].
    destruct (Nat.ltb_spec x c); cbn; apply Nat.eqb_neq; lia.
  - destruct (Nat.ltb_spec b c); [cbn; apply Nat.eqb_neq; lia |].
    destruct (Nat.eqb_spec b c); [subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | cbn; apply Nat.eqb_neq; lia] | cbn; apply Nat.eqb_neq; lia].
  - destruct (Nat.ltb_spec p c); [cbn; apply Nat.eqb_neq; lia |].
    destruct (Nat.eqb_spec p c); [subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | cbn; apply Nat.eqb_neq; lia] | cbn; apply Nat.eqb_neq; lia].
  - destruct (Nat.ltb_spec p c); [cbn; apply Nat.eqb_neq; lia |].
    destruct (Nat.eqb_spec p c); [subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | cbn; apply Nat.eqb_neq; lia] | cbn; apply Nat.eqb_neq; lia].
  - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite lift_cidx_add. cbn [Nat.add].
    pose proof (IHi1 val (S c) k ltac:(lia) H2 Hval) as Hi1'.
    pose proof (IHi2 val (S c) k ltac:(lia) H3 Hval) as Hi2'.
    rewrite Nat.add_succ_l in Hi1', Hi2'. rewrite Hi1', Hi2'.
    replace ((if s <? c then s else if s =? c then 0 else s - 1) =? c + k) with false; [reflexivity |].
    symmetry. apply Nat.eqb_neq.
    destruct (Nat.ltb_spec s c); [lia |]; destruct (Nat.eqb_spec s c); [| lia].
    subst s. destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [| lia].
    specialize (H0 Hz). cbn in H0. apply orb_false_iff in H0 as [H01 _].
    apply orb_false_iff in H01 as [H01 _]. apply Nat.eqb_neq in H01. lia.
Qed.

Lemma cty_uses_kinds_tvar_subst_cidx_0 : forall (D : JoinDomain) (T : cty D) (val : cidx D) k,
  cidx_uses_kinds false false false false false k val = false ->
  (k = 0 -> cty_uses_kinds true false false false false false false 0 T = false) ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (subst_cidx_in_cty 0 val T) = false.
Proof.
  intros D T val k Hval HT0 HT.
  assert (Hgen : forall (T0 : cty D) c val0,
    cidx_uses_kinds false false false false false k val0 = false ->
    (c + k = 0 -> cty_uses_kinds true false false false false false false 0 T0 = false) ->
    cty_uses_kinds false true false false false false false (S (c + k)) T0 = false ->
    cty_uses_kinds false true false false false false false (c + k) (subst_cidx_in_cty c (lift_cidx 0 c val0) T0) = false).
  { clear - Hval. intro T0. induction T0 using cty_ind_nested; intros c val0 Hv H0 Hsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ Hv H0 Hsk));
      try (apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
                   (IHT0_2 _ _ Hv (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2); reflexivity).
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (cidx_uses_kinds_tvar_subst_cidx _ _ _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2 Hv).
      reflexivity.
    - nat_bool_hyps. destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
        try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
        [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) val0 Hv ltac:(lia) Hk2) as H2.
      rewrite (lift_cidx_add D 1 c val0). exact H2.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) val0 Hv ltac:(lia) Hk2) as H2.
      rewrite (lift_cidx_add D 1 c val0). exact H2.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IHf Htl (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (cidx_uses_kinds_tvar_subst_cidx _ _ _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1 Hv),
              (IH (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity. }
  pose proof (Hgen T 0 val Hval HT0 HT) as H0.
  cbn [Nat.add] in H0. rewrite lift_cidx_0_0 in H0. exact H0.
Qed.

Lemma cidx_uses_kinds_tvar_subst_tvar : forall (D : JoinDomain) (i : cidx D) c k,
  (c + k = 0 -> cidx_uses_kinds false false false false false 0 i = false) ->
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false (c + k) (subst_tvar_in_cidx c i) = false.
Proof.
  intros D i. induction i; intros c k H0 Hi; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hi as [H1 H2];
         rewrite (IHi1 _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) H1),
                 (IHi2 _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) H2); reflexivity);
    try (apply (IHi _ _ H0 Hi));
    nat_bool_hyps.
  - destruct (Nat.ltb_spec x c); [| destruct (Nat.eqb_spec x c)]; cbn; apply Nat.eqb_neq;
      try lia; subst x; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
      try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec p c); [| destruct (Nat.eqb_spec p c)]; cbn; apply Nat.eqb_neq;
      try lia; subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec p c); [| destruct (Nat.eqb_spec p c)]; cbn; apply Nat.eqb_neq;
      try lia; subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    pose proof (IHi1 (S c) k ltac:(lia) H2) as Hi1'.
    pose proof (IHi2 (S c) k ltac:(lia) H3) as Hi2'.
    rewrite Nat.add_succ_l in Hi1', Hi2'. rewrite Hi1', Hi2'.
    replace ((if s <? c then s else if s =? c then 0 else s - 1) =? c + k) with false; [reflexivity |].
    symmetry. apply Nat.eqb_neq. destruct (Nat.ltb_spec s c); [| destruct (Nat.eqb_spec s c)]; try lia.
    subst s. destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [| lia].
    specialize (H0 Hz). cbn in H0. apply orb_false_iff in H0 as [H01 _].
    apply orb_false_iff in H01 as [H01 _]. apply Nat.eqb_neq in H01. lia.
Qed.

Lemma cty_uses_kinds_tvar_subst_tvar_0 : forall (D : JoinDomain) (T U : cty D) k,
  cty_uses_kinds false true false false false false false k U = false ->
  (k = 0 -> cty_uses_kinds false true false false false false false 0 T = false) ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (subst_tvar_in_cty 0 U T) = false.
Proof.
  intros D T U k HU HT0 HT.
  assert (Hgen : forall (T0 : cty D) c U0,
    cty_uses_kinds false true false false false false false k U0 = false ->
    (c + k = 0 -> cty_uses_kinds false true false false false false false 0 T0 = false) ->
    cty_uses_kinds false true false false false false false (S (c + k)) T0 = false ->
    cty_uses_kinds false true false false false false false (c + k) (subst_tvar_in_cty c (lift_cty 0 c U0) T0) = false).
  { clear - HU. intro T0. induction T0 using cty_ind_nested; intros c U0 Hu H0 Hsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ Hu H0 Hsk));
      try (apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT0_1 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
                   (IHT0_2 _ _ Hu (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2); reflexivity).
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (cidx_uses_kinds_tvar_subst_tvar _ _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2).
      reflexivity.
    - destruct (Nat.eqb_spec x c).
      + subst x. unfold lift_cty. eapply cty_uses_kinds_tvar_ren_gen with (k := k); [| exact Hu].
        intros y Hy. unfold ren_lift. destruct (Nat.ltb_spec y 0); cbn; lia.
      + destruct (Nat.ltb_spec x c); reflexivity.
    - nat_bool_hyps. destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
        try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
        [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) U0 Hu ltac:(lia) Hk2) as H2.
      rewrite (lift_cty_add D 1 c U0). exact H2.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) U0 Hu ltac:(lia) Hk2) as H2.
      rewrite (lift_cty_add D 1 c U0). exact H2.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IHf Htl (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (cidx_uses_kinds_tvar_subst_tvar _ _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IH (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity. }
  pose proof (Hgen T 0 U HU HT0 HT) as H0.
  cbn [Nat.add] in H0. rewrite lift_cty_0_0 in H0. exact H0.
Qed.

Lemma cidx_uses_kinds_tvar_subst_pair : forall (D : JoinDomain) (i fi si : cidx D) c k,
  (c + k = 0 -> cidx_uses_kinds false false true true false 0 i = false) ->
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false k fi = false ->
  cidx_uses_kinds false false false false false k si = false ->
  cidx_uses_kinds false false false false false (c + k)
    (subst_pair_cidx c (lift_cidx 0 c fi) (lift_cidx 0 c si) i) = false.
Proof.
  intros D i. induction i; intros fi si c k H0 Hi Hf Hs; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hi as [H1 H2];
         rewrite (IHi1 _ _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) H1 Hf Hs),
                 (IHi2 _ _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) H2 Hf Hs); reflexivity);
    try (apply (IHi _ _ _ _ H0 Hi Hf Hs));
    nat_bool_hyps.
  - destruct (Nat.ltb_spec x c); [| destruct (Nat.eqb_spec x c)]; cbn; apply Nat.eqb_neq;
      try lia; subst x; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
      try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.eqb_spec p c); [subst p; unfold lift_cidx; eapply cidx_uses_kinds_ren_tvar_gen with (k := k); [intros y Hy; unfold ren_lift; destruct (Nat.ltb_spec y 0); cbn; lia | exact Hf] |].
    destruct (Nat.ltb_spec p c); cbn; apply Nat.eqb_neq; lia.
  - destruct (Nat.eqb_spec p c); [subst p; unfold lift_cidx; eapply cidx_uses_kinds_ren_tvar_gen with (k := k); [intros y Hy; unfold ren_lift; destruct (Nat.ltb_spec y 0); cbn; lia | exact Hs] |].
    destruct (Nat.ltb_spec p c); cbn; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite !lift_cidx_add. cbn [Nat.add].
    pose proof (IHi1 fi si (S c) k ltac:(lia) H2 Hf Hs) as Hi1'.
    pose proof (IHi2 fi si (S c) k ltac:(lia) H3 Hf Hs) as Hi2'.
    rewrite Nat.add_succ_l in Hi1', Hi2'. rewrite Hi1', Hi2'.
    replace ((if s <? c then s else if s =? c then 0 else s - 1) =? c + k) with false; [reflexivity |].
    symmetry. apply Nat.eqb_neq. destruct (Nat.ltb_spec s c); [| destruct (Nat.eqb_spec s c)]; try lia.
    subst s. destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [| lia].
    specialize (H0 Hz). cbn in H0. apply orb_false_iff in H0 as [H01 _].
    apply orb_false_iff in H01 as [H01 _]. apply Nat.eqb_neq in H01. lia.
Qed.

Lemma cty_uses_kinds_tvar_subst_pair_0 : forall (D : JoinDomain) (T : cty D) (fi si : cidx D) k,
  cidx_uses_kinds false false false false false k fi = false ->
  cidx_uses_kinds false false false false false k si = false ->
  (k = 0 -> cty_uses_kinds false false false false true true false 0 T = false) ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (subst_pair_cty 0 fi si T) = false.
Proof.
  intros D T fi si k Hf Hs HT0 HT.
  assert (Hgen : forall (T0 : cty D) c fi0 si0,
    cidx_uses_kinds false false false false false k fi0 = false ->
    cidx_uses_kinds false false false false false k si0 = false ->
    (c + k = 0 -> cty_uses_kinds false false false false true true false 0 T0 = false) ->
    cty_uses_kinds false true false false false false false (S (c + k)) T0 = false ->
    cty_uses_kinds false true false false false false false (c + k)
      (subst_pair_cty c (lift_cidx 0 c fi0) (lift_cidx 0 c si0) T0) = false).
  { intro T0. induction T0 using cty_ind_nested; intros c fi0 si0 Hf0 Hs0 H0 Hsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hf0 Hs0 H0 Hsk));
      try (apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT0_1 _ _ _ Hf0 Hs0 (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
                   (IHT0_2 _ _ _ Hf0 Hs0 (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2); reflexivity).
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0 _ _ _ Hf0 Hs0 (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (cidx_uses_kinds_tvar_subst_pair _ _ _ _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2 Hf0 Hs0).
      reflexivity.
    - nat_bool_hyps. destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
        try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
        [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ _ Hf0 Hs0 (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) fi0 si0 Hf0 Hs0 ltac:(lia) Hk2) as H2.
      rewrite !(lift_cidx_add D 1 c). exact H2.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ _ Hf0 Hs0 (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) fi0 si0 Hf0 Hs0 ltac:(lia) Hk2) as H2.
      rewrite !(lift_cidx_add D 1 c). exact H2.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ _ Hf0 Hs0 (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IHf Htl (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (cidx_uses_kinds_tvar_subst_pair _ _ _ _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1 Hf0 Hs0),
              (IH (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity. }
  pose proof (Hgen T 0 fi si Hf Hs HT0 HT) as H0.
  cbn [Nat.add] in H0. rewrite !lift_cidx_0_0 in H0. exact H0.
Qed.

Lemma cidx_uses_kinds_tvar_subst_box_nat : forall (D : JoinDomain) (i : cidx D) q val c k,
  (c + k = 0 -> cidx_uses_kinds false true false false false 0 i = false) ->
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false k val = false ->
  cidx_uses_kinds false false false false false (c + k) (subst_box_nat_cidx c q (lift_cidx 0 c val) i) = false.
Proof.
  intros D i. induction i; intros q0 val c k H0 Hi Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hi as [H1 H2];
         rewrite (IHi1 q0 _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) H1 Hval),
                 (IHi2 q0 _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) H2 Hval); reflexivity);
    try (apply (IHi q0 _ _ _ H0 Hi Hval));
    nat_bool_hyps.
  - destruct (Nat.ltb_spec x c); [| destruct (Nat.eqb_spec x c)]; cbn; apply Nat.eqb_neq;
      try lia; subst x; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.eqb_spec b c); [subst b; unfold lift_cidx; eapply cidx_uses_kinds_ren_tvar_gen with (k := k); [intros y Hy; unfold ren_lift; destruct (Nat.ltb_spec y 0); cbn; lia | exact Hval] |].
    destruct (Nat.ltb_spec b c); cbn; apply Nat.eqb_neq; lia.
  - destruct (Nat.ltb_spec p c); [| destruct (Nat.eqb_spec p c)]; cbn; apply Nat.eqb_neq;
      try lia; subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec p c); [| destruct (Nat.eqb_spec p c)]; cbn; apply Nat.eqb_neq;
      try lia; subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite lift_cidx_add. cbn [Nat.add].
    pose proof (IHi1 q0 val (S c) k ltac:(lia) H2 Hval) as Hi1'.
    pose proof (IHi2 q0 val (S c) k ltac:(lia) H3 Hval) as Hi2'.
    rewrite Nat.add_succ_l in Hi1', Hi2'. rewrite Hi1', Hi2'.
    replace ((if s <? c then s else if s =? c then 0 else s - 1) =? c + k) with false; [reflexivity |].
    symmetry. apply Nat.eqb_neq. destruct (Nat.ltb_spec s c); [| destruct (Nat.eqb_spec s c)]; try lia.
    subst s. destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz]; [| lia].
    specialize (H0 Hz). cbn in H0. apply orb_false_iff in H0 as [H01 _].
    apply orb_false_iff in H01 as [H01 _]. apply Nat.eqb_neq in H01. lia.
Qed.

Lemma cty_uses_kinds_tvar_subst_box_nat_0 : forall (D : JoinDomain) (T : cty D) q val k,
  cidx_uses_kinds false false false false false k val = false ->
  (k = 0 -> cty_uses_kinds false false false true false false false 0 T = false) ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (subst_box_nat_cty 0 q val T) = false.
Proof.
  intros D T q val k Hval HT0 HT.
  assert (Hgen : forall (T0 : cty D) c val0,
    cidx_uses_kinds false false false false false k val0 = false ->
    (c + k = 0 -> cty_uses_kinds false false false true false false false 0 T0 = false) ->
    cty_uses_kinds false true false false false false false (S (c + k)) T0 = false ->
    cty_uses_kinds false true false false false false false (c + k) (subst_box_nat_cty c q (lift_cidx 0 c val0) T0) = false).
  { intro T0. induction T0 using cty_ind_nested; intros c val0 Hv H0 Hsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ Hv H0 Hsk));
      try (apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
                   (IHT0_2 _ _ Hv (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2); reflexivity).
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (cidx_uses_kinds_tvar_subst_box_nat _ _ _ _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2 Hv).
      reflexivity.
    - nat_bool_hyps. destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
        try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
        [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) val0 Hv ltac:(lia) Hk2) as H2.
      rewrite (lift_cidx_add D 1 c val0). exact H2.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) val0 Hv ltac:(lia) Hk2) as H2.
      rewrite (lift_cidx_add D 1 c val0). exact H2.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IHf Htl (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (cidx_uses_kinds_tvar_subst_box_nat _ _ _ _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1 Hv),
              (IH (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity. }
  pose proof (Hgen T 0 val Hval HT0 HT) as H0.
  cbn [Nat.add] in H0. rewrite lift_cidx_0_0 in H0. exact H0.
Qed.

Lemma cty_uses_kinds_tvar_subst_box_ty_0 : forall (D : JoinDomain) (T U : cty D) q k,
  cty_uses_kinds false true false false false false false k U = false ->
  (k = 0 -> cty_uses_kinds false false true false false false false 0 T = false) ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (subst_box_ty_cty 0 q U T) = false.
Proof.
  intros D T U q k HU HT0 HT.
  assert (Hgen : forall (T0 : cty D) c U0,
    cty_uses_kinds false true false false false false false k U0 = false ->
    (c + k = 0 -> cty_uses_kinds false false true false false false false 0 T0 = false) ->
    cty_uses_kinds false true false false false false false (S (c + k)) T0 = false ->
    cty_uses_kinds false true false false false false false (c + k) (subst_box_ty_cty c q (lift_cty 0 c U0) T0) = false).
  { intro T0. induction T0 using cty_ind_nested; intros c U0 Hu H0 Hsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ Hu H0 Hsk));
      try (apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT0_1 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
                   (IHT0_2 _ _ Hu (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2); reflexivity).
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (cidx_uses_kinds_tvar_subst_tvar _ _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2).
      reflexivity.
    - nat_bool_hyps. destruct (Nat.eqb_spec b c).
      + subst b. cbn. unfold lift_cty. eapply cty_uses_kinds_tvar_ren_gen with (k := k); [| exact Hu].
        intros y Hy. unfold ren_lift. destruct (Nat.ltb_spec y 0); cbn; lia.
      + destruct (Nat.ltb_spec b c); cbn; apply Nat.eqb_neq; lia.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) U0 Hu ltac:(lia) Hk2) as H2.
      rewrite (lift_cty_add D 1 c U0). exact H2.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1).
      pose proof (IHT0_2 (S c) U0 Hu ltac:(lia) Hk2) as H2.
      rewrite (lift_cty_add D 1 c U0). exact H2.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ Hu (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IHf Htl (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (cidx_uses_kinds_tvar_subst_tvar _ _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) Hk1),
              (IH (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) Hk2). reflexivity. }
  pose proof (Hgen T 0 U HU HT0 HT) as H0.
  cbn [Nat.add] in H0. rewrite lift_cty_0_0 in H0. exact H0.
Qed.

Lemma cidx_uses_kinds_tvar_subst_sum : forall (D : JoinDomain) (i : cidx D) is_left val c k,
  (c + k = 0 -> cidx_uses_kinds false false false false true 0 i = false) ->
  (c + k = 0 -> cidx_case_branch_nat is_left 0 i = true) ->
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false k val = false ->
  cidx_uses_kinds false false false false false (c + k) (subst_sum_cidx is_left c (lift_cidx 0 c val) i) = false.
Proof.
  intros D i is_left. induction i; intros val c k H0 Hbr0 Hi Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hi as [H1 H2];
         rewrite (IHi1 _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr0 Hz))) H1 Hval),
                 (IHi2 _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj2 (andb_prop _ _ (Hbr0 Hz))) H2 Hval); reflexivity);
    try (apply (IHi _ _ _ H0 Hbr0 Hi Hval));
    nat_bool_hyps.
  - destruct (Nat.ltb_spec x c); [| destruct (Nat.eqb_spec x c)]; cbn; apply Nat.eqb_neq;
      try lia; subst x; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
      try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec p c); [| destruct (Nat.eqb_spec p c)]; cbn; apply Nat.eqb_neq;
      try lia; subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - destruct (Nat.ltb_spec p c); [| destruct (Nat.eqb_spec p c)]; cbn; apply Nat.eqb_neq;
      try lia; subst p; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
      [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
  - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    destruct (Nat.eqb_spec s c).
    + subst s.
      assert (Hbr : cidx_uses_kinds false false false false false (S (c + k))
                      (subst_sum_cidx is_left (S c) (lift_cidx 0 1 (lift_cidx 0 c val)) (if is_left then i1 else i2)) = false).
      { rewrite lift_cidx_add. cbn [Nat.add].
        destruct is_left; [apply (IHi1 val (S c) k ltac:(lia) ltac:(lia) H2 Hval) | apply (IHi2 val (S c) k ltac:(lia) ltac:(lia) H3 Hval)]. }
      fold (lift_cidx 0 c val).
      rewrite <- (lift_cidx_0_0 (lift_cidx 0 c val)) at 1.
      apply (cidx_uses_kinds_tvar_subst_cidx D _ (lift_cidx 0 c val) 0 (c + k)); [| exact Hbr |].
      * intro Hzk. specialize (H0 Hzk); specialize (Hbr0 Hzk).
        assert (Hc0 : c = 0) by lia; assert (Hk0 : k = 0) by lia; subst c k.
        cbn in H0, Hbr0. apply orb_false_iff in H0 as [H01 H02].
        apply andb_true_iff in Hbr0 as [B12 B3]; apply andb_true_iff in B12 as [B0 B2].
        apply negb_true_iff in B0.
        assert (Hc_pres : forall (u v : cidx D) b0 c0,
          b0 < c0 ->
          cidx_uses_kinds true false false false false b0 u = false ->
          cidx_uses_kinds true false false false true c0 u = false ->
          cidx_case_branch_nat is_left c0 u = true ->
          cidx_uses_kinds true false false false false b0 v = false ->
          cidx_uses_kinds true false false false false b0 (subst_sum_cidx is_left c0 v u) = false).
        { clear.
          assert (Hren_zero : forall (v0 : cidx D) d r,
            (forall x, r x = d -> False) ->
            cidx_uses_kinds true false false false false d (ren_cidx r v0) = false).
          { intro v0. induction v0; intros d r Hr; cbn in *; try reflexivity;
              try (rewrite (IHv0_1 _ _ Hr), (IHv0_2 _ _ Hr); reflexivity);
              try (apply (IHv0 _ _ Hr));
              try (apply Nat.eqb_neq; intro Heq; exact (Hr _ Heq)).
            assert (Hrs : forall x, ren_shift r x = S d -> False) by
              (intros [| x'] Hx; unfold ren_shift in Hx; [discriminate | injection Hx; exact (Hr x')]).
            rewrite (IHv0_1 _ _ Hrs), (IHv0_2 _ _ Hrs).
            replace (r s =? d) with false by (symmetry; apply Nat.eqb_neq; intro Heq; exact (Hr s Heq)).
            reflexivity. }
          intros u. induction u; intros v b0 c0 Hpos H0u Hcu Hbu Hv0; cbn in *; try reflexivity;
            try (apply orb_false_iff in H0u as [A1 A2]; apply orb_false_iff in Hcu as [C1 C2];
                 apply andb_true_iff in Hbu as [D1 D2];
                 rewrite (IHu1 v b0 c0 Hpos A1 C1 D1 Hv0), (IHu2 v b0 c0 Hpos A2 C2 D2 Hv0); reflexivity);
            try (apply (IHu v b0 c0 Hpos H0u Hcu Hbu Hv0)).
          { destruct (b <? c0) eqn:Eb1; cbn; [exact H0u | destruct (b =? c0) eqn:Eb2; cbn; [discriminate Hcu | apply Nat.ltb_ge in Eb1; apply Nat.eqb_neq in Eb2; apply Nat.eqb_neq; lia]]. }
          { destruct (p <? c0) eqn:Ep1; cbn; [exact H0u | destruct (p =? c0) eqn:Ep2; cbn; [discriminate Hcu | apply Nat.ltb_ge in Ep1; apply Nat.eqb_neq in Ep2; apply Nat.eqb_neq; lia]]. }
          { destruct (p <? c0) eqn:Ep1; cbn; [exact H0u | destruct (p =? c0) eqn:Ep2; cbn; [discriminate Hcu | apply Nat.ltb_ge in Ep1; apply Nat.eqb_neq in Ep2; apply Nat.eqb_neq; lia]]. }
          apply orb_false_iff in H0u as [A12 A3]; apply orb_false_iff in A12 as [A1 A2].
          apply orb_false_iff in Hcu as [C2 C3].
          apply andb_true_iff in Hbu as [D12 D3]; apply andb_true_iff in D12 as [D0u D2'].
          destruct (s =? c0) eqn:Es_c0; cbn in *.
          - apply negb_true_iff in D0u.
            assert (Hlv_s : cidx_uses_kinds true false false false false (S b0) (lift_cidx 0 1 v) = false) by
              (unfold lift_cidx; eapply cidx_uses_kinds_ren_any with (k := b0); [intros y Hy; unfold ren_lift in Hy; destruct (y <? 0) eqn:Ey; [apply Nat.ltb_lt in Ey |]; lia | exact Hv0]).
            eapply cidx_uses_kinds_subst_cidx_ge; [lia | | | exact Hv0].
            + intro Hb0; subst b0.
              assert (Hlv_0 : cidx_uses_kinds true false false false false 0 (lift_cidx 0 1 v) = false) by
                (unfold lift_cidx; apply Hren_zero; intros y Hy; unfold ren_lift in Hy; destruct (y <? 0) eqn:Ey; [apply Nat.ltb_lt in Ey |]; lia).
              destruct is_left;
                [apply (IHu1 (lift_cidx 0 1 v) 0 (S c0) ltac:(lia) D0u C2 D2' Hlv_0)
                |apply (IHu2 (lift_cidx 0 1 v) 0 (S c0) ltac:(lia) D0u C3 D3 Hlv_0)].
            + destruct is_left;
                [apply (IHu1 (lift_cidx 0 1 v) (S b0) (S c0) ltac:(lia) A2 C2 D2' Hlv_s)
                |apply (IHu2 (lift_cidx 0 1 v) (S b0) (S c0) ltac:(lia) A3 C3 D3 Hlv_s)].
          - apply Nat.eqb_neq in Es_c0 as Hne.
            assert (Hlv_s : cidx_uses_kinds true false false false false (S b0) (lift_cidx 0 1 v) = false) by
              (unfold lift_cidx; eapply cidx_uses_kinds_ren_any with (k := b0); [intros y Hy; unfold ren_lift in Hy; destruct (y <? 0) eqn:Ey; [apply Nat.ltb_lt in Ey |]; lia | exact Hv0]).
            destruct (s <? c0) eqn:Es1; cbn;
              [rewrite (IHu1 (lift_cidx 0 1 v) (S b0) (S c0) ltac:(lia) A2 C2 D2' Hlv_s),
                       (IHu2 (lift_cidx 0 1 v) (S b0) (S c0) ltac:(lia) A3 C3 D3 Hlv_s), A1; reflexivity
              |rewrite (IHu1 (lift_cidx 0 1 v) (S b0) (S c0) ltac:(lia) A2 C2 D2' Hlv_s),
                       (IHu2 (lift_cidx 0 1 v) (S b0) (S c0) ltac:(lia) A3 C3 D3 Hlv_s);
               apply Nat.ltb_ge in Es1; apply Nat.eqb_neq in A1;
               replace (s - 1 =? b0) with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity]. }
        assert (Hc1_t : forall (u : cidx D) n0, cidx_uses_kinds false false false false true n0 u = false -> cidx_uses_kinds true false false false true n0 u = false) by
          (clear; intro u; induction u; intros n0 Hu; cbn in *; try reflexivity;
           try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHu1 _ Hu1), (IHu2 _ Hu2); reflexivity);
           try (apply (IHu _ Hu));
           exact Hu).
        assert (Hc1_f : forall (u : cidx D) n0, cidx_uses_kinds false false false false false n0 u = false -> cidx_uses_kinds true false false false false n0 u = false) by
          (clear; intro u; induction u; intros n0 Hu; cbn in *; try reflexivity;
           try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHu1 _ Hu1), (IHu2 _ Hu2); reflexivity);
           try (apply (IHu _ Hu));
           [ exact Hu | exact Hu | exact Hu
           | apply orb_false_iff in Hu as [H12 Hu3]; apply orb_false_iff in H12 as [Hu1 Hu2];
             rewrite (IHu1 _ Hu2), (IHu2 _ Hu3), Hu1; reflexivity ]).
        assert (Hlv : cidx_uses_kinds true false false false false 0 (lift_cidx 0 1 val) = false) by
          (unfold lift_cidx; eapply cidx_uses_kinds_ren_any with (k := 0); [intros y Hy; unfold ren_lift in Hy; destruct (y <? 0) eqn:Ey; [apply Nat.ltb_lt in Ey |]; lia | exact (Hc1_f _ _ Hval)]).
        fold (lift_cidx 0 0 val). rewrite lift_cidx_0_0.
        destruct is_left;
          [apply (Hc_pres _ _ 0 1); [lia | exact B0 | apply Hc1_t; exact H01 | exact B2 | exact Hlv]
          |apply (Hc_pres _ _ 0 1); [lia | exact B0 | apply Hc1_t; exact H02 | exact B3 | exact Hlv]].
      * unfold lift_cidx; eapply cidx_uses_kinds_ren_tvar_gen with (k := k); [intros y Hy; unfold ren_lift; destruct (Nat.ltb_spec y 0); cbn; lia | exact Hval].
    + cbn. rewrite lift_cidx_add. cbn [Nat.add].
      pose proof (IHi1 val (S c) k ltac:(lia) ltac:(lia) H2 Hval) as Hi1'.
      pose proof (IHi2 val (S c) k ltac:(lia) ltac:(lia) H3 Hval) as Hi2'.
      rewrite Nat.add_succ_l in Hi1', Hi2'. rewrite Hi1', Hi2'.
      replace ((if s <? c then s else s - 1) =? c + k) with false; [reflexivity |].
      symmetry. apply Nat.eqb_neq. destruct (Nat.ltb_spec s c); lia.
Qed.

Lemma cty_uses_kinds_tvar_subst_sum_0 : forall (D : JoinDomain) (T : cty D) is_left val k,
  cidx_uses_kinds false false false false false k val = false ->
  (k = 0 -> cty_uses_kinds false false false false false false true 0 T = false) ->
  (k = 0 -> cty_case_branch_nat is_left 0 T = true) ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (subst_sum_cty is_left 0 val T) = false.
Proof.
  intros D T is_left val k Hval HT0 Hbr0 HT.
  assert (Hgen : forall (T0 : cty D) c val0,
    cidx_uses_kinds false false false false false k val0 = false ->
    (c + k = 0 -> cty_uses_kinds false false false false false false true 0 T0 = false) ->
    (c + k = 0 -> cty_case_branch_nat is_left 0 T0 = true) ->
    cty_uses_kinds false true false false false false false (S (c + k)) T0 = false ->
    cty_uses_kinds false true false false false false false (c + k) (subst_sum_cty is_left c (lift_cidx 0 c val0) T0) = false).
  { intro T0. induction T0 using cty_ind_nested; intros c val0 Hv H0 Hbr Hsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ Hv H0 Hbr Hsk));
      try (apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr Hz))) Hk1),
                   (IHT0_2 _ _ Hv (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj2 (andb_prop _ _ (Hbr Hz))) Hk2); reflexivity).
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr Hz))) Hk1),
              (cidx_uses_kinds_tvar_subst_sum _ _ is_left _ _ _ (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj2 (andb_prop _ _ (Hbr Hz))) Hk2 Hv).
      reflexivity.
    - nat_bool_hyps. destruct (Nat.ltb_spec b c); [| destruct (Nat.eqb_spec b c)]; cbn; apply Nat.eqb_neq;
        try lia; subst b; destruct (Nat.eq_dec (c + k) 0) as [Hz | Hnz];
        [specialize (H0 Hz); cbn in H0; apply Nat.eqb_neq in H0; lia | lia].
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr Hz))) Hk1).
      pose proof (IHT0_2 (S c) val0 Hv ltac:(lia) ltac:(lia) Hk2) as H2.
      rewrite (lift_cidx_add D 1 c val0). exact H2.
    - apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHT0_1 _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr Hz))) Hk1).
      pose proof (IHT0_2 (S c) val0 Hv ltac:(lia) ltac:(lia) Hk2) as H2.
      rewrite (lift_cidx_add D 1 c val0). exact H2.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ Hv (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr Hz))) Hk1),
              (IHf Htl (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj2 (andb_prop _ _ (Hbr Hz))) Hk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (cidx_uses_kinds_tvar_subst_sum _ _ is_left _ _ _ (fun Hz => proj1 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj1 (andb_prop _ _ (Hbr Hz))) Hk1 Hv),
              (IH (fun Hz => proj2 (orb_false_elim _ _ (H0 Hz))) (fun Hz => proj2 (andb_prop _ _ (Hbr Hz))) Hk2). reflexivity. }
  pose proof (Hgen T 0 val Hval HT0 Hbr0 HT) as H0.
  cbn [Nat.add] in H0. rewrite lift_cidx_0_0 in H0. exact H0.
Qed.

Lemma cidx_uses_kinds_spec_box_body_tvar : forall (D : JoinDomain) (i : cidx D) q c k,
  cidx_uses_kinds false false false false false (S (c + k)) i = false ->
  cidx_uses_kinds false false false false false (S (c + k)) (spec_box_body_cidx q c i) = false.
Proof.
  intros D i q. induction i; intros c k Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [Hk1 Hk2];
         rewrite (IHi1 _ _ Hk1), (IHi2 _ _ Hk2); reflexivity);
    try (apply (IHi _ _ Hsk));
    try exact Hsk;
    nat_bool_hyps.
  - destruct (Nat.eqb_spec b c); cbn; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Hsk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2]; nat_bool_hyps.
    pose proof (IHi1 (S c) k Hk2) as Hi1'.
    pose proof (IHi2 (S c) k Hk3) as Hi2'.
    rewrite Nat.add_succ_l in Hi1', Hi2'. rewrite Hi1', Hi2'.
    rewrite (proj2 (Nat.eqb_neq _ _) Hk1). reflexivity.
Qed.

Lemma cty_uses_kinds_spec_box_body_tvar : forall (D : JoinDomain) (T : cty D) q c k,
  cty_uses_kinds false true false false false false false (S (c + k)) T = false ->
  cty_uses_kinds false true false false false false false (S (c + k)) (spec_box_body_cty q c T) = false.
Proof.
  intros D T q. induction T using cty_ind_nested; intros c k Hsk; cbn in *; try reflexivity;
    try (apply (IHT _ _ Hsk));
    try (apply orb_false_iff in Hsk as [Hk1 Hk2];
         rewrite (IHT1 _ _ Hk1), (IHT2 _ _ Hk2); reflexivity).
  - apply orb_false_iff in Hsk as [Hk1 Hk2].
    rewrite (IHT _ _ Hk1), (cidx_uses_kinds_spec_box_body_tvar _ _ q _ _ Hk2). reflexivity.
  - nat_bool_hyps. destruct (Nat.eqb_spec b c); cbn; [reflexivity | apply Nat.eqb_neq; exact Hsk].
  - apply orb_false_iff in Hsk as [Hk1 Hk2].
    pose proof (IHT2 (S c) k Hk2) as HT2'. rewrite Nat.add_succ_l in HT2'.
    rewrite (IHT1 _ _ Hk1), HT2'. reflexivity.
  - apply orb_false_iff in Hsk as [Hk1 Hk2].
    pose proof (IHT2 (S c) k Hk2) as HT2'. rewrite Nat.add_succ_l in HT2'.
    rewrite (IHT1 _ _ Hk1), HT2'. reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsk as [Hk1 Hk2].
    rewrite (Hhd _ _ Hk1), (IHf Htl Hk2). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hsk as [Hk1 Hk2].
    rewrite (cidx_uses_kinds_spec_box_body_tvar _ _ q _ _ Hk1), (IH Hk2). reflexivity.
Qed.

Lemma cidx_uses_kinds_spec_box_body_0 : forall (D : JoinDomain) (i : cidx D) q c,
  cidx_uses_kinds false false false false false c i = false ->
  cidx_uses_kinds false false false false false c (spec_box_body_cidx q c i) = false.
Proof.
  intros D i q. induction i; intros c Hc; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hc as [H1 H2]; rewrite (IHi1 _ H1), (IHi2 _ H2); reflexivity);
    try (apply (IHi _ Hc));
    try exact Hc;
    nat_bool_hyps.
  - destruct (Nat.eqb_spec b c); cbn; [apply Nat.eqb_neq; lia | apply Nat.eqb_neq; exact Hc].
  - apply orb_false_iff in Hc as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite (IHi1 (S c) H2), (IHi2 (S c) H3), (proj2 (Nat.eqb_neq _ _) H1); reflexivity.
Qed.

Lemma cty_uses_kinds_spec_box_body_0 : forall (D : JoinDomain) (T : cty D) q c,
  cty_uses_kinds false false true false false false false c T = false ->
  cty_uses_kinds false true false false false false false c (spec_box_body_cty q c T) = false.
Proof.
  intros D T q. induction T using cty_ind_nested; intros c Hc; cbn in *; try reflexivity;
    try (apply (IHT _ Hc));
    try (apply orb_false_iff in Hc as [H1 H2]; rewrite (IHT1 _ H1), (IHT2 _ H2); reflexivity).
  - apply orb_false_iff in Hc as [H1 H2].
    rewrite (IHT _ H1), (cidx_uses_kinds_spec_box_body_0 _ _ q _ H2); reflexivity.
  - nat_bool_hyps. destruct (Nat.eqb_spec b c) as [-> | Hne]; cbn; [reflexivity | apply Nat.eqb_neq; exact Hne].
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hc as [H1 H2].
    rewrite (Hhd _ H1), (IHf Htl H2); reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hc as [H1 H2].
    rewrite (cidx_uses_kinds_spec_box_body_0 _ _ q _ H1), (IH H2); reflexivity.
Qed.

Lemma cty_uses_kinds_tvar_ren_two : forall (D : JoinDomain) (T : cty D) rn d k c,
  (forall x, x <> d -> x <> k -> rn x <> c) ->
  cty_uses_kinds false true false false false false false d T = false ->
  cty_uses_kinds false true false false false false false k T = false ->
  cty_uses_kinds false true false false false false false c (ren_cty rn T) = false.
Proof.
  assert (Hi : forall (D : JoinDomain) (i : cidx D) rn d k c,
    (forall x, x <> d -> x <> k -> rn x <> c) ->
    cidx_uses_kinds false false false false false d i = false ->
    cidx_uses_kinds false false false false false k i = false ->
    cidx_uses_kinds false false false false false c (ren_cidx rn i) = false).
  { intros D i. induction i; intros rn d k c Hr Hd Hk; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2];
           rewrite (IHi1 _ _ _ _ Hr Hd1 Hk1), (IHi2 _ _ _ _ Hr Hd2 Hk2); reflexivity);
      try (apply (IHi _ _ _ _ Hr Hd Hk));
      nat_bool_hyps;
      try (apply Nat.eqb_neq; apply Hr; assumption).
    apply orb_false_iff in Hd as [Hd12 Hd3]; apply orb_false_iff in Hd12 as [Hd1 Hd2].
    apply orb_false_iff in Hk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2]; nat_bool_hyps.
    assert (Hrs : forall x, x <> S d -> x <> S k -> ren_shift rn x <> S c) by
      (intros [| x'] Hxd Hxk; unfold ren_shift; [lia | intro Heq; apply (Hr x' ltac:(lia) ltac:(lia)); lia]).
    rewrite (IHi1 _ _ _ _ Hrs Hd2 Hk2), (IHi2 _ _ _ _ Hrs Hd3 Hk3).
    replace (rn s =? c) with false by (symmetry; apply Nat.eqb_neq; apply Hr; assumption); reflexivity. }
  intros D T. induction T using cty_ind_nested; intros rn d k c Hr Hd Hk; cbn in *; try reflexivity;
    try (apply (IHT _ _ _ _ Hr Hd Hk));
    try (apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2];
         rewrite (IHT1 _ _ _ _ Hr Hd1 Hk1), (IHT2 _ _ _ _ Hr Hd2 Hk2); reflexivity).
  - apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    rewrite (IHT _ _ _ _ Hr Hd1 Hk1), (Hi D len _ _ _ _ Hr Hd2 Hk2); reflexivity.
  - nat_bool_hyps; apply Nat.eqb_neq; apply Hr; assumption.
  - apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    assert (Hrs : forall x, x <> S d -> x <> S k -> ren_shift rn x <> S c) by
      (intros [| x'] Hxd Hxk; unfold ren_shift; [lia | intro Heq; apply (Hr x' ltac:(lia) ltac:(lia)); lia]).
    rewrite (IHT1 _ _ _ _ Hr Hd1 Hk1), (IHT2 _ _ _ _ Hrs Hd2 Hk2); reflexivity.
  - apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    assert (Hrs : forall x, x <> S d -> x <> S k -> ren_shift rn x <> S c) by
      (intros [| x'] Hxd Hxk; unfold ren_shift; [lia | intro Heq; apply (Hr x' ltac:(lia) ltac:(lia)); lia]).
    rewrite (IHT1 _ _ _ _ Hr Hd1 Hk1), (IHT2 _ _ _ _ Hrs Hd2 Hk2); reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    rewrite (Hhd _ _ _ _ Hr Hd1 Hk1), (IHf Htl Hd2 Hk2); reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hd as [Hd1 Hd2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    rewrite (Hi D idx _ _ _ _ Hr Hd1 Hk1), (IH Hd2 Hk2); reflexivity.
Qed.

Lemma subst_sum_cty_no_use : forall (D : JoinDomain) (T : cty D) is_left c v1 v2,
  cty_uses_var c T = false ->
  subst_sum_cty is_left c v1 T = subst_sum_cty is_left c v2 T.
Proof.
  assert (Hi : forall (D : JoinDomain) (i : cidx D) is_left c v1 v2,
    cidx_uses_var c i = false ->
    subst_sum_cidx is_left c v1 i = subst_sum_cidx is_left c v2 i).
  { intros D i is_left. induction i; intros c v1 v2 Hi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 c v1 v2 H1), (IHi2 c v1 v2 H2); reflexivity);
      try (f_equal; apply (IHi c v1 v2 Hi)).
    apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
    rewrite H1. f_equal; [apply (IHi1 (S c) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H2) | apply (IHi2 (S c) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H3)]. }
  intros D T is_left. induction T using cty_ind_nested; intros c v1 v2 HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT c v1 v2 HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 c v1 v2 H1), (IHT2 c v1 v2 H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT c v1 v2 H1), (Hi D len is_left c v1 v2 H2); reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 c v1 v2 H1), (IHT2 (S c) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H2); reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 c v1 v2 H1), (IHT2 (S c) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H2); reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT as [H1 H2].
    rewrite (Hhd c v1 v2 H1), (IHf Htl H2); reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 H2]. rewrite (Hi D idx is_left c v1 v2 H1), (IH H2); reflexivity.
Qed.

Lemma cty_uses_kinds_tvar_unshift_0 : forall (D : JoinDomain) (T : cty D) k,
  cty_uses_var 0 T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false k (unshift_cty 0 T) = false.
Proof.
  intros D T k H0 HT. unfold unshift_cty.
  change (ren_cty (Nat.iter 0 ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) T) with (ren_cty (r_var 0 0) T).
  rewrite (ren_cty_r_var_no_use D T 0 0 (S (S k)) H0).
  eapply cty_uses_kinds_tvar_ren_gen with (k := S k); [| exact HT].
  intros [| z] Hz; [rewrite r_var_eq; lia | rewrite r_var_gt by lia; lia].
Qed.

Lemma core_derives_tvar_safe : forall (D : JoinDomain) (b : cbinding D) env_b lvl_b,
  cannotation b = CUniv lvl_b ->
  forall env t j, CoreDerives env t j ->
    forall env_a, env = env_a ++ b :: env_b ->
    cty_uses_kinds false true false false false false false (length env_a) (cresult_type j) = false.
Proof.
  intros D b env_b lvl_b Hb env t j H.
  induction H using CoreDerives_ind_mut with
    (P := fun env t j _ => forall env_a, env = env_a ++ b :: env_b ->
      cty_uses_kinds false true false false false false false (length env_a) (cresult_type j) = false)
    (P0 := fun env fs u v _ => True);
    try (intros env_a Henv; subst env; cbn [cresult_type]); try reflexivity; try exact I.
  - (* CoreVar *)
    lazymatch goal with
    | Hl : clookup _ x = Some e, Htd : CTypeDemand _ (cannotation e) row |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | ->] | Hgt];
        [ rewrite skipn_app in Htd;
          replace (S x - length env_a) with 0 in Htd by lia; cbn [skipn] in Htd;
          pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd (skipn (S x) env_a) eq_refl) as He;
          rewrite length_skipn in He;
          replace (length env_a) with (S x + (length env_a - S x)) by lia;
          apply cty_uses_kinds_tvar_ren_plus; exact He
        | unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia;
          inversion Hl; subst e; rewrite Hb; cbn; reflexivity
        | apply cty_uses_kinds_tvar_ren_gt; lia ]
    end.
  - (* CoreLam *)
    lazymatch goal with
    | Ha : CTypeDemand _ dom a |- _ =>
        pose proof (IHCoreDerives ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) eq_refl) as Hcod;
        cbn [length cresult_type] in Hcod;
        cbn; rewrite (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Ha env_a eq_refl), Hcod; reflexivity
    end.
  - (* CoreApp *)
    lazymatch goal with
    | Ha_dom : CTypeDemand _ dom a_dom, Hb_cod : CTypeDemand _ cod b0,
      Hdm_eq : cty_alpha_eq kind dom,
      Happ : app_result_ty dom cod arg = Some res_ty |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hb_cod ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) eq_refl) as Hcod_s;
        cbn [length] in Hcod_s;
        unfold app_result_ty in Happ;
        destruct dom;
        try (destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst res_ty; apply cty_uses_kinds_tvar_unshift_0; [exact Enf | exact Hcod_s]);
        [ destruct arg; cbn in Happ;
          try (destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst res_ty; apply cty_uses_kinds_tvar_unshift_0; [exact Enf | exact Hcod_s]);
          [ inversion Happ; subst res_ty;
            apply cty_uses_kinds_tvar_subst_cidx_0;
            [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
              [ exfalso; inversion H0; subst;
                lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
                  inversion Hlk; subst ee; unfold cty_alpha_eq in Hdm_eq; rewrite erase_hints_ren, Hb in Hdm_eq; cbn in Hdm_eq; discriminate
                end
              | cbn; apply Nat.eqb_neq; exact Hne ]
            | intros _; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ]
          | inversion Happ; subst res_ty; inversion H0; subst;
            apply cty_uses_kinds_tvar_subst_cidx_0;
            [ lazymatch goal with Hc : CIdxDemand _ _ _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hc env_a eq_refl) end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ] ]
        | destruct arg; cbn in Happ;
          try (destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst res_ty; apply cty_uses_kinds_tvar_unshift_0; [exact Enf | exact Hcod_s]);
          [ inversion Happ; subst res_ty;
            apply cty_uses_kinds_tvar_subst_tvar_0;
            [ cbn; reflexivity
            | intros _; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ]
          | inversion Happ; subst res_ty; inversion H0; subst;
            apply cty_uses_kinds_tvar_subst_tvar_0;
            [ lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) _ _ |- _ =>
                exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd env_a eq_refl)
              end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ] ] ]
    end.
  - (* CLet *)
    pose proof (IHCoreDerives2 (_ :: env_a) eq_refl) as Hbod_s.
    cbn [cresult_type length] in Hbod_s.
    apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hbod_s].
  - (* CPair *)
    lazymatch goal with
    | Ha : CTypeDemand _ fst_ty a, Hb_snd : CTypeDemand _ snd_ty b0 |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hb_snd ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) eq_refl) as Hsnd;
        cbn [length] in Hsnd;
        cbn; rewrite (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Ha env_a eq_refl), Hsnd; reflexivity
    end.
  - (* CLetPair *)
    lazymatch goal with
    | Hres : ?res_ty = spec_pair_subj_cty ?pr ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; pose proof Hmot as Hmot_saved; destruct pr; unfold spec_pair_subj_cty
    end;
    try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
    [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
      [ exfalso;
        lazymatch goal with Hdv : CoreDerives _ (CVar _) {| cresult_type := CSigma _ _ _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
          inversion Hdv; subst;
          lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSigma _ _ _ _ |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
            inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
          end
        end
      | unfold subst_var_in_cty; eapply cty_uses_kinds_tvar_ren_gen with (k := S (length env_a)); [| exact Hm_s];
        intros [| z0] Hz0; cbn; lia ]
    | destruct (term_as_cidx pr1) as [c1_idx |] eqn:E1; [destruct (term_as_cidx pr2) as [c2_idx |] eqn:E2 |];
      try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
      lazymatch goal with Hpr : CoreDerives _ (CPair _ _ _ _ _ _) _ |- _ => inversion Hpr; subst end;
      assert (Hc_pair : forall c1_i c2_i,
        (erase_hints A = CNat -> cidx_uses_kinds false false false false false (length env_a) c1_i = false) ->
        (erase_hints B = CNat -> cidx_uses_kinds false false false false false (length env_a) c2_i = false) ->
        cty_uses_kinds false true false false false false false (length env_a) (subst_pair_cty 0 c1_i c2_i mot) = false);
      [ intros c1_i c2_i Hfc1 Hfc2;
        assert (Hnf1 : erase_hints A <> CNat ->
          forall (T0 : cty D) c (fi1 fi2 si0 : cidx D),
            cty_uses_kinds false false false false false true false c T0 = false ->
            subst_pair_cty c fi1 si0 T0 = subst_pair_cty c fi2 si0 T0);
        [ clear - Hmot_saved; intros _;
          assert (Hi_nf : forall (i : cidx D) c fi1 fi2 si0,
            cidx_uses_kinds false false false true false c i = false ->
            subst_pair_cidx c fi1 si0 i = subst_pair_cidx c fi2 si0 i) by
            (intro i; induction i; intros c fi1 fi2 si0 Hi; cbn in *; try reflexivity;
             try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ fi1 fi2 si0 H1), (IHi2 _ fi1 fi2 si0 H2); reflexivity);
             try (f_equal; apply (IHi _ fi1 fi2 si0 Hi));
             nat_bool_hyps; try (destruct (Nat.eqb_spec p c); [lia | reflexivity]);
             apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2];
             rewrite (IHi1 _ (lift_cidx 0 1 fi1) (lift_cidx 0 1 fi2) (lift_cidx 0 1 si0) H2),
                     (IHi2 _ (lift_cidx 0 1 fi1) (lift_cidx 0 1 fi2) (lift_cidx 0 1 si0) H3); reflexivity);
          intro T0; induction T0 using cty_ind_nested; intros c fi1 fi2 si0 HT; cbn in *; try reflexivity;
            try (f_equal; apply (IHT0 _ fi1 fi2 si0 HT));
            try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT0_1 _ fi1 fi2 si0 H1), (IHT0_2 _ fi1 fi2 si0 H2); reflexivity);
            [ apply orb_false_iff in HT as [H1 H2]; rewrite (IHT0 _ fi1 fi2 si0 H1), (Hi_nf len _ fi1 fi2 si0 H2); reflexivity
            | apply orb_false_iff in HT as [H1 H2]; f_equal; [apply (IHT0_1 _ fi1 fi2 si0 H1) | apply (IHT0_2 _ (lift_cidx 0 1 fi1) (lift_cidx 0 1 fi2) (lift_cidx 0 1 si0) H2)]
            | apply orb_false_iff in HT as [H1 H2]; f_equal; [apply (IHT0_1 _ fi1 fi2 si0 H1) | apply (IHT0_2 _ (lift_cidx 0 1 fi1) (lift_cidx 0 1 fi2) (lift_cidx 0 1 si0) H2)]
            | f_equal; induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |];
              inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd; apply orb_false_iff in HT as [H1 H2t];
              rewrite (Hhd _ fi1 fi2 si0 H1), (IHf Htl H2t); reflexivity
            | f_equal; induction indices as [| idx rest IH]; cbn in *; [reflexivity |];
              apply orb_false_iff in HT as [H1 H2t]; rewrite (Hi_nf idx _ fi1 fi2 si0 H1), (IH H2t); reflexivity ]
        |];
        assert (Hnf2 : erase_hints B <> CNat ->
          forall (T0 : cty D) c (fi0 si1 si2 : cidx D),
            cty_uses_kinds false false false false true false true c T0 = false ->
            subst_pair_cty c fi0 si1 T0 = subst_pair_cty c fi0 si2 T0);
        [ clear - Hmot_saved; intros _;
          assert (Hi_nf : forall (i : cidx D) c fi0 si1 si2,
            cidx_uses_kinds false false true false true c i = false ->
            subst_pair_cidx c fi0 si1 i = subst_pair_cidx c fi0 si2 i) by
            (intro i; induction i; intros c fi0 si1 si2 Hi; cbn in *; try reflexivity;
             try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ fi0 si1 si2 H1), (IHi2 _ fi0 si1 si2 H2); reflexivity);
             try (f_equal; apply (IHi _ fi0 si1 si2 Hi));
             nat_bool_hyps; try (destruct (Nat.eqb_spec p c); [lia | reflexivity]);
             apply orb_false_iff in Hi as [H2 H3];
             rewrite (IHi1 _ (lift_cidx 0 1 fi0) (lift_cidx 0 1 si1) (lift_cidx 0 1 si2) H2),
                     (IHi2 _ (lift_cidx 0 1 fi0) (lift_cidx 0 1 si1) (lift_cidx 0 1 si2) H3); reflexivity);
          intro T0; induction T0 using cty_ind_nested; intros c fi0 si1 si2 HT; cbn in *; try reflexivity;
            try (f_equal; apply (IHT0 _ fi0 si1 si2 HT));
            try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT0_1 _ fi0 si1 si2 H1), (IHT0_2 _ fi0 si1 si2 H2); reflexivity);
            [ apply orb_false_iff in HT as [H1 H2]; rewrite (IHT0 _ fi0 si1 si2 H1), (Hi_nf len _ fi0 si1 si2 H2); reflexivity
            | apply orb_false_iff in HT as [H1 H2]; f_equal; [apply (IHT0_1 _ fi0 si1 si2 H1) | apply (IHT0_2 _ (lift_cidx 0 1 fi0) (lift_cidx 0 1 si1) (lift_cidx 0 1 si2) H2)]
            | apply orb_false_iff in HT as [H1 H2]; f_equal; [apply (IHT0_1 _ fi0 si1 si2 H1) | apply (IHT0_2 _ (lift_cidx 0 1 fi0) (lift_cidx 0 1 si1) (lift_cidx 0 1 si2) H2)]
            | f_equal; induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |];
              inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd; apply orb_false_iff in HT as [H1 H2t];
              rewrite (Hhd _ fi0 si1 si2 H1), (IHf Htl H2t); reflexivity
            | f_equal; induction indices as [| idx rest IH]; cbn in *; [reflexivity |];
              apply orb_false_iff in HT as [H1 H2t]; rewrite (Hi_nf idx _ fi0 si1 si2 H1), (IH H2t); reflexivity ]
        |];
        assert (Hc1_ex : exists c1', subst_pair_cty 0 c1_i c2_i mot = subst_pair_cty 0 c1' c2_i mot /\
          cidx_uses_kinds false false false false false (length env_a) c1' = false) by
          (destruct (erase_hints A) eqn:Efst;
           only 1: (exists c1_i; split; [reflexivity | exact (Hfc1 eq_refl)]);
           (exists (CIdxLit 0); split; [| reflexivity];
            apply Hnf1; [congruence |];
            eapply ctype_demand_uses_kinds;
            [exact Hmot_saved | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; rewrite Efst; destruct (erase_hints B); cbn; try reflexivity; exact I]));
        destruct Hc1_ex as [c1' [Heqc1 Hc1']]; rewrite Heqc1;
        assert (Hc2_ex : exists c2', subst_pair_cty 0 c1' c2_i mot = subst_pair_cty 0 c1' c2' mot /\
          cidx_uses_kinds false false false false false (length env_a) c2' = false) by
          (destruct (erase_hints B) eqn:Esnd;
           only 1: (exists c2_i; split; [reflexivity | exact (Hfc2 eq_refl)]);
           (exists (CIdxLit 0); split; [| reflexivity];
            apply Hnf2; [congruence |];
            eapply ctype_demand_uses_kinds;
            [exact Hmot_saved | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; rewrite Esnd; destruct (erase_hints A); cbn; try reflexivity; exact I]));
        destruct Hc2_ex as [c2' [Heqc2 Hc2']]; rewrite Heqc2;
        apply cty_uses_kinds_tvar_subst_pair_0;
        [ exact Hc1'
        | exact Hc2'
        | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSigma; [apply cty_alpha_eq_refl | reflexivity | reflexivity]]
        | exact Hm_s ]
      | apply Hc_pair;
        [ intro Ef; destruct pr1; cbn in E1; try discriminate; inversion E1; subst;
          [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
            [ exfalso; lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                inversion Hdv; subst;
                lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : cty_alpha_eq _ ?ft, Hef : erase_hints ?ft = CNat |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                  unfold cty_alpha_eq in Heq; rewrite erase_hints_ren, Hb, Hef in Heq; cbn in Heq; discriminate
                end
              end
            | cbn; apply Nat.eqb_neq; exact Hne ]
          | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
              inversion Hdv; subst;
              lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) end
            end ]
        | intro Es; destruct pr2; cbn in E2; try discriminate; inversion E2; subst;
          [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
            [ exfalso; lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                inversion Hdv; subst;
                lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : cty_alpha_eq _ ?exp_s |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                  unfold cty_alpha_eq in Heq; rewrite erase_hints_ren, Hb in Heq; cbn in Heq;
                  lazymatch goal with
                  | Hst : app_result_ty ?ft ?st ?p1 = Some ?es |- _ =>
                      destruct st; cbn in Es; try discriminate;
                      assert (Hcnat : forall (ft0 : cty D) p0 es0, app_result_ty ft0 CNat p0 = Some es0 -> es0 = CNat) by
                        (intros ft0 p0 es0 Ha0; unfold app_result_ty in Ha0; destruct ft0; cbn in Ha0;
                         try (inversion Ha0; reflexivity);
                         try (destruct (term_as_cidx p0); cbn in Ha0; inversion Ha0; reflexivity);
                         destruct p0; cbn in Ha0; inversion Ha0; reflexivity);
                      apply Hcnat in Hst; subst; cbn in Heq; discriminate
                  end
                end
              end
            | cbn; apply Nat.eqb_neq; exact Hne ]
          | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
              inversion Hdv; subst;
              lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) end
            end ] ] ] ].
  - (* CorePromote *)
    cbn; exact (IHCoreDerives env_a eq_refl).
  - (* CoreLetBox *)
    lazymatch goal with
    | Hres : ?res_ty = spec_box_subj_cty ?box_term ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; pose proof Hmot as Hmot_saved; destruct box_term; unfold spec_box_subj_cty
    end;
    try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
    [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
      [ exfalso;
        lazymatch goal with Hdv : CoreDerives _ (CVar _) {| cresult_type := CBox _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
          inversion Hdv; subst;
          lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CBox _ _ |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
            inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
          end
        end
      | unfold subst_var_in_cty; eapply cty_uses_kinds_tvar_ren_gen with (k := S (length env_a)); [| exact Hm_s];
        intros [| z0] Hz0; cbn; lia ]
    | destruct box_term; try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
      [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
        [ unfold subst_var_in_cty; eapply cty_uses_kinds_tvar_ren_two with (d := 0) (k := S (length env_a));
          [ intros [| z0] Hz0 Hzs; cbn; lia
          | apply cty_uses_kinds_spec_box_body_0;
            eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity |];
            lazymatch goal with Hdp : CoreDerives _ (CPromote _ (CVar _)) {| cresult_type := CBox _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
              inversion Hdp; subst;
              lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                inversion Hdv; subst;
                lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
                  inversion Hlk; subst ee; unfold flags_allow; rewrite erase_hints_ren, Hb; cbn; reflexivity
                end
              end
            end
          | apply (cty_uses_kinds_spec_box_body_tvar D mot _ 0 (length env_a)); exact Hm_s ]
        | unfold subst_var_in_cty; eapply cty_uses_kinds_tvar_ren_gen with (k := S (length env_a));
          [intros [| z0] Hz0; cbn; lia |];
          apply (cty_uses_kinds_spec_box_body_tvar D mot _ 0 (length env_a)); exact Hm_s ]
      | lazymatch goal with Hdp : CoreDerives _ (CPromote _ (CNatVal _)) _ |- _ =>
          inversion Hdp; subst;
          lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
            inversion Hdv; subst;
            apply cty_uses_kinds_tvar_subst_box_nat_0;
            [ lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | unfold flags_allow; cbn; reflexivity]
            | exact Hm_s ]
          end
        end
      | lazymatch goal with Hdp : CoreDerives _ (CPromote _ (CTypeVal _)) _ |- _ =>
          inversion Hdp; subst;
          lazymatch goal with Hdv : CoreDerives _ (CTypeVal ?tt) _ |- _ =>
            inversion Hdv; subst;
            apply cty_uses_kinds_tvar_subst_box_ty_0;
            [ lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) ?tt _ |- _ => exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd env_a eq_refl) end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | unfold flags_allow; cbn; reflexivity]
            | exact Hm_s ]
          end
        end ] ].
  - (* CoreInl *)
    lazymatch goal with
    | Hrhs : CTypeDemand _ rhs_ty ?b0 |- _ =>
        pose proof (IHCoreDerives env_a eq_refl) as HA; cbn [cresult_type] in HA;
        cbn; rewrite HA, (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hrhs env_a eq_refl); reflexivity
    end.
  - (* CoreInr *)
    lazymatch goal with
    | Hlhs : CTypeDemand _ ?lhs_ty ?a0 |- _ =>
        pose proof (IHCoreDerives env_a eq_refl) as HB; cbn [cresult_type] in HB;
        cbn; rewrite (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hlhs env_a eq_refl), HB; reflexivity
    end.
  - (* CoreMatchSum *)
    lazymatch goal with
    | Hres : ?res_ty = spec_sum_subj_cty ?scrut ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; pose proof Hmot as Hmot_saved; destruct scrut; unfold spec_sum_subj_cty
    end;
    try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
    [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
      [ exfalso;
        lazymatch goal with Hdv : CoreDerives _ (CVar _) {| cresult_type := CSum _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
          inversion Hdv; subst;
          lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSum _ _ |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
            inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
          end
        end
      | unfold subst_var_in_cty; eapply cty_uses_kinds_tvar_ren_gen with (k := S (length env_a)); [| exact Hm_s];
        intros [| z0] Hz0; cbn; lia ]
    | destruct (term_as_cidx scrut) as [c_idx |] eqn:Ev; try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
      lazymatch goal with Hsc : CoreDerives _ (CInl _ _) _ |- _ => inversion Hsc; subst end;
      lazymatch type of Hmot_saved with
      | CTypeDemand ({| cbinder := 0; cannotation := CSum ?AA ?BB; ctype_uses := _ |} :: _) _ _ =>
          destruct AA;
          try (rewrite (subst_sum_cty_no_use D mot true 0 c_idx (CIdxLit 0)) by assumption;
               apply cty_uses_kinds_tvar_subst_sum_0;
               [ reflexivity
               | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSum; [apply cty_alpha_eq_refl | reflexivity]]
               | intros _; apply cty_uses_var_case_branch_nat; assumption
               | exact Hm_s ]);
          assert (Hc : cidx_uses_kinds false false false false false (length env_a) c_idx = false) by
            (destruct scrut; cbn in Ev; try discriminate; inversion Ev; subst;
             [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
               [ exfalso; lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                   inversion Hdv; subst;
                   lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CNat |- _ =>
                     unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                     rewrite Hb in Heq; cbn in Heq; discriminate
                   end
                 end
               | cbn; apply Nat.eqb_neq; exact Hne ]
             | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) end
               end ]);
          apply cty_uses_kinds_tvar_subst_sum_0;
          [ exact Hc
          | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSum; [apply cty_alpha_eq_refl | reflexivity]]
          | intros _;
            lazymatch type of Hmot_saved with CTypeDemand (?hd' :: _) _ _ =>
              refine (proj2 (cdemand_case_branch_nat D hd' (env_a ++ b :: env_b) true CNat BB _ _) _ _ _ Hmot_saved [] eq_refl);
              [unfold cty_alpha_eq; reflexivity | reflexivity]
            end
          | exact Hm_s ]
      end
    | destruct (term_as_cidx scrut) as [c_idx |] eqn:Ev; try (apply cty_uses_kinds_tvar_unshift_0; [assumption | exact Hm_s]);
      lazymatch goal with Hsc : CoreDerives _ (CInr _ _) _ |- _ => inversion Hsc; subst end;
      lazymatch type of Hmot_saved with
      | CTypeDemand ({| cbinder := 0; cannotation := CSum ?AA ?BB; ctype_uses := _ |} :: _) _ _ =>
          destruct BB;
          try (rewrite (subst_sum_cty_no_use D mot false 0 c_idx (CIdxLit 0)) by assumption;
               apply cty_uses_kinds_tvar_subst_sum_0;
               [ reflexivity
               | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSum; [apply cty_alpha_eq_refl | reflexivity]]
               | intros _; apply cty_uses_var_case_branch_nat; assumption
               | exact Hm_s ]);
          assert (Hc : cidx_uses_kinds false false false false false (length env_a) c_idx = false) by
            (destruct scrut; cbn in Ev; try discriminate; inversion Ev; subst;
             [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
               [ exfalso; lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                   inversion Hdv; subst;
                   lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CNat |- _ =>
                     unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                     rewrite Hb in Heq; cbn in Heq; discriminate
                   end
                 end
               | cbn; apply Nat.eqb_neq; exact Hne ]
             | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) end
               end ]);
          apply cty_uses_kinds_tvar_subst_sum_0;
          [ exact Hc
          | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSum; [apply cty_alpha_eq_refl | reflexivity]]
          | intros _;
            lazymatch type of Hmot_saved with CTypeDemand (?hd' :: _) _ _ =>
              refine (proj2 (cdemand_case_branch_nat D hd' (env_a ++ b :: env_b) false AA CNat _ _) _ _ _ Hmot_saved [] eq_refl);
              [unfold cty_alpha_eq; reflexivity | reflexivity]
            end
          | exact Hm_s ]
      end ].
  - (* CoreIf *)
    cbn [cresult_type] in IHCoreDerives2; exact (IHCoreDerives2 env_a eq_refl).
  - (* CoreRecordMk *)
    cbn. clear IHCoreDerives.
    lazymatch goal with
    | Hrec : CRecordElemDerives _ ?fs _ _ |- _ =>
        assert (Hgo : forall env0 fs0 u0 v0, CRecordElemDerives env0 fs0 u0 v0 ->
          env0 = env_a ++ b :: env_b ->
          (fix go_fs (fs1 : list (nat * grade D * cty D)) : bool :=
             match fs1 with
             | [] => false
             | (_, _, ft) :: rest =>
                 cty_uses_kinds false true false false false false false (length env_a) ft || go_fs rest
             end) (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fs0) = false);
        [ intros env0 fs0 u0 v0 H0; induction H0; intro H0env; subst; cbn;
          [ reflexivity
          | lazymatch goal with Htd : CTypeDemand _ _ _ |- _ =>
              rewrite (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd env_a eq_refl), (IHCRecordElemDerives eq_refl); reflexivity
            end ]
        | exact (Hgo _ _ _ _ Hrec eq_refl) ]
    end.
  - (* CoreMatchRecord *)
    lazymatch goal with
    | Hmot : CTypeDemand _ ?mot _ |- cty_uses_kinds _ _ _ _ _ _ _ _ ?mot = false =>
        exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot env_a eq_refl)
    end.
  - (* CoreSubgrade *)
    lazymatch goal with
    | Hvt : CTypeDemand _ ?target _ |- cty_uses_kinds _ _ _ _ _ _ _ _ ?target = false =>
        exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hvt env_a eq_refl)
    end.
  - (* CoreFix *)
    lazymatch goal with
    | Hres : ?res_ty = spec_fix_subj_cty ?scrut ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot,
      Hdep : match term_as_cidx ?scrut with Some _ => True | None => cty_uses_var 0 ?mot = false end |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; unfold spec_fix_subj_cty;
        destruct (term_as_cidx scrut) as [c_idx |] eqn:Es;
        [ assert (Hc : cidx_uses_kinds false false false false false (length env_a) c_idx = false) by
            (destruct scrut; cbn in Es; try discriminate; inversion Es; subst;
             [ lazymatch goal with Hdv : CoreDerives _ (CVar ?vx) _ |- _ =>
                 destruct (Nat.eq_dec vx (length env_a)) as [-> | Hne];
                 [ exfalso; inversion Hdv; subst;
                   lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CNat |- _ =>
                     unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                     rewrite Hb in Heq; cbn in Heq; discriminate
                   end
                 | cbn; apply Nat.eqb_neq; exact Hne ]
               end
             | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) end
               end ]);
          apply cty_uses_kinds_tvar_subst_cidx_0;
          [ exact Hc
          | intros _; eapply ctype_demand_uses_kinds; [exact Hmot | reflexivity | unfold flags_allow; cbn; reflexivity]
          | exact Hm_s ]
        | apply cty_uses_kinds_tvar_unshift_0; [exact Hdep | exact Hm_s] ]
    end.
Qed.


Lemma subst_tvar_box_var_to_ty_gen : forall (D : JoinDomain) (mot U : cty D) q c k,
  cty_uses_kinds false false true false false false false c mot = false ->
  cty_uses_kinds false true false false false false false (S (c + k)) mot = false ->
  subst_tvar_in_cty (c + k) (lift_cty 0 (c + k) U) (subst_var_in_cty c k (spec_box_body_cty q c mot)) =
  subst_box_ty_cty c q (lift_cty 0 (c + k) U) (subst_tvar_in_cty (S (c + k)) (lift_cty 0 (S (c + k)) U) mot).
Proof.
  assert (Hidx : forall (D : JoinDomain) (i : cidx D) q c k,
    cidx_uses_kinds false false false false false c i = false ->
    cidx_uses_kinds false false false false false (S (c + k)) i = false ->
    subst_tvar_in_cidx (c + k) (subst_var_in_cidx c k (spec_box_body_cidx q c i)) =
    subst_tvar_in_cidx c (subst_tvar_in_cidx (S (c + k)) i)).
  { assert (Hr : forall c x y,
      Nat.iter c ren_shift (fun i => match i with 0 => y | S i' => i' end) x =
      if x <? c then x else if x =? c then c + y else x - 1).
    { clear. intro c. induction c as [| c IHc]; intros x y.
      - change (Nat.iter 0 ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)
          with (match x with 0 => y | S i' => i' end).
        destruct x; [rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn; lia | repeat (rw_nat_bool; cbv iota); lia].
      - change (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)
          with (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)) x).
        destruct x; [reflexivity |].
        change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)) (S x))
          with (S (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)).
        rewrite IHc. repeat (rw_nat_bool; cbv iota); destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia. }
    assert (Hv : forall v c k, v <> c -> v <> S (c + k) ->
      (let r1 := Nat.iter c ren_shift (fun i => match i with 0 => k | S i' => i' end) v in
       if r1 <? c + k then r1 else if r1 =? c + k then 0 else r1 - 1) =
      (let r2 := if v <? S (c + k) then v else if v =? S (c + k) then 0 else v - 1 in
       if r2 <? c then r2 else if r2 =? c then 0 else r2 - 1)).
    { intros v c k Hc Hsk. rewrite Hr. cbv zeta.
      destruct (Nat.ltb_spec v c); destruct (Nat.eqb_spec v c);
      destruct (Nat.ltb_spec v (S (c + k))); destruct (Nat.eqb_spec v (S (c + k)));
      cbv iota; try lia;
      repeat (match goal with |- context [?x <? ?y] => destruct (Nat.ltb_spec x y)
                            | |- context [?x =? ?y] => destruct (Nat.eqb_spec x y) end);
      lia. }
    intros D i q. induction i; intros c k Hc Hsk; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHi1 _ _ Hc1 Hk1), (IHi2 _ _ Hc2 Hk2); reflexivity);
      try (f_equal; apply (IHi _ _ Hc Hsk));
      nat_bool_hyps.
    - f_equal. apply Hv; assumption.
    - destruct (Nat.eqb_spec b c); [lia |]. unfold subst_var_in_cidx; cbn. f_equal. apply Hv; assumption.
    - f_equal. apply Hv; assumption.
    - f_equal. apply Hv; assumption.
    - apply orb_false_iff in Hc as [Hc12 Hc3]; apply orb_false_iff in Hc12 as [Hc1 Hc2].
      apply orb_false_iff in Hsk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2]; nat_bool_hyps.
      pose proof (IHi1 (S c) k Hc2 ltac:(rewrite Nat.add_succ_l; exact Hk2)) as Hi1'.
      pose proof (IHi2 (S c) k Hc3 ltac:(rewrite Nat.add_succ_l; exact Hk3)) as Hi2'.
      unfold subst_var_in_cidx in Hi1', Hi2' |- *.
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => k | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i => match i with 0 => k | S i' => i' end))) in *.
      rewrite Nat.add_succ_l in Hi1', Hi2'.
      rewrite (Hv s c k Hc1 Hk1).
      replace (Nat.iter c ren_shift (fun i => match i with 0 => k | S i' => i' end) s)
        with (if s <? c then s else if s =? c then c + k else s - 1) by (symmetry; apply Hr).
      destruct (Nat.ltb_spec s c); destruct (Nat.eqb_spec s c);
      destruct (Nat.ltb_spec s (S (c + k))); destruct (Nat.eqb_spec s (S (c + k)));
      cbv iota; try lia;
      repeat (match goal with |- context [?x <? ?y] => destruct (Nat.ltb_spec x y)
                            | |- context [?x =? ?y] => destruct (Nat.eqb_spec x y) end);
      try lia; rewrite <- Hi1', <- Hi2'; reflexivity. }
  assert (Hr : forall c x y,
    Nat.iter c ren_shift (fun i => match i with 0 => y | S i' => i' end) x =
    if x <? c then x else if x =? c then c + y else x - 1).
  { clear. intro c. induction c as [| c IHc]; intros x y.
    - change (Nat.iter 0 ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)
        with (match x with 0 => y | S i' => i' end).
      destruct x; [rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn; lia | repeat (rw_nat_bool; cbv iota); lia].
    - change (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)
        with (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)) x).
      destruct x; [reflexivity |].
      change (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end)) (S x))
        with (S (Nat.iter c ren_shift (fun i : nat => match i with 0 => y | S i' => i' end) x)).
      rewrite IHc. repeat (rw_nat_bool; cbv iota); destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); lia. }
  assert (Hgen : forall (D : JoinDomain) (mot U : cty D) q c k,
    cty_uses_kinds false false true false false false false c mot = false ->
    cty_uses_kinds false true false false false false false (S (c + k)) mot = false ->
    subst_tvar_in_cty (c + k) (lift_cty 0 (c + k) U)
      (ren_cty (Nat.iter c ren_shift (fun i => match i with 0 => k | S i' => i' end)) (spec_box_body_cty q c mot)) =
    subst_box_ty_cty c q (lift_cty 0 (c + k) U) (subst_tvar_in_cty (S (c + k)) (lift_cty 0 (S (c + k)) U) mot)).
  { unfold subst_var_in_cidx in Hidx.
    intros D mot. induction mot using cty_ind_nested; intros U qb c k Hc Hsk;
      cbn [spec_box_body_cty subst_box_ty_cty subst_tvar_in_cty ren_cty cty_uses_kinds] in *; try reflexivity;
      try (f_equal; apply (IHmot _ _ _ _ Hc Hsk));
      try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2];
           rewrite (IHmot1 _ _ _ _ Hc1 Hk1), (IHmot2 _ _ _ _ Hc2 Hk2); reflexivity).
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHmot _ _ _ _ Hc1 Hk1), (Hidx D len qb _ _ Hc2 Hk2); reflexivity.
    - nat_bool_hyps. rewrite Hr.
      destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; [| contradiction |];
        destruct (lt_eq_lt_dec x (S (c + k))) as [[? | ->] | ?];
        repeat (rw_nat_bool; cbv iota); cbn;
        try (repeat (rw_nat_bool; cbv iota); f_equal; lia).
      rewrite (subst_box_ty_cty_lift_above D U c qb (lift_cty 0 (c + k) U) 0 (S (c + k)) ltac:(lia) ltac:(lia)).
      f_equal; lia.
    - nat_bool_hyps. destruct (Nat.eqb_spec b c) as [-> | Hbc];
        cbn [ren_cty subst_tvar_in_cty subst_box_ty_cty] in *.
      + cbn. rewrite Hr, Nat.ltb_irrefl, Nat.eqb_refl.
        rewrite (proj2 (Nat.ltb_lt c (S (c + k))) ltac:(lia)). cbn.
        rewrite Nat.eqb_refl. f_equal.
        destruct (Nat.ltb_spec (c + k) (c + k)); [lia |]. rewrite Nat.eqb_refl. reflexivity.
      + rewrite Hr. destruct (lt_eq_lt_dec b c) as [[? | ?] | ?]; [| contradiction |];
          destruct (lt_eq_lt_dec b (S (c + k))) as [[? | ?] | ?]; try contradiction;
          repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHmot1 _ _ _ _ Hc1 Hk1).
      pose proof (IHmot2 U qb (S c) k Hc2 ltac:(rewrite Nat.add_succ_l; exact Hk2)) as H2.
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => k | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i => match i with 0 => k | S i' => i' end))) in H2.
      rewrite Nat.add_succ_l in H2. rewrite !lift_cty_add. cbn [Nat.add] in H2 |- *.
      rewrite H2. reflexivity.
    - apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (IHmot1 _ _ _ _ Hc1 Hk1).
      pose proof (IHmot2 U qb (S c) k Hc2 ltac:(rewrite Nat.add_succ_l; exact Hk2)) as H2.
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => k | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i => match i with 0 => k | S i' => i' end))) in H2.
      rewrite Nat.add_succ_l in H2. rewrite !lift_cty_add. cbn [Nat.add] in H2 |- *.
      rewrite H2. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
      apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hhd _ _ _ _ Hc1 Hk1), (IHf Htl Hc2 Hk2); reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsk as [Hk1 Hk2].
      rewrite (Hidx D idx qb _ _ Hc1 Hk1), (IH Hc2 Hk2); reflexivity. }
  intros. apply Hgen; assumption.
Qed.

Lemma subst_sum_cty_no_use_unshift : forall (D : JoinDomain) (T : cty D) is_left val,
  cty_uses_var 0 T = false ->
  subst_sum_cty is_left 0 val T = unshift_cty 0 T.
Proof.
  assert (Hi : forall (D : JoinDomain) (i : cidx D) is_left c val,
    cidx_uses_var c i = false ->
    subst_sum_cidx is_left c val i = unshift_cidx c i).
  { intros D i is_left. induction i; intros c val Hi; cbn in *;
      try (unfold unshift_cidx; cbn; reflexivity);
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ val H1), (IHi2 _ val H2); reflexivity);
      try (rewrite (IHi _ val Hi); unfold unshift_cidx; reflexivity).
    - change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      cbn; nat_bool_hyps; destruct (lt_eq_lt_dec x c) as [[? | ?] | ?]; try contradiction;
      [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity.
    - change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      cbn; nat_bool_hyps; destruct (lt_eq_lt_dec b c) as [[? | ?] | ?]; try contradiction;
      [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity.
    - change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      cbn; nat_bool_hyps; destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; try contradiction;
      [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity.
    - change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      cbn; nat_bool_hyps; destruct (lt_eq_lt_dec p c) as [[? | ?] | ?]; try contradiction;
      [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity.
    - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
      rewrite (IHi1 _ (lift_cidx 0 1 val) H2), (IHi2 _ (lift_cidx 0 1 val) H3).
      change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      nat_bool_hyps. destruct (lt_eq_lt_dec s c) as [[? | ?] | ?]; try contradiction;
      [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity. }
  intros D T is_left val HT.
  assert (Hgen : forall (T0 : cty D) c val0,
    cty_uses_var c T0 = false ->
    subst_sum_cty is_left c val0 T0 = unshift_cty c T0).
  { intro T0. induction T0 using cty_ind_nested; intros c val0 HT0; cbn in *; try reflexivity;
      try (f_equal; apply (IHT0 _ val0 HT0));
      try (apply orb_false_iff in HT0 as [H1 H2]; rewrite (IHT0_1 _ val0 H1), (IHT0_2 _ val0 H2); reflexivity);
      try (unfold unshift_cty; cbn;
           change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0);
           nat_bool_hyps; match goal with |- context [?v <? c] => destruct (lt_eq_lt_dec v c) as [[? | ?] | ?] end; try contradiction;
           [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2].
      rewrite (IHT0 _ val0 H1), (Hi D len is_left _ val0 H2).
      unfold unshift_cty, unshift_cidx. cbn. reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      rewrite (IHT0_1 _ val0 H1), (IHT0_2 (S c) (lift_cidx 0 1 val0) H2). reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      rewrite (IHT0_1 _ val0 H1), (IHT0_2 (S c) (lift_cidx 0 1 val0) H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      rewrite (Hhd _ val0 H1).
      pose proof (IHf Htl H2) as Hr. unfold unshift_cty in Hr |- *; cbn in Hr |- *. congruence.
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [H1 H2]. rewrite (Hi D idx is_left _ val0 H1).
      pose proof (IH H2) as Hr. unfold unshift_cty, unshift_cidx in Hr |- *; cbn in Hr |- *. congruence. }
  exact (Hgen T 0 val HT).
Qed.

Lemma subst_pair_cty_no_use_unshift : forall (D : JoinDomain) (T : cty D) fi si,
  cty_uses_var 0 T = false ->
  subst_pair_cty 0 fi si T = unshift_cty 0 T.
Proof.
  assert (Hi : forall (D : JoinDomain) (i : cidx D) c fi si,
    cidx_uses_var c i = false ->
    subst_pair_cidx c fi si i = unshift_cidx c i).
  { intros D i. induction i; intros c fi si Hi; cbn in *;
      try (unfold unshift_cidx; cbn; reflexivity);
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ fi si H1), (IHi2 _ fi si H2); reflexivity);
      try (rewrite (IHi _ fi si Hi); unfold unshift_cidx; reflexivity);
      try (change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0);
           cbn; nat_bool_hyps; match goal with |- context [?v =? c] => destruct (lt_eq_lt_dec v c) as [[? | ?] | ?] end; try contradiction;
           [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity).
    apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
    rewrite (IHi1 (S c) (lift_cidx 0 1 fi) (lift_cidx 0 1 si) H2),
            (IHi2 (S c) (lift_cidx 0 1 fi) (lift_cidx 0 1 si) H3).
    change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
    nat_bool_hyps. destruct (lt_eq_lt_dec s c) as [[? | ?] | ?]; try contradiction;
    [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity. }
  intros D T fi si HT.
  assert (Hgen : forall (T0 : cty D) c fi0 si0,
    cty_uses_var c T0 = false ->
    subst_pair_cty c fi0 si0 T0 = unshift_cty c T0).
  { intro T0. induction T0 using cty_ind_nested; intros c fi0 si0 HT0; cbn in *; try reflexivity;
      try (f_equal; apply (IHT0 _ fi0 si0 HT0));
      try (apply orb_false_iff in HT0 as [H1 H2]; rewrite (IHT0_1 _ fi0 si0 H1), (IHT0_2 _ fi0 si0 H2); reflexivity);
      try (unfold unshift_cty; cbn;
           change (Nat.iter c ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var c 0);
           nat_bool_hyps; match goal with |- context [?v <? c] => destruct (lt_eq_lt_dec v c) as [[? | ?] | ?] end; try contradiction;
           [rewrite r_var_lt by lia | rewrite r_var_gt by lia]; repeat (rw_nat_bool; cbv iota); reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2]. rewrite (IHT0 _ fi0 si0 H1), (Hi D len _ fi0 si0 H2).
      unfold unshift_cty, unshift_cidx. cbn. reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2]. rewrite (IHT0_1 _ fi0 si0 H1), (IHT0_2 (S c) (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0) H2). reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2]. rewrite (IHT0_1 _ fi0 si0 H1), (IHT0_2 (S c) (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0) H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      rewrite (Hhd _ fi0 si0 H1). pose proof (IHf Htl H2) as Hr. unfold unshift_cty in Hr |- *; cbn in Hr |- *. congruence.
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [H1 H2]. rewrite (Hi D idx _ fi0 si0 H1).
      pose proof (IH H2) as Hr. unfold unshift_cty, unshift_cidx in Hr |- *; cbn in Hr |- *. congruence. }
  exact (Hgen T 0 fi si HT).
Qed.

Lemma term_as_cidx_subst_tvar_none : forall (D : JoinDomain) (t : cterm D) k U,
  term_as_cidx t = None ->
  term_as_cidx (subst_tvar_in_cterm k U t) = None.
Proof.
  intros D t k U H. destruct t; cbn in *; try discriminate; reflexivity.
Qed.

Lemma term_as_cidx_subst_tvar_some : forall (D : JoinDomain) (b : cbinding D) env_a env_b lvl_b (t : cterm D) j c_idx U,
  cannotation b = CUniv lvl_b ->
  CoreDerives (env_a ++ b :: env_b) t j ->
  cresult_type j = CNat ->
  term_as_cidx t = Some c_idx ->
  cidx_uses_kinds false false false false false (length env_a) c_idx = false /\
  term_as_cidx (subst_tvar_in_cterm (length env_a) U t) = Some (subst_tvar_in_cidx (length env_a) c_idx).
Proof.
  intros D b env_a env_b lvl_b t j c_idx U Hb Hdv Hnat Hev.
  destruct t; cbn in Hev; try discriminate; inversion Hev; subst.
  - destruct (Nat.eq_dec x (length env_a)) as [-> | Hne].
    + exfalso. inversion Hdv; subst; cbn [cresult_type] in Hnat.
      lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
        inversion Hlk; subst ee; rewrite Hb in Hnat; cbn in Hnat; discriminate
      end.
    + cbn. rewrite (proj2 (Nat.eqb_neq x (length env_a)) Hne). split; [reflexivity | destruct (Nat.ltb_spec x (length env_a)); reflexivity].
  - inversion Hdv; subst.
    lazymatch goal with Hcd : CIdxDemand _ c_idx _ |- _ =>
      split; [exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) | reflexivity]
    end.
Qed.

Lemma term_as_cidx_subst_tvar_some_non_univ : forall (D : JoinDomain) (b : cbinding D) env_a env_b lvl_b (t : cterm D) j c_idx U,
  cannotation b = CUniv lvl_b ->
  CoreDerives (env_a ++ b :: env_b) t j ->
  cty_non_univ (cresult_type j) = true ->
  term_as_cidx t = Some c_idx ->
  cidx_uses_kinds false false false false false (length env_a) c_idx = false /\
  term_as_cidx (subst_tvar_in_cterm (length env_a) U t) = Some (subst_tvar_in_cidx (length env_a) c_idx).
Proof.
  intros D b env_a env_b lvl_b t j c_idx U Hb Hdv Hnu Hev.
  destruct t; cbn in Hev; try discriminate; inversion Hev; subst.
  - destruct (Nat.eq_dec x (length env_a)) as [-> | Hne].
    + exfalso. inversion Hdv; subst; cbn [cresult_type] in Hnu.
      lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
        inversion Hlk; subst ee; rewrite Hb in Hnu; cbn in Hnu; discriminate
      end.
    + cbn. rewrite (proj2 (Nat.eqb_neq x (length env_a)) Hne). split; [reflexivity | destruct (Nat.ltb_spec x (length env_a)); reflexivity].
  - inversion Hdv; subst.
    lazymatch goal with Hcd : CIdxDemand _ c_idx _ |- _ =>
      split; [exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) | reflexivity]
    end.
Qed.

Lemma cty_uses_var_subst_tvar_0 : forall (D : JoinDomain) (T U : cty D) k,
  cty_uses_var 0 T = false ->
  cty_uses_kinds false true false false false false false (S k) T = false ->
  cty_uses_var 0 (subst_tvar_in_cty (S k) (lift_cty 0 (S k) U) T) = false.
Proof.
  intros D T U k HT0 HTk.
  replace (lift_cty 0 (S k) U) with (lift_cty 0 1 (lift_cty 0 k U)) by
    (rewrite lift_cty_add; f_equal; lia).
  exact (subst_tvar_in_cty_uses_var_0 D T (lift_cty 0 k U) k HT0 HTk).
Qed.



Lemma vec_subst_nth_zero_indep : forall (D : JoinDomain) k (z1 z2 u : list (grade D)),
  nth_grade u k = zero ->
  length z1 = length z2 ->
  vec_subst k z1 u = vec_subst k z2 u.
Proof.
  intros D k. induction k as [| k IH]; intros z1 z2 [| a u'] Hz Hlen; cbn in *; try reflexivity;
    [ rewrite Hz, !vec_scale_zero, Hlen; reflexivity | f_equal; apply (IH z1 z2 u' Hz Hlen) ].
Qed.

Lemma cidx_demand_tvar_nth_zero : forall (D : JoinDomain) (b : cbinding D) env_b lvl_b,
  ErasureDomain D ->
  cannotation b = CUniv lvl_b ->
  forall env i d,
    CIdxDemand env i d ->
    forall env_a, env = env_a ++ b :: env_b ->
    nth_grade d (length env_a) = zero.
Proof.
  intros D b env_b lvl_b ED Hb env i d H.
  induction H; intros env_a Henv; subst env.
  - destruct (Nat.eq_dec x (length env_a)) as [-> | Hne].
    + exfalso. unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; subst e.
      unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    + apply nth_grade_single_other; exact Hne.
  - apply nth_grade_zero.
  - rewrite nth_grade_add by (rewrite (cidx_demand_length _ _ _ _ H), (cidx_demand_length _ _ _ _ H0); reflexivity).
    rewrite (IHCIdxDemand1 env_a eq_refl), (IHCIdxDemand2 env_a eq_refl), add_zero; reflexivity.
  - rewrite nth_grade_scale, (IHCIdxDemand env_a eq_refl), mul_zero_r; reflexivity.
  - destruct (Nat.eq_dec b0 (length env_a)) as [-> | Hne].
    + exfalso. unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; subst e.
      unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    + apply nth_grade_single_other; exact Hne.
  - destruct (Nat.eq_dec p (length env_a)) as [-> | Hne].
    + exfalso. unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; subst e.
      unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    + apply nth_grade_single_other; exact Hne.
  - destruct (Nat.eq_dec p (length env_a)) as [-> | Hne].
    + exfalso. unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; subst e.
      unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    + apply nth_grade_single_other; exact Hne.
  - assert (Hs : s <> length env_a).
    { intro Heq; subst s. unfold clookup in H; rewrite nth_error_app2, Nat.sub_diag in H by lia; inversion H; subst e.
      unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate. }
    pose proof (IHCIdxDemand1 (_ :: env_a) eq_refl) as Hl.
    pose proof (IHCIdxDemand2 (_ :: env_a) eq_refl) as Hr.
    cbn [length] in Hl, Hr.
    pose proof (cidx_demand_length D _ _ _ H1) as Hlen1.
    pose proof (cidx_demand_length D _ _ _ H2) as Hlen2.
    destruct dl as [| dl0 dl']; destruct dr as [| dr0 dr']; cbn in *; try lia.
    unfold BranchVec in H3. destruct (grade_join D) as [j |] eqn:Hj.
    + subst d_br.
      rewrite nth_grade_add by (rewrite vec_single_length, vec_join_length; lia).
      rewrite nth_grade_single_other by exact Hs.
      rewrite add_zero.
      assert (Hnj : forall (u v : list (grade D)) idx,
        nth_grade u idx = zero -> nth_grade v idx = zero ->
        nth_grade (vec_join j u v) idx = zero).
      { clear - ED Hj. induction u as [| a u IHu]; intros [| c v] idx Hu Hv;
          cbn in *; try (destruct idx; reflexivity).
        destruct idx as [| idx']; cbn in *.
        - unfold nth_grade in *; cbn in *; subst a c.
          apply (erasure_allows_zero_eq D ED), (join_least D j Hj); apply allows_refl.
        - apply IHu; assumption. }
      apply Hnj; assumption.
    + destruct H3 as [_ ->].
      rewrite nth_grade_add by (rewrite vec_single_length; lia).
      rewrite nth_grade_single_other by exact Hs.
      rewrite add_zero. exact Hl.
Qed.

Lemma BranchVec_subst_tail : forall (D : JoinDomain) k (z v1 v2 v_br v1' v2' : list (grade D)) (q1 q2 : grade D) n_b,
  (grade_join D = None -> z = vec_zero n_b) ->
  length z = n_b ->
  length v1 = S (k + n_b) ->
  length v2 = S (k + n_b) ->
  BranchVec v1 v2 v_br ->
  branch_rel v1' (vec_add (vec_subst k z v1) (vec_zero k ++ vec_scale q1 z)) ->
  branch_rel v2' (vec_add (vec_subst k z v2) (vec_zero k ++ vec_scale q2 z)) ->
  exists v_br' q_t,
    BranchVec v1' v2' v_br' /\
    branch_rel v_br' (vec_add (vec_subst k z v_br) (vec_zero k ++ vec_scale q_t z)).
Proof.
  intros D k z v1 v2 v_br v1' v2' q1 q2 n_b Hnone_z Hz Hv1 Hv2 Hbr H1 H2.
  unfold BranchVec, branch_rel in *.
  destruct (grade_join D) as [j |] eqn:Hj.
  - subst v_br. exists (vec_join j v1' v2'), (j q1 q2). split; [reflexivity |].
    assert (Hq1 : branch_rel (vec_scale q1 z) (vec_scale (j q1 q2) z)).
    { apply branch_rel_vec_scale_mono; [intro Hbad; rewrite Hj in Hbad; discriminate | apply (join_left D j Hj)]. }
    assert (Hq2 : branch_rel (vec_scale q2 z) (vec_scale (j q1 q2) z)).
    { apply branch_rel_vec_scale_mono; [intro Hbad; rewrite Hj in Hbad; discriminate | apply (join_right D j Hj)]. }
    unfold branch_rel in Hq1, Hq2; rewrite Hj in Hq1, Hq2.
    assert (Hm1 : vec_allows v1' (vec_add (vec_subst k z v1) (vec_zero k ++ vec_scale (j q1 q2) z))).
    { eapply vec_allows_trans; [exact H1 |].
      apply vec_allows_add; [apply vec_allows_refl | apply Forall2_app; [apply vec_allows_refl | exact Hq1]]. }
    assert (Hm2 : vec_allows v2' (vec_add (vec_subst k z v2) (vec_zero k ++ vec_scale (j q1 q2) z))).
    { eapply vec_allows_trans; [exact H2 |].
      apply vec_allows_add; [apply vec_allows_refl | apply Forall2_app; [apply vec_allows_refl | exact Hq2]]. }
    eapply vec_allows_join_least; [exact Hj | |].
    + eapply vec_allows_trans; [exact Hm1 |].
      apply vec_allows_add; [| apply vec_allows_refl].
      apply vec_subst_allows. apply (vec_allows_join_left D j); [exact Hj | lia].
    + eapply vec_allows_trans; [exact Hm2 |].
      apply vec_allows_add; [| apply vec_allows_refl].
      apply vec_subst_allows. apply (vec_allows_join_right D j); [exact Hj | lia].
  - destruct Hbr as [-> ->].
    rewrite (Hnone_z eq_refl), !vec_scale_zero_vec in H1, H2.
    replace (vec_zero (D := D) k ++ vec_zero (D := D) n_b)
      with (vec_zero (D := D) (length (vec_subst k (vec_zero (D := D) n_b) v2))) in H1, H2
      by (rewrite (vec_subst_length D k (vec_zero n_b) v2 n_b); [unfold vec_zero; rewrite repeat_app; f_equal; lia | apply vec_zero_length | exact Hv2]).
    rewrite vec_add_zero_r in H1, H2. subst v1' v2'.
    exists (vec_subst k (vec_zero n_b) v2), zero. split; [split; reflexivity |].
    rewrite (Hnone_z eq_refl), vec_scale_zero_vec.
    replace (vec_zero (D := D) k ++ vec_zero (D := D) n_b)
      with (vec_zero (D := D) (length (vec_subst k (vec_zero (D := D) n_b) v2)))
      by (rewrite (vec_subst_length D k (vec_zero n_b) v2 n_b); [unfold vec_zero; rewrite repeat_app; f_equal; lia | apply vec_zero_length | exact Hv2]).
    rewrite vec_add_zero_r. reflexivity.
Qed.

Lemma cdemand_not_tvar_0_safe : forall (D : JoinDomain) (env : cenv D) e0 T d,
  (forall lvl, erase_hints (cannotation e0) <> CUniv lvl) ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds true false true true true true true 0 T = false.
Proof.
  intros D env e0 T d Hnu HT.
  eapply ctype_demand_uses_kinds; [exact HT | reflexivity |].
  unfold flags_allow. rewrite erase_hints_ren.
  destruct (erase_hints (cannotation e0)) eqn:Ee; cbn;
    try exact I; try reflexivity;
    try (exfalso; eapply Hnu; first [reflexivity | exact Ee]).
  - match goal with |- context [ren_cty _ ?x] => destruct x; cbn end;
      try exact I; try reflexivity;
      match goal with |- context [ren_cty _ ?y] => destruct y; cbn end;
      repeat split; first [exact I | reflexivity].
  - match goal with |- context [ren_cty _ ?x] => destruct x; cbn end; first [exact I | reflexivity].
Qed.

Lemma subst_tvar_app_type_arg_demand :
  forall (D : JoinDomain) (ED : ErasureDomain D) (U : cty D) (b : cbinding D) (env_a env_b : cenv D)
    (lvl_b : nat) (z : list (grade D)) (dom dom0 kind rt_arg : cty D) (arg : cterm D)
    (u_arg v_arg u_arg' v_arg' : list (grade D)) (q_arg : grade D),
    cannotation b = CUniv lvl_b ->
    CTypeDemand env_b U z ->
    (grade_join D = None -> z = vec_zero (length env_b)) ->
    (forall j, grade_join D = Some j -> forall g, @allows D zero g) ->
    CoreDerives (env_a ++ b :: env_b) arg {| cresult_type := kind; ccomp_demand := u_arg; ctype_demand_row := v_arg |} ->
    cty_alpha_eq kind dom ->
    cty_alpha_eq dom0 (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) dom) ->
    CoreDerives (subst_tvar_cenv U z env_a ++ env_b)
      (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) arg)
      {| cresult_type := rt_arg; ccomp_demand := u_arg'; ctype_demand_row := v_arg' |} ->
    branch_rel u_arg' (vec_subst (length env_a) (vec_zero (length env_b)) u_arg) ->
    branch_rel v_arg' (vec_add (vec_subst (length env_a) z v_arg) (vec_zero (length env_a) ++ vec_scale q_arg z)) ->
    exists q_z : grade D,
      branch_rel
        (app_type_arg_demand dom0 (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) arg) u_arg' v_arg')
        (vec_add (vec_subst (length env_a) z (app_type_arg_demand dom arg u_arg v_arg))
                 (vec_zero (length env_a) ++ vec_scale q_z z)).
Proof.
  intros D ED U b env_a env_b lvl_b z dom dom0 kind rt_arg arg u_arg v_arg u_arg' v_arg' q_arg
    Hb HU Hnone_z Hsome_z Harg Hkind Hdom0 Harg' Hu_arg' Hv_arg'.
  pose proof (ctype_demand_length D _ _ _ HU) as Hz_len.
  pose proof (core_derives_lengths D _ _ _ Harg) as [Hlen_ua Hlen_va].
  rewrite length_app in Hlen_ua, Hlen_va; cbn [ccomp_demand ctype_demand_row length] in Hlen_ua, Hlen_va.
  assert (H_uv_subst : branch_rel u_arg' (vec_subst (length env_a) z u_arg)) by
    (eapply branch_rel_trans; [exact Hu_arg' | apply branch_rel_subst_zero_z; [exact Hnone_z | exact Hsome_z | exact Hz_len]]).
  assert (Hu_tail : forall q0,
    branch_rel u_arg' (vec_add (vec_subst (length env_a) z u_arg) (vec_zero (length env_a) ++ vec_scale q0 z))).
  { intro q0. eapply branch_rel_trans; [exact H_uv_subst |].
    apply branch_rel_add_zero_tail;
      [ intro Hn; rewrite (Hnone_z Hn), vec_zero_length; reflexivity
      | exact Hsome_z
      | apply vec_subst_length; [reflexivity | rewrite Hz_len; lia] ]. }
  destruct dom0;
    try (cbn [app_type_arg_demand]; destruct dom, arg;
         try (exists zero; apply Hu_tail);
         unfold cty_alpha_eq in Hdom0; cbn in Hdom0; discriminate).
  remember (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) arg) as targ eqn:Harg_eq.
  destruct targ;
    try (cbn [app_type_arg_demand]; destruct dom, arg;
         try (exists zero; apply Hu_tail);
         cbn in Harg_eq; discriminate).
  destruct dom; cbn [app_type_arg_demand];
    try (unfold cty_alpha_eq in Hdom0; cbn in Hdom0; discriminate).
  - (* dom = CUniv n0 *)
    destruct arg eqn:Harg_orig; cbn in Harg_eq; try discriminate.
    + destruct (Nat.eq_dec x (length env_a)) as [Hx_eq | Hne].
      * subst x. rewrite Nat.eqb_refl in Harg_eq. inversion Harg_eq; subst.
        exists zero.
        assert (Hv_dem : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) (lift_cty 0 (length env_a) U) v_arg') by
          (inversion Harg'; subst;
           try (match goal with
                | Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} =
                         {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                    injection Hrec; intros; subst
                end); assumption).
        destruct (weaken_ctype_demand_app_left D env_b U z HU (subst_tvar_cenv U z env_a)) as [z' [Hz' Hbrz']].
        rewrite subst_tvar_cenv_length in Hz', Hbrz'.
        assert (Heq_v : v_arg' = z') by
          (eapply ctype_demand_unique; [apply cenv_alpha_eq_refl | exact Hv_dem | exact Hz']).
        subst v_arg'.
        try rewrite Harg_orig in Harg. inversion Harg; subst;
          try (match goal with
               | Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} =
                        {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                   injection Hrec; intros; subst
               end).
        rewrite length_app; cbn [length]; rewrite Nat.add_succ_r.
        rewrite (vec_subst_single_eq D (length env_a) z (length env_b) one Hz_len), vec_scale_one.
        eapply branch_rel_trans; [exact Hbrz' |].
        apply branch_rel_add_zero_tail;
          [ intro Hn; rewrite (Hnone_z Hn), vec_zero_length; reflexivity
          | exact Hsome_z
          | rewrite length_app, vec_zero_length; reflexivity ].
      * rewrite (proj2 (Nat.eqb_neq x (length env_a)) Hne) in Harg_eq.
        destruct (Nat.ltb_spec x (length env_a)); discriminate.
    + exists q_arg. exact Hv_arg'.
  - (* dom = CTVar x *)
    destruct arg eqn:Harg_orig; cbn in Harg_eq; try discriminate.
    + destruct (Nat.eq_dec x0 (length env_a)) as [Hx_eq | Hne].
      * subst x0. try rewrite Harg_orig in Harg. inversion Harg; subst.
        lazymatch goal with Hlk : clookup _ (length env_a) = Some ?ee |- _ =>
          unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
          inversion Hlk; subst ee;
          try (match goal with
               | Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} =
                        {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                   injection Hrec; intros; subst
               end);
          unfold cty_alpha_eq in Hkind; rewrite erase_hints_ren, Hb in Hkind; cbn in Hkind; discriminate
        end.
      * rewrite (proj2 (Nat.eqb_neq x0 (length env_a)) Hne) in Harg_eq.
        destruct (Nat.ltb_spec x0 (length env_a)); discriminate.
    + try rewrite Harg_orig in Harg. inversion Harg; subst;
        try (match goal with
             | Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} =
                      {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                 injection Hrec; intros; subst
             end).
      unfold cty_alpha_eq in Hkind; cbn in Hkind; discriminate.
Qed.

Theorem core_type_substitution : forall (D : JoinDomain),
  ErasureDomain D ->
  (grade_join D = None -> forall a b, @allows D a b -> a = b) ->
  (forall j, grade_join D = Some j -> forall g, @allows D zero g) ->
  forall (U : cty D) lvl_b z env_a (b : cbinding D) env_b t j,
    cannotation b = CUniv lvl_b ->
    cenv_tvar_safe env_a (length env_a) ->
    CTypeDemand env_b U z ->
    CUniverseLevel env_b U lvl_b ->
    (grade_join D = None -> z = vec_zero (length env_b)) ->
    CoreDerives (env_a ++ b :: env_b) t j ->
    exists j',
      CoreDerives (subst_tvar_cenv U z env_a ++ env_b)
        (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) t) j' /\
      cty_alpha_eq (cresult_type j')
        (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) (cresult_type j)) /\
      branch_rel (ccomp_demand j')
        (vec_subst (length env_a) (vec_zero (length env_b)) (ccomp_demand j)) /\
      exists q_t : grade D,
        branch_rel (ctype_demand_row j')
          (vec_add (vec_subst (length env_a) z (ctype_demand_row j))
                   (vec_zero (length env_a) ++ vec_scale q_t z)).
Proof.
  intros D ED Hnone_eq Hsome_z U lvl_b z env_a b env_b t j Hb Hsafe HU Hlvl Hnone_z H.
  assert (Hz_len : length z = length env_b) by (eapply ctype_demand_length; exact HU).
  assert (Hvz_len : forall k (u : list (grade D)),
    length u = S (k + length env_b) ->
    length (vec_subst k z u) = k + length env_b) by
    (intros kk uu Hlu; exact (vec_subst_length D kk z uu (length env_b) Hz_len Hlu)).
  assert (Hv0_len : forall k (u : list (grade D)),
    length u = S (k + length env_b) ->
    length (vec_subst k (vec_zero (length env_b)) u) = k + length env_b) by
    (intros kk uu Hlu; exact (vec_subst_length D kk (vec_zero (length env_b)) uu (length env_b) (vec_zero_length D (length env_b)) Hlu)).
  assert (Htl_zero_tail : forall k (q0 : grade D),
    tl (vec_zero (S k) ++ vec_scale q0 z) = vec_zero k ++ vec_scale q0 z) by
    (intros k q0; reflexivity).
  assert (Hadd_zero_tail : forall (v : list (grade D)) k (q0 : grade D),
    length v = k + length env_b ->
    branch_rel v (vec_add v (vec_zero k ++ vec_scale q0 z))) by
    (intros v k q0 Hlen; rewrite <- Hz_len in Hlen;
     apply branch_rel_add_zero_tail; [intro Hn; rewrite (Hnone_z Hn); rewrite vec_zero_length; reflexivity | exact Hsome_z | exact Hlen]).
  assert (H_uv_subst : forall v' v k,
    length v = S (k + length env_b) ->
    branch_rel v' (vec_subst k (vec_zero (length env_b)) v) ->
    branch_rel v' (vec_subst k z v)) by
    (intros v' v k Hlv Hb'; eapply branch_rel_trans; [exact Hb' | apply branch_rel_subst_zero_z; [exact Hnone_z | exact Hsome_z | exact Hz_len]]).
  remember (env_a ++ b :: env_b) as env1 eqn:Henv1.
  revert env_a Henv1 Hsafe.
  induction H using CoreDerives_ind_mut with
    (P := fun env1 t j _ => forall env_a, env1 = env_a ++ b :: env_b ->
      cenv_tvar_safe env_a (length env_a) ->
      exists j',
        CoreDerives (subst_tvar_cenv U z env_a ++ env_b)
          (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) t) j' /\
        cty_alpha_eq (cresult_type j')
          (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) (cresult_type j)) /\
        branch_rel (ccomp_demand j')
          (vec_subst (length env_a) (vec_zero (length env_b)) (ccomp_demand j)) /\
        exists q_t : grade D,
          branch_rel (ctype_demand_row j')
            (vec_add (vec_subst (length env_a) z (ctype_demand_row j))
                     (vec_zero (length env_a) ++ vec_scale q_t z)))
    (P0 := fun env1 fs u v _ => forall env_a, env1 = env_a ++ b :: env_b ->
      cenv_tvar_safe env_a (length env_a) ->
      exists u' v',
        CRecordElemDerives (subst_tvar_cenv U z env_a ++ env_b)
          (map (fun '(fn, fg, ft, fv) =>
             (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft,
                      subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) fv)) fs)
          u' v' /\
        branch_rel u' (vec_subst (length env_a) (vec_zero (length env_b)) u) /\
        exists q_t : grade D,
          branch_rel v'
            (vec_add (vec_subst (length env_a) z v)
                     (vec_zero (length env_a) ++ vec_scale q_t z)));
    intros env_a Henv1 Hsafe; subst env; cbn [subst_tvar_in_cterm].
  - (* CoreVar *)
    lazymatch goal with
    | Hl : clookup _ x = Some e, Htd : CTypeDemand _ (cannotation e) row, Hva : vec_allows row (ctype_uses e) |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt]; repeat (rw_nat_bool; cbv iota);
        [ destruct (subst_tvar_lookup_lt D U z env_a b env_b x e Hlt Hsafe Hl) as [e' [Hl' [Hren [Hvec [Hsk1 Hsk2]]]]];
          destruct (subst_tvar_lookup_lt_ann_raw D U z env_a b env_b x e Hlt Hl) as [e_raw [Hl_raw [Hann_raw [Hvec_raw [Hsk1_raw Hsk2_raw]]]]];
          assert (He'_eq : e' = e_raw) by (rewrite Hl' in Hl_raw; inversion Hl_raw; reflexivity); subst e_raw;
          rewrite Hsk2 in Htd;
          assert (Hsafe_sk : cenv_tvar_safe (skipn (S x) env_a) (length (skipn (S x) env_a))) by (apply cenv_tvar_safe_skipn; exact Hsafe);
          destruct (subst_tvar_type_demand D U z (skipn (S x) env_a) b env_b lvl_b (cannotation e) row Hb Hsafe_sk HU Htd) as [row' [Hrow' Hbr_row]];
          rewrite length_skipn in Hrow', Hbr_row;
          rewrite <- Hann_raw, <- Hsk1 in Hrow';
          assert (Huses' : ctype_uses e' = vec_subst (length env_a - S x) z (ctype_uses e)) by
            (pose proof (f_equal (skipn (S x)) Hvec) as Hsk_v;
             rewrite <- vec_subst_skipn_prefix in Hsk_v by lia;
             rewrite !skipn_vec_zero_app in Hsk_v;
             exact Hsk_v);
          assert (Hva' : vec_allows row' (ctype_uses e')) by
            (eapply branch_rel_allows_trans; [exact Hbr_row | rewrite Huses'; apply vec_subst_allows; exact Hva]);
          eexists; split; [| split; [| split]];
          [ eapply CoreVar; [exact Hl' | exact Hrow' | exact Hva']
          | cbn [cresult_type]; rewrite Hren; apply cty_alpha_eq_refl
          | cbn [ccomp_demand]; rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
            [apply branch_rel_refl | rewrite vec_zero_length; reflexivity | exact Hlt]
          | cbn [ctype_demand_row]; exists zero; rewrite Hvec; apply Hadd_zero_tail;
            rewrite Hvz_len; [lia | rewrite length_app, vec_zero_length, <- (vec_allows_length D _ _ Hva), (ctype_demand_length D _ _ _ Htd), length_app, length_skipn; cbn [length]; lia] ]
        | subst x;
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia; inversion Hl; reflexivity);
          subst e;
          rewrite skipn_app, Nat.sub_succ_l in Htd by lia;
          rewrite Nat.sub_diag, skipn_all2 in Htd by lia; cbn [app skipn] in Htd;
          rewrite Hb in Htd;
          inversion Htd; subst row;
          destruct (weaken_ctype_demand_app_left D env_b U z HU (subst_tvar_cenv U z env_a)) as [z' [Hz' Hbr_z]];
          rewrite subst_tvar_cenv_length in Hz', Hbr_z;
          pose proof (weaken_cuniverse_level_app_left D env_b U lvl_b Hlvl (subst_tvar_cenv U z env_a)) as Hlvl';
          rewrite subst_tvar_cenv_length in Hlvl';
          eexists; split; [| split; [| split]];
          [ apply (CoreTypeVal _ _ lvl_b); [exact Hz' | exact Hlvl']
          | cbn [cresult_type]; rewrite Hb; cbn [lift_cty ren_cty]; apply cty_alpha_eq_refl
          | cbn [ccomp_demand]; rewrite !length_app, subst_tvar_cenv_length; cbn [length];
            rewrite Nat.add_succ_r, vec_subst_single_eq, vec_scale_one by (rewrite vec_zero_length; reflexivity);
            rewrite vec_zero_app; apply branch_rel_refl
          | cbn [ctype_demand_row]; exists one;
            assert (Hlen_ub : length z = length (ctype_uses b)) by
              (rewrite <- (vec_allows_length D _ _ v), vec_zero_length; exact Hz_len);
            rewrite (vec_subst_zero_prefix D (length env_a) z (ctype_uses b) Hlen_ub), vec_scale_one;
            eapply branch_rel_trans; [exact Hbr_z |];
            replace (vec_zero (D := D) (length env_a) ++ z)
              with (vec_add (vec_zero (D := D) (length env_a) ++ vec_zero (D := D) (length env_b))
                            (vec_zero (D := D) (length env_a) ++ z)) at 1
              by (rewrite vec_zero_app;
                  replace (length env_a + length env_b) with (length (vec_zero (D := D) (length env_a) ++ z))
                    by (rewrite length_app, vec_zero_length, Hz_len; reflexivity);
                  rewrite vec_add_zero_l; reflexivity);
            apply branch_rel_add;
            [ apply branch_rel_app; [apply branch_rel_refl | eapply vec_allows_zero_branch_rel; [intros Hn g Hg; symmetry; exact (Hnone_eq Hn _ _ Hg) | exact v]]
            | apply branch_rel_refl ] ]
        | assert (Hlen_e : length (vec_zero (S x) ++ ctype_uses e) = S (length env_a + length env_b)) by
            (rewrite length_app, vec_zero_length, <- (vec_allows_length D _ _ Hva), (ctype_demand_length D _ _ _ Htd), length_skipn, length_app;
             cbn [length];
             assert (Hx_lt : x < length (env_a ++ b :: env_b)) by (unfold clookup in Hl; apply nth_error_Some; congruence);
             rewrite length_app in Hx_lt; cbn [length] in Hx_lt; lia);
          destruct (subst_tvar_lookup_gt D U z env_a b env_b x e Hgt Hz_len Hlen_e Hl) as [e' [Hl' [Hann [Hvec Hsk]]]];
          destruct (subst_tvar_lookup_gt_ann D U z env_a b env_b x e Hgt Hl) as [e_raw [Hl_raw [He_eq [Hann_raw Hsk_raw]]]];
          assert (He'_eq : e' = e_raw) by (rewrite Hl' in Hl_raw; inversion Hl_raw; reflexivity); subst e_raw;
          rewrite <- Hsk in Htd;
          assert (Huses' : ctype_uses e' = ctype_uses e) by (rewrite He'_eq; reflexivity);
          assert (Hva' : vec_allows row (ctype_uses e')) by (rewrite Huses'; exact Hva);
          rewrite <- He'_eq in Htd;
          eexists; split; [| split; [| split]];
          [ eapply CoreVar; [exact Hl' | exact Htd | exact Hva']
          | cbn [cresult_type]; rewrite Hann; apply cty_alpha_eq_refl
          | cbn [ccomp_demand]; rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
            [ apply branch_rel_refl
            | rewrite vec_zero_length; reflexivity
            | exact Hgt
            | assert (Hx_lt : x < length (env_a ++ b :: env_b)) by (unfold clookup in Hl; apply nth_error_Some; congruence);
              rewrite length_app in Hx_lt; cbn [length] in Hx_lt; lia ]
          | cbn [ctype_demand_row]; exists zero; rewrite Hvec; apply Hadd_zero_tail;
            rewrite Hvz_len; [lia |
              rewrite length_app, vec_zero_length, <- (vec_allows_length D _ _ Hva), (ctype_demand_length D _ _ _ Htd), length_skipn, length_app, subst_tvar_cenv_length;
              assert (Hx_lt : x < length (env_a ++ b :: env_b)) by (unfold clookup in Hl; apply nth_error_Some; congruence);
              rewrite length_app in Hx_lt; cbn [length] in Hx_lt; lia] ] ]
    end.
  - (* CoreNatVal *)
    lazymatch goal with
    | Hcd : CIdxDemand _ i d |- _ =>
        destruct (subst_tvar_idx_demand D U z env_a b env_b lvl_b i d Hb Hsafe HU Hcd) as [d' [Hd' Hbrd]];
        pose proof (cidx_demand_tvar_nth_zero D b env_b lvl_b ED Hb _ _ _ Hcd env_a eq_refl) as Hnth;
        rewrite (vec_subst_nth_zero_indep D (length env_a) z (vec_zero (length env_b)) d Hnth ltac:(rewrite vec_zero_length; exact Hz_len)) in Hbrd;
        eexists; split; [| split; [| split]];
        [ apply CoreNatVal; exact Hd'
        | cbn [cresult_type subst_tvar_in_cty]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; exact Hbrd
        | cbn [ctype_demand_row]; exists zero;
          rewrite !length_app, subst_tvar_cenv_length; cbn [length];
          rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len;
          apply Hadd_zero_tail; rewrite vec_zero_length; reflexivity ]
    end.
  - (* CoreBoolVal *)
    eexists; split; [| split; [| split]];
    [ apply CoreBoolVal
    | cbn [cresult_type subst_tvar_in_cty]; apply cty_alpha_eq_refl
    | cbn [ccomp_demand]; rewrite !length_app, subst_tvar_cenv_length; cbn [length];
      rewrite Nat.add_succ_r, vec_subst_zero by (apply vec_zero_length); apply branch_rel_refl
    | cbn [ctype_demand_row]; exists zero;
      rewrite !length_app, subst_tvar_cenv_length; cbn [length];
      rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len;
      apply Hadd_zero_tail; rewrite vec_zero_length; reflexivity ].
  - (* CoreTypeVal *)
    lazymatch goal with
    | Htd : CTypeDemand _ ?ty ?d, Hlu : CUniverseLevel _ ?ty ?lvl |- _ =>
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b ty d Hb Hsafe HU Htd) as [d' [Hd' Hbrd]];
        pose proof (subst_tvar_cuniverse_level D U z env_a b env_b lvl_b ty lvl Hb Hlvl Hlu) as Hlu';
        eexists; split; [| split; [| split]];
        [ apply CoreTypeVal; [exact Hd' | exact Hlu']
        | cbn [cresult_type subst_tvar_in_cty]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; rewrite !length_app, subst_tvar_cenv_length; cbn [length];
          rewrite Nat.add_succ_r, vec_subst_zero by (apply vec_zero_length); apply branch_rel_refl
        | cbn [ctype_demand_row]; exists zero;
          eapply branch_rel_trans; [exact Hbrd |];
          apply Hadd_zero_tail; rewrite Hvz_len; [lia |
          pose proof (ctype_demand_length D _ _ _ Htd) as Hlt;
          rewrite length_app in Hlt; cbn [length] in Hlt; lia ] ]
    end.
  - (* CoreLam *)
    lazymatch goal with
    | Ha : CTypeDemand _ dom a, Hcd : allows (nth_grade ?u_bod 0) s, Hbd : allows (nth_grade ?v_bod 0) r |- _ =>
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Ha env_a eq_refl) as Hdom_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b dom a Hb Hsafe HU Ha) as [a' [Ha' Hbra]];
        assert (Hsafe_x : cenv_tvar_safe ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [exact Hdom_safe | exact Hsafe]);
        destruct (IHCoreDerives ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) eq_refl Hsafe_x)
          as [[rt' u' v'] [Hb' [Hrt' [Hu' [q_bod Hv']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hb', Hrt', Hu', Hv';
        rewrite (lift_cty_1_S D (length env_a) U) in Hb', Hrt';
        assert (Hrel_x : cenv_demand_rel
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) dom; ctype_uses := a' |}
           :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) dom; ctype_uses := vec_subst (length env_a) z a |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | apply cty_alpha_eq_refl | exact Ha' | exact Hbra]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hb' _ Hrel_x) as [[rt2 u2 v2] [Hb2 [Hrt2 [Hu2 Hv2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hrt2, Hu2, Hv2;
        assert (Hu_tr : branch_rel u2 (vec_subst (S (length env_a)) (vec_zero (length env_b)) u_bod)) by (eapply branch_rel_trans; [exact Hu2 | exact Hu']);
        assert (Hv_tr : branch_rel v2 (vec_add (vec_subst (S (length env_a)) z v_bod) (vec_zero (S (length env_a)) ++ vec_scale q_bod z))) by
          (eapply branch_rel_trans; [exact Hv2 | exact Hv']);
        pose proof (core_derives_lengths D _ _ _ H) as [Hlu Hlv_len];
        cbn [ccomp_demand ctype_demand_row length] in Hlu, Hlv_len;
        rewrite length_app in Hlu, Hlv_len; cbn [length] in Hlu, Hlv_len;
        assert (Hcd' : allows (nth_grade u2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hcd]);
        assert (Hbd' : allows (nth_grade v2 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hv_tr) |
           rewrite nth_grade_add by (rewrite Hvz_len, length_app, vec_zero_length, vec_scale_length, Hz_len by lia; lia);
           rewrite vec_subst_nth_lt by lia;
           change (vec_zero (D := D) (S (length env_a)) ++ vec_scale q_bod z) with (zero :: (vec_zero (D := D) (length env_a) ++ vec_scale q_bod z));
           rewrite nth_grade_0_cons, add_zero_r; exact Hbd]);
        eexists; split; [| split; [| split]];
        [ eapply CoreLam; [exact Ha' | exact Hb2 | exact Hcd' | exact Hbd']
        | cbn [cresult_type subst_tvar_in_cty]; unfold cty_alpha_eq in *; cbn;
          rewrite (cty_alpha_eq_trans D _ _ _ Hrt2 Hrt'); reflexivity
        | cbn [ccomp_demand]; rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu_tr
        | cbn [ctype_demand_row]; exists q_bod;
          pose proof (branch_rel_tl D _ _ Hv_tr) as Htl;
          rewrite tl_vec_add, <- vec_subst_tl, Htl_zero_tail in Htl;
          pose proof (ctype_demand_length D _ _ _ Ha) as Hla_len;
          rewrite length_app in Hla_len; cbn [length] in Hla_len;
          rewrite (vec_subst_add D (length env_a) z a (tl v_bod) (length env_b))
            by (try exact Hz_len; destruct v_bod; cbn in *; lia);
          rewrite <- vec_add_assoc;
          apply branch_rel_add; [exact Hbra | exact Htl] ]
    end.
  - (* CoreApp *)
    lazymatch goal with
    | Hdm_eq : cty_alpha_eq kind dom,
      Ha_dom : CTypeDemand _ dom a_dom,
      Hb_cod : CTypeDemand _ cod ?b0,
      Hbr_allow : allows (nth_grade ?b0 0) r,
      Huniv : forall lvl arg_ty, dom = CUniv lvl -> _,
      Happ : app_result_ty dom cod arg = Some res_ty,
      Hz_ty : z_type = app_type_arg_demand dom arg u_arg v_arg |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[rt_fn w' v_fn'] [Hfn' [Hrt_fn [Hw' [q_fn Hv_fn']]]]];
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[rt_arg u_arg' v_arg'] [Harg' [Hrt_arg [Hu_arg' [q_arg Hv_arg']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in *;
        destruct (cty_alpha_eq_CPi_inv D rt_fn x s r
                    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) dom)
                    (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) cod) Hrt_fn)
          as [x0 [dom0 [cod0 [-> [Hdom0 Hcod0]]]]];
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Ha_dom env_a eq_refl) as Hdom_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hb_cod ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) eq_refl) as Hcod_safe;
        cbn [length] in Hcod_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b dom a_dom Hb Hsafe HU Ha_dom) as [a_dom' [Ha_dom' Hbra]];
        assert (Ha_dom0 : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) dom0 a_dom') by
          (eapply CTypeDemand_alpha_ty; [exact Ha_dom' | apply cty_alpha_eq_sym; exact Hdom0]);
        assert (Hsafe_x : cenv_tvar_safe ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [exact Hdom_safe | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) b env_b lvl_b cod b0 Hb Hsafe_x HU Hb_cod)
          as [b_cod' [Hb_cod' Hbrb]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hb_cod', Hbrb;
        rewrite (lift_cty_1_S D (length env_a) U) in Hb_cod';
        assert (Hb_cod0 : CTypeDemand ({| cbinder := x0; cannotation := dom0; ctype_uses := a_dom' |} :: subst_tvar_cenv U z env_a ++ env_b) cod0 b_cod') by
          (eapply CTypeDemand_alpha_ty;
           [ eapply CTypeDemand_alpha_env; [| exact Hb_cod'];
             constructor; [cbn; apply cty_alpha_eq_sym; exact Hdom0 | apply cenv_alpha_eq_refl]
           | apply cty_alpha_eq_sym; exact Hcod0 ]);
        assert (Hdm_eq0 : cty_alpha_eq rt_arg dom0) by
          (eapply cty_alpha_eq_trans; [exact Hrt_arg | eapply cty_alpha_eq_trans; [apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hdm_eq] | apply cty_alpha_eq_sym; exact Hdom0]]);
        pose proof (ctype_demand_length D _ _ _ Hb_cod) as Hlen_b;
        cbn [ccomp_demand ctype_demand_row length] in Hlen_b; rewrite length_app in Hlen_b; cbn [ccomp_demand ctype_demand_row length] in Hlen_b;
        assert (Hbr_allow0 : allows (nth_grade b_cod' 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | rewrite vec_subst_nth_lt by lia; exact Hbr_allow]);
        assert (Hcod0_flags : match dom with
                              | CNat => cty_uses_kinds true false true true true true true 0 cod = false
                              | CUniv _ => cty_uses_kinds false true false false false false false 0 cod = false
                              | _ => True
                              end) by
          (destruct dom; try exact I;
           [ eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
           | eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity] ]);
        assert (Harg_safe : match arg with
                            | CNatVal i => cidx_uses_kinds false false false false false (length env_a) i = false
                            | CTypeVal T0 => cty_uses_kinds false true false false false false false (length env_a) T0 = false
                            | CVar y => match dom with CUniv _ => True | _ => y <> length env_a end
                            | _ => True
                            end) by
          (destruct arg; try exact I;
           [ destruct dom; try exact I;
             intro Heq; subst; inversion H0; subst;
             lazymatch goal with Hlk : clookup _ (length env_a) = Some ?ee |- _ =>
               unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
               unfold cty_alpha_eq in Hdm_eq; rewrite erase_hints_ren, Hb in Hdm_eq; cbn in Hdm_eq; discriminate
             end
           | inversion H0; subst;
             lazymatch goal with Hc : CIdxDemand _ _ _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hc env_a eq_refl) end
           | inversion H0; subst;
             lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) ?tt _ |- _ => exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd env_a eq_refl) end ]);
        rewrite <- (lift_cty_1_S D (length env_a) U) in Hcod0;
        destruct (app_result_ty_subst_tvar D dom dom0 cod cod0 U arg (length env_a) res_ty
                    Hdom0 Hcod0 Hcod_safe Hcod0_flags Harg_safe Happ) as [res' [Hres' Hres_eq]];
        assert (Huniv0 : forall lvl arg_ty, dom0 = CUniv lvl ->
                  (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) arg = CTypeVal arg_ty \/
                   (exists y, subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) arg = CVar y /\ arg_ty = CTVar y)) ->
                  CUniverseLevel (subst_tvar_cenv U z env_a ++ env_b) arg_ty lvl) by
          (intros lvl arg_ty Hdom0_u [Hctv | [y [Hcv ->]]];
           [ subst dom0; unfold cty_alpha_eq in Hdom0; destruct dom; cbn in Hdom0; try discriminate;
             [ inversion Hdom0; subst;
               destruct arg; cbn in Hctv; try discriminate;
               [ lazymatch type of Hctv with context [?xa =? length env_a] =>
                   destruct (Nat.eqb_spec xa (length env_a)) as [Heq_x | Hne];
                   [ cbn in Hctv; inversion Hctv; subst arg_ty;
                     lazymatch goal with |- CUniverseLevel _ _ ?lv =>
                       assert (Hlv_eq : lv = lvl_b) by
                         (subst xa; inversion H0; subst;
                          lazymatch goal with Hlk : clookup _ (length env_a) = Some ?ee, Heq : cty_alpha_eq (ren_cty _ (cannotation ?ee)) (CUniv _) |- _ =>
                            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                            unfold cty_alpha_eq in Heq; rewrite erase_hints_ren, Hb in Heq; cbn in Heq; inversion Heq; reflexivity
                          end);
                       subst lv
                     end;
                     pose proof (weaken_cuniverse_level_app_left D env_b U lvl_b Hlvl (subst_tvar_cenv U z env_a)) as Hwk_u;
                     rewrite subst_tvar_cenv_length in Hwk_u; exact Hwk_u
                   | cbn in Hctv;
                     destruct (Nat.ltb_spec xa (length env_a)); discriminate ]
                 end
               | inversion Hctv; subst arg_ty;
                 eapply subst_tvar_cuniverse_level; [exact Hb | exact Hlvl | eapply Huniv; [reflexivity | left; reflexivity]] ]
             | lazymatch type of Hdom0 with context [?xd =? length env_a] =>
                 destruct (Nat.eqb_spec xd (length env_a)) as [Heq_xd | Hnex];
                 [ destruct arg; cbn in Hctv; try discriminate;
                   [ lazymatch type of Hctv with context [?xa =? length env_a] =>
                       destruct (Nat.eqb_spec xa (length env_a)) as [Heq_x | Hne];
                       [ subst xa; exfalso; apply Harg_safe; reflexivity
                       | cbn in Hctv;
                         destruct (Nat.ltb_spec xa (length env_a)); discriminate ]
                     end
                   | inversion H0; subst;
                     lazymatch goal with Hc : cty_alpha_eq (CUniv _) (CTVar _) |- _ =>
                       unfold cty_alpha_eq in Hc; cbn in Hc; discriminate
                     end ]
                 | cbn in Hdom0;
                   destruct (Nat.ltb_spec xd (length env_a)); discriminate ]
               end ]
           | subst dom0; rewrite Hcv in Harg'; inversion Harg'; subst;
             lazymatch goal with Hlk : clookup _ y = Some ?ey |- _ =>
               eapply CLevelTVar; [exact Hlk |];
               pose proof Hdm_eq0 as Hren_eq;
               unfold cty_alpha_eq in Hren_eq |- *; rewrite erase_hints_ren in Hren_eq;
               destruct (cannotation ey); cbn in Hren_eq |- *; try discriminate; exact Hren_eq
             end ]);
        eexists; split; [| split; [| split]];
        [ eapply CoreApp; [exact Hfn' | exact Harg' | exact Hdm_eq0 | exact Ha_dom0 | exact Hb_cod0 | exact Hbr_allow0
                          | exact Huniv0 | exact Hres' | reflexivity]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
          pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ua _];
          rewrite length_app in Hlen_w, Hlen_ua; cbn [ccomp_demand ctype_demand_row length] in Hlen_w, Hlen_ua;
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) w (vec_scale s u_arg) (length env_b))
            by (try apply vec_zero_length; try rewrite vec_scale_length; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [exact Hw' | apply branch_rel_scale; exact Hu_arg']
        | cbn [ctype_demand_row];
          destruct (subst_tvar_app_type_arg_demand D ED U b env_a env_b lvl_b z dom dom0 kind rt_arg arg
                      u_arg v_arg u_arg' v_arg' q_arg Hb HU Hnone_z Hsome_z H0 Hdm_eq Hdom0 Harg' Hu_arg' Hv_arg') as [q_z Hqz];
          exists (mul r q_z);
          pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ua Hlen_va];
          rewrite length_app in Hlen_ua, Hlen_va; cbn [ccomp_demand ctype_demand_row length] in Hlen_ua, Hlen_va;
          assert (Hlen_b0 : length (tl b0) = length env_a + S (length env_b)) by (destruct b0; cbn in *; lia);
          assert (Hlen_z : length (app_type_arg_demand dom arg u_arg v_arg) = length env_a + S (length env_b)) by
            (unfold app_type_arg_demand; destruct dom, arg; lia);
          rewrite Hz_ty;
          rewrite (vec_subst_add D (length env_a) z (tl b0) (vec_scale r (app_type_arg_demand dom arg u_arg v_arg)) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; lia);
          rewrite vec_subst_scale, <- (vec_scale_zero_tail_assoc D z (length env_a) r q_z);
          rewrite <- vec_add_assoc;
          apply branch_rel_add;
          [ apply branch_rel_tl in Hbrb; rewrite <- vec_subst_tl in Hbrb by lia; exact Hbrb
          | rewrite <- vec_scale_add; apply branch_rel_scale; exact Hqz ] ]
    end.
  - (* CoreLet *)
    lazymatch goal with
    | Hann : CTypeDemand _ ann ?a_dom, Hbod_cd : allows (nth_grade u_bod 0) s, Hbod_ty : allows (nth_grade v_bod 0) r,
      Hnf : cty_uses_var 0 bod_ty = false |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[rt_rhs u_rhs' v_rhs'] [Hrhs' [Hrt_rhs [Hu_rhs' [q_rhs Hv_rhs']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hrt_rhs, Hu_rhs', Hv_rhs';
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hann env_a eq_refl) as Hann_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b ann a_dom Hb Hsafe HU Hann) as [a_dom' [Ha_dom' Hbra]];
        assert (Hsafe_x : cenv_tvar_safe ({| cbinder := x; cannotation := ann; ctype_uses := a_dom |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [exact Hann_safe | exact Hsafe]);
        destruct (IHCoreDerives2 ({| cbinder := x; cannotation := ann; ctype_uses := a_dom |} :: env_a) eq_refl Hsafe_x)
          as [[rt_bod1 u_bod1 v_bod1] [Hbod1 [Hrt_bod1 [Hu_bod1 [q_bod Hv_bod1]]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hbod1, Hrt_bod1, Hu_bod1, Hv_bod1;
        assert (Hrel_x : cenv_demand_rel
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ann; ctype_uses := a_dom' |}
           :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ann; ctype_uses := vec_subst (length env_a) z a_dom |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | apply cty_alpha_eq_refl | exact Ha_dom' | exact Hbra]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hbod1 _ Hrel_x) as [[rt_bod2 u_bod2 v_bod2] [Hbod2 [Hrt_bod2 [Hu_bod2 Hv_bod2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hrt_bod2, Hu_bod2, Hv_bod2;
        assert (Hu_tr : branch_rel u_bod2 (vec_subst (S (length env_a)) (vec_zero (length env_b)) u_bod)) by (eapply branch_rel_trans; [exact Hu_bod2 | exact Hu_bod1]);
        assert (Hv_tr : branch_rel v_bod2 (vec_add (vec_subst (S (length env_a)) z v_bod) (vec_zero (S (length env_a)) ++ vec_scale q_bod z))) by
          (eapply branch_rel_trans; [exact Hv_bod2 | exact Hv_bod1]);
        assert (Hrt_bod_tr : cty_alpha_eq rt_bod2 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) bod_ty)) by
          (eapply cty_alpha_eq_trans; [exact Hrt_bod2 | exact Hrt_bod1]);
        pose proof (core_derives_tvar_safe D b env_b lvl_b Hb _ _ _ H0 ({| cbinder := x; cannotation := ann; ctype_uses := a_dom |} :: env_a) eq_refl) as Hbod_safe;
        cbn [cresult_type length] in Hbod_safe;
        assert (Hnf2 : cty_uses_var 0 rt_bod2 = false) by
          (rewrite (cty_uses_var_alpha_eq D 0 rt_bod2 _ Hrt_bod_tr);
           apply cty_uses_var_subst_tvar_0; [exact Hnf | exact Hbod_safe]);
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_ur Hlen_vr];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ub Hlen_vb];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_ur, Hlen_vr, Hlen_ub, Hlen_vb;
        rewrite length_app in Hlen_ur, Hlen_vr, Hlen_ub, Hlen_vb; cbn [length] in Hlen_ur, Hlen_vr, Hlen_ub, Hlen_vb;
        assert (Hbod_cd' : allows (nth_grade u_bod2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hbod_cd]);
        assert (Hbod_ty' : allows (nth_grade v_bod2 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hv_tr) |
           rewrite nth_grade_add, vec_subst_nth_lt
             by (rewrite ?Hvz_len, ?length_app, ?vec_zero_length, ?vec_scale_length, ?Hz_len by lia; lia);
           change (vec_zero (D := D) (S (length env_a)) ++ vec_scale q_bod z) with (zero :: (vec_zero (D := D) (length env_a) ++ vec_scale q_bod z));
           rewrite nth_grade_0_cons, add_zero_r; exact Hbod_ty]);
        assert (Hrt_rhs0 : cty_alpha_eq rt_rhs (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ann)) by
          (eapply cty_alpha_eq_trans; [exact Hrt_rhs | apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | assumption]]);
        eexists; split; [| split; [| split]];
        [ rewrite (lift_cty_1_S D (length env_a) U) in Hbod2;
          eapply CoreLet; [exact Ha_dom' | exact Hrhs' | exact Hrt_rhs0 | exact Hbod2 | exact Hbod_cd' | exact Hbod_ty' | exact Hnf2]
        | cbn [cresult_type subst_tvar_in_cty];
          eapply cty_alpha_eq_trans; [apply cty_alpha_eq_unshift; exact Hrt_bod_tr |];
          rewrite (lift_cty_1_S D (length env_a) U);
          rewrite <- (subst_tvar_in_cty_unshift_0 D bod_ty (lift_cty 0 (length env_a) U) (length env_a) Hnf Hbod_safe);
          apply cty_alpha_eq_refl
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) (tl u_bod) (vec_scale s u_rhs) (length env_b))
            by (try apply vec_zero_length; try rewrite vec_scale_length; destruct u_bod; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu_tr
          | apply branch_rel_scale; exact Hu_rhs' ]
        | cbn [ctype_demand_row];
          assert (Htl_vb : branch_rel (tl v_bod2) (vec_add (vec_subst (length env_a) z (tl v_bod)) (vec_zero (length env_a) ++ vec_scale q_bod z))) by
            (pose proof (branch_rel_tl D _ _ Hv_tr) as Htl;
             rewrite tl_vec_add, <- vec_subst_tl, Htl_zero_tail in Htl; exact Htl);
          destruct (subst_tvar_app_type_arg_demand D ED U b env_a env_b lvl_b z ann
                      (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ann)
                      rhs_ty rt_rhs rhs u_rhs v_rhs u_rhs' v_rhs' q_rhs Hb HU Hnone_z Hsome_z
                      H ltac:(assumption) ltac:(apply cty_alpha_eq_refl) Hrhs' Hu_rhs' Hv_rhs') as [q_z Hqz];
          assert (Hlen_z : length (app_type_arg_demand ann rhs u_rhs v_rhs) = length env_a + S (length env_b)) by
            (unfold app_type_arg_demand; destruct ann, rhs; lia);
          exists (add q_bod (mul r q_z));
          rewrite (vec_subst_add D (length env_a) z (tl v_bod) (vec_scale r (app_type_arg_demand ann rhs u_rhs v_rhs)) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_bod; cbn in *; lia);
          rewrite vec_subst_scale, <- branch_rel_scale_add_tail, <- vec_scale_zero_tail_assoc;
          rewrite <- (vec_add_assoc D (vec_subst (length env_a) z (tl v_bod)) (vec_scale r (vec_subst (length env_a) z (app_type_arg_demand ann rhs u_rhs v_rhs))) _);
          rewrite (vec_add_assoc D (vec_scale r (vec_subst (length env_a) z (app_type_arg_demand ann rhs u_rhs v_rhs))) (vec_zero (length env_a) ++ vec_scale q_bod z) _);
          rewrite (vec_add_comm D (vec_scale r (vec_subst (length env_a) z (app_type_arg_demand ann rhs u_rhs v_rhs))) (vec_zero (length env_a) ++ vec_scale q_bod z));
          rewrite <- (vec_add_assoc D (vec_zero (length env_a) ++ vec_scale q_bod z) _ _);
          rewrite (vec_add_assoc D (vec_subst (length env_a) z (tl v_bod)) (vec_zero (length env_a) ++ vec_scale q_bod z) _);
          apply branch_rel_add;
          [ exact Htl_vb
          | rewrite <- vec_scale_add; apply branch_rel_scale; exact Hqz ] ]
    end.
  - (* CorePair *)
    lazymatch goal with
    | Ha : CTypeDemand _ fst_ty a, Hb_snd : CTypeDemand _ snd_ty ?b0, Hrb : allows (nth_grade ?b0 0) r,
      Hft : cty_alpha_eq fst_act fst_ty, Happ : app_result_ty fst_ty snd_ty fst_val = Some exp_snd,
      Hsd : cty_alpha_eq snd_act exp_snd |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[fa' ul' vl'] [Hf' [Hfa' [Hul' [ql Hvl']]]]];
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[sa' ur' vr'] [Hs' [Hsa' [Hur' [qr Hvr']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in *;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Ha env_a eq_refl) as Hfst_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hb_snd ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) eq_refl) as Hsnd_safe;
        cbn [length] in Hsnd_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b fst_ty a Hb Hsafe HU Ha) as [a' [Ha' Hbra]];
        assert (Hsafe_x : cenv_tvar_safe ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [exact Hfst_safe | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) b env_b lvl_b snd_ty b0 Hb Hsafe_x HU Hb_snd)
          as [b0' [Hb0' Hbrb]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hb0', Hbrb;
        rewrite (lift_cty_1_S D (length env_a) U) in Hb0';
        pose proof (ctype_demand_length D _ _ _ Hb_snd) as Hlen_b0;
        cbn [ccomp_demand ctype_demand_row length] in Hlen_b0; rewrite length_app in Hlen_b0; cbn [length] in Hlen_b0;
        assert (Hrb' : allows (nth_grade b0' 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | rewrite vec_subst_nth_lt by lia; exact Hrb]);
        assert (Hft' : cty_alpha_eq fa' (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) fst_ty)) by
          (eapply cty_alpha_eq_trans; [exact Hfa' | apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hft]]);
        assert (Hsnd_flags : match fst_ty with
                             | CNat => cty_uses_kinds true false true true true true true 0 snd_ty = false
                             | CUniv _ => cty_uses_kinds false true false false false false false 0 snd_ty = false
                             | _ => True
                             end) by
          (destruct fst_ty; try exact I;
           [ eapply ctype_demand_uses_kinds; [exact Hb_snd | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
           | eapply ctype_demand_uses_kinds; [exact Hb_snd | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity] ]);
        assert (Hfval_safe : match fst_val with
                             | CNatVal i => cidx_uses_kinds false false false false false (length env_a) i = false
                             | CTypeVal T0 => cty_uses_kinds false true false false false false false (length env_a) T0 = false
                             | CVar y => match fst_ty with CUniv _ => True | _ => y <> length env_a end
                             | _ => True
                             end) by
          (destruct fst_val; try exact I;
           [ destruct fst_ty; try exact I;
             intro Heq; subst; inversion H; subst;
             lazymatch goal with Hlk : clookup _ (length env_a) = Some ?ee |- _ =>
               unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
               unfold cty_alpha_eq in Hft; rewrite erase_hints_ren, Hb in Hft; cbn in Hft; discriminate
             end
           | inversion H; subst;
             lazymatch goal with Hc : CIdxDemand _ _ _ |- _ => exact (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hc env_a eq_refl) end
           | inversion H; subst;
             lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) ?tt _ |- _ => exact (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd env_a eq_refl) end ]);
        destruct (app_result_ty_subst_tvar D fst_ty (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) fst_ty)
                    snd_ty (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) snd_ty) U fst_val (length env_a) exp_snd
                    (cty_alpha_eq_refl D _) (cty_alpha_eq_refl D _) Hsnd_safe Hsnd_flags Hfval_safe Happ) as [exp_snd' [Happ' Hexp_eq]];
        assert (Hsd' : cty_alpha_eq sa' exp_snd') by
          (eapply cty_alpha_eq_trans; [exact Hsa' |];
           eapply cty_alpha_eq_trans; [apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hsd] | apply cty_alpha_eq_sym; exact Hexp_eq]);
        assert (Hb0'' : CTypeDemand
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) fst_ty; ctype_uses := a' |}
           :: subst_tvar_cenv U z env_a ++ env_b)
          (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) snd_ty) b0') by
          (eapply CTypeDemand_alpha_env; [| exact Hb0']; constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]);
        pose proof (core_derives_lengths D _ _ _ H) as [Hlu_l _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlu_r _];
        pose proof (ctype_demand_length D _ _ _ Ha) as Hla;
        cbn [ccomp_demand ctype_demand_row length] in Hlu_l, Hlu_r, Hla;
        rewrite length_app in Hlu_l, Hlu_r, Hla; cbn [length] in Hlu_l, Hlu_r, Hla;
        eexists; split; [| split; [| split]];
        [ eapply CorePair; [exact Ha' | exact Hb0'' | exact Hrb' | exact Hf' | exact Hft' | exact Hs' | rewrite (lift_cty_1_S D (length env_a) U) in Happ'; exact Happ' | exact Hsd']
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) u_l u_r (length env_b)) by (try apply vec_zero_length; lia);
          apply branch_rel_add; assumption
        | cbn [ctype_demand_row]; exists zero;
          rewrite (vec_subst_add D (length env_a) z a (tl b0) (length env_b)) by (try exact Hz_len; destruct b0; cbn in *; lia);
          eapply branch_rel_trans;
          [ apply branch_rel_add; [exact Hbra | apply branch_rel_tl in Hbrb; rewrite <- vec_subst_tl in Hbrb; exact Hbrb]
          | apply Hadd_zero_tail;
            rewrite vec_add_length;
            [ rewrite Hvz_len by lia; lia
            | rewrite !Hvz_len by (destruct b0; cbn in *; lia); reflexivity ] ] ]
    end.
  - (* CoreLetPair *)
    lazymatch goal with
    | Ha : CTypeDemand _ A a, Hb_B : CTypeDemand _ B ?b0, Hmot : CTypeDemand _ mot v_mot,
      Hkap : allows (nth_grade v_mot 0) kappa, Hexp : exp_mot = spec_pair_body_cty 0 mot,
      Hmot_eq : cty_alpha_eq act_mot exp_mot, Hs1 : allows (nth_grade u_b 1) s, Hs0 : allows (nth_grade u_b 0) s,
      Hdep : context [cty_uses_var 0 mot = false], Hres : res_ty = spec_pair_subj_cty pr mot |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[tp' w' vp'] [Hpr' [Htp' [Hw' [qp Hvp']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in Htp', Hw', Hvp';
        destruct (cty_alpha_eq_CSigma_inv D tp' z0 r
                    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A)
                    (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) B) Htp')
          as [z0' [A0 [B0 [Htp_eq [HA0 HB0]]]]];
        rewrite Htp_eq in Hpr', Htp'; clear Htp_eq;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Ha env_a eq_refl) as HA_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hb_B ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl) as HB_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot ({| cbinder := 0; cannotation := CSigma z0 r A B; ctype_uses := vec_add a (tl b0) |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in HB_safe, Hmot_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b A a Hb Hsafe HU Ha) as [a' [Ha' Hbra]];
        assert (HA0' : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) A0 a') by
          (eapply CTypeDemand_alpha_ty; [exact Ha' | apply cty_alpha_eq_sym; exact HA0]);
        assert (Hsafe_x : cenv_tvar_safe ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [exact HA_safe | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) b env_b lvl_b B b0 Hb Hsafe_x HU Hb_B)
          as [b0' [Hb0' Hbrb]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hb0', Hbrb;
        rewrite (lift_cty_1_S D (length env_a) U) in Hb0';
        assert (HB0' : CTypeDemand ({| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_tvar_cenv U z env_a ++ env_b) B0 b0') by
          (eapply CTypeDemand_alpha_ty;
           [ eapply CTypeDemand_alpha_env; [| exact Hb0']; constructor; [cbn; apply cty_alpha_eq_sym; exact HA0 | apply cenv_alpha_eq_refl]
           | apply cty_alpha_eq_sym; exact HB0 ]);
        assert (Hsafe_sig : cenv_tvar_safe ({| cbinder := 0; cannotation := CSigma z0 r A B; ctype_uses := vec_add a (tl b0) |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [cbn; rewrite HA_safe, HB_safe; reflexivity | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := 0; cannotation := CSigma z0 r A B; ctype_uses := vec_add a (tl b0) |} :: env_a) b env_b lvl_b mot v_mot Hb Hsafe_sig HU Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hv_mot', Hbr_mot;
        pose proof (ctype_demand_length D _ _ _ Ha) as Hla;
        pose proof (ctype_demand_length D _ _ _ Hb_B) as Hlb0;
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        cbn [length] in Hla, Hlb0, Hlen_vm; rewrite length_app in Hla, Hlb0, Hlen_vm; cbn [length] in Hla, Hlb0, Hlen_vm;
        assert (Hbr_sig : branch_rel (vec_add a' (tl b0')) (vec_subst (length env_a) z (vec_add a (tl b0)))) by
          (rewrite (vec_subst_add D (length env_a) z a (tl b0) (length env_b)) by (try exact Hz_len; destruct b0; cbn in *; lia);
           apply branch_rel_add; [exact Hbra | apply branch_rel_tl in Hbrb; rewrite <- vec_subst_tl in Hbrb; exact Hbrb]);
        assert (Hv_mot0 : CTypeDemand
          ({| cbinder := 0; cannotation := CSigma z0' r A0 B0; ctype_uses := vec_add a' (tl b0') |} :: subst_tvar_cenv U z env_a ++ env_b)
          (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) v_mot') by
          (eapply CTypeDemand_alpha_env; [| exact Hv_mot'];
           constructor; [cbn; unfold cty_alpha_eq in HA0, HB0 |- *; cbn; rewrite HA0, HB0; reflexivity | apply cenv_alpha_eq_refl]);
        assert (Hsafe_xy : cenv_tvar_safe ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (S (length env_a)))) by
          (apply cenv_tvar_safe_cons; [exact HB_safe | exact Hsafe_x]);
        destruct (IHCoreDerives2 ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl Hsafe_xy)
          as [[am1 ub1 vb1] [Hb1 [Ham1 [Hub1 [qb Hvb1]]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hb1, Ham1, Hub1, Hvb1;
        rewrite (lift_cty_2_SS D (length env_a) U) in Hb1, Ham1;
        assert (Hrel_xy : cenv_demand_rel
          ({| cbinder := y; cannotation := B0; ctype_uses := b0' |}
           :: {| cbinder := x; cannotation := A0; ctype_uses := a' |}
           :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := y; cannotation := subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) B; ctype_uses := vec_subst (S (length env_a)) z b0 |}
           :: {| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A; ctype_uses := vec_subst (length env_a) z a |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons;
           [ apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HA0 | exact HA0' | exact Hbra]
           | rewrite <- (lift_cty_1_S D (length env_a) U) in HB0; exact HB0
           | exact HB0' | exact Hbrb ]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hb1 _ Hrel_xy) as [[am2 ub2 vb2] [Hb2 [Ham2 [Hub2 Hvb2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Ham2, Hub2, Hvb2;
        assert (Hu_tr : branch_rel ub2 (vec_subst (S (S (length env_a))) (vec_zero (length env_b)) u_b)) by
          (eapply branch_rel_trans; [exact Hub2 | exact Hub1]);
        assert (Ham_tr : cty_alpha_eq am2 (subst_tvar_in_cty (S (S (length env_a))) (lift_cty 0 2 (lift_cty 0 (length env_a) U)) act_mot)) by
          (eapply cty_alpha_eq_trans; [exact Ham2 | exact Ham1]);
        assert (Hspec_body : subst_tvar_in_cty (S (S (length env_a))) (lift_cty 0 2 (lift_cty 0 (length env_a) U)) (spec_pair_body_cty 0 mot) =
                             spec_pair_body_cty 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot)) by
          (rewrite <- (lift_cty_2_SS D (length env_a) U);
           apply subst_tvar_spec_pair_body; [lia | exact Hmot_safe]);
        assert (Hmot_eq2 : cty_alpha_eq am2 (spec_pair_body_cty 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))) by
          (eapply cty_alpha_eq_trans; [exact Ham_tr |]; rewrite <- Hspec_body, <- Hexp; apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hmot_eq]);
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ub _];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_w, Hlen_ub;
        rewrite length_app in Hlen_w, Hlen_ub; cbn [length] in Hlen_w, Hlen_ub;
        assert (Hkap2 : allows (nth_grade v_mot' 0) kappa) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; exact Hkap]);
        assert (Hs1_2 : allows (nth_grade ub2 1) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 1 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hs1]);
        assert (Hs0_2 : allows (nth_grade ub2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hs0]);
        assert (Hmot_nf_fn : cty_uses_var 0 mot = false ->
                  cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false) by
          (intro Hnf; apply cty_uses_var_subst_tvar_0; [exact Hnf | exact Hmot_safe]);
        assert (Hpr_not_var : forall yp, pr = CVar yp -> yp <> length env_a) by
          (intros yp -> ->; inversion H; subst;
           lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSigma _ _ _ _ |- _ =>
             unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
             rewrite Hb in Heq; cbn in Heq; discriminate
           end);
        assert (Hdep2 : match subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr with
                        | CPair _ _ _ _ fv sv => match term_as_cidx fv, term_as_cidx sv, cty_non_univ A0, cty_non_univ B0 with Some _, Some _, true, true => True | _, _, _, _ => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false end
                        | CVar _ => True
                        | _ => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false
                        end) by
          (destruct pr; cbn [subst_tvar_in_cterm]; try (apply Hmot_nf_fn; exact Hdep);
           [ destruct (Nat.eq_dec x0 (length env_a)) as [Heqn | Hne];
             [ exfalso; exact (Hpr_not_var x0 eq_refl Heqn)
             | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec x0 (length env_a)); exact I ]
           | destruct (term_as_cidx pr1) eqn:E1;
             [ destruct (term_as_cidx pr2) eqn:E2;
               [ destruct (cty_non_univ A) eqn:Ena;
                 [ destruct (cty_non_univ B) eqn:Enb;
                   [ assert (HA0_nu : cty_non_univ A0 = true) by
                       (rewrite (cty_non_univ_alpha _ _ _ HA0); apply cty_non_univ_subst_tvar_true; exact Ena);
                     assert (HB0_nu : cty_non_univ B0 = true) by
                       (rewrite (cty_non_univ_alpha _ _ _ HB0); apply cty_non_univ_subst_tvar_true; exact Enb);
                     inversion H; subst;
                     lazymatch goal with
                     | H_e1 : term_as_cidx ?p1 = Some _, H_e2 : term_as_cidx ?p2 = Some _,
                       Hdv1 : CoreDerives _ ?p1 {| cresult_type := ?fa; ccomp_demand := _; ctype_demand_row := _ |},
                       Hft : cty_alpha_eq ?fa A,
                       Happ : app_result_ty A B ?p1 = Some ?es,
                       Hdv2 : CoreDerives _ ?p2 {| cresult_type := ?sa; ccomp_demand := _; ctype_demand_row := _ |},
                       Hsd : cty_alpha_eq ?sa ?es |- _ =>
                         assert (Hfa_nu : cty_non_univ fa = true) by
                           (rewrite (cty_non_univ_alpha _ _ _ Hft); exact Ena);
                         assert (Hsa_nu : cty_non_univ sa = true) by
                           (rewrite (cty_non_univ_alpha _ _ _ Hsd); eapply cty_non_univ_app_result; [exact Ena | exact Enb | exact Happ]);
                         destruct (term_as_cidx_subst_tvar_some_non_univ D b env_a env_b lvl_b p1 _ _ (lift_cty 0 (length env_a) U) Hb Hdv1 Hfa_nu H_e1) as [_ ->];
                         destruct (term_as_cidx_subst_tvar_some_non_univ D b env_a env_b lvl_b p2 _ _ (lift_cty 0 (length env_a) U) Hb Hdv2 Hsa_nu H_e2) as [_ ->];
                         rewrite HA0_nu, HB0_nu; exact I
                     end
                   | destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr1)),
                              (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr2)),
                              (cty_non_univ A0), (cty_non_univ B0); first [exact I | apply Hmot_nf_fn; exact Hdep] ]
                 | destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr1)),
                            (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr2)),
                            (cty_non_univ A0), (cty_non_univ B0); first [exact I | apply Hmot_nf_fn; exact Hdep] ]
               | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ E2);
                 destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr1)), (cty_non_univ A0), (cty_non_univ B0);
                 apply Hmot_nf_fn; exact Hdep ]
             | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ E1);
               destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr2)), (cty_non_univ A0), (cty_non_univ B0);
               apply Hmot_nf_fn; exact Hdep ] ]);
        assert (Hres_eq : cty_alpha_eq (spec_pair_subj_cty (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr)
                                         (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))
                            (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) res_ty)) by
          (rewrite Hres; destruct pr; unfold spec_pair_subj_cty; cbn [subst_tvar_in_cterm];
            try (rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe), <- (lift_cty_1_S D (length env_a) U); apply cty_alpha_eq_refl);
           [ lazymatch goal with |- context [if ?nv =? _ then _ else _] =>
               destruct (Nat.eq_dec nv (length env_a)) as [Heqn | Hne]; [exfalso; exact (Hpr_not_var nv eq_refl Heqn) |];
               rewrite (proj2 (Nat.eqb_neq _ _) Hne);
               pose proof (subst_tvar_in_cty_subst_var_0 D mot U (length env_a) nv Hne Hmot_safe) as Hrv;
               destruct (nv <? length env_a); rewrite Hrv; apply cty_alpha_eq_refl
             end
           | destruct (term_as_cidx pr1) eqn:E1;
             [ destruct (term_as_cidx pr2) eqn:E2;
               [ destruct (cty_non_univ A) eqn:Ena;
                 [ destruct (cty_non_univ B) eqn:Enb;
                   [ inversion H; subst;
                     lazymatch goal with
                     | H_e1 : term_as_cidx ?p1 = Some ?cc1, H_e2 : term_as_cidx ?p2 = Some ?cc2,
                       Hdv1 : CoreDerives _ ?p1 {| cresult_type := ?fa; ccomp_demand := _; ctype_demand_row := _ |},
                       Hft : cty_alpha_eq ?fa A,
                       Happ : app_result_ty A B ?p1 = Some ?es,
                       Hdv2 : CoreDerives _ ?p2 {| cresult_type := ?sa; ccomp_demand := _; ctype_demand_row := _ |},
                       Hsd : cty_alpha_eq ?sa ?es |- _ =>
                         assert (Hfa_nu : cty_non_univ fa = true) by
                           (rewrite (cty_non_univ_alpha _ _ _ Hft); exact Ena);
                         assert (Hsa_nu : cty_non_univ sa = true) by
                           (rewrite (cty_non_univ_alpha _ _ _ Hsd); eapply cty_non_univ_app_result; [exact Ena | exact Enb | exact Happ]);
                         destruct (term_as_cidx_subst_tvar_some_non_univ D b env_a env_b lvl_b p1 _ cc1 (lift_cty 0 (length env_a) U) Hb Hdv1 Hfa_nu H_e1) as [Hc1' ->];
                         destruct (term_as_cidx_subst_tvar_some_non_univ D b env_a env_b lvl_b p2 _ cc2 (lift_cty 0 (length env_a) U) Hb Hdv2 Hsa_nu H_e2) as [Hc2' ->];
                         assert (Hm_ntv : cty_uses_kinds true false true true true true true 0 mot = false) by
                           (eapply cdemand_not_tvar_0_safe; [| exact Hmot]; intros ? Heq; cbn in Heq; discriminate);
                         pose proof (subst_tvar_in_cty_subst_pair D mot U 0 (length env_a) cc1 cc2 ltac:(lia) Hm_ntv Hmot_safe Hc1' Hc2') as Hcm;
                         rewrite Hcm; apply cty_alpha_eq_refl
                     end
                   | ]
                 | ];
                 destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr1)),
                          (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr2));
                 try rewrite (subst_pair_cty_no_use_unshift D _ _ _ (Hmot_nf_fn Hdep));
                 rewrite (subst_pair_cty_no_use_unshift D mot _ _ Hdep),
                         (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                         <- (lift_cty_1_S D (length env_a) U);
                 apply cty_alpha_eq_refl
               | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ E2);
                 destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr1));
                 rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                         <- (lift_cty_1_S D (length env_a) U);
                 apply cty_alpha_eq_refl ]
             | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ E1);
               destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) pr2));
               rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                       <- (lift_cty_1_S D (length env_a) U);
               apply cty_alpha_eq_refl ] ]);
        pose proof (core_derives_lengths D _ _ _ H) as [_ Hlen_vp];
        pose proof (core_derives_lengths D _ _ _ Hpr') as [_ Hlen_vp'];
        cbn [ccomp_demand ctype_demand_row] in Hlen_vp, Hlen_vp';
        rewrite length_app in Hlen_vp, Hlen_vp'; rewrite subst_tvar_cenv_length in Hlen_vp'; cbn [length] in Hlen_vp;
        eexists; rewrite <- (lift_cty_1_S D (length env_a) U); split; [| split; [| split]];
        [ eapply CoreLetPair;
          [ exact Hpr' | exact HA0' | exact HB0' | exact Hv_mot0 | exact Hkap2 | exact Hb2
          | reflexivity | exact Hmot_eq2 | exact Hs1_2 | exact Hs0_2 | exact Hdep2 | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) (tl (tl u_b)) (vec_scale s w) (length env_b))
            by (try apply vec_zero_length; try rewrite vec_scale_length; destruct u_b as [| ? [| ? ?]]; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite !vec_subst_tl by (destruct u_b; cbn in *; lia); apply branch_rel_tl, branch_rel_tl; exact Hu_tr
          | apply branch_rel_scale; exact Hw' ]
        | cbn [ctype_demand_row]; exists zero;
          eapply branch_rel_trans;
          [| apply Hadd_zero_tail; rewrite Hvz_len; [reflexivity | rewrite vec_add_length by (destruct v_mot; cbn in *; rewrite vec_scale_length; lia); destruct v_mot; cbn in *; lia] ];
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale kappa w) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot
          | apply branch_rel_scale; apply H_uv_subst; [lia | exact Hw'] ] ]
    end.
  - (* CorePromote *)
    destruct (IHCoreDerives env_a eq_refl Hsafe) as [[A' u' v'] [Hpv' [HA' [Hu' [qv Hv']]]]].
    cbn [cresult_type ccomp_demand ctype_demand_row] in HA', Hu', Hv'.
    pose proof (core_derives_lengths D _ _ _ H) as [_ Hlen_v].
    cbn [ctype_demand_row] in Hlen_v; rewrite length_app in Hlen_v; cbn [length] in Hlen_v.
    eexists; split; [| split; [| split]];
    [ apply CorePromote; exact Hpv'
    | cbn [cresult_type subst_tvar_in_cty]; unfold cty_alpha_eq in *; cbn; rewrite HA'; reflexivity
    | cbn [ccomp_demand]; rewrite vec_subst_scale; apply branch_rel_scale; exact Hu'
    | cbn [ctype_demand_row]; exists qv; exact Hv' ].
  - (* CoreLetBox *)
    lazymatch goal with
    | HA : CTypeDemand _ A a, Hmot : CTypeDemand _ mot v_mot, Hkap : allows (nth_grade v_mot 0) kappa,
      Hexp : exp_mot = spec_box_body_cty q 0 mot, Hmot_eq : cty_alpha_eq act_mot exp_mot,
      Hwq : allows (nth_grade w 0) q, Hbw : allows (nth_grade bw 0) (mul q kappa),
      Hdep : context [cty_uses_var 0 mot = false],
      Hres : res_ty = spec_box_subj_cty box_term mot,
      Hzty : ?z_ty = _ |- context [vec_scale _ ?z_ty] =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[bt' zb' vz'] [Hbx' [Hbt [Hzb' [qbx Hvz']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in Hbt, Hzb', Hvz';
        destruct (cty_alpha_eq_CBox_inv D bt' q (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A) Hbt)
          as [A0 [-> HA0]];
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ HA env_a eq_refl) as HA_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b A a Hb Hsafe HU HA) as [a' [Ha' Hbra]];
        assert (HA0' : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) A0 a') by
          (eapply CTypeDemand_alpha_ty; [exact Ha' | apply cty_alpha_eq_sym; exact HA0]);
        assert (Hsafe_box : cenv_tvar_safe ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [cbn; exact HA_safe | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env_a) b env_b lvl_b mot v_mot Hb Hsafe_box HU Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := 0; cannotation := CBox q A0; ctype_uses := a' |} :: subst_tvar_cenv U z env_a ++ env_b)
                                      (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) v_mot') by
          (eapply CTypeDemand_alpha_env; [| exact Hv_mot'];
           constructor; [cbn; unfold cty_alpha_eq in HA0 |- *; cbn; rewrite HA0; reflexivity | apply cenv_alpha_eq_refl]);
        assert (Hsafe_A : cenv_tvar_safe ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; assumption);
        destruct (IHCoreDerives2 ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl Hsafe_A)
          as [[act_mot1 w1 bw1] [Hb1 [Hact1 [Hw1 [qbw Hbw1]]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hb1, Hact1, Hw1, Hbw1;
        rewrite (lift_cty_1_S D (length env_a) U) in Hb1, Hact1;
        assert (Hrel_A : cenv_demand_rel
          ({| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A;
              ctype_uses := vec_subst (length env_a) z a |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HA0 | exact HA0' | exact Hbra]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hb1 _ Hrel_A) as [[act_mot2 w2 bw2] [Hb2 [Hact2 [Hw2 Hbw2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hact2, Hw2, Hbw2;
        assert (Hw_tr : branch_rel w2 (vec_subst (S (length env_a)) (vec_zero (length env_b)) w)) by (eapply branch_rel_trans; [exact Hw2 | exact Hw1]);
        assert (Hbw_tr : branch_rel bw2 (vec_add (vec_subst (S (length env_a)) z bw) (vec_zero (S (length env_a)) ++ vec_scale qbw z))) by
          (eapply branch_rel_trans; [exact Hbw2 | exact Hbw1]);
        assert (Hact_tr : cty_alpha_eq act_mot2 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) act_mot)) by
          (eapply cty_alpha_eq_trans; [exact Hact2 | exact Hact1]);
        assert (Hspec_body : subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) (spec_box_body_cty q 0 mot) =
                             spec_box_body_cty q 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot)) by
          (rewrite <- (lift_cty_1_S D (length env_a) U); apply subst_tvar_spec_box_body; [lia | exact Hmot_safe]);
        assert (Hmot_eq2 : cty_alpha_eq act_mot2 (spec_box_body_cty q 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))) by
          (eapply cty_alpha_eq_trans; [exact Hact_tr |]; rewrite <- Hspec_body, <- Hexp; apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hmot_eq]);
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_zb Hlen_vz];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_w Hlen_bw];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_vm, Hlen_zb, Hlen_vz, Hlen_w, Hlen_bw;
        rewrite length_app in Hlen_vm, Hlen_zb, Hlen_vz, Hlen_w, Hlen_bw; cbn [length] in Hlen_vm, Hlen_zb, Hlen_vz, Hlen_w, Hlen_bw;
        assert (Hkap2 : allows (nth_grade v_mot' 0) kappa) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; exact Hkap]);
        assert (Hwq2 : allows (nth_grade w2 0) q) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hw_tr) | rewrite vec_subst_nth_lt by lia; exact Hwq]);
        assert (Hbw2_a : allows (nth_grade bw2 0) (mul q kappa)) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbw_tr) |
           rewrite nth_grade_add by (rewrite Hvz_len, length_app, vec_zero_length, vec_scale_length; lia);
           rewrite vec_subst_nth_lt by lia;
           change (vec_zero (D := D) (S (length env_a)) ++ vec_scale qbw z) with (zero :: (vec_zero (D := D) (length env_a) ++ vec_scale qbw z));
           rewrite nth_grade_0_cons, add_zero_r; exact Hbw]);
        assert (Hmot_nf_fn : cty_uses_var 0 mot = false ->
                  cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false) by
          (intro Hnf; apply cty_uses_var_subst_tvar_0; [exact Hnf | exact Hmot_safe]);
        assert (Hbx_not_var : forall yb, box_term = CVar yb -> yb <> length env_a) by
          (intros yb -> ->; inversion H; subst;
           lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CBox _ _ |- _ =>
             unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
             rewrite Hb in Heq; cbn in Heq; discriminate
           end);
        assert (Hdep2 : match subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) box_term with
                        | CPromote _ (CNatVal _) | CPromote _ (CTypeVal _) | CPromote _ (CVar _) | CVar _ => True
                        | _ => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false
                        end) by
          (destruct box_term; cbn [subst_tvar_in_cterm]; try (apply Hmot_nf_fn; exact Hdep);
           [ destruct (Nat.eq_dec x0 (length env_a)) as [Heqn | Hne];
             [ exfalso; exact (Hbx_not_var x0 eq_refl Heqn)
             | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec x0 (length env_a)); exact I ]
           | destruct box_term; cbn [subst_tvar_in_cterm]; try (apply Hmot_nf_fn; exact Hdep); try exact I;
             repeat (destruct (_ =? _) || destruct (_ <? _)); exact I ]);
        assert (Hres_eq : cty_alpha_eq (spec_box_subj_cty (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) box_term)
                                         (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))
                            (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) res_ty)) by
          (rewrite Hres; destruct box_term; unfold spec_box_subj_cty; cbn [subst_tvar_in_cterm];
            try (rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe), <- (lift_cty_1_S D (length env_a) U); apply cty_alpha_eq_refl);
           [ destruct (Nat.eq_dec x0 (length env_a)) as [Heqn | Hne]; [exfalso; exact (Hbx_not_var x0 eq_refl Heqn) |];
             rewrite (proj2 (Nat.eqb_neq _ _) Hne);
             pose proof (subst_tvar_in_cty_subst_var_0 D mot U (length env_a) x0 Hne Hmot_safe) as Hrv;
             destruct (x0 <? length env_a); rewrite Hrv; apply cty_alpha_eq_refl
           | destruct box_term; cbn [subst_tvar_in_cterm];
             try (rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe), <- (lift_cty_1_S D (length env_a) U); apply cty_alpha_eq_refl);
             [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
               [ rewrite Nat.eqb_refl; cbn [spec_box_subj_cty];
                 assert (Hm0 : cty_uses_kinds false false true false false false false 0 mot = false) by
                   (inversion H; subst;
                    lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                      inversion Hdv; subst;
                      lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                        eapply ctype_demand_uses_kinds; [exact Hmot | reflexivity |];
                        unfold flags_allow; rewrite !erase_hints_ren, Hb; cbn; reflexivity
                      end
                    end);
                 pose proof (subst_tvar_box_var_to_ty_gen D mot U q0 0 (length env_a) Hm0 ltac:(cbn [Nat.add]; exact Hmot_safe)) as Hbvt;
                 cbn [Nat.add] in Hbvt; rewrite Hbvt; apply cty_alpha_eq_refl
               | rewrite (proj2 (Nat.eqb_neq _ _) Hne); cbn [spec_box_subj_cty];
                 pose proof (cty_uses_kinds_spec_box_body_tvar D mot q0 0 (length env_a) ltac:(cbn [Nat.add]; exact Hmot_safe)) as Hsb_safe;
                 cbn [Nat.add] in Hsb_safe;
                 pose proof (subst_tvar_in_cty_subst_var_0 D (spec_box_body_cty q0 0 mot) U (length env_a) x0 Hne Hsb_safe) as Hrv;
                 destruct (x0 <? length env_a); rewrite Hrv, (subst_tvar_spec_box_body D mot U q0 0 (length env_a) ltac:(lia) Hmot_safe); apply cty_alpha_eq_refl ]
             | inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ =>
                   pose proof (proj1 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hcd env_a eq_refl) as Hi_safe;
                   assert (Hm_ntv : cty_uses_kinds true false true true true true true 0 mot = false) by
                     (eapply cdemand_not_tvar_0_safe; [| exact Hmot]; intros ? Heq; cbn in Heq; discriminate);
                   pose proof (subst_tvar_in_cty_subst_box_nat D mot U 0 (length env_a) q ii ltac:(lia) Hm_ntv Hmot_safe Hi_safe) as Hcm;
                   rewrite Hcm; apply cty_alpha_eq_refl
                 end
               end
             | inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ (CTypeVal ?tt) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) ?tt _ |- _ =>
                   pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Htd env_a eq_refl) as HT_safe;
                   assert (Hm_ntv : cty_uses_kinds true false true true true true true 0 mot = false) by
                     (eapply cdemand_not_tvar_0_safe; [| exact Hmot]; intros ? Heq; cbn in Heq; discriminate);
                   pose proof (subst_tvar_in_cty_subst_box_ty D mot U tt 0 (length env_a) q ltac:(lia) Hm_ntv Hmot_safe HT_safe) as Hcm;
                   rewrite Hcm; apply cty_alpha_eq_refl
                 end
               end ] ]);
        assert (Hzty_ex : exists q_z,
          branch_rel
            (match subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) box_term with
             | CPromote q' (CTypeVal _) => vec_scale q' vz' | _ => zb' end)
            (vec_add (vec_subst (length env_a) z z_ty) (vec_zero (length env_a) ++ vec_scale q_z z))) by
          (rewrite Hzty; destruct box_term; cbn [subst_tvar_in_cterm];
           lazymatch goal with
           | |- context [subst_tvar_in_cterm _ _ ?inner] =>
               destruct inner; cbn [subst_tvar_in_cterm];
               lazymatch goal with
               | |- context [if ?x0 =? _ then _ else _] =>
                   destruct (Nat.eq_dec x0 (length env_a)) as [Hx_eq | Hne];
               [ subst x0; cbn [subst_tvar_in_cterm] in Hbx'; rewrite Nat.eqb_refl in Hbx' |- *;
                 exists zero;
                 inversion H; subst;
                 try (match goal with Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} = {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ => injection Hrec; intros; subst end);
                 lazymatch goal with Hdv_v : CoreDerives _ (CVar _) _ |- _ =>
                   inversion Hdv_v; subst;
                   lazymatch goal with Hlk_v : clookup _ _ = Some ?ee, Htd_v : CTypeDemand _ _ _ |- _ =>
                     unfold clookup in Hlk_v; rewrite nth_error_app2, Nat.sub_diag in Hlk_v by lia; inversion Hlk_v; subst ee;
                     inversion Hbx'; subst;
                     try (match goal with Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} = {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ => injection Hrec; intros; subst end);
                     lazymatch goal with Htv_u : CoreDerives _ (CTypeVal _) _ |- _ =>
                       inversion Htv_u; subst;
                       try (match goal with Hrec : {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} = {| cresult_type := _; ccomp_demand := _; ctype_demand_row := _ |} |- _ => injection Hrec; intros; subst end);
                       lazymatch goal with Htd_U : CTypeDemand _ (lift_cty 0 (length env_a) U) _ |- _ =>
                         destruct (weaken_ctype_demand_app_left D env_b U z HU (subst_tvar_cenv U z env_a)) as [z_u [Hz_u Hbr_zu]];
                         rewrite subst_tvar_cenv_length in Hz_u, Hbr_zu;
                         pose proof (ctype_demand_unique D _ _ _ _ _ (cenv_alpha_eq_refl D _) Htd_U Hz_u) as ->;
                         eapply branch_rel_trans;
                         [ apply branch_rel_scale; exact Hbr_zu
                         | rewrite vec_scale_app, vec_scale_zero_vec;
                           replace (vec_subst (length env_a) z (vec_scale q (vec_single (length (env_a ++ b :: env_b)) (length env_a) one)))
                             with (vec_zero (D := D) (length env_a) ++ vec_scale q z) by
                             (rewrite vec_subst_scale, length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_eq by exact Hz_len;
                              rewrite vec_scale_app, vec_scale_zero_vec, vec_scale_mul, mul_one_r; reflexivity);
                           apply Hadd_zero_tail; rewrite length_app, vec_zero_length, vec_scale_length; lia ]
                       end
                     end
                   end
                 end
               | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec x0 (length env_a));
                 (exists zero; eapply branch_rel_trans; [| apply Hadd_zero_tail; rewrite Hvz_len by lia; reflexivity]; apply H_uv_subst; [lia | exact Hzb']) ]
               | |- context [vec_scale ?q1 vz'] =>
                   exists (mul q1 qbx);
                   rewrite vec_subst_scale, <- (vec_scale_zero_tail_assoc D z (length env_a) q1 qbx), <- vec_scale_add;
                   apply branch_rel_scale; exact Hvz'
               | |- _ =>
                   exists zero; eapply branch_rel_trans; [| apply Hadd_zero_tail; rewrite Hvz_len by lia; reflexivity]; apply H_uv_subst; [lia | exact Hzb']
               end
           | |- context [if _ =? _ then _ else _] =>
               repeat (destruct (_ =? _) || destruct (_ <? _));
               (exists zero; eapply branch_rel_trans; [| apply Hadd_zero_tail; rewrite Hvz_len by lia; reflexivity]; apply H_uv_subst; [lia | exact Hzb'])
           | |- _ =>
               exists zero; eapply branch_rel_trans; [| apply Hadd_zero_tail; rewrite Hvz_len by lia; reflexivity]; apply H_uv_subst; [lia | exact Hzb']
           end);
        destruct Hzty_ex as [q_z Hzty'];
        assert (Hlen_zty : length z_ty = length env_a + S (length env_b)) by
          (rewrite Hzty; destruct box_term; try exact Hlen_zb;
           lazymatch goal with |- length (match ?inn with _ => _ end) = _ =>
             destruct inn; try exact Hlen_zb; rewrite vec_scale_length; exact Hlen_vz
           end);
        eexists; rewrite <- (lift_cty_1_S D (length env_a) U); split; [| split; [| split]];
        [ rewrite <- (lift_cty_1_S D (length env_a) U) in Hb2; eapply CoreLetBox;
          [ exact Hbx' | exact HA0' | exact Hv_mot0 | exact Hkap2 | exact Hb2
          | reflexivity | exact Hmot_eq2 | exact Hwq2 | exact Hbw2_a | exact Hdep2 | reflexivity | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) (tl w) z_b (length env_b))
            by (try apply vec_zero_length; destruct w; cbn in *; lia);
          apply branch_rel_add; [rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hw_tr | exact Hzb']
        | cbn [ctype_demand_row]; exists (mul kappa q_z);
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale kappa z_ty) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale, <- (vec_scale_zero_tail_assoc D z (length env_a) kappa q_z);
          rewrite <- vec_add_assoc;
          apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot
          | rewrite <- vec_scale_add; apply branch_rel_scale; exact Hzty' ] ]
    end.
  - (* CoreInl *)
    lazymatch goal with
    | Hrhs : CTypeDemand _ rhs_ty ?b0 |- _ =>
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[A' u' a'] [Hv' [HA' [Hu' [ql Ha']]]]];
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b rhs_ty b0 Hb Hsafe HU Hrhs) as [b' [Hb' Hbrb]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in HA', Hu', Ha';
        pose proof (core_derives_lengths D _ _ _ H) as [_ Hlen_a];
        pose proof (ctype_demand_length D _ _ _ Hrhs) as Hlen_b;
        rewrite length_app in Hlen_a, Hlen_b; cbn [ctype_demand_row length] in Hlen_a, Hlen_b;
        eexists; split; [| split; [| split]];
        [ eapply CoreInl; [exact Hv' | exact Hb']
        | cbn [cresult_type subst_tvar_in_cty]; unfold cty_alpha_eq in *; cbn; rewrite HA'; reflexivity
        | cbn [ccomp_demand]; exact Hu'
        | cbn [ctype_demand_row]; exists ql;
          rewrite (vec_subst_add D (length env_a) z a b0 (length env_b)) by lia;
          rewrite <- (vec_add_assoc D (vec_subst (length env_a) z a) (vec_subst (length env_a) z b0) _),
                  (vec_add_comm D (vec_subst (length env_a) z b0) _),
                  vec_add_assoc;
          apply branch_rel_add; [exact Ha' | exact Hbrb] ]
    end.
  - (* CoreInr *)
    lazymatch goal with
    | Hlhs : CTypeDemand _ lhs_ty ?a_r |- context [vec_add ?a_r ?b_r] =>
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b lhs_ty a_r Hb Hsafe HU Hlhs) as [a' [Ha' Hbra]];
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[B' u' b'] [Hv' [HB' [Hu' [qr Hb']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in HB', Hu', Hb';
        pose proof (ctype_demand_length D _ _ _ Hlhs) as Hlen_a;
        pose proof (core_derives_lengths D _ _ _ H) as [_ Hlen_b];
        cbn [ctype_demand_row length] in Hlen_a, Hlen_b;
        rewrite length_app in Hlen_a, Hlen_b; cbn [length] in Hlen_a, Hlen_b;
        eexists; split; [| split; [| split]];
        [ eapply CoreInr; [exact Ha' | exact Hv']
        | cbn [cresult_type subst_tvar_in_cty]; unfold cty_alpha_eq in *; cbn; rewrite HB'; reflexivity
        | cbn [ccomp_demand]; exact Hu'
        | cbn [ctype_demand_row]; exists qr;
          rewrite (vec_subst_add D (length env_a) z a_r b_r (length env_b)) by lia;
          rewrite <- vec_add_assoc;
          apply branch_rel_add; [exact Hbra | exact Hb'] ]
    end.
  - (* CoreMatchSum *)
    lazymatch goal with
    | Hsne : s <> zero, HA : CTypeDemand _ A a, HB : CTypeDemand _ B ?b0,
      Hmot : CTypeDemand _ mot v_mot, Hkap : allows (nth_grade v_mot 0) kappa,
      Ht1 : cty_alpha_eq t1 (spec_sum_branch_cty true 0 mot),
      Ht2 : cty_alpha_eq t2 (spec_sum_branch_cty false 0 mot),
      Hs1 : allows (nth_grade u1 0) s, Hs2 : allows (nth_grade u2 0) s,
      Hbv : BranchVec (tl u1) (tl u2) u_br,
      Hdep : context [cty_uses_var 0 mot = false],
      Hres : res_ty = spec_sum_subj_cty scrut mot |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[srt' w' vs'] [Hscr' [Hsrt [Hw' [qs Hvs']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in Hsrt, Hw', Hvs';
        destruct (cty_alpha_eq_CSum_inv D srt'
                    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A)
                    (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) B) Hsrt)
          as [A0 [B0 [-> [HA0 HB0]]]];
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ HA env_a eq_refl) as HA_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ HB env_a eq_refl) as HB_safe;
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b0 |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b A a Hb Hsafe HU HA) as [a' [Ha' Hbra]];
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b B b0 Hb Hsafe HU HB) as [b' [Hb' Hbrb]];
        assert (HA0' : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) A0 a') by
          (eapply CTypeDemand_alpha_ty; [exact Ha' | apply cty_alpha_eq_sym; exact HA0]);
        assert (HB0' : CTypeDemand (subst_tvar_cenv U z env_a ++ env_b) B0 b') by
          (eapply CTypeDemand_alpha_ty; [exact Hb' | apply cty_alpha_eq_sym; exact HB0]);
        assert (Hsafe_sum : cenv_tvar_safe ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b0 |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [cbn; rewrite HA_safe, HB_safe; reflexivity | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b0 |} :: env_a) b env_b lvl_b mot v_mot Hb Hsafe_sum HU Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := 0; cannotation := CSum A0 B0; ctype_uses := vec_add a' b' |} :: subst_tvar_cenv U z env_a ++ env_b)
                                      (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) v_mot') by
          (eapply CTypeDemand_alpha_env; [| exact Hv_mot'];
           constructor; [cbn; unfold cty_alpha_eq in HA0, HB0 |- *; cbn; rewrite HA0, HB0; reflexivity | apply cenv_alpha_eq_refl]);
        assert (Hsafe_A : cenv_tvar_safe ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; assumption);
        assert (Hsafe_B : cenv_tvar_safe ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; assumption);
        destruct (IHCoreDerives2 ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl Hsafe_A)
          as [[tl1 u1_1 b1_1] [Hlb1 [Htl1 [Hu1_1 [q1 Hb1_1]]]]];
        destruct (IHCoreDerives3 ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: env_a) eq_refl Hsafe_B)
          as [[tr1 u2_1 b2_1] [Hrb1 [Htr1 [Hu2_1 [q2 Hb2_1]]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_cenv length cbinder cannotation ctype_uses app] in Hlb1, Htl1, Hu1_1, Hb1_1, Hrb1, Htr1, Hu2_1, Hb2_1;
        rewrite (lift_cty_1_S D (length env_a) U) in Hlb1, Htl1, Hrb1, Htr1;
        assert (Hrel_A : cenv_demand_rel
          ({| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) A;
              ctype_uses := vec_subst (length env_a) z a |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HA0 | exact HA0' | exact Hbra]);
        assert (Hrel_B : cenv_demand_rel
          ({| cbinder := y; cannotation := B0; ctype_uses := b' |} :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := y; cannotation := subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) B;
              ctype_uses := vec_subst (length env_a) z b0 |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HB0 | exact HB0' | exact Hbrb]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hlb1 _ Hrel_A) as [[tl2 u1_2 b1_2] [Hlb2 [Htl2 [Hu1_2 Hb1_2]]]];
        destruct (core_derives_cenv_rel D ED _ _ _ Hrb1 _ Hrel_B) as [[tr2 u2_2 b2_2] [Hrb2 [Htr2 [Hu2_2 Hb2_2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htl2, Hu1_2, Hb1_2, Htr2, Hu2_2, Hb2_2;
        assert (Hu1_tr : branch_rel u1_2 (vec_subst (S (length env_a)) (vec_zero (length env_b)) u1)) by (eapply branch_rel_trans; [exact Hu1_2 | exact Hu1_1]);
        assert (Hu2_tr : branch_rel u2_2 (vec_subst (S (length env_a)) (vec_zero (length env_b)) u2)) by (eapply branch_rel_trans; [exact Hu2_2 | exact Hu2_1]);
        assert (Htl_tr : cty_alpha_eq tl2 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) t1)) by
          (eapply cty_alpha_eq_trans; [exact Htl2 | exact Htl1]);
        assert (Htr_tr : cty_alpha_eq tr2 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) t2)) by
          (eapply cty_alpha_eq_trans; [exact Htr2 | exact Htr1]);
        assert (Hspec_l : subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) (spec_sum_branch_cty true 0 mot) =
                          spec_sum_branch_cty true 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot)) by
          (rewrite <- (lift_cty_1_S D (length env_a) U); apply subst_tvar_spec_sum_branch; [lia | exact Hmot_safe]);
        assert (Hspec_r : subst_tvar_in_cty (S (length env_a)) (lift_cty 0 1 (lift_cty 0 (length env_a) U)) (spec_sum_branch_cty false 0 mot) =
                          spec_sum_branch_cty false 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot)) by
          (rewrite <- (lift_cty_1_S D (length env_a) U); apply subst_tvar_spec_sum_branch; [lia | exact Hmot_safe]);
        assert (Ht1_2 : cty_alpha_eq tl2 (spec_sum_branch_cty true 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htl_tr | rewrite <- Hspec_l; apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Ht1]]);
        assert (Ht2_2 : cty_alpha_eq tr2 (spec_sum_branch_cty false 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htr_tr | rewrite <- Hspec_r; apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Ht2]]);
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w Hlen_vs];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_u1 _];
        pose proof (core_derives_lengths D _ _ _ H1) as [Hlen_u2 _];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_vm, Hlen_w, Hlen_vs, Hlen_u1, Hlen_u2;
        rewrite length_app in Hlen_vm, Hlen_w, Hlen_vs, Hlen_u1, Hlen_u2; cbn [length] in Hlen_vm, Hlen_w, Hlen_vs, Hlen_u1, Hlen_u2;
        assert (Hkap2 : allows (nth_grade v_mot' 0) kappa) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; exact Hkap]);
        assert (Hs1_2 : allows (nth_grade u1_2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu1_tr) | rewrite vec_subst_nth_lt by lia; exact Hs1]);
        assert (Hs2_2 : allows (nth_grade u2_2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu2_tr) | rewrite vec_subst_nth_lt by lia; exact Hs2]);
        assert (Hbr_tl1 : branch_rel (tl u1_2) (vec_subst (length env_a) (vec_zero (length env_b)) (tl u1))) by
          (rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu1_tr);
        assert (Hbr_tl2 : branch_rel (tl u2_2) (vec_subst (length env_a) (vec_zero (length env_b)) (tl u2))) by
          (rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu2_tr);
        destruct (BranchVec_subst D (length env_a) (vec_zero (length env_b)) (tl u1) (tl u2) u_br (tl u1_2) (tl u2_2) (length env_b)
                    (vec_zero_length D (length env_b)) ltac:(destruct u1; cbn in *; lia) ltac:(destruct u2; cbn in *; lia) Hbv Hbr_tl1 Hbr_tl2)
          as [ubr' [Hubr' Hbr_u]];
        assert (Hmot_nf_fn : cty_uses_var 0 mot = false ->
                  cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false) by
          (intro Hnf; apply cty_uses_var_subst_tvar_0; [exact Hnf | exact Hmot_safe]);
        assert (Hscr_not_var : forall ys, scrut = CVar ys -> ys <> length env_a) by
          (intros ys -> ->; inversion H; subst;
           lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSum _ _ |- _ =>
             unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
             rewrite Hb in Heq; cbn in Heq; discriminate
           end);
        assert (Hdep2 : match subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut with
                        | CInl _ v => match term_as_cidx v, A0 with Some _, CNat => True | _, _ => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false end
                        | CInr _ v => match term_as_cidx v, B0 with Some _, CNat => True | _, _ => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false end
                        | CVar _ => True
                        | _ => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false
                        end) by
          (destruct scrut; cbn [subst_tvar_in_cterm]; try (apply Hmot_nf_fn; exact Hdep);
           [ destruct (Nat.eq_dec x0 (length env_a)) as [Heqn | Hne];
             [ exfalso; exact (Hscr_not_var x0 eq_refl Heqn)
             | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec x0 (length env_a)); exact I ]
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct A; try (destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut)), A0; first [exact I | apply Hmot_nf_fn; exact Hdep]);
               destruct A0; unfold cty_alpha_eq in HA0; cbn in HA0; try discriminate;
               inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ scrut {| cresult_type := CNat; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                 destruct (term_as_cidx_subst_tvar_some D b env_a env_b lvl_b scrut _ _ (lift_cty 0 (length env_a) U) Hb Hdv eq_refl Ev) as [_ ->]; exact I
               end
             | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ Ev); destruct A0; apply Hmot_nf_fn; exact Hdep ]
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct B; try (destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut)), B0; first [exact I | apply Hmot_nf_fn; exact Hdep]);
               destruct B0; unfold cty_alpha_eq in HB0; cbn in HB0; try discriminate;
               inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ scrut {| cresult_type := CNat; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                 destruct (term_as_cidx_subst_tvar_some D b env_a env_b lvl_b scrut _ _ (lift_cty 0 (length env_a) U) Hb Hdv eq_refl Ev) as [_ ->]; exact I
               end
             | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ Ev); destruct B0; apply Hmot_nf_fn; exact Hdep ] ]);
        assert (Hres_eq : cty_alpha_eq (spec_sum_subj_cty (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut)
                                         (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))
                            (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) res_ty)) by
          (rewrite Hres; destruct scrut; unfold spec_sum_subj_cty; cbn [subst_tvar_in_cterm];
            try (rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe), <- (lift_cty_1_S D (length env_a) U); apply cty_alpha_eq_refl);
           [ destruct (Nat.eq_dec x0 (length env_a)) as [Heqn | Hne]; [exfalso; exact (Hscr_not_var x0 eq_refl Heqn) |];
             rewrite (proj2 (Nat.eqb_neq _ _) Hne);
             pose proof (subst_tvar_in_cty_subst_var_0 D mot U (length env_a) x0 Hne Hmot_safe) as Hrv;
             destruct (x0 <? length env_a); rewrite Hrv; apply cty_alpha_eq_refl
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct A;
               [ inversion H; subst;
                 lazymatch goal with H_ev : term_as_cidx ?v = Some ?cc, Hdv : CoreDerives _ ?v {| cresult_type := CNat; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                   destruct (term_as_cidx_subst_tvar_some D b env_a env_b lvl_b v _ cc (lift_cty 0 (length env_a) U) Hb Hdv eq_refl H_ev) as [Hc' ->];
                   assert (Hm_ntv : cty_uses_kinds true false true true true true true 0 mot = false) by
                     (eapply cdemand_not_tvar_0_safe; [| exact Hmot]; intros ? Heq; cbn in Heq; discriminate);
                   pose proof (subst_tvar_in_cty_subst_sum D mot U true 0 (length env_a) cc ltac:(lia) Hm_ntv Hmot_safe Hc') as Hcm;
                   rewrite Hcm; apply cty_alpha_eq_refl
                 end
               | .. ];
               destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut));
               try rewrite (subst_sum_cty_no_use_unshift D _ true _ (Hmot_nf_fn Hdep));
               rewrite (subst_sum_cty_no_use_unshift D mot true _ Hdep),
                       (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                       <- (lift_cty_1_S D (length env_a) U);
               apply cty_alpha_eq_refl
             | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ Ev);
               rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                       <- (lift_cty_1_S D (length env_a) U);
               apply cty_alpha_eq_refl ]
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct B;
               [ inversion H; subst;
                 lazymatch goal with H_ev : term_as_cidx ?v = Some ?cc, Hdv : CoreDerives _ ?v {| cresult_type := CNat; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
                   destruct (term_as_cidx_subst_tvar_some D b env_a env_b lvl_b v _ cc (lift_cty 0 (length env_a) U) Hb Hdv eq_refl H_ev) as [Hc' ->];
                   assert (Hm_ntv : cty_uses_kinds true false true true true true true 0 mot = false) by
                     (eapply cdemand_not_tvar_0_safe; [| exact Hmot]; intros ? Heq; cbn in Heq; discriminate);
                   pose proof (subst_tvar_in_cty_subst_sum D mot U false 0 (length env_a) cc ltac:(lia) Hm_ntv Hmot_safe Hc') as Hcm;
                   rewrite Hcm; apply cty_alpha_eq_refl
                 end
               | .. ];
               destruct (term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut));
               try rewrite (subst_sum_cty_no_use_unshift D _ false _ (Hmot_nf_fn Hdep));
               rewrite (subst_sum_cty_no_use_unshift D mot false _ Hdep),
                       (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                       <- (lift_cty_1_S D (length env_a) U);
               apply cty_alpha_eq_refl
             | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ Ev);
               rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe),
                       <- (lift_cty_1_S D (length env_a) U);
               apply cty_alpha_eq_refl ] ]);
        eexists; rewrite <- (lift_cty_1_S D (length env_a) U); split; [| split; [| split]];
        [ rewrite <- (lift_cty_1_S D (length env_a) U) in Hlb2, Hrb2; eapply CoreMatchSum;
          [ exact Hsne | exact Hscr' | exact HA0' | exact HB0' | exact Hv_mot0 | exact Hkap2
          | exact Hlb2 | exact Hrb2 | exact Ht1_2 | exact Ht2_2 | exact Hs1_2 | exact Hs2_2
          | exact Hubr' | exact Hdep2 | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          pose proof (BranchVec_length D (tl u1) (tl u2) u_br ltac:(destruct u1, u2; cbn in *; lia) Hbv) as Hlen_ubr;
          cbn [length] in Hlen_ubr;
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) (vec_scale s w) u_br (length env_b))
            by (try apply vec_zero_length; try rewrite vec_scale_length; destruct u1; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [apply branch_rel_scale; exact Hw' | exact Hbr_u]
        | cbn [ctype_demand_row]; exists zero;
          eapply branch_rel_trans;
          [| apply Hadd_zero_tail; rewrite Hvz_len; [reflexivity | rewrite vec_add_length by (destruct v_mot; cbn in *; rewrite vec_scale_length; lia); destruct v_mot; cbn in *; lia] ];
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale kappa w) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot
          | apply branch_rel_scale; apply H_uv_subst; [lia | exact Hw'] ] ]
    end.
  - (* CoreIf *)
    lazymatch goal with
    | Heq : cty_alpha_eq t1 t2, Hbu : BranchVec u1 u2 u_br, Hbv : BranchVec v1 v2 v_br |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[tc' uc' vc'] [Hc' [Htc [Huc' [qc Hvc']]]]];
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[t1' u1' v1'] [Hth' [Ht1 [Hu1' [q1 Hv1']]]]];
        destruct (IHCoreDerives3 env_a eq_refl Hsafe) as [[t2' u2' v2'] [Hel' [Ht2 [Hu2' [q2 Hv2']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in Htc, Huc', Hvc', Ht1, Hu1', Hv1', Ht2, Hu2', Hv2';
        apply cty_alpha_eq_CBool_inv in Htc; subst tc';
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_uc _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_u1 Hlen_v1];
        pose proof (core_derives_lengths D _ _ _ H1) as [Hlen_u2 Hlen_v2];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_uc, Hlen_u1, Hlen_v1, Hlen_u2, Hlen_v2;
        rewrite length_app in Hlen_uc, Hlen_u1, Hlen_v1, Hlen_u2, Hlen_v2; cbn [length] in Hlen_uc, Hlen_u1, Hlen_v1, Hlen_u2, Hlen_v2;
        destruct (BranchVec_subst D (length env_a) (vec_zero (length env_b)) u1 u2 u_br u1' u2' (length env_b)
                    (vec_zero_length D (length env_b)) ltac:(lia) ltac:(lia) Hbu Hu1' Hu2') as [ubr' [Hubr' Hbr_u]];
        destruct (BranchVec_subst_tail D (length env_a) z v1 v2 v_br v1' v2' q1 q2 (length env_b)
                    Hnone_z Hz_len ltac:(lia) ltac:(lia) Hbv Hv1' Hv2') as [vbr' [qbr [Hvbr' Hbr_v]]];
        eexists; split; [| split; [| split]];
        [ eapply CoreIf;
          [ exact Hc' | exact Hth' | exact Hel'
          | eapply cty_alpha_eq_trans; [exact Ht1 | eapply cty_alpha_eq_trans; [apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Heq] | apply cty_alpha_eq_sym; exact Ht2]]
          | exact Hubr' | exact Hvbr' ]
        | cbn [cresult_type]; exact Ht1
        | cbn [ccomp_demand];
          pose proof (BranchVec_length D u1 u2 u_br ltac:(lia) Hbu) as Hlen_ubr;
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) u_c u_br (length env_b)) by (try apply vec_zero_length; lia);
          apply branch_rel_add; [exact Huc' | exact Hbr_u]
        | cbn [ctype_demand_row]; exists qbr; exact Hbr_v ]
    end.
  - (* CoreRecordMk *)
    destruct (IHCoreDerives env_a eq_refl Hsafe) as [u' [v' [Helems [Hu' [qr Hv']]]]].
    eexists; split; [| split; [| split]];
    [ apply CoreRecordMk; exact Helems
    | cbn [cresult_type subst_tvar_in_cty];
      replace (map (fun '(fn, fg, ft, _) => (fn, fg, ft))
                (map (fun '(fn, fg, ft, fv) =>
                   (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft,
                            subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) fv)) fields))
        with (map (fun '(fn, fg, ft) => (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft))
                (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields))
        by (rewrite !map_map; apply map_ext; intros [[[fn fg] ft] fv]; reflexivity);
      apply cty_alpha_eq_refl
    | cbn [ccomp_demand]; exact Hu'
    | cbn [ctype_demand_row]; exists qr; exact Hv' ].
  - (* CoreMatchRecord *)
    lazymatch goal with
    | Hsne : s <> zero, Hmot : CTypeDemand _ mot v_mot,
      Hlen_eq : length bs = length fields,
      Hext : CRecordExtendEnv _ bs fields body_env,
      Htb_eq : cty_alpha_eq t_b (lift_cty 0 (length fields) mot),
      Hfa_rec : CRecordFieldAllows s fields (firstn (length fields) u_b) |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[tr' w' vs'] [Hscr' [Htr [Hw' [qs Hvs']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in Htr, Hw', Hvs';
        destruct (cty_alpha_eq_CRecord_inv D tr' id
                    (map (fun '(fn, fg, ft) => (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft)) fields) Htr)
          as [fields' [-> Hfs_sub]];
        assert (Hfs_a : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\
                  cty_alpha_eq t1 (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) t2)) fields' fields) by
          (clear - Hfs_sub; revert fields Hfs_sub; induction fields' as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
           cbn in Hfs; inversion Hfs; subst; [apply Forall2_nil | apply Forall2_cons; [assumption | apply IH; assumption]]);
        assert (Hlen_fs : length bs = length fields') by (rewrite Hlen_eq; symmetry; apply (Forall2_length Hfs_a));
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot env_a eq_refl) as Hmot_safe;
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b mot v_mot Hb Hsafe HU Hmot) as [v_mot' [Hv_mot' Hbr_mot]];
        destruct (record_extend_subst_tvar D U z env_b b lvl_b Hb HU _ bs fields body_env env_a fields' eq_refl Hsafe Hext Hfs_a)
          as [ext_a [body_env' [Hbody [Hlen_ext [Hsafe_ext [Hext' Hrel_ext]]]]]];
        destruct (IHCoreDerives2 ext_a Hbody Hsafe_ext) as [[tb1 ub1 vb1] [Hbod1 [Htb1 [Hub1 [qb Hvb1]]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htb1, Hub1, Hvb1;
        destruct (core_derives_cenv_rel D ED _ _ _ Hbod1 _ Hrel_ext) as [[tb2 ub2 vb2] [Hbod2 [Htb2 [Hub2 Hvb2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htb2, Hub2, Hvb2;
        assert (Hub_tr : branch_rel ub2 (vec_subst (length ext_a) (vec_zero (length env_b)) u_b)) by (eapply branch_rel_trans; [exact Hub2 | exact Hub1]);
        assert (Htb_tr : cty_alpha_eq tb2 (subst_tvar_in_cty (length ext_a) (lift_cty 0 (length ext_a) U) t_b)) by
          (eapply cty_alpha_eq_trans; [exact Htb2 | exact Htb1]);
        rewrite Hlen_ext in Htb_tr, Hub_tr;
        assert (Htb2_eq : cty_alpha_eq tb2 (lift_cty 0 (length fields') (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) mot))) by
          (rewrite (Forall2_length Hfs_a);
           eapply cty_alpha_eq_trans; [exact Htb_tr |];
           eapply cty_alpha_eq_trans; [apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Htb_eq] |];
           rewrite <- (lift_cty_add D (length fields) (length env_a) U), (subst_tvar_in_cty_lift_n_comm D (length fields) (length env_a) mot (lift_cty 0 (length env_a) U) Hmot_safe);
           apply cty_alpha_eq_refl);
        assert (Hfa2 : Forall2 (@allows D) (firstn (length fields) ub2) (firstn (length fields) u_b)) by
          (pose proof (branch_rel_firstn D (length fields) _ _ Hub_tr) as Hfr;
           rewrite vec_subst_firstn_prefix in Hfr by lia;
           apply branch_rel_allows; exact Hfr);
        assert (Hfa_map : CRecordFieldAllows s
                            (map (fun '(fn, fg, ft) => (fn, fg, subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) ft)) fields)
                            (firstn (length fields) u_b)) by
          (clear - Hfa_rec; induction Hfa_rec; cbn; [apply CRecordAllowsNil | apply CRecordAllowsCons; assumption]);
        assert (Hallows2 : CRecordFieldAllows s fields' (firstn (length fields') ub2)) by
          (rewrite (Forall2_length Hfs_a); eapply record_allows_mono; [exact Hfa_map | exact Hfa2 | exact Hfs_sub]);
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ub _];
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        cbn [ccomp_demand ctype_demand_row length] in Hlen_ub, Hlen_w, Hlen_vm;
        rewrite Hbody, length_app, Hlen_ext in Hlen_ub; cbn [length] in Hlen_ub;
        rewrite length_app in Hlen_w, Hlen_vm; cbn [length] in Hlen_w, Hlen_vm;
        eexists; split; [| split; [| split]];
        [ rewrite Hlen_ext, <- Hlen_eq, <- lift_cty_add in Hbod2;
          eapply CoreMatchRecord; [exact Hsne | exact Hscr' | exact Hv_mot' | exact Hlen_fs | exact Hext' | exact Hbod2 | exact Htb2_eq | exact Hallows2]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; rewrite (Forall2_length Hfs_a);
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) (vec_scale s w) (skipn (length fields) u_b) (length env_b))
            by (try apply vec_zero_length; try rewrite vec_scale_length; try rewrite length_skipn; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ apply branch_rel_scale; exact Hw'
          | replace (vec_subst (length env_a) (vec_zero (length env_b)) (skipn (length fields) u_b))
              with (skipn (length fields) (vec_subst (length fields + length env_a) (vec_zero (length env_b)) u_b))
              by (rewrite <- (vec_subst_skipn_prefix D (length fields) (length fields + length env_a) (vec_zero (length env_b)) u_b ltac:(lia)); f_equal; lia);
            apply branch_rel_skipn; exact Hub_tr ]
        | cbn [ctype_demand_row]; exists zero;
          eapply branch_rel_trans; [exact Hbr_mot | apply Hadd_zero_tail; rewrite Hvz_len by lia; reflexivity] ]
    end.
  - (* CoreSubgrade *)
    lazymatch goal with
    | Hsub : Subty _ actual target, Hvt : CTypeDemand _ target vt |- _ =>
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[act' u' v'] [Hb' [Hact' [Hu' [qb Hv']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hact', Hu', Hv';
        pose proof (subst_tvar_subty D U z env_a b env_b actual target Hsub) as Hsub';
        assert (Hsub0 : Subty (subst_tvar_cenv U z env_a ++ env_b) act'
                          (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) target)) by
          (eapply Subty_alpha; [exact Hsub' | apply cenv_alpha_eq_refl | apply cty_alpha_eq_sym; exact Hact' | apply cty_alpha_eq_refl]);
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b target vt Hb Hsafe HU Hvt) as [vt' [Hvt' Hbr_vt]];
        pose proof (ctype_demand_length D _ _ _ Hvt) as Hlen_vt;
        rewrite length_app in Hlen_vt; cbn [length] in Hlen_vt;
        eexists; split; [| split; [| split]];
        [ eapply CoreSubgrade; [exact Hb' | exact Hsub0 | exact Hvt']
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; exact Hu'
        | cbn [ctype_demand_row]; exists zero;
          eapply branch_rel_trans; [exact Hbr_vt | apply Hadd_zero_tail; rewrite Hvz_len by lia; reflexivity] ]
    end.
  - (* CoreFix *)
    lazymatch goal with
    | Hmot : CTypeDemand _ mot v_mot,
      Hbeq : cty_alpha_eq t_b (subst_cidx_in_cty 0 (CIdxLit 0) mot),
      Hsteq : cty_alpha_eq t_st (spec_fix_step_cty mot),
      Hrec0 : allows (nth_grade u_st 0) s_rec, Hrec1 : allows (nth_grade u_st 1) s_rec,
      Hrecok : fix_recurrence_ok s_rec (tl (tl u_st)),
      Hdep : match term_as_cidx scrut with Some _ => True | None => cty_uses_var 0 mot = false end,
      Hres : res_ty = spec_fix_subj_cty scrut mot |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[st' us' vs'] [Hscr' [Hst [Hus' [qs Hvs']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_in_cty] in Hst, Hus', Hvs';
        apply cty_alpha_eq_CNat_inv in Hst; subst st';
        pose proof (proj2 (cdemand_tvar_safe D b env_b lvl_b Hb) _ _ _ Hmot ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        assert (Hsafe_xn : cenv_tvar_safe ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) (S (length env_a))) by
          (apply cenv_tvar_safe_cons; [reflexivity | exact Hsafe]);
        destruct (subst_tvar_type_demand D U z ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) b env_b lvl_b mot v_mot Hb Hsafe_xn HU Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_tvar_cenv length cbinder cannotation ctype_uses app subst_tvar_in_cty] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (subst_tvar_cenv U z env_a ++ env_b)) |} :: subst_tvar_cenv U z env_a ++ env_b)
                                      (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) v_mot') by
          (eapply CTypeDemand_alpha_env; [| exact Hv_mot']; constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]);
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[tb' ub' vb'] [Hbas' [Htb' [Hub' [qb Hvb']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htb', Hub', Hvb';
        assert (Hm_ntv : cty_uses_kinds true false true true true true true 0 mot = false) by
          (eapply cdemand_not_tvar_0_safe; [| exact Hmot]; intros ? Heq; cbn in Heq; discriminate);
        assert (Hbeq' : cty_alpha_eq tb' (subst_cidx_in_cty 0 (CIdxLit 0) (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htb' |];
           eapply cty_alpha_eq_trans; [apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hbeq] |];
           pose proof (subst_tvar_in_cty_subst_cidx_0 D mot (lift_cty 0 (length env_a) U) (CIdxLit 0) (length env_a) Hm_ntv Hmot_safe ltac:(cbn; reflexivity)) as Hcm;
           cbn [subst_tvar_in_cidx] in Hcm; rewrite lift_cty_add in Hcm; replace (1 + length env_a) with (S (length env_a)) in Hcm by lia;
           rewrite Hcm; apply cty_alpha_eq_refl);
        assert (Hsafe_xr : cenv_tvar_safe ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
                                          {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a)
                                         (S (S (length env_a)))) by
          (apply cenv_tvar_safe_cons; [exact Hmot_safe | exact Hsafe_xn]);
        destruct (IHCoreDerives3 ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
                                  {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl Hsafe_xr)
          as [[tst1 ust1 vst1] [Hstp1 [Htst1 [Hust1 [qst Hvst1]]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_tvar_cenv length cbinder cannotation ctype_uses app subst_tvar_in_cty] in Hstp1, Htst1, Hust1, Hvst1;
        rewrite (lift_cty_2_SS D (length env_a) U) in Hstp1, Htst1;
        assert (Hrel_xr : cenv_demand_rel
          ({| cbinder := xr; cannotation := subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot; ctype_uses := v_mot' |}
           :: {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (subst_tvar_cenv U z env_a ++ env_b)) |}
           :: subst_tvar_cenv U z env_a ++ env_b)
          ({| cbinder := xr; cannotation := subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot;
              ctype_uses := vec_subst (S (length env_a)) z v_mot |}
           :: {| cbinder := xn; cannotation := CNat;
                 ctype_uses := vec_subst (length env_a) z (vec_zero (length (env_a ++ b :: env_b))) |}
           :: subst_tvar_cenv U z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons;
           [ apply cenv_demand_rel_cons;
             [ apply cenv_demand_rel_refl
             | apply cty_alpha_eq_refl
             | apply CTypeNat
             | rewrite !length_app, subst_tvar_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len; apply branch_rel_refl ]
           | apply cty_alpha_eq_refl
           | exact Hv_mot0
           | exact Hbr_mot ]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hstp1 _ Hrel_xr) as [[tst2 ust2 vst2] [Hstp2 [Htst2 [Hust2 Hvst2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htst2, Hust2, Hvst2;
        assert (Hust_tr : branch_rel ust2 (vec_subst (S (S (length env_a))) (vec_zero (length env_b)) u_st)) by (eapply branch_rel_trans; [exact Hust2 | exact Hust1]);
        assert (Htst_tr : cty_alpha_eq tst2 (subst_tvar_in_cty (S (S (length env_a))) (lift_cty 0 2 (lift_cty 0 (length env_a) U)) t_st)) by
          (eapply cty_alpha_eq_trans; [exact Htst2 | exact Htst1]);
        assert (Hsteq' : cty_alpha_eq tst2 (spec_fix_step_cty (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htst_tr |];
           eapply cty_alpha_eq_trans; [apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Hsteq] |];
           rewrite <- (lift_cty_2_SS D (length env_a) U), (subst_tvar_spec_fix_step D mot U (length env_a) Hm_ntv Hmot_safe);
           apply cty_alpha_eq_refl);
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_us _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ub _];
        pose proof (core_derives_lengths D _ _ _ H1) as [Hlen_ust _];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_vm, Hlen_us, Hlen_ub, Hlen_ust;
        rewrite length_app in Hlen_vm, Hlen_us, Hlen_ub, Hlen_ust; cbn [length] in Hlen_vm, Hlen_us, Hlen_ub, Hlen_ust;
        assert (Hrec0' : allows (nth_grade ust2 0) s_rec) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hust_tr) | rewrite vec_subst_nth_lt by lia; exact Hrec0]);
        assert (Hrec1' : allows (nth_grade ust2 1) s_rec) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 1 Hust_tr) | rewrite vec_subst_nth_lt by lia; exact Hrec1]);
        assert (Hust_tl_br : branch_rel (tl (tl ust2)) (vec_subst (length env_a) (vec_zero (length env_b)) (tl (tl u_st)))) by
          (rewrite !vec_subst_tl by (destruct u_st; cbn in *; lia); apply branch_rel_tl, branch_rel_tl; exact Hust_tr);
        assert (Hrecok' : fix_recurrence_ok s_rec (tl (tl ust2))) by
          (unfold fix_recurrence_ok in Hrecok |- *;
           destruct (vec_is_zero (tl (tl u_st))) eqn:Ez;
           [ apply vec_is_zero_iff in Ez;
             replace (length (tl (tl u_st))) with (S (length env_a + length env_b)) in Ez by (destruct u_st as [| ? [| ? ?]]; cbn in *; lia);
             rewrite Ez, vec_subst_zero in Hust_tl_br by (apply vec_zero_length);
             rewrite (branch_rel_vec_is_zero D ED _ _ Hust_tl_br); exact I
           | destruct (vec_is_zero (tl (tl ust2))); [exact I | exact Hrecok] ]);
        assert (Hdep2 : match term_as_cidx (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut) with
                        | Some _ => True
                        | None => cty_uses_var 0 (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot) = false
                        end) by
          (destruct (term_as_cidx scrut) as [ci |] eqn:Es;
           [ destruct (term_as_cidx_subst_tvar_some D b env_a env_b lvl_b scrut _ ci (lift_cty 0 (length env_a) U) Hb H eq_refl Es) as [_ ->]; exact I
           | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ Es);
             apply cty_uses_var_subst_tvar_0; [exact Hdep | exact Hmot_safe] ]);
        assert (Hres_eq : cty_alpha_eq (spec_fix_subj_cty (subst_tvar_in_cterm (length env_a) (lift_cty 0 (length env_a) U) scrut)
                                         (subst_tvar_in_cty (S (length env_a)) (lift_cty 0 (S (length env_a)) U) mot))
                            (subst_tvar_in_cty (length env_a) (lift_cty 0 (length env_a) U) res_ty)) by
          (rewrite Hres; unfold spec_fix_subj_cty;
           destruct (term_as_cidx scrut) as [ci |] eqn:Es;
           [ destruct (term_as_cidx_subst_tvar_some D b env_a env_b lvl_b scrut _ ci (lift_cty 0 (length env_a) U) Hb H eq_refl Es) as [Hc_safe ->];
             pose proof (subst_tvar_in_cty_subst_cidx_0 D mot (lift_cty 0 (length env_a) U) ci (length env_a) Hm_ntv Hmot_safe Hc_safe) as Hcm;
             rewrite lift_cty_add in Hcm; replace (1 + length env_a) with (S (length env_a)) in Hcm by lia;
             rewrite Hcm; apply cty_alpha_eq_refl
           | rewrite (term_as_cidx_subst_tvar_none _ _ _ _ Es);
             rewrite (subst_tvar_in_cty_unshift_0 D mot (lift_cty 0 (length env_a) U) (length env_a) Hdep Hmot_safe), <- (lift_cty_1_S D (length env_a) U);
             apply cty_alpha_eq_refl ]);
        eexists; rewrite <- (lift_cty_1_S D (length env_a) U); split; [| split; [| split]];
        [ eapply CoreFix;
          [ exact Hscr' | exact Hv_mot0 | exact Hbas' | exact Hbeq' | exact Hstp2 | exact Hsteq'
          | exact Hrec0' | exact Hrec1' | exact Hrecok' | exact Hdep2 | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          assert (Hlen_tlu : length (tl (tl u_st)) = S (length env_a + length env_b)) by (destruct u_st as [| ? [| ? ?]]; cbn in *; lia);
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) u_s (vec_add u_b (vec_scale s_rec (tl (tl u_st)))) (length env_b))
            by (try apply vec_zero_length; try (rewrite vec_add_length by (rewrite vec_scale_length; lia)); lia);
          rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) u_b (vec_scale s_rec (tl (tl u_st))) (length env_b))
            by (try apply vec_zero_length; try rewrite vec_scale_length; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [exact Hus' | apply branch_rel_add; [exact Hub' | apply branch_rel_scale; exact Hust_tl_br]]
        | cbn [ctype_demand_row]; exists zero;
          eapply branch_rel_trans;
          [| apply Hadd_zero_tail; rewrite Hvz_len; [reflexivity | rewrite vec_add_length by (destruct v_mot; cbn in *; rewrite vec_scale_length; lia); destruct v_mot; cbn in *; lia] ];
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale (nth_grade v_mot 0) u_s) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot
          | apply branch_rel_scale_grade;
            [ eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; apply allows_refl]
            | intro Hnone; unfold branch_rel in Hbr_mot; rewrite Hnone in Hbr_mot; rewrite Hbr_mot, vec_subst_nth_lt by lia; reflexivity
            | apply H_uv_subst; [lia | exact Hus'] ] ] ]
    end.
  - (* CRecordElemNil *)
    eexists _, _; split; [cbn [map]; apply CRecordElemNil |];
    rewrite !length_app, subst_tvar_cenv_length; cbn [length];
    rewrite Nat.add_succ_r, !vec_subst_zero by (try apply vec_zero_length; exact Hz_len);
    split; [apply branch_rel_refl | exists zero; apply Hadd_zero_tail; rewrite vec_zero_length; reflexivity].
  - (* CRecordElemCons *)
    lazymatch goal with
    | Htv : cty_alpha_eq t_v ft, Hdt : CTypeDemand _ ft dt, Hrec : CRecordElemDerives _ _ _ _ |- _ =>
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[tv' uv' vv'] [Hv' [Htv' [Huv' [qv Hvv']]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htv', Huv', Hvv';
        destruct (subst_tvar_type_demand D U z env_a b env_b lvl_b ft dt Hb Hsafe HU Hdt) as [dt' [Hdt' Hbr_dt]];
        destruct (IHCoreDerives0 env_a eq_refl Hsafe) as [ur' [vr' [Hrest' [Hur' [qrest Hvr']]]]];
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_uv _];
        pose proof (record_elem_derives_lengths D _ _ _ _ Hrec) as [Hlen_ur Hlen_vr];
        pose proof (ctype_demand_length D _ _ _ Hdt) as Hlen_dt;
        cbn [ccomp_demand ctype_demand_row length] in Hlen_uv, Hlen_ur, Hlen_dt, Hlen_vr;
        rewrite length_app in Hlen_uv, Hlen_ur, Hlen_dt, Hlen_vr; cbn [length] in Hlen_uv, Hlen_ur, Hlen_dt, Hlen_vr;
        eexists _, _; split;
        [ cbn [map]; eapply CRecordElemCons;
          [ exact Hv'
          | eapply cty_alpha_eq_trans; [exact Htv' | apply subst_tvar_in_cty_alpha_eq; [apply cty_alpha_eq_refl | exact Htv]]
          | exact Hdt'
          | exact Hrest' ]
        | split;
          [ rewrite (vec_subst_add D (length env_a) (vec_zero (length env_b)) (vec_scale fg u_v) u_rest (length env_b))
              by (try apply vec_zero_length; try rewrite vec_scale_length; lia);
            rewrite vec_subst_scale; apply branch_rel_add; [apply branch_rel_scale; exact Huv' | exact Hur']
          | exists qrest;
            rewrite (vec_subst_add D (length env_a) z dt v_rest (length env_b)) by lia;
            rewrite <- vec_add_assoc;
            apply branch_rel_add; [exact Hbr_dt | exact Hvr'] ] ]
    end.
Qed.

End GradedCoreTypeSubst.
