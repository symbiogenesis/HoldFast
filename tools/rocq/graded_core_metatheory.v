(* SPDX-License-Identifier: Apache-2.0 *)

From Corelib Require Import Init.Datatypes.
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Bool.Bool Lia.
Require Import graded_pure graded_domains graded_core.
Import ListNotations GradedDomains GradedCore.
Local Arguments Nat.ltb !_ !_ : simpl nomatch.
Local Arguments Nat.eqb !_ !_ : simpl nomatch.

Module GradedCoreMetatheory.

Scheme CTypeDemand_ind_mut := Induction for CTypeDemand Sort Prop
  with CRecordFieldDemand_ind_mut := Induction for CRecordFieldDemand Sort Prop
  with CIdxListDemand_ind_mut := Induction for CIdxListDemand Sort Prop.

Scheme CUniverseLevel_ind_mut := Induction for CUniverseLevel Sort Prop
  with CRecordFieldLevel_ind_mut := Induction for CRecordFieldLevel Sort Prop.

(* ================================================================= *)
(* Part 1: Domain Erasure Laws, Lengths, and Vector Algebra          *)
(* ================================================================= *)

Record ErasureDomain (D : JoinDomain) : Prop := {
  erasure_one_nonzero : ~ allows one (@zero D);
  erasure_allows_zero_eq : forall a, allows a (@zero D) -> a = zero;
  erasure_add_zero : forall a b, @add D a b = zero -> a = zero /\ b = zero;
  erasure_mul_zero : forall a b, @mul D a b = zero -> a = zero \/ b = zero
}.

Lemma nat_exact_erasure : ErasureDomain NatExactJoin.
Proof.
  constructor; cbn; [discriminate | auto | intros; lia | intros a b H; apply Nat.eq_mul_0; exact H].
Qed.

Lemma nat_bound_erasure : ErasureDomain NatBoundJoin.
Proof.
  constructor; cbn; [lia | intros; lia | intros; lia | intros a b H; apply Nat.eq_mul_0; exact H].
Qed.

Lemma presence_erasure : ErasureDomain PresenceJoin.
Proof.
  constructor; cbn; unfold presence_le.
  - intro H. discriminate (H eq_refl).
  - intros [] H; [discriminate (H eq_refl) | reflexivity].
  - intros [] [] H; cbn in H; try discriminate; auto.
  - intros [] [] H; cbn in H; auto.
Qed.

Lemma linear_erasure : ErasureDomain LinearDomain.
Proof.
  constructor; cbn; [discriminate | auto | intros [] [] H; cbn in H; try discriminate; auto | intros [] [] H; cbn in H; try discriminate; auto].
Qed.

Lemma affine_erasure : ErasureDomain AffineDomain.
Proof.
  constructor; cbn; [auto | intros [] H; cbn in H; try contradiction; reflexivity | intros [] [] H; cbn in H; try discriminate; auto | intros [] [] H; cbn in H; try discriminate; auto].
Qed.

Lemma security_erasure : ErasureDomain SecurityLoHi.
Proof.
  constructor; cbn; unfold sec_le.
  - intro H. discriminate (H eq_refl).
  - intros [] H; [reflexivity | discriminate (H eq_refl)].
  - intros [] [] H; cbn in H; try discriminate; auto.
  - intros [] [] H; cbn in H; auto.
Qed.

Lemma vec_allows_zero_eq : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (u : list (grade D)), vec_allows u (vec_zero (D := D) (length u)) -> u = vec_zero (D := D) (length u).
Proof.
  intros D ED u. unfold vec_allows, vec_zero.
  induction u as [| a u IH]; intro H; cbn in *; [reflexivity |].
  inversion H as [| ? ? ? ? Ha Hrest]; subst.
  apply (erasure_allows_zero_eq D ED) in Ha. subst a.
  f_equal. apply IH; exact Hrest.
Qed.

Lemma nth_grade_zero : forall (D : JoinDomain) n k,
  nth_grade (vec_zero (D := D) n) k = zero.
Proof.
  intros D n. induction n as [| n IH]; intros [| k]; cbn; [reflexivity | reflexivity | reflexivity | apply IH].
Qed.

Lemma nth_grade_single_same : forall (D : JoinDomain) n x q,
  x < n -> nth_grade (vec_single (D := D) n x q) x = q.
Proof.
  intros D n. induction n as [| n IH]; intros [| x] q Hlt; cbn; try lia; [reflexivity | apply IH; lia].
Qed.

Lemma nth_grade_single_other : forall (D : JoinDomain) n x y q,
  x <> y -> nth_grade (vec_single (D := D) n x q) y = zero.
Proof.
  intros D n. induction n as [| n IH]; intros [| x] [| y] q Hne; cbn;
    try reflexivity; try congruence; try apply nth_grade_zero.
  apply IH; lia.
Qed.

Lemma nth_grade_add : forall (D : JoinDomain) (u v : list (grade D)) k,
  length u = length v ->
  nth_grade (vec_add u v) k = add (nth_grade u k) (nth_grade v k).
Proof.
  intros D u. induction u as [| a u IH]; intros [| b v] k Hlen; cbn in *; try discriminate.
  - unfold nth_grade, nth_default. destruct k; cbn; rewrite (add_zero D); reflexivity.
  - unfold nth_grade, nth_default in *. destruct k; cbn; [reflexivity | apply IH; congruence].
Qed.

Lemma mul_zero_r : forall (D : Domain) (q : grade D),
  mul q zero = zero.
Proof.
  intros D q. rewrite (mul_comm D q zero). apply (mul_zero D).
Qed.

Lemma nth_grade_scale : forall (D : JoinDomain) (q : grade D) u k,
  nth_grade (vec_scale q u) k = mul q (nth_grade u k).
Proof.
  intros D q u. induction u as [| a u IH]; intros [| k]; cbn;
    rewrite ?(mul_zero_r D); try reflexivity; apply IH.
Qed.

Lemma nth_grade_allows : forall (D : JoinDomain) (u v : list (grade D)) k,
  vec_allows u v -> allows (nth_grade u k) (nth_grade v k).
Proof.
  intros D u v k H. revert k. induction H; intros [| k]; cbn;
    try apply allows_refl; try assumption; apply IHForall2.
Qed.

Lemma nth_grade_tl : forall (D : JoinDomain) (u : list (grade D)) k,
  nth_grade (tl u) k = nth_grade u (S k).
Proof.
  intros D [| a u] k; cbn; [destruct k; reflexivity | reflexivity].
Qed.

Lemma BranchVec_length : forall (D : JoinDomain) (u1 u2 u : list (grade D)),
  length u1 = length u2 ->
  BranchVec u1 u2 u ->
  length u = length u1.
Proof.
  intros D u1 u2 u Hlen Hbr. unfold BranchVec in Hbr.
  destruct (grade_join D) as [j |].
  - subst u. apply vec_join_length; exact Hlen.
  - destruct Hbr as [_ ->]. reflexivity.
Qed.

Lemma cidx_demand_length : forall (D : JoinDomain) (env : cenv D) i d,
  CIdxDemand env i d -> length d = length env.
Proof.
  intros D env i d H. induction H; cbn;
    try apply vec_single_length;
    try apply vec_zero_length;
    try (rewrite vec_add_length; congruence);
    try (rewrite vec_scale_length; congruence).
  rewrite vec_add_length; [apply vec_single_length |].
  rewrite vec_single_length.
  erewrite BranchVec_length; [| | eassumption];
    cbn in IHCIdxDemand1, IHCIdxDemand2;
    destruct dl, dr; cbn in *; lia.
Qed.

Lemma cidx_list_demand_length : forall (D : JoinDomain) (env : cenv D) l d,
  CIdxListDemand env l d -> length d = length env.
Proof.
  intros D env l d H. induction H; cbn.
  - apply vec_zero_length.
  - rewrite vec_add_length; [eapply cidx_demand_length; eassumption |].
    erewrite cidx_demand_length; [| eassumption]. symmetry; exact IHCIdxListDemand.
Qed.

Lemma ctype_demand_length : forall (D : JoinDomain) (env : cenv D) T d,
  CTypeDemand env T d -> length d = length env.
Proof.
  intros D env T d H.
  induction H using CTypeDemand_ind_mut with
    (P := fun env T d _ => length d = length env)
    (P0 := fun env fs df _ => length df = length env)
    (P1 := fun env ls dl _ => length dl = length env); cbn;
    try apply vec_zero_length;
    try apply vec_single_length;
    try (rewrite vec_scale_length; assumption);
    try assumption.
  - rewrite vec_add_length; [exact IHCTypeDemand |].
    eapply eq_trans; [exact IHCTypeDemand | symmetry; eapply cidx_demand_length; eassumption].
  - rewrite vec_add_length; [exact IHCTypeDemand1 |].
    cbn in IHCTypeDemand2. destruct b; cbn in *; lia.
  - rewrite vec_add_length; [exact IHCTypeDemand1 |].
    cbn in IHCTypeDemand2. destruct b; cbn in *; lia.
  - rewrite vec_add_length; congruence.
  - rewrite vec_add_length; congruence.
  - rewrite vec_add_length; [eapply cidx_demand_length; eassumption |].
    eapply eq_trans; [eapply cidx_demand_length; eassumption | symmetry; exact IHCTypeDemand].
Qed.

Lemma record_extend_length : forall (D : JoinDomain) (env : cenv D) bs fields ext,
  CRecordExtendEnv env bs fields ext ->
  length ext = length fields + length env.
Proof.
  intros D env bs fields ext H. induction H; cbn; [reflexivity |].
  rewrite IHCRecordExtendEnv, length_map. cbn. lia.
Qed.

Lemma core_derives_lengths : forall (D : JoinDomain) (env : cenv D) t j,
  CoreDerives env t j ->
  length (ccomp_demand j) = length env /\ length (ctype_demand_row j) = length env.
Proof.
  intros D env t j H.
  induction H using CoreDerives_ind_mut with
    (P := fun env t j _ => length (ccomp_demand j) = length env /\ length (ctype_demand_row j) = length env)
    (P0 := fun env fs u v _ => length u = length env /\ length v = length env); cbn;
    repeat match goal with
    | [ IH : _ /\ _ |- _ ] => destruct IH
    | [ Hd : CTypeDemand _ _ _ |- _ ] => apply ctype_demand_length in Hd
    | [ Hd : CIdxDemand _ _ _ |- _ ] => apply cidx_demand_length in Hd
    | [ Hd : CRecordExtendEnv _ _ _ _ |- _ ] => apply record_extend_length in Hd
    | [ Ha : vec_allows _ _ |- _ ] => apply vec_allows_length in Ha
    end;
    try (split; apply vec_zero_length).
  - (* CoreVar *)
    split; [apply vec_single_length |].
    rewrite length_app, repeat_length.
    rewrite ?length_skipn in *.
    destruct (nth_error_Some env x) as [Hs _].
    assert (Hx : x < length env) by (apply Hs; unfold clookup in *; congruence).
    lia.
  - (* CoreNatVal *)
    split; [assumption | apply vec_zero_length].
  - (* CoreTypeVal *)
    split; [apply vec_zero_length | assumption].
  - (* CoreLam *)
    cbn in *.
    split; [destruct u; cbn in *; lia |].
    rewrite vec_add_length; [assumption | destruct v; cbn in *; lia].
  - (* CoreApp *)
    cbn in *.
    split.
    + rewrite vec_add_length; [assumption | rewrite vec_scale_length; congruence].
    + rewrite vec_add_length; [destruct b; cbn in *; lia |].
      rewrite vec_scale_length. destruct b; cbn in *; try lia.
      subst z_type. destruct dom; cbn; try congruence. destruct arg; cbn; congruence.
  - (* CoreLet *)
    cbn in *.
    split.
    + rewrite vec_add_length; [destruct u_bod; cbn in *; lia | rewrite vec_scale_length; destruct u_bod; cbn in *; lia].
    + rewrite vec_add_length; [destruct v_bod; cbn in *; lia |].
      rewrite vec_scale_length. destruct v_bod; cbn in *; try lia.
      destruct ann; cbn; try lia. destruct rhs; cbn; lia.
  - (* CorePair *)
    cbn in *.
    split; [rewrite vec_add_length; congruence | rewrite vec_add_length; [assumption | destruct b; cbn in *; lia]].
  - (* CoreLetPair *)
    cbn in *.
    split.
    + rewrite vec_add_length; [destruct u_b as [| ? [| ? ?]]; cbn in *; lia | rewrite vec_scale_length; destruct u_b as [| ? [| ? ?]]; cbn in *; lia].
    + rewrite vec_add_length; [destruct v_mot; cbn in *; lia | rewrite vec_scale_length; destruct v_mot; cbn in *; lia].
  - (* CorePromote *)
    split; [rewrite vec_scale_length; assumption | assumption].
  - (* CoreLetBox *)
    cbn in *.
    split.
    + rewrite vec_add_length; [destruct w; cbn in *; lia | destruct w; cbn in *; lia].
    + rewrite vec_add_length; [destruct v_mot; cbn in *; lia |].
      rewrite vec_scale_length. subst z_ty. destruct v_mot; cbn in *; try lia.
      destruct box_term as [| | | | | | | | | q' iv | | | | | | | | |]; try lia.
      destruct iv; try lia. rewrite vec_scale_length; lia.
  - (* CoreInl *)
    cbn in *. split; [assumption | rewrite vec_add_length; congruence].
  - (* CoreInr *)
    cbn in *. split; [assumption | rewrite vec_add_length; congruence].
  - (* CoreMatchSum *)
    cbn in *.
    match goal with
    | [ Hbr : BranchVec (tl u1) (tl u2) u_br |- _ ] =>
        pose proof (BranchVec_length D (tl u1) (tl u2) u_br ltac:(destruct u1, u2; cbn in *; lia) Hbr)
    end.
    split.
    + rewrite vec_add_length; rewrite vec_scale_length; [assumption | destruct u1; cbn in *; lia].
    + rewrite vec_add_length; [destruct v_mot; cbn in *; lia | rewrite vec_scale_length; destruct v_mot; cbn in *; lia].
  - (* CoreIf *)
    cbn in *.
    match goal with
    | [ Hbr1 : BranchVec u1 u2 u_br, Hbr2 : BranchVec v1 v2 v_br |- _ ] =>
        pose proof (BranchVec_length D u1 u2 u_br ltac:(congruence) Hbr1);
        pose proof (BranchVec_length D v1 v2 v_br ltac:(congruence) Hbr2)
    end.
    split; [rewrite vec_add_length; congruence | congruence].
  - (* CoreRecordMk *)
    cbn in *. split; assumption.
  - (* CoreMatchRecord *)
    cbn in *.
    split; [| assumption].
    rewrite vec_add_length; rewrite vec_scale_length; [assumption | rewrite length_skipn; lia].
  - (* CoreSubgrade *)
    cbn in *. split; assumption.
  - (* CoreFix *)
    cbn in *.
    split.
    + rewrite vec_add_length; [assumption |].
      rewrite vec_add_length; [congruence |].
      rewrite vec_scale_length. destruct u_st as [| ? [| ? ?]]; cbn in *; lia.
    + rewrite vec_add_length; [destruct v_mot; cbn in *; lia | rewrite vec_scale_length; destruct v_mot; cbn in *; lia].
  - (* CRecordElemCons *)
    cbn in *. split; rewrite vec_add_length; rewrite ?vec_scale_length; congruence.
Qed.

Lemma record_elem_derives_lengths : forall (D : JoinDomain) (env : cenv D) fs u v,
  CRecordElemDerives env fs u v ->
  length u = length env /\ length v = length env.
Proof.
  intros D env fs u v H.
  exact (core_derives_lengths D env (CRecordMk 0 fs) _ (CoreRecordMk env 0 fs u v H)).
Qed.

(* ================================================================= *)
(* Part 2: Parallel Renaming, Weakening, and Exchange                *)
(* ================================================================= *)

Lemma ren_cidx_ext : forall (D : JoinDomain) (rho1 rho2 : nat -> nat) (i : cidx D),
  (forall x, rho1 x = rho2 x) ->
  ren_cidx rho1 i = ren_cidx rho2 i.
Proof.
  intros D rho1 rho2 i. revert rho1 rho2.
  induction i; intros rho1 rho2 H; cbn; try reflexivity;
    try (rewrite H; reflexivity);
    try (rewrite (IHi1 _ _ H), (IHi2 _ _ H); reflexivity).
  - rewrite (IHi _ _ H). reflexivity.
  - rewrite H. f_equal; [apply IHi1 | apply IHi2]; intros [| y]; cbn; auto.
Qed.

Lemma ren_cty_ext : forall (D : JoinDomain) (rho1 rho2 : nat -> nat) (T : cty D),
  (forall x, rho1 x = rho2 x) ->
  ren_cty rho1 T = ren_cty rho2 T.
Proof.
  intros D rho1 rho2 T. revert rho1 rho2.
  induction T using cty_ind_nested; intros rho1 rho2 Hext; cbn; try reflexivity.
  - rewrite (IHT _ _ Hext), (ren_cidx_ext D _ _ len Hext). reflexivity.
  - rewrite Hext; reflexivity.
  - rewrite (IHT _ _ Hext); reflexivity.
  - rewrite Hext; reflexivity.
  - f_equal; [apply IHT1; exact Hext | apply IHT2; intros [| y]; cbn; auto].
  - f_equal; [apply IHT1; exact Hext | apply IHT2; intros [| y]; cbn; auto].
  - f_equal; apply IHT; exact Hext.
  - f_equal; [apply IHT1 | apply IHT2]; exact Hext.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2.
    rewrite (H2 _ _ Hext), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite (ren_cidx_ext D _ _ idx Hext), IH. reflexivity.
Qed.

Lemma ren_cidx_comp : forall (D : JoinDomain) (rho1 rho2 : nat -> nat) (i : cidx D),
  ren_cidx rho2 (ren_cidx rho1 i) = ren_cidx (fun x => rho2 (rho1 x)) i.
Proof.
  intros D rho1 rho2 i. revert rho1 rho2.
  induction i; intros rho1 rho2; cbn; try reflexivity;
    try (rewrite IHi1, IHi2; reflexivity).
  - rewrite IHi. reflexivity.
  - f_equal; [rewrite IHi1; apply ren_cidx_ext | rewrite IHi2; apply ren_cidx_ext];
      intros [| y]; cbn; reflexivity.
Qed.

Lemma ren_cty_comp : forall (D : JoinDomain) (rho1 rho2 : nat -> nat) (T : cty D),
  ren_cty rho2 (ren_cty rho1 T) = ren_cty (fun x => rho2 (rho1 x)) T.
Proof.
  intros D rho1 rho2 T. revert rho1 rho2.
  induction T using cty_ind_nested; intros rho1 rho2; cbn; try reflexivity.
  - rewrite IHT, ren_cidx_comp. reflexivity.
  - rewrite IHT; reflexivity.
  - f_equal; [apply IHT1 | rewrite IHT2; apply ren_cty_ext; intros [| y]; cbn; reflexivity].
  - f_equal; [apply IHT1 | rewrite IHT2; apply ren_cty_ext; intros [| y]; cbn; reflexivity].
  - f_equal; apply IHT.
  - f_equal; [apply IHT1 | apply IHT2].
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite ren_cidx_comp, IH. reflexivity.
Qed.

Lemma ren_cidx_id : forall (D : JoinDomain) (i : cidx D),
  ren_cidx (fun x => x) i = i.
Proof.
  intros D i. induction i; cbn; try congruence.
  f_equal; [rewrite (ren_cidx_ext D _ (fun x => x)); [exact IHi1 | intros [| y]; reflexivity]
           |rewrite (ren_cidx_ext D _ (fun x => x)); [exact IHi2 | intros [| y]; reflexivity]].
Qed.

Lemma ren_cty_id : forall (D : JoinDomain) (T : cty D),
  ren_cty (fun x => x) T = T.
Proof.
  intros D T. induction T using cty_ind_nested; cbn; try reflexivity.
  - rewrite IHT. f_equal. apply ren_cidx_id.
  - rewrite IHT; reflexivity.
  - rewrite IHT1. f_equal.
    rewrite (ren_cty_ext D _ (fun x => x)); [exact IHT2 | intros [| y]; reflexivity].
  - rewrite IHT1. f_equal.
    rewrite (ren_cty_ext D _ (fun x => x)); [exact IHT2 | intros [| y]; reflexivity].
  - rewrite IHT; reflexivity.
  - rewrite IHT1, IHT2; reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply ren_cidx_id | exact IH].
Qed.

Lemma erase_hints_ren : forall (D : JoinDomain) rho (T : cty D),
  erase_hints (ren_cty rho T) = ren_cty rho (erase_hints T).
Proof.
  intros D rho T. revert rho.
  induction T using cty_ind_nested; intro rho; cbn; try reflexivity; try (f_equal; auto; fail).
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
Qed.

Lemma ren_cty_alpha_eq : forall (D : JoinDomain) rho (T1 T2 : cty D),
  cty_alpha_eq T1 T2 ->
  cty_alpha_eq (ren_cty rho T1) (ren_cty rho T2).
Proof.
  intros D rho T1 T2 H. unfold cty_alpha_eq in *. rewrite !erase_hints_ren, H. reflexivity.
Qed.

Lemma ren_cidx_uses_var_gen : forall (D : JoinDomain) (i : cidx D) k (r : nat -> nat),
  (forall x, (x <= k -> r x = x) /\ (x > k -> r x > k)) ->
  cidx_uses_var k (ren_cidx r i) = cidx_uses_var k i.
Proof.
  intros D i. induction i; intros k r Hk; cbn; try reflexivity;
    try (rewrite IHi1, IHi2; auto; reflexivity).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
    assert (H1 : Nat.eqb x k = false) by (apply Nat.eqb_neq; exact Hne).
    assert (H2 : Nat.eqb (r x) k = false).
    { apply Nat.eqb_neq. destruct (le_lt_dec x k); [rewrite (proj1 (Hk x) l); exact Hne | pose proof (proj2 (Hk x) l); lia]. }
    rewrite H1, H2; reflexivity.
  - apply IHi; exact Hk.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
    assert (H1 : Nat.eqb b k = false) by (apply Nat.eqb_neq; exact Hne).
    assert (H2 : Nat.eqb (r b) k = false).
    { apply Nat.eqb_neq. destruct (le_lt_dec b k); [rewrite (proj1 (Hk b) l); exact Hne | pose proof (proj2 (Hk b) l); lia]. }
    rewrite H1, H2; reflexivity.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
    assert (H1 : Nat.eqb p k = false) by (apply Nat.eqb_neq; exact Hne).
    assert (H2 : Nat.eqb (r p) k = false).
    { apply Nat.eqb_neq. destruct (le_lt_dec p k); [rewrite (proj1 (Hk p) l); exact Hne | pose proof (proj2 (Hk p) l); lia]. }
    rewrite H1, H2; reflexivity.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
    assert (H1 : Nat.eqb p k = false) by (apply Nat.eqb_neq; exact Hne).
    assert (H2 : Nat.eqb (r p) k = false).
    { apply Nat.eqb_neq. destruct (le_lt_dec p k); [rewrite (proj1 (Hk p) l); exact Hne | pose proof (proj2 (Hk p) l); lia]. }
    rewrite H1, H2; reflexivity.
  - assert (Hs0 : Nat.eqb (r s) k = Nat.eqb s k).
    { destruct (Nat.eq_dec s k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
      assert (H1 : Nat.eqb s k = false) by (apply Nat.eqb_neq; exact Hne).
      assert (H2 : Nat.eqb (r s) k = false).
      { apply Nat.eqb_neq. destruct (le_lt_dec s k); [rewrite (proj1 (Hk s) l); exact Hne | pose proof (proj2 (Hk s) l); lia]. }
      rewrite H1, H2; reflexivity. }
    assert (Hs2 : forall x, (x <= S k -> ren_shift r x = x) /\ (x > S k -> ren_shift r x > S k)).
    { intros [| x']; cbn; split; intro Hlt; try lia;
        [rewrite (proj1 (Hk x') ltac:(lia)); reflexivity | pose proof (proj2 (Hk x') ltac:(lia)); lia]. }
    rewrite Hs0, (IHi1 (S k) (ren_shift r) Hs2), (IHi2 (S k) (ren_shift r) Hs2). reflexivity.
Qed.

Lemma ren_cty_uses_var_gen : forall (D : JoinDomain) (T : cty D) k (rn : nat -> nat),
  (forall x, (x <= k -> rn x = x) /\ (x > k -> rn x > k)) ->
  cty_uses_var k (ren_cty rn T) = cty_uses_var k T.
Proof.
  intros D T. induction T using cty_ind_nested; intros k rn Hk; cbn; try reflexivity.
  - rewrite (IHT k rn Hk), (ren_cidx_uses_var_gen D len k rn Hk). reflexivity.
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
    assert (H1 : Nat.eqb x k = false) by (apply Nat.eqb_neq; exact Hne).
    assert (H2 : Nat.eqb (rn x) k = false).
    { apply Nat.eqb_neq. destruct (le_lt_dec x k); [rewrite (proj1 (Hk x) l); exact Hne | pose proof (proj2 (Hk x) l); lia]. }
    rewrite H1, H2; reflexivity.
  - apply IHT; exact Hk.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite (proj1 (Hk k) (le_n k)), Nat.eqb_refl; reflexivity |].
    assert (H1 : Nat.eqb b k = false) by (apply Nat.eqb_neq; exact Hne).
    assert (H2 : Nat.eqb (rn b) k = false).
    { apply Nat.eqb_neq. destruct (le_lt_dec b k); [rewrite (proj1 (Hk b) l); exact Hne | pose proof (proj2 (Hk b) l); lia]. }
    rewrite H1, H2; reflexivity.
  - assert (Hs2 : forall x, (x <= S k -> ren_shift rn x = x) /\ (x > S k -> ren_shift rn x > S k)).
    { intros [| x']; cbn; split; intro Hlt; try lia;
        [rewrite (proj1 (Hk x') ltac:(lia)); reflexivity | pose proof (proj2 (Hk x') ltac:(lia)); lia]. }
    rewrite (IHT1 k rn Hk), (IHT2 (S k) (ren_shift rn) Hs2). reflexivity.
  - assert (Hs2 : forall x, (x <= S k -> ren_shift rn x = x) /\ (x > S k -> ren_shift rn x > S k)).
    { intros [| x']; cbn; split; intro Hlt; try lia;
        [rewrite (proj1 (Hk x') ltac:(lia)); reflexivity | pose proof (proj2 (Hk x') ltac:(lia)); lia]. }
    rewrite (IHT1 k rn Hk), (IHT2 (S k) (ren_shift rn) Hs2). reflexivity.
  - apply IHT; exact Hk.
  - rewrite (IHT1 k rn Hk), (IHT2 k rn Hk). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 k rn Hk), (IHf H3). reflexivity.
  - induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite (ren_cidx_uses_var_gen D idx k rn Hk), IH. reflexivity.
Qed.

Lemma ren_cty_uses_var_shift : forall (D : JoinDomain) rho (T : cty D),
  cty_uses_var 0 (ren_cty (ren_shift rho) T) = cty_uses_var 0 T.
Proof.
  intros D rho T. apply ren_cty_uses_var_gen.
  intros [| x']; cbn; split; intro Hlt; lia.
Qed.

(* Commutation of ren with unshift / subst / spec *)

Lemma unshift_var_S : forall k y,
  y <> k ->
  unshift_var (S k) (S y) = S (unshift_var k y).
Proof.
  intros k y Hne. unfold unshift_var.
  destruct (Nat.ltb_spec (S y) (S k)), (Nat.ltb_spec y k); lia.
Qed.

Lemma ren_cidx_ext_except : forall (D : JoinDomain) (i : cidx D) k (f g : nat -> nat),
  cidx_uses_var k i = false ->
  (forall x, x <> k -> f x = g x) ->
  ren_cidx f i = ren_cidx g i.
Proof.
  intros D i. induction i; intros k f g Huse Hext; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huse as [H1 H2];
         rewrite (IHi1 k f g H1 Hext), (IHi2 k f g H2 Hext); reflexivity).
  - f_equal; apply Hext; apply Nat.eqb_neq; exact Huse.
  - f_equal; apply IHi with (k := k); assumption.
  - f_equal; apply Hext; apply Nat.eqb_neq; exact Huse.
  - f_equal; apply Hext; apply Nat.eqb_neq; exact Huse.
  - f_equal; apply Hext; apply Nat.eqb_neq; exact Huse.
  - apply orb_false_iff in Huse as [H12 H3]. apply orb_false_iff in H12 as [H1 H2].
    f_equal; [apply Hext; apply Nat.eqb_neq; exact H1 | |].
    + apply IHi1 with (k := S k); [exact H2 | intros [| x'] Hne; cbn; [reflexivity | f_equal; apply Hext; lia]].
    + apply IHi2 with (k := S k); [exact H3 | intros [| x'] Hne; cbn; [reflexivity | f_equal; apply Hext; lia]].
Qed.

Lemma ren_cty_ext_except : forall (D : JoinDomain) (T : cty D) k (f g : nat -> nat),
  cty_uses_var k T = false ->
  (forall x, x <> k -> f x = g x) ->
  ren_cty f T = ren_cty g T.
Proof.
  intros D T. induction T using cty_ind_nested; intros k f g Huse Hext; cbn in *; try reflexivity.
  - apply orb_false_iff in Huse as [HT Hl].
    f_equal; [apply IHT with (k := k); assumption | apply ren_cidx_ext_except with (k := k); assumption].
  - f_equal; apply Hext; apply Nat.eqb_neq; exact Huse.
  - f_equal; apply IHT with (k := k); assumption.
  - f_equal; apply Hext; apply Nat.eqb_neq; exact Huse.
  - apply orb_false_iff in Huse as [H1 H2].
    f_equal; [apply IHT1 with (k := k); assumption |].
    apply IHT2 with (k := S k); [exact H2 | intros [| x'] Hne; cbn; [reflexivity | f_equal; apply Hext; lia]].
  - apply orb_false_iff in Huse as [H1 H2].
    f_equal; [apply IHT1 with (k := k); assumption |].
    apply IHT2 with (k := S k); [exact H2 | intros [| x'] Hne; cbn; [reflexivity | f_equal; apply Hext; lia]].
  - f_equal; apply IHT with (k := k); assumption.
  - apply orb_false_iff in Huse as [H1 H2].
    f_equal; [apply IHT1 with (k := k) | apply IHT2 with (k := k)]; assumption.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huse as [Hft Hrest].
    rewrite (H2 k f g Hft Hext), (IHf H3 Hrest). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huse as [Hi Hrest].
    rewrite (ren_cidx_ext_except D idx k f g Hi Hext), (IH Hrest). reflexivity.
Qed.

Lemma cidx_uses_var_ren_ne : forall (D : JoinDomain) (i : cidx D) k (r : nat -> nat),
  cidx_uses_var k i = false ->
  (forall x, x <> k -> r x <> k) ->
  cidx_uses_var k (ren_cidx r i) = false.
Proof.
  intros D i. induction i; intros k rn Huse Hne; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huse as [H1 H2]; rewrite (IHi1 k rn H1 Hne), (IHi2 k rn H2 Hne); reflexivity).
  - apply Nat.eqb_neq. apply Hne. apply Nat.eqb_neq; exact Huse.
  - apply IHi; assumption.
  - apply Nat.eqb_neq. apply Hne. apply Nat.eqb_neq; exact Huse.
  - apply Nat.eqb_neq. apply Hne. apply Nat.eqb_neq; exact Huse.
  - apply Nat.eqb_neq. apply Hne. apply Nat.eqb_neq; exact Huse.
  - apply orb_false_iff in Huse as [H12 H3]. apply orb_false_iff in H12 as [H1 H2].
    assert (Hs : forall x, x <> S k -> ren_shift rn x <> S k)
      by (intros [| x'] Hx; cbn; [lia | pose proof (Hne x' ltac:(lia)); lia]).
    rewrite (proj2 (Nat.eqb_neq _ _) (Hne s (proj1 (Nat.eqb_neq _ _) H1))).
    rewrite (IHi1 (S k) (ren_shift rn) H2 Hs), (IHi2 (S k) (ren_shift rn) H3 Hs). reflexivity.
Qed.

Lemma cty_uses_var_ren_ne : forall (D : JoinDomain) (T : cty D) k (r : nat -> nat),
  cty_uses_var k T = false ->
  (forall x, x <> k -> r x <> k) ->
  cty_uses_var k (ren_cty r T) = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros k rn Huse Hne; cbn in *; try reflexivity.
  - apply orb_false_iff in Huse as [HT Hl].
    rewrite (IHT k rn HT Hne), (cidx_uses_var_ren_ne D len k rn Hl Hne). reflexivity.
  - apply Nat.eqb_neq. apply Hne. apply Nat.eqb_neq; exact Huse.
  - apply IHT; assumption.
  - apply Nat.eqb_neq. apply Hne. apply Nat.eqb_neq; exact Huse.
  - apply orb_false_iff in Huse as [H1 H2].
    assert (Hs : forall x, x <> S k -> ren_shift rn x <> S k)
      by (intros [| x'] Hx; cbn; [lia | pose proof (Hne x' ltac:(lia)); lia]).
    rewrite (IHT1 k rn H1 Hne), (IHT2 (S k) (ren_shift rn) H2 Hs). reflexivity.
  - apply orb_false_iff in Huse as [H1 H2].
    assert (Hs : forall x, x <> S k -> ren_shift rn x <> S k)
      by (intros [| x'] Hx; cbn; [lia | pose proof (Hne x' ltac:(lia)); lia]).
    rewrite (IHT1 k rn H1 Hne), (IHT2 (S k) (ren_shift rn) H2 Hs). reflexivity.
  - apply IHT; assumption.
  - apply orb_false_iff in Huse as [H1 H2]. rewrite (IHT1 k rn H1 Hne), (IHT2 k rn H2 Hne). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huse as [Hft Hrest].
    rewrite (H2 k rn Hft Hne), (IHf H3 Hrest). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huse as [Hi Hrest].
    rewrite (cidx_uses_var_ren_ne D idx k rn Hi Hne), (IH Hrest). reflexivity.
Qed.

Lemma ren_unshift_cidx_gen : forall (D : JoinDomain) (i : cidx D) k (r1 r2 : nat -> nat),
  (forall x, x <> k -> r2 x <> k /\ r1 (unshift_var k x) = unshift_var k (r2 x)) ->
  cidx_uses_var k i = false ->
  ren_cidx r1 (ren_cidx (unshift_var k) i) = ren_cidx (unshift_var k) (ren_cidx r2 i).
Proof.
  intros D i. induction i; intros k r1 r2 Hext Huse; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huse as [H1 H2];
         rewrite (IHi1 k r1 r2 Hext H1), (IHi2 k r1 r2 Hext H2); reflexivity).
  - f_equal; apply (proj2 (Hext x (proj1 (Nat.eqb_neq _ _) Huse))).
  - f_equal; apply IHi; assumption.
  - f_equal; apply (proj2 (Hext b (proj1 (Nat.eqb_neq _ _) Huse))).
  - f_equal; apply (proj2 (Hext p (proj1 (Nat.eqb_neq _ _) Huse))).
  - f_equal; apply (proj2 (Hext p (proj1 (Nat.eqb_neq _ _) Huse))).
  - apply orb_false_iff in Huse as [H12 H3]. apply orb_false_iff in H12 as [H1 H2].
    assert (Hs : forall x, x <> S k ->
                   ren_shift r2 x <> S k /\ ren_shift r1 (unshift_var (S k) x) = unshift_var (S k) (ren_shift r2 x)).
    { intros [| x'] Hne; [unfold unshift_var; cbn; split; [lia | reflexivity] |].
      destruct (Hext x' ltac:(lia)) as [Hr2 Hrw].
      split; [cbn; lia | cbn; rewrite (unshift_var_S k x' ltac:(lia)), (unshift_var_S k (r2 x') Hr2); cbn; f_equal; exact Hrw]. }
    assert (Hsk : forall x, x <> S k -> ren_shift (unshift_var k) x = unshift_var (S k) x).
    { intros [| x'] Hne; [unfold unshift_var; reflexivity | cbn; symmetry; apply unshift_var_S; lia]. }
    f_equal; [apply (proj2 (Hext s (proj1 (Nat.eqb_neq _ _) H1))) | |].
    + rewrite (ren_cidx_ext_except D i1 (S k) _ _ H2 Hsk).
      rewrite (ren_cidx_ext_except D (ren_cidx (ren_shift r2) i1) (S k) _ _
                 (cidx_uses_var_ren_ne D i1 (S k) (ren_shift r2) H2 (fun x Hx => proj1 (Hs x Hx))) Hsk).
      apply IHi1; assumption.
    + rewrite (ren_cidx_ext_except D i2 (S k) _ _ H3 Hsk).
      rewrite (ren_cidx_ext_except D (ren_cidx (ren_shift r2) i2) (S k) _ _
                 (cidx_uses_var_ren_ne D i2 (S k) (ren_shift r2) H3 (fun x Hx => proj1 (Hs x Hx))) Hsk).
      apply IHi2; assumption.
Qed.

Lemma ren_unshift_cidx : forall (D : JoinDomain) rho (i : cidx D),
  cidx_uses_var 0 i = false ->
  ren_cidx rho (unshift_cidx 0 i) = unshift_cidx 0 (ren_cidx (ren_shift rho) i).
Proof.
  intros D rho i Huse. unfold unshift_cidx. cbn.
  assert (Huv : forall y, (match y with 0 => 0 | S i' => i' end) = unshift_var 0 y)
    by (intros [| y]; unfold unshift_var; cbn; [reflexivity | lia]).
  rewrite (ren_cidx_ext D _ (unshift_var 0) i Huv).
  rewrite (ren_cidx_ext D _ (unshift_var 0) (ren_cidx (ren_shift rho) i) Huv).
  apply (ren_unshift_cidx_gen D i 0 rho (ren_shift rho)); [| exact Huse].
  intros [| x'] Hne; [contradiction | unfold unshift_var; cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]].
Qed.

Lemma ren_unshift_cty_gen : forall (D : JoinDomain) (T : cty D) k (r1 r2 : nat -> nat),
  (forall x, x <> k -> r2 x <> k /\ r1 (unshift_var k x) = unshift_var k (r2 x)) ->
  cty_uses_var k T = false ->
  ren_cty r1 (ren_cty (unshift_var k) T) = ren_cty (unshift_var k) (ren_cty r2 T).
Proof.
  intros D T. induction T using cty_ind_nested; intros k r1 r2 Hext Huse; cbn in *; try reflexivity.
  - apply orb_false_iff in Huse as [HT Hl].
    f_equal; [apply IHT; assumption | apply ren_unshift_cidx_gen; assumption].
  - f_equal; apply (proj2 (Hext x (proj1 (Nat.eqb_neq _ _) Huse))).
  - f_equal; apply IHT; assumption.
  - f_equal; apply (proj2 (Hext b (proj1 (Nat.eqb_neq _ _) Huse))).
  - apply orb_false_iff in Huse as [H1 H2].
    assert (Hs : forall x, x <> S k ->
                   ren_shift r2 x <> S k /\ ren_shift r1 (unshift_var (S k) x) = unshift_var (S k) (ren_shift r2 x)).
    { intros [| x'] Hne; [unfold unshift_var; cbn; split; [lia | reflexivity] |].
      destruct (Hext x' ltac:(lia)) as [Hr2 Hrw].
      split; [cbn; lia | cbn; rewrite (unshift_var_S k x' ltac:(lia)), (unshift_var_S k (r2 x') Hr2); cbn; f_equal; exact Hrw]. }
    assert (Hsk : forall x, x <> S k -> ren_shift (unshift_var k) x = unshift_var (S k) x).
    { intros [| x'] Hne; [unfold unshift_var; reflexivity | cbn; symmetry; apply unshift_var_S; lia]. }
    f_equal; [apply IHT1; assumption |].
    rewrite (ren_cty_ext_except D T2 (S k) _ _ H2 Hsk).
    rewrite (ren_cty_ext_except D (ren_cty (ren_shift r2) T2) (S k) _ _
               (cty_uses_var_ren_ne D T2 (S k) (ren_shift r2) H2 (fun x Hx => proj1 (Hs x Hx))) Hsk).
    apply IHT2; assumption.
  - apply orb_false_iff in Huse as [H1 H2].
    assert (Hs : forall x, x <> S k ->
                   ren_shift r2 x <> S k /\ ren_shift r1 (unshift_var (S k) x) = unshift_var (S k) (ren_shift r2 x)).
    { intros [| x'] Hne; [unfold unshift_var; cbn; split; [lia | reflexivity] |].
      destruct (Hext x' ltac:(lia)) as [Hr2 Hrw].
      split; [cbn; lia | cbn; rewrite (unshift_var_S k x' ltac:(lia)), (unshift_var_S k (r2 x') Hr2); cbn; f_equal; exact Hrw]. }
    assert (Hsk : forall x, x <> S k -> ren_shift (unshift_var k) x = unshift_var (S k) x).
    { intros [| x'] Hne; [unfold unshift_var; reflexivity | cbn; symmetry; apply unshift_var_S; lia]. }
    f_equal; [apply IHT1; assumption |].
    rewrite (ren_cty_ext_except D T2 (S k) _ _ H2 Hsk).
    rewrite (ren_cty_ext_except D (ren_cty (ren_shift r2) T2) (S k) _ _
               (cty_uses_var_ren_ne D T2 (S k) (ren_shift r2) H2 (fun x Hx => proj1 (Hs x Hx))) Hsk).
    apply IHT2; assumption.
  - f_equal; apply IHT; assumption.
  - apply orb_false_iff in Huse as [H1 H2]. f_equal; [apply IHT1 | apply IHT2]; assumption.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huse as [Hft Hrest].
    rewrite (H2 k r1 r2 Hext Hft), (IHf H3 Hrest). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huse as [Hi Hrest].
    rewrite (ren_unshift_cidx_gen D idx k r1 r2 Hext Hi), (IH Hrest). reflexivity.
Qed.

Lemma ren_unshift_cty : forall (D : JoinDomain) rho (T : cty D),
  cty_uses_var 0 T = false ->
  ren_cty rho (unshift_cty 0 T) = unshift_cty 0 (ren_cty (ren_shift rho) T).
Proof.
  intros D rho T Huse. unfold unshift_cty. cbn.
  assert (Huv : forall y, (match y with 0 => 0 | S i' => i' end) = unshift_var 0 y)
    by (intros [| y]; unfold unshift_var; cbn; [reflexivity | lia]).
  rewrite (ren_cty_ext D _ (unshift_var 0) T Huv).
  rewrite (ren_cty_ext D _ (unshift_var 0) (ren_cty (ren_shift rho) T) Huv).
  apply (ren_unshift_cty_gen D T 0 rho (ren_shift rho)); [| exact Huse].
  intros [| x'] Hne; [contradiction | unfold unshift_var; cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]].
Qed.

Lemma ren_lift0_cidx : forall (D : JoinDomain) rho (i : cidx D),
  ren_cidx (ren_shift rho) (lift_cidx 0 1 i) = lift_cidx 0 1 (ren_cidx rho i).
Proof.
  intros D rho i. unfold lift_cidx. rewrite !ren_cidx_comp.
  apply ren_cidx_ext. intro y; unfold ren_lift; rewrite !(proj2 (Nat.ltb_ge _ 0) ltac:(lia)).
  replace (y + 1) with (S y) by lia; cbn; lia.
Qed.

Lemma ren_lift0_cty : forall (D : JoinDomain) rho (T : cty D),
  ren_cty (ren_shift rho) (lift_cty 0 1 T) = lift_cty 0 1 (ren_cty rho T).
Proof.
  intros D rho T. unfold lift_cty. rewrite !ren_cty_comp.
  apply ren_cty_ext. intro y; unfold ren_lift; rewrite !(proj2 (Nat.ltb_ge _ 0) ltac:(lia)).
  replace (y + 1) with (S y) by lia; cbn; lia.
Qed.

Fixpoint cidx_uses_kinds {D : JoinDomain} (idx unbox fst snd scase : bool) (k : nat) (i : cidx D) : bool :=
  match i with
  | CIdxVar x => if idx then false else x =? k
  | CIdxLit _ => false
  | CIdxAdd l r => cidx_uses_kinds idx unbox fst snd scase k l || cidx_uses_kinds idx unbox fst snd scase k r
  | CIdxProm _ i' => cidx_uses_kinds idx unbox fst snd scase k i'
  | CIdxUnbox b => if unbox then false else b =? k
  | CIdxFst p => if fst then false else p =? k
  | CIdxSnd p => if snd then false else p =? k
  | CIdxCase s l r =>
      (if scase then false else s =? k)
      || cidx_uses_kinds idx unbox fst snd scase (S k) l
      || cidx_uses_kinds idx unbox fst snd scase (S k) r
  end.

Fixpoint cty_uses_kinds {D : JoinDomain} (idx tvar tunbox unbox fst snd scase : bool) (k : nat) (T : cty D) : bool :=
  match T with
  | CNat | CBool | CUniv _ => false
  | CVec elem len => cty_uses_kinds idx tvar tunbox unbox fst snd scase k elem || cidx_uses_kinds idx unbox fst snd scase k len
  | CTVar x => if tvar then false else x =? k
  | CTProm _ inner | CBox _ inner => cty_uses_kinds idx tvar tunbox unbox fst snd scase k inner
  | CTUnbox b => if tunbox then false else b =? k
  | CPi _ _ _ dom cod | CSigma _ _ dom cod =>
      cty_uses_kinds idx tvar tunbox unbox fst snd scase k dom
      || cty_uses_kinds idx tvar tunbox unbox fst snd scase (S k) cod
  | CSum l r => cty_uses_kinds idx tvar tunbox unbox fst snd scase k l || cty_uses_kinds idx tvar tunbox unbox fst snd scase k r
  | CRecord _ fields =>
      (fix go_fs (fs : list (nat * grade D * cty D)) : bool :=
         match fs with
         | [] => false
         | (_, _, ft) :: rest => cty_uses_kinds idx tvar tunbox unbox fst snd scase k ft || go_fs rest
         end) fields
  | CInd _ indices =>
      (fix go_is (ls : list (cidx D)) : bool :=
         match ls with
         | [] => false
         | hd :: rest => cidx_uses_kinds idx unbox fst snd scase k hd || go_is rest
         end) indices
  end.

Definition flags_allow {D : JoinDomain} (T : cty D) (idx tvar tunbox unbox fst snd scase : bool) : Prop :=
  match erase_hints T with
  | CNat => idx = true
  | CUniv _ => tvar = true
  | CBox _ CNat => unbox = true
  | CBox _ (CUniv _) => tunbox = true
  | CSigma _ _ CNat CNat => fst = true /\ snd = true
  | CSigma _ _ CNat _ => fst = true
  | CSigma _ _ _ CNat => snd = true
  | CSum _ _ => scase = true
  | _ => True
  end.

Lemma flags_allow_ren_plus : forall (D : JoinDomain) (T : cty D) m n idx tvar tunbox unbox fst snd scase,
  flags_allow (ren_cty (plus m) T) idx tvar tunbox unbox fst snd scase ->
  flags_allow (ren_cty (plus n) T) idx tvar tunbox unbox fst snd scase.
Proof.
  intros D T m n idx tvar tunbox unbox fst snd scase H.
  unfold flags_allow in *. rewrite erase_hints_ren in *.
  destruct (erase_hints T); cbn in *; try exact H;
    match goal with
    | x : cty D, y : cty D |- _ => destruct x, y; cbn in *; exact H
    | x : cty D |- _ => destruct x; cbn in *; exact H
    end.
Qed.

Lemma flags_allow_CNat : forall (D : JoinDomain) (T : cty D) idx tvar tunbox unbox fst snd scase,
  cty_alpha_eq T CNat -> idx = true -> flags_allow T idx tvar tunbox unbox fst snd scase.
Proof. intros D T idx tvar tunbox unbox fst snd scase Ha Hi. unfold flags_allow, cty_alpha_eq in *; rewrite Ha; exact Hi. Qed.

Lemma flags_allow_CUniv : forall (D : JoinDomain) (T : cty D) lvl idx tvar tunbox unbox fst snd scase,
  cty_alpha_eq T (CUniv lvl) -> tvar = true -> flags_allow T idx tvar tunbox unbox fst snd scase.
Proof. intros D T lvl idx tvar tunbox unbox fst snd scase Ha Ht. unfold flags_allow, cty_alpha_eq in *; rewrite Ha; exact Ht. Qed.

Lemma flags_allow_CBox_Nat : forall (D : JoinDomain) (T : cty D) q idx tvar tunbox unbox fst snd scase,
  cty_alpha_eq T (CBox q CNat) -> unbox = true -> flags_allow T idx tvar tunbox unbox fst snd scase.
Proof. intros D T q idx tvar tunbox unbox fst snd scase Ha Hu. unfold flags_allow, cty_alpha_eq in *; rewrite Ha; exact Hu. Qed.

Lemma flags_allow_CBox_Univ : forall (D : JoinDomain) (T : cty D) q lvl idx tvar tunbox unbox fst snd scase,
  cty_alpha_eq T (CBox q (CUniv lvl)) -> tunbox = true -> flags_allow T idx tvar tunbox unbox fst snd scase.
Proof. intros D T q lvl idx tvar tunbox unbox fst snd scase Ha Hu. unfold flags_allow, cty_alpha_eq in *; rewrite Ha; exact Hu. Qed.

Lemma flags_allow_CSigma : forall (D : JoinDomain) (T : cty D) z r A B idx tvar tunbox unbox fst snd scase,
  cty_alpha_eq T (CSigma z r A B) -> fst = true -> snd = true -> flags_allow T idx tvar tunbox unbox fst snd scase.
Proof.
  intros D T z r A B idx tvar tunbox unbox fst snd scase Ha Hf Hs.
  unfold flags_allow, cty_alpha_eq in *; rewrite Ha. cbn.
  destruct (erase_hints A), (erase_hints B); try exact Hf; try exact Hs; auto.
Qed.

Lemma flags_allow_CSum : forall (D : JoinDomain) (T : cty D) A B idx tvar tunbox unbox fst snd scase,
  cty_alpha_eq T (CSum A B) -> scase = true -> flags_allow T idx tvar tunbox unbox fst snd scase.
Proof. intros D T A B idx tvar tunbox unbox fst snd scase Ha Hs. unfold flags_allow, cty_alpha_eq in *; rewrite Ha; exact Hs. Qed.

Lemma cidx_demand_uses_kinds : forall (D : JoinDomain) (env : cenv D) i d,
  CIdxDemand env i d ->
  forall k e idx tvar tunbox unbox fst snd scase,
    clookup env k = Some e ->
    flags_allow (ren_cty (plus (S k)) (cannotation e)) idx tvar tunbox unbox fst snd scase ->
    cidx_uses_kinds idx unbox fst snd scase k i = false.
Proof.
  intros D env i d H. induction H; intros k e0 idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf; cbn;
    try reflexivity;
    try (rewrite (IHCIdxDemand1 k e0 idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf),
                 (IHCIdxDemand2 k e0 idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf); reflexivity);
    try (apply IHCIdxDemand with (e := e0) (tvar := tvar0) (tunbox := tunbox0); assumption).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [| destruct idx0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
    rewrite H in Hl; inversion Hl; subst.
    unfold flags_allow in Hf. rewrite erase_hints_ren in Hf.
    unfold cty_alpha_eq in H0; cbn in H0; rewrite H0 in Hf; cbn in Hf. rewrite Hf; reflexivity.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [| destruct unbox0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
    rewrite H in Hl; inversion Hl; subst.
    unfold flags_allow in Hf. rewrite erase_hints_ren in Hf.
    unfold cty_alpha_eq in H0; cbn in H0; rewrite H0 in Hf; cbn in Hf. rewrite Hf; reflexivity.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [| destruct fst0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
    rewrite H in Hl; inversion Hl; subst.
    unfold flags_allow in Hf. rewrite erase_hints_ren in Hf.
    unfold cty_alpha_eq in H0; cbn in H0; rewrite H0 in Hf; cbn in Hf.
    destruct (ren_cty _ (erase_hints snd_ty)); try (rewrite Hf; reflexivity); destruct Hf as [Hf1 _]; rewrite Hf1; reflexivity.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [| destruct snd0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
    rewrite H in Hl; inversion Hl; subst.
    unfold flags_allow in Hf. rewrite erase_hints_ren in Hf.
    unfold cty_alpha_eq in H0; cbn in H0; rewrite H0 in Hf; cbn in Hf.
    destruct (ren_cty _ (erase_hints fst_ty)); try (rewrite Hf; reflexivity); destruct Hf as [_ Hf2]; rewrite Hf2; reflexivity.
  - assert (Hs_ok : (if scase0 then false else s =? k) = false).
    { destruct (Nat.eq_dec s k) as [-> | Hne]; [| destruct scase0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
      rewrite H in Hl; inversion Hl; subst.
      unfold flags_allow in Hf. unfold cty_alpha_eq in H0; rewrite H0 in Hf; cbn in Hf. rewrite Hf; reflexivity. }
    rewrite Hs_ok. cbn.
    pose proof (flags_allow_ren_plus D (cannotation e0) (S k) (S (S k)) idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hf) as Hf'.
    rewrite (IHCIdxDemand1 (S k) e0 idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf').
    rewrite (IHCIdxDemand2 (S k) e0 idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf').
    reflexivity.
Qed.

Lemma ctype_demand_uses_kinds : forall (D : JoinDomain) (env : cenv D) T d,
  CTypeDemand env T d ->
  forall k e idx tvar tunbox unbox fst snd scase,
    clookup env k = Some e ->
    flags_allow (ren_cty (plus (S k)) (cannotation e)) idx tvar tunbox unbox fst snd scase ->
    cty_uses_kinds idx tvar tunbox unbox fst snd scase k T = false.
Proof.
  intros D env T d H.
  induction H using CTypeDemand_ind_mut with
    (P := fun env T d _ => forall k e idx tvar tunbox unbox fst snd scase,
            clookup env k = Some e ->
            flags_allow (ren_cty (plus (S k)) (cannotation e)) idx tvar tunbox unbox fst snd scase ->
            cty_uses_kinds idx tvar tunbox unbox fst snd scase k T = false)
    (P0 := fun env fs df _ => forall k e idx tvar tunbox unbox fst snd scase,
            clookup env k = Some e ->
            flags_allow (ren_cty (plus (S k)) (cannotation e)) idx tvar tunbox unbox fst snd scase ->
            (fix go_fs (fs0 : list (nat * grade D * cty D)) : bool :=
               match fs0 with [] => false | (_, _, ft) :: rest => cty_uses_kinds idx tvar tunbox unbox fst snd scase k ft || go_fs rest end) fs = false)
    (P1 := fun env ls dl _ => forall k e idx tvar tunbox unbox fst snd scase,
            clookup env k = Some e ->
            flags_allow (ren_cty (plus (S k)) (cannotation e)) idx tvar tunbox unbox fst snd scase ->
            (fix go_is (ls0 : list (cidx D)) : bool :=
               match ls0 with [] => false | hd :: rest => cidx_uses_kinds idx unbox fst snd scase k hd || go_is rest end) ls = false);
    intros k env_e idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf; cbn; try reflexivity.
  - rewrite (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf).
    match goal with
    | Hc : CIdxDemand _ _ _ |- _ =>
        rewrite (cidx_demand_uses_kinds D _ _ _ Hc k env_e idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf)
    end. reflexivity.
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [| destruct tvar0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
    match goal with
    | Hlk : clookup _ k = Some _, Ha : cty_alpha_eq (cannotation _) (CUniv _) |- _ =>
        rewrite Hlk in Hl; inversion Hl; subst;
        unfold flags_allow in Hf; rewrite erase_hints_ren in Hf;
        unfold cty_alpha_eq in Ha; cbn in Ha; rewrite Ha in Hf; cbn in Hf; rewrite Hf; reflexivity
    end.
  - apply (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf).
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [| destruct tunbox0; [reflexivity | apply Nat.eqb_neq; exact Hne]].
    match goal with
    | Hlk : clookup _ k = Some _, Ha : cty_alpha_eq (cannotation _) (CBox _ (CUniv _)) |- _ =>
        rewrite Hlk in Hl; inversion Hl; subst;
        unfold flags_allow in Hf; rewrite erase_hints_ren in Hf;
        unfold cty_alpha_eq in Ha; cbn in Ha; rewrite Ha in Hf; cbn in Hf; rewrite Hf; reflexivity
    end.
  - rewrite (IHCTypeDemand1 _ _ _ _ _ _ _ _ _ Hl Hf).
    pose proof (flags_allow_ren_plus D (cannotation env_e) (S k) (S (S k)) idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hf) as Hf'.
    rewrite (IHCTypeDemand2 (S k) env_e _ _ _ _ _ _ _ Hl Hf'). reflexivity.
  - rewrite (IHCTypeDemand1 _ _ _ _ _ _ _ _ _ Hl Hf).
    pose proof (flags_allow_ren_plus D (cannotation env_e) (S k) (S (S k)) idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hf) as Hf'.
    rewrite (IHCTypeDemand2 (S k) env_e _ _ _ _ _ _ _ Hl Hf'). reflexivity.
  - apply (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf).
  - rewrite (IHCTypeDemand1 _ _ _ _ _ _ _ _ _ Hl Hf), (IHCTypeDemand2 _ _ _ _ _ _ _ _ _ Hl Hf). reflexivity.
  - apply (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf).
  - apply (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf).
  - rewrite (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf), (IHCTypeDemand0 _ _ _ _ _ _ _ _ _ Hl Hf). reflexivity.
  - match goal with
    | Hc : CIdxDemand _ _ _ |- _ =>
        rewrite (cidx_demand_uses_kinds D _ _ _ Hc k env_e idx0 tvar0 tunbox0 unbox0 fst0 snd0 scase0 Hl Hf)
    end.
    rewrite (IHCTypeDemand _ _ _ _ _ _ _ _ _ Hl Hf). reflexivity.
Qed.

Ltac nat_bool_hyps :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
  | H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Nat.eqb_neq in H
  end.

Ltac rw_nat_bool :=
  repeat match goal with
  | |- context [?a <? ?b] =>
      first [ rewrite (proj2 (Nat.ltb_lt a b) ltac:(nat_bool_hyps; lia))
            | rewrite (proj2 (Nat.ltb_ge a b) ltac:(nat_bool_hyps; lia)) ]
  | |- context [?a =? ?b] =>
      first [ rewrite (proj2 (Nat.eqb_eq a b) ltac:(nat_bool_hyps; lia))
            | rewrite (proj2 (Nat.eqb_neq a b) ltac:(nat_bool_hyps; lia)) ]
  end.

Ltac solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Huse :=
  destruct (Nat.eq_dec b k) as [-> | Hne];
  [ exfalso; rewrite Nat.eqb_refl in Huse; discriminate
  | destruct (le_lt_dec k b);
    [ destruct (Hgt b ltac:(lia)) as [Hr2 Hr1]; rw_nat_bool; exact Hr1
    | destruct (Hlt b ltac:(lia)) as [Hr1 Hr2]; rw_nat_bool; exact Hr1 ]].

Lemma ren_subst_cidx_gen : forall (D : JoinDomain) (i val : cidx D) k r1 r2,
  cidx_uses_kinds true false false false false k i = false ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cidx r1 (subst_cidx k val i) = subst_cidx k (ren_cidx r1 val) (ren_cidx r2 i).
Proof.
  intros D i. induction i; intros val k r1 r2 Huse Hlt Heqk Hgt; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huse as [Hu1 Hu2];
         rewrite (IHi1 _ _ _ _ Hu1 Hlt Heqk Hgt), (IHi2 _ _ _ _ Hu2 Hlt Heqk Hgt); reflexivity).
  - destruct (Nat.eq_dec x k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. reflexivity.
    + destruct (le_lt_dec k x).
      * destruct (Hgt x ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
      * destruct (Hlt x ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - rewrite (IHi _ _ _ _ Huse Hlt Heqk Hgt). reflexivity.
  - f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Huse.
  - f_equal; solve_disallowed_idx p k r1 r2 Hlt Heqk Hgt Huse.
  - f_equal; solve_disallowed_idx p k r1 r2 Hlt Heqk Hgt Huse.
  - apply orb_false_iff in Huse as [H12 Hu3]. apply orb_false_iff in H12 as [Hu1 Hu2].
    f_equal.
    + solve_disallowed_idx s k r1 r2 Hlt Heqk Hgt Hu1.
    + rewrite (IHi1 (lift_cidx 0 1 val) (S k) (ren_shift r1) (ren_shift r2));
        [rewrite ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |].
      * intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      * intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
          replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
    + rewrite (IHi2 (lift_cidx 0 1 val) (S k) (ren_shift r1) (ren_shift r2));
        [rewrite ren_lift0_cidx; reflexivity | exact Hu3 | | cbn; congruence |].
      * intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      * intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
          replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
Qed.

Lemma ren_subst_cidx_0 : forall (D : JoinDomain) (i val : cidx D) rho,
  cidx_uses_kinds true false false false false 0 i = false ->
  ren_cidx rho (subst_cidx 0 val i) = subst_cidx 0 (ren_cidx rho val) (ren_cidx (ren_shift rho) i).
Proof.
  intros D i val rho Hu. apply ren_subst_cidx_gen; [exact Hu | intros; lia | reflexivity |].
  intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]].
Qed.

Lemma ren_subst_cidx_in_cty_gen : forall (D : JoinDomain) (T : cty D) val k r1 r2,
  cty_uses_kinds true false false false false false false k T = false ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cty r1 (subst_cidx_in_cty k val T) = subst_cidx_in_cty k (ren_cidx r1 val) (ren_cty r2 T).
Proof.
  intros D T. induction T using cty_ind_nested; intros val k r1 r2 Huse Hlt Heqk Hgt; cbn in *; try reflexivity.
  - apply orb_false_iff in Huse as [Hu1 Hu2].
    rewrite (IHT _ _ _ _ Hu1 Hlt Heqk Hgt), (ren_subst_cidx_gen D len val k r1 r2 Hu2 Hlt Heqk Hgt). reflexivity.
  - f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Huse.
  - f_equal; apply IHT; assumption.
  - f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Huse.
  - apply orb_false_iff in Huse as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    rewrite (IHT2 (lift_cidx 0 1 val) (S k) (ren_shift r1) (ren_shift r2));
      [rewrite ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |].
    + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
    + intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
        replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
  - apply orb_false_iff in Huse as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    rewrite (IHT2 (lift_cidx 0 1 val) (S k) (ren_shift r1) (ren_shift r2));
      [rewrite ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |].
    + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
    + intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
        replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
  - f_equal; apply IHT; assumption.
  - apply orb_false_iff in Huse as [Hu1 Hu2]. f_equal; [apply IHT1 | apply IHT2]; assumption.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huse as [Hu1 Hu2].
    rewrite (H2 _ _ _ _ Hu1 Hlt Heqk Hgt), (IHf H3 Hu2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huse as [Hu1 Hu2].
    rewrite (ren_subst_cidx_gen D idx val k r1 r2 Hu1 Hlt Heqk Hgt), (IH Hu2). reflexivity.
Qed.

Lemma ren_subst_cidx_in_cty_0 : forall (D : JoinDomain) (T : cty D) val rho,
  cty_uses_kinds true false false false false false false 0 T = false ->
  ren_cty rho (subst_cidx_in_cty 0 val T) =
  subst_cidx_in_cty 0 (ren_cidx rho val) (ren_cty (ren_shift rho) T).
Proof.
  intros D T val rho Hu. apply ren_subst_cidx_in_cty_gen; [exact Hu | intros; lia | reflexivity |].
  intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]].
Qed.

Lemma ren_subst_tvar_in_cidx_gen : forall (D : JoinDomain) (i : cidx D) k r1 r2,
  cidx_uses_kinds false false false false false k i = false ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cidx r1 (subst_tvar_in_cidx k i) = subst_tvar_in_cidx k (ren_cidx r2 i).
Proof.
  intros D i. induction i; intros k r1 r2 Huse Hlt Heqk Hgt; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huse as [Hu1 Hu2];
         rewrite (IHi1 _ _ _ Hu1 Hlt Heqk Hgt), (IHi2 _ _ _ Hu2 Hlt Heqk Hgt); reflexivity).
  - f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Huse.
  - f_equal; apply IHi; assumption.
  - f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Huse.
  - f_equal; solve_disallowed_idx p k r1 r2 Hlt Heqk Hgt Huse.
  - f_equal; solve_disallowed_idx p k r1 r2 Hlt Heqk Hgt Huse.
  - apply orb_false_iff in Huse as [H12 Hu3]. apply orb_false_iff in H12 as [Hu1 Hu2].
    f_equal.
    + solve_disallowed_idx s k r1 r2 Hlt Heqk Hgt Hu1.
    + apply IHi1; [exact Hu2 | | cbn; congruence |].
      * intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      * intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
          replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
    + apply IHi2; [exact Hu3 | | cbn; congruence |].
      * intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      * intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
          replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
Qed.

Lemma ren_subst_tvar_in_cty_gen : forall (D : JoinDomain) (T U : cty D) k r1 r2,
  cty_uses_kinds false true false false false false false k T = false ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cty r1 (subst_tvar_in_cty k U T) = subst_tvar_in_cty k (ren_cty r1 U) (ren_cty r2 T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U k r1 r2 Huse Hlt Heqk Hgt; cbn in *; try reflexivity.
  - apply orb_false_iff in Huse as [Hu1 Hu2].
    rewrite (IHT _ _ _ _ Hu1 Hlt Heqk Hgt), (ren_subst_tvar_in_cidx_gen D len k r1 r2 Hu2 Hlt Heqk Hgt). reflexivity.
  - destruct (Nat.eq_dec x k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. reflexivity.
    + destruct (le_lt_dec k x).
      * destruct (Hgt x ltac:(lia)) as [Hr2 Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
      * destruct (Hlt x ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - f_equal; apply IHT; assumption.
  - f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Huse.
  - apply orb_false_iff in Huse as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    rewrite (IHT2 (lift_cty 0 1 U) (S k) (ren_shift r1) (ren_shift r2));
      [rewrite ren_lift0_cty; reflexivity | exact Hu2 | | cbn; congruence |].
    + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
    + intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
        replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
  - apply orb_false_iff in Huse as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    rewrite (IHT2 (lift_cty 0 1 U) (S k) (ren_shift r1) (ren_shift r2));
      [rewrite ren_lift0_cty; reflexivity | exact Hu2 | | cbn; congruence |].
    + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
    + intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
        replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1].
  - f_equal; apply IHT; assumption.
  - apply orb_false_iff in Huse as [Hu1 Hu2]. f_equal; [apply IHT1 | apply IHT2]; assumption.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huse as [Hu1 Hu2].
    rewrite (H2 _ _ _ _ Hu1 Hlt Heqk Hgt), (IHf H3 Hu2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huse as [Hu1 Hu2].
    rewrite (ren_subst_tvar_in_cidx_gen D idx k r1 r2 Hu1 Hlt Heqk Hgt), (IH Hu2). reflexivity.
Qed.

Lemma ren_subst_tvar_in_cty_0 : forall (D : JoinDomain) (T U : cty D) rho,
  cty_uses_kinds false true false false false false false 0 T = false ->
  ren_cty rho (subst_tvar_in_cty 0 U T) =
  subst_tvar_in_cty 0 (ren_cty rho U) (ren_cty (ren_shift rho) T).
Proof.
  intros D T U rho Hu. apply ren_subst_tvar_in_cty_gen; [exact Hu | intros; lia | reflexivity |].
  intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]].
Qed.

Lemma ren_app_result_ty : forall (D : JoinDomain) rho (dom cod res : cty D) (arg : cterm D),
  (dom = CNat -> cty_uses_kinds true false false false false false false 0 cod = false) ->
  (forall lvl, dom = CUniv lvl -> cty_uses_kinds false true false false false false false 0 cod = false) ->
  app_result_ty dom cod arg = Some res ->
  app_result_ty (ren_cty rho dom) (ren_cty (ren_shift rho) cod) (ren_cterm rho arg) =
  Some (ren_cty rho res).
Proof.
  intros D rho dom cod res arg Hnat Huniv H.
  unfold app_result_ty in *.
  destruct dom; destruct arg; cbn in *;
    try (rewrite ren_cty_uses_var_shift;
         destruct (cty_uses_var 0 cod) eqn:Huse; inversion H; subst;
         f_equal; first [apply ren_unshift_cty; exact Huse | symmetry; apply ren_unshift_cty; exact Huse]).
  - (* CNat, CVar *)
    inversion H; subst; f_equal; symmetry; apply ren_subst_cidx_in_cty_0; apply Hnat; reflexivity.
  - (* CNat, CNatVal *)
    inversion H; subst; f_equal; symmetry; apply ren_subst_cidx_in_cty_0; apply Hnat; reflexivity.
  - (* CUniv, CVar *)
    inversion H; subst; f_equal; symmetry; apply ren_subst_tvar_in_cty_0; eapply Huniv; reflexivity.
  - (* CUniv, CTypeVal *)
    inversion H; subst; f_equal; symmetry; apply ren_subst_tvar_in_cty_0; eapply Huniv; reflexivity.
Qed.

(* Renaming spec specialization lemmas for Box/Pair/Sum/Fix *)

Lemma ren_spec_box_body : forall (D : JoinDomain) (q : grade D) (mot : cty D) rho,
  ren_cty (ren_shift rho) (spec_box_body_cty q 0 mot) =
  spec_box_body_cty q 0 (ren_cty (ren_shift rho) mot).
Proof.
  intros D q mot rho.
  assert (Hcidx : forall i k r,
    (forall x, x < k -> r x = x /\ r x < k) ->
    r k = k ->
    (forall x, x > k -> r x > k) ->
    ren_cidx r (spec_box_body_cidx q k i) = spec_box_body_cidx q k (ren_cidx r i)).
  { induction i; intros k r Hlt Heqk Hgt; cbn; try reflexivity;
      try (f_equal; [apply IHi1 | apply IHi2]; assumption).
    - f_equal; apply IHi; assumption.
    - destruct (Nat.eq_dec b k) as [-> | Hne].
      + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl; cbn; rewrite Heqk; reflexivity.
      + assert (H1 : (b =? k) = false) by (apply Nat.eqb_neq; exact Hne).
        assert (H2 : (r b =? k) = false).
        { apply Nat.eqb_neq. destruct (le_lt_dec k b); [pose proof (Hgt b ltac:(lia)); lia | destruct (Hlt b l); lia]. }
        rewrite H1, H2; reflexivity.
    - f_equal; [apply IHi1 | apply IHi2]; auto.
      + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      + cbn; congruence.
      + intros [| x'] Hx'; [lia | pose proof (Hgt x' ltac:(lia)); cbn; lia].
      + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      + cbn; congruence.
      + intros [| x'] Hx'; [lia | pose proof (Hgt x' ltac:(lia)); cbn; lia]. }
  assert (Hcty : forall T k rn,
    (forall x, x < k -> rn x = x /\ rn x < k) ->
    rn k = k ->
    (forall x, x > k -> rn x > k) ->
    ren_cty rn (spec_box_body_cty q k T) = spec_box_body_cty q k (ren_cty rn T)).
  { induction T using cty_ind_nested; intros k rn Hlt Heqk Hgt; cbn; try reflexivity.
    - rewrite (IHT _ _ Hlt Heqk Hgt), (Hcidx _ _ _ Hlt Heqk Hgt). reflexivity.
    - f_equal; apply IHT; assumption.
    - destruct (Nat.eq_dec b k) as [-> | Hne].
      + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl; cbn; rewrite Heqk; reflexivity.
      + assert (H1 : (b =? k) = false) by (apply Nat.eqb_neq; exact Hne).
        assert (H2 : (rn b =? k) = false).
        { apply Nat.eqb_neq. destruct (le_lt_dec k b); [pose proof (Hgt b ltac:(lia)); lia | destruct (Hlt b l); lia]. }
        rewrite H1, H2; reflexivity.
    - f_equal; [apply IHT1; assumption |].
      apply IHT2; [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia] | cbn; congruence |
                   intros [| x'] Hx'; [lia | pose proof (Hgt x' ltac:(lia)); cbn; lia]].
    - f_equal; [apply IHT1; assumption |].
      apply IHT2; [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia] | cbn; congruence |
                   intros [| x'] Hx'; [lia | pose proof (Hgt x' ltac:(lia)); cbn; lia]].
    - f_equal; apply IHT; assumption.
    - f_equal; [apply IHT1 | apply IHT2]; assumption.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
      inversion H; subst; cbn in H2. rewrite (H2 _ _ Hlt Heqk Hgt), (IHf H3). reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
      rewrite (Hcidx _ _ _ Hlt Heqk Hgt), IH. reflexivity. }
  apply Hcty; [intros; lia | reflexivity | intros [| x'] Hx'; [lia | cbn; lia]].
Qed.

Lemma ren_subst_var_in_cty : forall (D : JoinDomain) (mot : cty D) y rho,
  ren_cty rho (subst_var_in_cty 0 y mot) =
  subst_var_in_cty 0 (rho y) (ren_cty (ren_shift rho) mot).
Proof.
  intros D mot y rho. unfold subst_var_in_cty. rewrite !ren_cty_comp.
  apply ren_cty_ext. intros [| x']; reflexivity.
Qed.

Lemma ren_spec_box_subj : forall (D : JoinDomain) (box_term : cterm D) (mot : cty D) rho,
  (match box_term with
   | CPromote _ (CNatVal _) => cty_uses_kinds false false false true false false false 0 mot = false
   | CPromote _ (CTypeVal _) => cty_uses_kinds false false true false false false false 0 mot = false
   | CPromote _ (CVar _) | CVar _ => True
   | _ => cty_uses_var 0 mot = false
   end) ->
  ren_cty rho (spec_box_subj_cty box_term mot) =
  spec_box_subj_cty (ren_cterm rho box_term) (ren_cty (ren_shift rho) mot).
Proof.
  intros D box_term mot rho Huse.
  destruct box_term; cbn in *; try (apply ren_unshift_cty; exact Huse).
  - apply ren_subst_var_in_cty.
  - destruct box_term; cbn in *; try (apply ren_unshift_cty; exact Huse).
    + rewrite ren_subst_var_in_cty, ren_spec_box_body. reflexivity.
    + (* CPromote q (CNatVal i) *)
      assert (Hcidx : forall j k r1 r2 (qg : grade D) (i0 : cidx D),
        cidx_uses_kinds false true false false false k j = false ->
        (forall x, x < k -> r1 x = r2 x /\ r2 x < k) -> r2 k = k ->
        (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
        ren_cidx r1 (subst_box_nat_cidx k qg i0 j) = subst_box_nat_cidx k qg (ren_cidx r1 i0) (ren_cidx r2 j)).
      { induction j; intros k r1 r2 qg i0 Hu Hlt Heqk Hgt; cbn in *; try reflexivity;
          try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHj1 k r1 r2 qg i0 Hu1 Hlt Heqk Hgt), (IHj2 k r1 r2 qg i0 Hu2 Hlt Heqk Hgt); reflexivity).
        - f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Hu.
        - f_equal; apply IHj; assumption.
        - destruct (Nat.eq_dec b k) as [-> | Hne].
          + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. cbn. reflexivity.
          + destruct (le_lt_dec k b).
            * destruct (Hgt b ltac:(lia)) as [Hr2 Hr1]. rw_nat_bool. cbn; f_equal; exact Hr1.
            * destruct (Hlt b ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. cbn; f_equal; exact Hr1.
        - f_equal; solve_disallowed_idx p k r1 r2 Hlt Heqk Hgt Hu.
        - f_equal; solve_disallowed_idx p k r1 r2 Hlt Heqk Hgt Hu.
        - apply orb_false_iff in Hu as [H12 Hu3]; apply orb_false_iff in H12 as [Hu1 Hu2].
          f_equal; [solve_disallowed_idx s k r1 r2 Hlt Heqk Hgt Hu1 | |].
          + rewrite (IHj1 (S k) (ren_shift r1) (ren_shift r2) qg (lift_cidx 0 1 i0)); [rewrite ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |];
              [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
              |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
                replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]].
          + rewrite (IHj2 (S k) (ren_shift r1) (ren_shift r2) qg (lift_cidx 0 1 i0)); [rewrite ren_lift0_cidx; reflexivity | exact Hu3 | | cbn; congruence |];
              [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
              |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
                replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]]. }
      assert (Hcty : forall T k r1 r2 (qg : grade D) (i0 : cidx D),
        cty_uses_kinds false false false true false false false k T = false ->
        (forall x, x < k -> r1 x = r2 x /\ r2 x < k) -> r2 k = k ->
        (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
        ren_cty r1 (subst_box_nat_cty k qg i0 T) = subst_box_nat_cty k qg (ren_cidx r1 i0) (ren_cty r2 T)).
      { induction T using cty_ind_nested; intros k r1 r2 qg i0 Hu Hlt Heqk Hgt; cbn in *; try reflexivity.
        - apply orb_false_iff in Hu as [Hu1 Hu2].
          rewrite (IHT _ _ _ _ _ Hu1 Hlt Heqk Hgt), (Hcidx _ _ _ _ _ _ Hu2 Hlt Heqk Hgt). reflexivity.
        - f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Hu.
        - f_equal; apply IHT; assumption.
        - f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Hu.
        - apply orb_false_iff in Hu as [Hu1 Hu2].
          f_equal; [apply IHT1; assumption |].
          rewrite (IHT2 (S k) (ren_shift r1) (ren_shift r2) qg (lift_cidx 0 1 i0)); [rewrite ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |];
            [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
            |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
              replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]].
        - apply orb_false_iff in Hu as [Hu1 Hu2].
          f_equal; [apply IHT1; assumption |].
          rewrite (IHT2 (S k) (ren_shift r1) (ren_shift r2) qg (lift_cidx 0 1 i0)); [rewrite ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |];
            [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
            |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
              replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]].
        - f_equal; apply IHT; assumption.
        - apply orb_false_iff in Hu as [Hu1 Hu2]. f_equal; [apply IHT1 | apply IHT2]; assumption.
        - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
          inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [Hu1 Hu2].
          rewrite (H2 _ _ _ _ _ Hu1 Hlt Heqk Hgt), (IHf H3 Hu2). reflexivity.
        - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
          apply orb_false_iff in Hu as [Hu1 Hu2].
          rewrite (Hcidx _ _ _ _ _ _ Hu1 Hlt Heqk Hgt), (IH Hu2). reflexivity. }
      apply Hcty; [exact Huse | intros; lia | reflexivity | intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]]].
    + (* CPromote q (CTypeVal T) *)
      assert (Hcty : forall T0 k r1 r2 (qg : grade D) (U0 : cty D),
        cty_uses_kinds false false true false false false false k T0 = false ->
        (forall x, x < k -> r1 x = r2 x /\ r2 x < k) -> r2 k = k ->
        (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
        ren_cty r1 (subst_box_ty_cty k qg U0 T0) = subst_box_ty_cty k qg (ren_cty r1 U0) (ren_cty r2 T0)).
      { induction T0 using cty_ind_nested; intros k r1 r2 qg U0 Hu Hlt Heqk Hgt; cbn in *; try reflexivity.
        - apply orb_false_iff in Hu as [Hu1 Hu2].
          rewrite (IHT0 _ _ _ _ _ Hu1 Hlt Heqk Hgt), (ren_subst_tvar_in_cidx_gen D len k r1 r2 Hu2 Hlt Heqk Hgt). reflexivity.
        - f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Hu.
        - f_equal; apply IHT0; assumption.
        - destruct (Nat.eq_dec b k) as [-> | Hne].
          + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. cbn. reflexivity.
          + destruct (le_lt_dec k b).
            * destruct (Hgt b ltac:(lia)) as [Hr2 Hr1]. rw_nat_bool. cbn; f_equal; exact Hr1.
            * destruct (Hlt b ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. cbn; f_equal; exact Hr1.
        - apply orb_false_iff in Hu as [Hu1 Hu2].
          f_equal; [apply IHT0_1; assumption |].
          rewrite (IHT0_2 (S k) (ren_shift r1) (ren_shift r2) qg (lift_cty 0 1 U0)); [rewrite ren_lift0_cty; reflexivity | exact Hu2 | | cbn; congruence |];
            [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
            |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
              replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]].
        - apply orb_false_iff in Hu as [Hu1 Hu2].
          f_equal; [apply IHT0_1; assumption |].
          rewrite (IHT0_2 (S k) (ren_shift r1) (ren_shift r2) qg (lift_cty 0 1 U0)); [rewrite ren_lift0_cty; reflexivity | exact Hu2 | | cbn; congruence |];
            [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
            |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
              replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]].
        - f_equal; apply IHT0; assumption.
        - apply orb_false_iff in Hu as [Hu1 Hu2]. f_equal; [apply IHT0_1 | apply IHT0_2]; assumption.
        - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
          inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [Hu1 Hu2].
          rewrite (H2 _ _ _ _ _ Hu1 Hlt Heqk Hgt), (IHf H3 Hu2). reflexivity.
        - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
          apply orb_false_iff in Hu as [Hu1 Hu2].
          rewrite (ren_subst_tvar_in_cidx_gen D idx k r1 r2 Hu1 Hlt Heqk Hgt), (IH Hu2). reflexivity. }
      apply Hcty; [exact Huse | intros; lia | reflexivity | intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]]].
Qed.

Lemma ren_spec_pair_body : forall (D : JoinDomain) (mot : cty D) rho,
  ren_cty (ren_shift (ren_shift rho)) (spec_pair_body_cty 0 mot) =
  spec_pair_body_cty 0 (ren_cty (ren_shift rho) mot).
Proof.
  intros D mot rho.
  assert (Hcidx : forall (i : cidx D) k r1 r2,
    (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
    r1 k = k -> r1 (S k) = S k -> r2 k = k ->
    (forall x, x > k -> r1 (S x) = S (r2 x) /\ r2 x > k) ->
    ren_cidx r1 (spec_pair_body_cidx k i) = spec_pair_body_cidx k (ren_cidx r2 i)).
  { induction i; intros k r1 r2 Hlt Hk1 Hsk Hk2 Hgt; cbn; try reflexivity;
      try (f_equal; [apply IHi1 | apply IHi2]; assumption).
    - f_equal. destruct (le_lt_dec k x).
      + destruct (Nat.eq_dec x k) as [-> | Hne].
        * rewrite Hk2, !Nat.ltb_irrefl. exact Hsk.
        * destruct (Hgt x ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
      + destruct (Hlt x l) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
    - f_equal; apply IHi; assumption.
    - f_equal. destruct (le_lt_dec k b).
      + destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite Hk2, !Nat.ltb_irrefl; exact Hsk |].
        destruct (Hgt b ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
      + destruct (Hlt b l) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
    - destruct (Nat.eq_dec p k) as [-> | Hne].
      + rewrite Nat.eqb_refl, Hk2, Nat.eqb_refl. cbn. rewrite Hsk. reflexivity.
      + destruct (le_lt_dec k p).
        * destruct (Hgt p ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. cbn; f_equal; exact Hr1.
        * destruct (Hlt p l) as [Hr1 Hr2]. rw_nat_bool. cbn; f_equal; exact Hr1.
    - destruct (Nat.eq_dec p k) as [-> | Hne].
      + rewrite Nat.eqb_refl, Hk2, Nat.eqb_refl. cbn. rewrite Hk1. reflexivity.
      + destruct (le_lt_dec k p).
        * destruct (Hgt p ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. cbn; f_equal; exact Hr1.
        * destruct (Hlt p l) as [Hr1 Hr2]. rw_nat_bool. cbn; f_equal; exact Hr1.
    - f_equal.
      + destruct (le_lt_dec k s).
        * destruct (Nat.eq_dec s k) as [-> | Hne]; [rewrite Hk2, !Nat.ltb_irrefl; exact Hsk |].
          destruct (Hgt s ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
        * destruct (Hlt s l) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
      + apply IHi1; [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia] |
                     cbn; congruence | cbn; congruence | cbn; congruence |
                     intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)); cbn; split; lia]].
      + apply IHi2; [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia] |
                     cbn; congruence | cbn; congruence | cbn; congruence |
                     intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)); cbn; split; lia]]. }
  assert (Hcty : forall (T : cty D) k r1 r2,
    (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
    r1 k = k -> r1 (S k) = S k -> r2 k = k ->
    (forall x, x > k -> r1 (S x) = S (r2 x) /\ r2 x > k) ->
    ren_cty r1 (spec_pair_body_cty k T) = spec_pair_body_cty k (ren_cty r2 T)).
  { induction T using cty_ind_nested; intros k r1 r2 Hlt Hk1 Hsk Hk2 Hgt; cbn; try reflexivity.
    - rewrite (IHT _ _ _ Hlt Hk1 Hsk Hk2 Hgt), (Hcidx _ _ _ _ Hlt Hk1 Hsk Hk2 Hgt). reflexivity.
    - f_equal. destruct (le_lt_dec k x).
      + destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite Hk2, !Nat.ltb_irrefl; exact Hsk |].
        destruct (Hgt x ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
      + destruct (Hlt x l) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
    - f_equal; apply IHT; assumption.
    - f_equal. destruct (le_lt_dec k b).
      + destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite Hk2, !Nat.ltb_irrefl; exact Hsk |].
        destruct (Hgt b ltac:(lia)) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
      + destruct (Hlt b l) as [Hr1 Hr2]. rw_nat_bool. exact Hr1.
    - f_equal; [apply IHT1; assumption |].
      apply IHT2; [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia] |
                   cbn; congruence | cbn; congruence | cbn; congruence |
                   intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)); cbn; split; lia]].
    - f_equal; [apply IHT1; assumption |].
      apply IHT2; [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia] |
                   cbn; congruence | cbn; congruence | cbn; congruence |
                   intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)); cbn; split; lia]].
    - f_equal; apply IHT; assumption.
    - f_equal; [apply IHT1 | apply IHT2]; assumption.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
      inversion H; subst; cbn in H2. rewrite (H2 _ _ _ Hlt Hk1 Hsk Hk2 Hgt), (IHf H3). reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
      rewrite (Hcidx _ _ _ _ Hlt Hk1 Hsk Hk2 Hgt), IH. reflexivity. }
  apply Hcty; [intros; lia | reflexivity | reflexivity | reflexivity |].
  intros [| x'] Hx'; cbn; split; lia.
Qed.

Lemma ren_spec_pair_subj : forall (D : JoinDomain) (pr : cterm D) (mot : cty D) rho,
  (match pr with
   | CPair _ _ _ _ fv sv =>
       match term_as_cidx fv, term_as_cidx sv with
       | Some _, Some _ => cty_uses_kinds false false false false true true false 0 mot = false
       | _, _ => cty_uses_var 0 mot = false
       end
   | CVar _ => True
   | _ => cty_uses_var 0 mot = false
   end) ->
  ren_cty rho (spec_pair_subj_cty pr mot) =
  spec_pair_subj_cty (ren_cterm rho pr) (ren_cty (ren_shift rho) mot).
Proof.
  intros D pr mot rho Huse.
  destruct pr; cbn in *; try (apply ren_unshift_cty; exact Huse).
  - apply ren_subst_var_in_cty.
  - destruct (term_as_cidx pr1) as [fi |] eqn:Hfi; destruct (term_as_cidx pr2) as [si |] eqn:Hsi;
      destruct pr1; destruct pr2; cbn in *; try discriminate;
      try (apply ren_unshift_cty; exact Huse).
    all: inversion Hfi; inversion Hsi; subst; clear Hfi Hsi.
    all: assert (Hcidx : forall j k r1 r2 (fi0 si0 : cidx D),
      cidx_uses_kinds false false true true false k j = false ->
      (forall x, x < k -> r1 x = r2 x /\ r2 x < k) -> r2 k = k ->
      (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
      ren_cidx r1 (subst_pair_cidx k fi0 si0 j) =
      subst_pair_cidx k (ren_cidx r1 fi0) (ren_cidx r1 si0) (ren_cidx r2 j));
    [clear; induction j; intros k r1 r2 fi0 si0 Hu Hlt Heqk Hgt; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHj1 _ _ _ _ _ Hu1 Hlt Heqk Hgt), (IHj2 _ _ _ _ _ Hu2 Hlt Heqk Hgt); reflexivity);
      [ f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Hu
      | f_equal; apply IHj; assumption
      | f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Hu
      | destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl; reflexivity |]
      ; destruct (le_lt_dec k p);
        [ destruct (Hgt p ltac:(lia)) as [Hr2 Hr1]; rw_nat_bool; cbn; f_equal; exact Hr1
        | destruct (Hlt p ltac:(lia)) as [Hr1 Hr2]; rw_nat_bool; cbn; f_equal; exact Hr1]
      | destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl; reflexivity |]
      ; destruct (le_lt_dec k p);
        [ destruct (Hgt p ltac:(lia)) as [Hr2 Hr1]; rw_nat_bool; cbn; f_equal; exact Hr1
        | destruct (Hlt p ltac:(lia)) as [Hr1 Hr2]; rw_nat_bool; cbn; f_equal; exact Hr1]
      | apply orb_false_iff in Hu as [H12 Hu3]; apply orb_false_iff in H12 as [Hu1 Hu2];
        f_equal;
        [ solve_disallowed_idx s k r1 r2 Hlt Heqk Hgt Hu1
        | rewrite (IHj1 (S k) (ren_shift r1) (ren_shift r2) (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0)); [rewrite !ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |];
          [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
          |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
            replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]]
        | rewrite (IHj2 (S k) (ren_shift r1) (ren_shift r2) (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0)); [rewrite !ren_lift0_cidx; reflexivity | exact Hu3 | | cbn; congruence |];
          [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
          |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
            replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]] ] ] |].
    all: assert (Hcty : forall T k r1 r2 (fi0 si0 : cidx D),
      cty_uses_kinds false false false false true true false k T = false ->
      (forall x, x < k -> r1 x = r2 x /\ r2 x < k) -> r2 k = k ->
      (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
      ren_cty r1 (subst_pair_cty k fi0 si0 T) =
      subst_pair_cty k (ren_cidx r1 fi0) (ren_cidx r1 si0) (ren_cty r2 T));
    [clear -Hcidx; induction T using cty_ind_nested; intros k r1 r2 fi0 si0 Hu Hlt Heqk Hgt; cbn in *; try reflexivity;
      [ apply orb_false_iff in Hu as [Hu1 Hu2];
        rewrite (IHT _ _ _ _ _ Hu1 Hlt Heqk Hgt), (Hcidx _ _ _ _ _ _ Hu2 Hlt Heqk Hgt); reflexivity
      | f_equal; solve_disallowed_idx x k r1 r2 Hlt Heqk Hgt Hu
      | f_equal; apply IHT; assumption
      | f_equal; solve_disallowed_idx b k r1 r2 Hlt Heqk Hgt Hu
      | apply orb_false_iff in Hu as [Hu1 Hu2];
        f_equal; [apply IHT1; assumption |];
        rewrite (IHT2 (S k) (ren_shift r1) (ren_shift r2) (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0)); [rewrite !ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |];
        [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
        |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
          replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]]
      | apply orb_false_iff in Hu as [Hu1 Hu2];
        f_equal; [apply IHT1; assumption |];
        rewrite (IHT2 (S k) (ren_shift r1) (ren_shift r2) (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0)); [rewrite !ren_lift0_cidx; reflexivity | exact Hu2 | | cbn; congruence |];
        [intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]
        |intros [| x'] Hx'; [lia | destruct (Hgt x' ltac:(lia)) as [Hr2 Hr1]; cbn; split; try lia;
          replace (x' - 0) with (S (x' - 1)) by lia; replace (r2 x' - 0) with (S (r2 x' - 1)) by lia; cbn; f_equal; exact Hr1]]
      | f_equal; apply IHT; assumption
      | apply orb_false_iff in Hu as [Hu1 Hu2]; f_equal; [apply IHT1 | apply IHT2]; assumption
      | f_equal; induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |];
        inversion H; subst; cbn in H2; apply orb_false_iff in Hu as [Hu1 Hu2];
        rewrite (H2 _ _ _ _ _ Hu1 Hlt Heqk Hgt), (IHf H3 Hu2); reflexivity
      | f_equal; induction indices as [| idx rest IH]; cbn in *; [reflexivity |];
        apply orb_false_iff in Hu as [Hu1 Hu2];
        rewrite (Hcidx _ _ _ _ _ _ Hu1 Hlt Heqk Hgt), (IH Hu2); reflexivity ] |].
    all: apply Hcty; [exact Huse | intros; lia | reflexivity | intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]]].
Qed.

Lemma ren_subst_cidx_0_var : forall (D : JoinDomain) (i : cidx D) k d r1 r2,
  r1 d = d ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k -> r1 0 = 0 ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cidx r1 (subst_cidx k (CIdxVar d) i) = subst_cidx k (CIdxVar d) (ren_cidx r2 i).
Proof.
  intros D i. induction i; intros k d r1 r2 Hd Hlt Heqk Hr10 Hgt; cbn in *; try reflexivity;
    try (f_equal; [apply IHi1 | apply IHi2]; assumption);
    try (f_equal; apply IHi; assumption).
  - destruct (Nat.eq_dec x k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. cbn. rewrite Hd. reflexivity.
    + destruct (le_lt_dec k x).
      * destruct (Hgt x ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
      * destruct (Hlt x ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - f_equal. destruct (Nat.eq_dec b k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k b).
      * destruct (Hgt b ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt b ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - f_equal. destruct (Nat.eq_dec p k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k p).
      * destruct (Hgt p ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt p ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - f_equal. destruct (Nat.eq_dec p k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k p).
      * destruct (Hgt p ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt p ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - f_equal.
    + destruct (Nat.eq_dec s k) as [-> | Hne].
      * rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
      * destruct (le_lt_dec k s).
        -- destruct (Hgt s ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
        -- destruct (Hlt s ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
    + replace (ren_lift 0 1 d) with (S d) by (unfold ren_lift; rw_nat_bool; lia).
      apply IHi1; [cbn; f_equal; exact Hd | | cbn; f_equal; exact Heqk | reflexivity |].
      * intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      * intros [| [| y]] Hx'; [lia | lia | destruct (Hgt (S y) ltac:(lia)) as [Hr2 Hr1]; cbn in *; rewrite Nat.sub_0_r in Hr1; split; lia].
    + replace (ren_lift 0 1 d) with (S d) by (unfold ren_lift; rw_nat_bool; lia).
      apply IHi2; [cbn; f_equal; exact Hd | | cbn; f_equal; exact Heqk | reflexivity |].
      * intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
      * intros [| [| y]] Hx'; [lia | lia | destruct (Hgt (S y) ltac:(lia)) as [Hr2 Hr1]; cbn in *; rewrite Nat.sub_0_r in Hr1; split; lia].
Qed.

Lemma ren_subst_sum_cidx_var0 : forall (D : JoinDomain) is_left (i : cidx D) k d r1 r2,
  r1 d = d ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k -> r1 0 = 0 ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cidx r1 (subst_sum_cidx is_left k (CIdxVar d) i) =
  subst_sum_cidx is_left k (CIdxVar d) (ren_cidx r2 i).
Proof.
  intros D is_left i. induction i; intros k d r1 r2 Hd Hlt Heqk Hr10 Hgt; cbn in *; try reflexivity;
    try (f_equal; [apply IHi1 | apply IHi2]; assumption);
    try (f_equal; apply IHi; assumption).
  - f_equal. destruct (Nat.eq_dec x k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k x).
      * destruct (Hgt x ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt x ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - f_equal. destruct (Nat.eq_dec b k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k b).
      * destruct (Hgt b ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt b ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - f_equal. destruct (Nat.eq_dec p k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k p).
      * destruct (Hgt p ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt p ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - f_equal. destruct (Nat.eq_dec p k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rw_nat_bool. exact Hr10.
    + destruct (le_lt_dec k p).
      * destruct (Hgt p ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. exact Hr1.
      * destruct (Hlt p ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. exact Hr1.
  - assert (Hlt' : forall x, x < S k -> ren_shift r1 x = ren_shift r2 x /\ ren_shift r2 x < S k).
    { intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]. }
    assert (Heqk' : ren_shift r2 (S k) = S k) by (cbn; f_equal; exact Heqk).
    assert (Hgt' : forall x, x > S k -> ren_shift r2 x > S k /\ ren_shift r1 (x - 1) = ren_shift r2 x - 1).
    { intros [| [| y]] Hx'; [lia | lia | destruct (Hgt (S y) ltac:(lia)) as [Hr2 Hr1]; cbn in *; rewrite Nat.sub_0_r in Hr1; split; lia]. }
    assert (Hlift : ren_lift 0 1 d = S d) by (unfold ren_lift; rw_nat_bool; lia).
    destruct (Nat.eq_dec s k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl. rewrite Hlift.
      rewrite (ren_subst_cidx_0_var D _ 0 d r1 (ren_shift r1) Hd ltac:(intros; lia) eq_refl Hr10
                 ltac:(intros [| y] Hx'; [lia | cbn; rewrite Nat.sub_0_r; split; lia])).
      f_equal. destruct is_left; [apply IHi1 | apply IHi2]; try assumption; try reflexivity; cbn; f_equal; assumption.
    + destruct (le_lt_dec k s).
      * destruct (Hgt s ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn.
        f_equal; [exact Hr1 | unfold lift_cidx; rewrite Hlift; apply IHi1 | unfold lift_cidx; rewrite Hlift; apply IHi2]; try assumption; try reflexivity; cbn; f_equal; assumption.
      * destruct (Hlt s ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn.
        f_equal; [exact Hr1 | unfold lift_cidx; rewrite Hlift; apply IHi1 | unfold lift_cidx; rewrite Hlift; apply IHi2]; try assumption; try reflexivity; cbn; f_equal; assumption.
Qed.

Lemma ren_spec_sum_branch : forall (D : JoinDomain) is_left (mot : cty D) rho,
  ren_cty (ren_shift rho) (spec_sum_branch_cty is_left 0 mot) =
  spec_sum_branch_cty is_left 0 (ren_cty (ren_shift rho) mot).
Proof.
  intros D is_left mot rho.
  assert (Hcidx : forall (i : cidx D) k r,
    (forall x, x <= k -> r x = x) -> (forall x, x > k -> r x > k) ->
    ren_cidx r (spec_sum_branch_cidx is_left k i) = spec_sum_branch_cidx is_left k (ren_cidx r i)).
  { induction i; intros k r Hle Hgt; cbn; try reflexivity;
      try (f_equal; [apply IHi1 | apply IHi2]; assumption);
      try (f_equal; apply IHi; assumption).
    destruct (Nat.eq_dec s k) as [-> | Hne].
    - rewrite Nat.eqb_refl, (Hle k (Nat.le_refl k)), Nat.eqb_refl.
      rewrite !ren_cidx_comp.
      replace (ren_cidx (fun x => r (sum_branch_rot k x)) (subst_sum_cidx is_left (S k) (CIdxVar 0) (if is_left then i1 else i2)))
         with (ren_cidx (sum_branch_rot k) (ren_cidx r (subst_sum_cidx is_left (S k) (CIdxVar 0) (if is_left then i1 else i2)))).
      2:{ rewrite ren_cidx_comp. apply ren_cidx_ext. intro y. unfold sum_branch_rot.
          destruct (y =? 0) eqn:E0; [apply Nat.eqb_eq in E0; subst y; rewrite (Hle 0 ltac:(lia)), (Hle k (Nat.le_refl k)); reflexivity |].
          destruct (le_lt_dec y k).
          - destruct (y <=? k) eqn:Ey; [| apply Nat.leb_gt in Ey; lia].
            rewrite (Hle y ltac:(lia)), (Hle (y - 1) ltac:(lia)), E0, Ey. reflexivity.
          - destruct (y <=? k) eqn:Ey; [apply Nat.leb_le in Ey; lia |].
            pose proof (Hgt y ltac:(lia)).
            destruct (r y =? 0) eqn:Er0; [apply Nat.eqb_eq in Er0; lia |].
            destruct (r y <=? k) eqn:Erk; [apply Nat.leb_le in Erk; lia | reflexivity]. }
      f_equal. destruct is_left;
        (apply ren_subst_sum_cidx_var0;
         [ apply Hle; lia
         | intros [| x'] Hx'; [cbn; rewrite (Hle 0 ltac:(lia)); split; lia | cbn; rewrite (Hle (S x') ltac:(lia)), (Hle x' ltac:(lia)); split; lia]
         | cbn; f_equal; apply Hle; lia
         | apply Hle; lia
         | intros [| y] Hx'; [lia | cbn; split; [pose proof (Hgt y ltac:(lia)); lia | rewrite !Nat.sub_0_r; reflexivity]] ]).
    - destruct (le_lt_dec k s).
      + pose proof (Hgt s ltac:(lia)). rw_nat_bool. cbn; f_equal;
          [apply IHi1 | apply IHi2];
          [ intros [| x'] Hx'; cbn; [reflexivity | rewrite (Hle x' ltac:(lia)); reflexivity]
          | intros [| x'] Hx'; [lia | cbn; pose proof (Hgt x' ltac:(lia)); lia]
          | intros [| x'] Hx'; cbn; [reflexivity | rewrite (Hle x' ltac:(lia)); reflexivity]
          | intros [| x'] Hx'; [lia | cbn; pose proof (Hgt x' ltac:(lia)); lia] ].
      + pose proof (Hle s ltac:(lia)). rw_nat_bool. cbn; f_equal;
          [apply IHi1 | apply IHi2];
          [ intros [| x'] Hx'; cbn; [reflexivity | rewrite (Hle x' ltac:(lia)); reflexivity]
          | intros [| x'] Hx'; [lia | cbn; pose proof (Hgt x' ltac:(lia)); lia]
          | intros [| x'] Hx'; cbn; [reflexivity | rewrite (Hle x' ltac:(lia)); reflexivity]
          | intros [| x'] Hx'; [lia | cbn; pose proof (Hgt x' ltac:(lia)); lia] ]. }
  assert (Hcty : forall (T : cty D) k rn,
    (forall x, x <= k -> rn x = x) -> (forall x, x > k -> rn x > k) ->
    ren_cty rn (spec_sum_branch_cty is_left k T) = spec_sum_branch_cty is_left k (ren_cty rn T)).
  { induction T using cty_ind_nested; intros k rn Hle Hgt; cbn; try reflexivity.
    - rewrite (IHT _ _ Hle Hgt), (Hcidx _ _ _ Hle Hgt). reflexivity.
    - f_equal; apply IHT; assumption.
    - f_equal; [apply IHT1; assumption |].
      apply IHT2; [intros [| x'] Hx'; cbn; [reflexivity | rewrite (Hle x' ltac:(lia)); reflexivity] |
                   intros [| x'] Hx'; [lia | cbn; pose proof (Hgt x' ltac:(lia)); lia]].
    - f_equal; [apply IHT1; assumption |].
      apply IHT2; [intros [| x'] Hx'; cbn; [reflexivity | rewrite (Hle x' ltac:(lia)); reflexivity] |
                   intros [| x'] Hx'; [lia | cbn; pose proof (Hgt x' ltac:(lia)); lia]].
    - f_equal; apply IHT; assumption.
    - f_equal; [apply IHT1 | apply IHT2]; assumption.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
      inversion H; subst; cbn in H2. rewrite (H2 _ _ Hle Hgt), (IHf H3). reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
      rewrite (Hcidx _ _ _ Hle Hgt), IH. reflexivity. }
  apply Hcty; [intros [| x'] Hx'; [reflexivity | lia] | intros [| x'] Hx'; [lia | cbn; lia]].
Qed.

Lemma cidx_uses_kinds_lift_c : forall (D : JoinDomain) idx unbox fst snd scase c (i : cidx D),
  cidx_uses_kinds idx unbox fst snd scase c (lift_cidx c 1 i) = false.
Proof.
  intros D idx unbox fst snd scase c i. revert c.
  induction i; intros c; cbn; try reflexivity;
    try (rewrite IHi1, IHi2; reflexivity);
    try (apply IHi);
    try (unfold ren_lift; destruct (Nat.ltb_spec x c); destruct idx; try reflexivity; apply Nat.eqb_neq; lia);
    try (unfold ren_lift; destruct (Nat.ltb_spec b c); destruct unbox; try reflexivity; apply Nat.eqb_neq; lia);
    try (unfold ren_lift; destruct (Nat.ltb_spec p c); destruct fst; try reflexivity; apply Nat.eqb_neq; lia);
    try (unfold ren_lift; destruct (Nat.ltb_spec p c); destruct snd; try reflexivity; apply Nat.eqb_neq; lia).
  - assert (Hs : (if scase then false else ren_lift c 1 s =? c) = false).
    { unfold ren_lift; destruct (Nat.ltb_spec s c); destruct scase; try reflexivity; apply Nat.eqb_neq; lia. }
    rewrite Hs.
    replace (ren_cidx (ren_shift (ren_lift c 1)) i1) with (lift_cidx (S c) 1 i1)
      by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y c); rw_nat_bool; lia]).
    replace (ren_cidx (ren_shift (ren_lift c 1)) i2) with (lift_cidx (S c) 1 i2)
      by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y c); rw_nat_bool; lia]).
    rewrite (IHi1 (S c)), (IHi2 (S c)). reflexivity.
Qed.

Lemma cidx_uses_kinds_lift0 : forall (D : JoinDomain) idx unbox fst snd scase (i : cidx D),
  cidx_uses_kinds idx unbox fst snd scase 0 (lift_cidx 0 1 i) = false.
Proof.
  intros D idx unbox fst snd scase i. apply cidx_uses_kinds_lift_c.
Qed.

Lemma cidx_uses_kinds_lift_shift_gen : forall (D : JoinDomain) (v : cidx D) c d,
  c <= d ->
  cidx_uses_kinds true false false false false d v = false ->
  cidx_uses_kinds true false false false false (S d) (lift_cidx c 1 v) = false.
Proof.
  intros D v. induction v; intros c d Hcd Hv; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hv as [Hv1 Hv2]; rewrite (IHv1 c d Hcd Hv1), (IHv2 c d Hcd Hv2); reflexivity).
  - apply IHv; assumption.
  - unfold ren_lift; destruct (Nat.ltb_spec b c); rw_nat_bool; reflexivity.
  - unfold ren_lift; destruct (Nat.ltb_spec p c); rw_nat_bool; reflexivity.
  - unfold ren_lift; destruct (Nat.ltb_spec p c); rw_nat_bool; reflexivity.
  - apply orb_false_iff in Hv as [H12 Hv3]; apply orb_false_iff in H12 as [Hv1 Hv2].
    assert (Hs0 : (ren_lift c 1 s =? S d) = false) by (unfold ren_lift; destruct (Nat.ltb_spec s c); rw_nat_bool; reflexivity).
    rewrite Hs0.
    replace (ren_cidx (ren_shift (ren_lift c 1)) v1) with (lift_cidx (S c) 1 v1)
      by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y c); rw_nat_bool; lia]).
    replace (ren_cidx (ren_shift (ren_lift c 1)) v2) with (lift_cidx (S c) 1 v2)
      by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y c); rw_nat_bool; lia]).
    rewrite (IHv1 (S c) (S d) ltac:(lia) Hv2), (IHv2 (S c) (S d) ltac:(lia) Hv3). reflexivity.
Qed.

Lemma cidx_uses_kinds_lift_shift : forall (D : JoinDomain) (v : cidx D) d,
  cidx_uses_kinds true false false false false d v = false ->
  cidx_uses_kinds true false false false false (S d) (lift_cidx 0 1 v) = false.
Proof.
  intros D v d Hv. apply cidx_uses_kinds_lift_shift_gen; [lia | exact Hv].
Qed.

Lemma cidx_uses_kinds_subst_cidx : forall (D : JoinDomain) (i val : cidx D) c,
  cidx_uses_kinds true false false false false c i = false ->
  cidx_uses_kinds true false false false false (S c) i = false ->
  cidx_uses_kinds true false false false false c val = false ->
  cidx_uses_kinds true false false false false c (subst_cidx c val i) = false.
Proof.
  intros D i. induction i; intros val c Hc Hsc Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hsc as [Hsc1 Hsc2];
         rewrite (IHi1 val c Hc1 Hsc1 Hval), (IHi2 val c Hc2 Hsc2 Hval); reflexivity).
  - destruct (x =? c); [exact Hval | destruct (x <? c); cbn; reflexivity].
  - apply IHi; assumption.
  - destruct (b <? c) eqn:Elt; [cbn; exact Hc |].
    destruct (Nat.eq_dec b c) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Hc; discriminate |].
    rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn. apply Nat.eqb_neq. apply Nat.eqb_neq in Hsc. apply Nat.ltb_ge in Elt. lia.
  - destruct (p <? c) eqn:Elt; [cbn; exact Hc |].
    destruct (Nat.eq_dec p c) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Hc; discriminate |].
    rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn. apply Nat.eqb_neq. apply Nat.eqb_neq in Hsc. apply Nat.ltb_ge in Elt. lia.
  - destruct (p <? c) eqn:Elt; [cbn; exact Hc |].
    destruct (Nat.eq_dec p c) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Hc; discriminate |].
    rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn. apply Nat.eqb_neq. apply Nat.eqb_neq in Hsc. apply Nat.ltb_ge in Elt. lia.
  - apply orb_false_iff in Hc as [H12 Hc3]; apply orb_false_iff in H12 as [Hc1 Hc2].
    apply orb_false_iff in Hsc as [H34 Hsc3]; apply orb_false_iff in H34 as [Hsc1 Hsc2].
    assert (Hs : (if false then false
                  else (if s <? c then s else if s =? c then 0 else s - 1) =? c) = false).
    { destruct (s <? c) eqn:Elt; [exact Hc1 |].
      destruct (Nat.eq_dec s c) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Hc1; discriminate |].
      rewrite (proj2 (Nat.eqb_neq _ _) Hne). apply Nat.eqb_neq. apply Nat.eqb_neq in Hsc1. apply Nat.ltb_ge in Elt. lia. }
    rewrite Hs.
    assert (Hvl : cidx_uses_kinds true false false false false (S c) (lift_cidx 0 1 val) = false)
      by (apply cidx_uses_kinds_lift_shift; exact Hval).
    rewrite (IHi1 (lift_cidx 0 1 val) (S c) Hc2 Hsc2 Hvl), (IHi2 (lift_cidx 0 1 val) (S c) Hc3 Hsc3 Hvl). reflexivity.
Qed.

Lemma cidx_uses_kinds_subst_cidx_ge : forall (D : JoinDomain) (i val : cidx D) d c,
  d <= c ->
  (d = c -> cidx_uses_kinds true false false false false c i = false) ->
  cidx_uses_kinds true false false false false (S c) i = false ->
  cidx_uses_kinds true false false false false c val = false ->
  cidx_uses_kinds true false false false false c (subst_cidx d val i) = false.
Proof.
  intros D i. induction i; intros val d c Hdc Hdeq Hsc Hval; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsc as [Hsc1 Hsc2];
         rewrite (IHi1 val d c Hdc (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hdeq Heq))) Hsc1 Hval),
                 (IHi2 val d c Hdc (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hdeq Heq))) Hsc2 Hval); reflexivity).
  - destruct (x =? d); [exact Hval | destruct (x <? d); cbn; reflexivity].
  - apply IHi; assumption.
  - destruct (b <? d) eqn:Elt; [cbn; apply Nat.eqb_neq; apply Nat.ltb_lt in Elt; lia |].
    destruct (Nat.eq_dec b d) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn. apply Nat.eqb_neq. intro Heq.
      assert (Hdceq : d = c) by lia. specialize (Hdeq Hdceq). rewrite <- Hdceq, Nat.eqb_refl in Hdeq. discriminate.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn. apply Nat.eqb_neq.
      apply Nat.eqb_neq in Hsc. apply Nat.ltb_ge in Elt. lia.
  - destruct (p <? d) eqn:Elt; [cbn; apply Nat.eqb_neq; apply Nat.ltb_lt in Elt; lia |].
    destruct (Nat.eq_dec p d) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn. apply Nat.eqb_neq. intro Heq.
      assert (Hdceq : d = c) by lia. specialize (Hdeq Hdceq). rewrite <- Hdceq, Nat.eqb_refl in Hdeq. discriminate.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn. apply Nat.eqb_neq.
      apply Nat.eqb_neq in Hsc. apply Nat.ltb_ge in Elt. lia.
  - destruct (p <? d) eqn:Elt; [cbn; apply Nat.eqb_neq; apply Nat.ltb_lt in Elt; lia |].
    destruct (Nat.eq_dec p d) as [-> | Hne].
    + rewrite Nat.eqb_refl. cbn. apply Nat.eqb_neq. intro Heq.
      assert (Hdceq : d = c) by lia. specialize (Hdeq Hdceq). rewrite <- Hdceq, Nat.eqb_refl in Hdeq. discriminate.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn. apply Nat.eqb_neq.
      apply Nat.eqb_neq in Hsc. apply Nat.ltb_ge in Elt. lia.
  - apply orb_false_iff in Hsc as [H34 Hsc3]; apply orb_false_iff in H34 as [Hsc1 Hsc2].
    assert (Hs : ((if s <? d then s else if s =? d then 0 else s - 1) =? c) = false).
    { destruct (s <? d) eqn:Elt; [apply Nat.eqb_neq; apply Nat.ltb_lt in Elt; lia |].
      destruct (Nat.eq_dec s d) as [-> | Hne].
      - rewrite Nat.eqb_refl. apply Nat.eqb_neq. intro Heq.
        assert (Hdceq : d = c) by lia. specialize (Hdeq Hdceq). rewrite <- Hdceq, Nat.eqb_refl in Hdeq. discriminate.
      - rewrite (proj2 (Nat.eqb_neq _ _) Hne). apply Nat.eqb_neq.
        apply Nat.eqb_neq in Hsc1. apply Nat.ltb_ge in Elt. lia. }
    rewrite Hs.
    assert (Hvl : cidx_uses_kinds true false false false false (S c) (lift_cidx 0 1 val) = false)
      by (apply cidx_uses_kinds_lift_shift; exact Hval).
    rewrite (IHi1 (lift_cidx 0 1 val) (S d) (S c) ltac:(lia)
               (fun Heq => proj2 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hdeq ltac:(lia))))))
               Hsc2 Hvl),
            (IHi2 (lift_cidx 0 1 val) (S d) (S c) ltac:(lia)
               (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hdeq ltac:(lia))))
               Hsc3 Hvl).
    reflexivity.
Qed.

Fixpoint cidx_sum_ok {D : JoinDomain} (is_left : bool) (k : nat) (mask : list bool) (i : cidx D) : bool :=
  match i with
  | CIdxVar x => negb (x =? k)
  | CIdxLit _ => true
  | CIdxAdd l r => cidx_sum_ok is_left k mask l && cidx_sum_ok is_left k mask r
  | CIdxProm _ i' => cidx_sum_ok is_left k mask i'
  | CIdxUnbox b | CIdxFst b | CIdxSnd b => negb (b =? k) && negb (nth b mask false)
  | CIdxCase s l r =>
      if s =? k then
        cidx_sum_ok is_left (S k) (true :: mask) (if is_left then l else r)
      else
        negb (nth s mask false) &&
        cidx_sum_ok is_left (S k) (false :: mask) l &&
        cidx_sum_ok is_left (S k) (false :: mask) r
  end.

Fixpoint cty_sum_ok {D : JoinDomain} (is_left : bool) (k : nat) (mask : list bool) (T : cty D) : bool :=
  match T with
  | CNat | CBool | CUniv _ => true
  | CVec elem len => cty_sum_ok is_left k mask elem && cidx_sum_ok is_left k mask len
  | CTVar x | CTUnbox x => negb (x =? k) && negb (nth x mask false)
  | CTProm _ inner | CBox _ inner => cty_sum_ok is_left k mask inner
  | CPi _ _ _ dom cod | CSigma _ _ dom cod =>
      cty_sum_ok is_left k mask dom && cty_sum_ok is_left (S k) (false :: mask) cod
  | CSum l r => cty_sum_ok is_left k mask l && cty_sum_ok is_left k mask r
  | CRecord _ fields =>
      (fix go_fs (fs : list (nat * grade D * cty D)) : bool :=
         match fs with [] => true | (_, _, ft) :: rest => cty_sum_ok is_left k mask ft && go_fs rest end) fields
  | CInd _ indices =>
      (fix go_is (ls : list (cidx D)) : bool :=
         match ls with [] => true | hd :: rest => cidx_sum_ok is_left k mask hd && go_is rest end) indices
  end.

Lemma cidx_uses_kinds_subst_sum_mask : forall (D : JoinDomain) is_left (i : cidx D) k mask val,
  length mask = k ->
  cidx_sum_ok is_left k mask i = true ->
  (forall c, nth c mask false = true -> cidx_uses_kinds true false false false false c val = false) ->
  forall c, nth c mask false = true ->
  cidx_uses_kinds true false false false false c (subst_sum_cidx is_left k val i) = false.
Proof.
  intros D is_left i. induction i; intros k mask val Hlen Hok Hval c Hc; cbn in *; try reflexivity;
    try (apply andb_true_iff in Hok as [Ho1 Ho2];
         rewrite (IHi1 k mask val Hlen Ho1 Hval c Hc), (IHi2 k mask val Hlen Ho2 Hval c Hc); reflexivity).
  - apply IHi with (k := k) (mask := mask); assumption.
  - apply andb_true_iff in Hok as [Hne Hnth].
    assert (Hck : c < k) by (rewrite <- Hlen; destruct (le_lt_dec (length mask) c); [rewrite nth_overflow in Hc; [discriminate | exact l] | exact l]).
    destruct (b <? k) eqn:Elt; [cbn; apply Nat.eqb_neq; intro Heq; subst; rewrite Hc in Hnth; discriminate |].
    destruct (b =? k) eqn:Eb; [discriminate |].
    cbn. apply Nat.eqb_neq. apply Nat.ltb_ge in Elt. apply Nat.eqb_neq in Eb. lia.
  - apply andb_true_iff in Hok as [Hne Hnth].
    assert (Hck : c < k) by (rewrite <- Hlen; destruct (le_lt_dec (length mask) c); [rewrite nth_overflow in Hc; [discriminate | exact l] | exact l]).
    destruct (p <? k) eqn:Elt; [cbn; apply Nat.eqb_neq; intro Heq; subst; rewrite Hc in Hnth; discriminate |].
    destruct (p =? k) eqn:Eb; [discriminate |].
    cbn. apply Nat.eqb_neq. apply Nat.ltb_ge in Elt. apply Nat.eqb_neq in Eb. lia.
  - apply andb_true_iff in Hok as [Hne Hnth].
    assert (Hck : c < k) by (rewrite <- Hlen; destruct (le_lt_dec (length mask) c); [rewrite nth_overflow in Hc; [discriminate | exact l] | exact l]).
    destruct (p <? k) eqn:Elt; [cbn; apply Nat.eqb_neq; intro Heq; subst; rewrite Hc in Hnth; discriminate |].
    destruct (p =? k) eqn:Eb; [discriminate |].
    cbn. apply Nat.eqb_neq. apply Nat.ltb_ge in Elt. apply Nat.eqb_neq in Eb. lia.
  - assert (Hck : c < k) by (rewrite <- Hlen; destruct (le_lt_dec (length mask) c); [rewrite nth_overflow in Hc; [discriminate | exact l] | exact l]).
    assert (Hval' : forall c', nth c' (true :: mask) false = true ->
      cidx_uses_kinds true false false false false c' (lift_cidx 0 1 val) = false).
    { intros [| c'] Hc'; [apply cidx_uses_kinds_lift0 | apply cidx_uses_kinds_lift_shift; apply Hval; exact Hc']. }
    destruct (s =? k) eqn:Es; cbn.
    + assert (Hz : cidx_uses_kinds true false false false false 0
                     (subst_sum_cidx is_left (S k) (lift_cidx 0 1 val) (if is_left then i1 else i2)) = false).
      { destruct is_left;
          [apply (IHi1 (S k) (true :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Hok Hval' 0); cbn; reflexivity
          |apply (IHi2 (S k) (true :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Hok Hval' 0); cbn; reflexivity]. }
      apply cidx_uses_kinds_subst_cidx_ge; [lia | | | apply Hval; exact Hc].
      * intros <-. exact Hz.
      * destruct is_left;
          [apply (IHi1 (S k) (true :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Hok Hval' (S c)); cbn; exact Hc
          |apply (IHi2 (S k) (true :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Hok Hval' (S c)); cbn; exact Hc].
    + apply andb_true_iff in Hok as [H12 Ho3]; apply andb_true_iff in H12 as [Hnth Ho2].
      assert (Hvalf : forall c', nth c' (false :: mask) false = true ->
        cidx_uses_kinds true false false false false c' (lift_cidx 0 1 val) = false).
      { intros [| c'] Hc'; [cbn in Hc'; discriminate | apply cidx_uses_kinds_lift_shift; apply Hval; exact Hc']. }
      destruct (s <? k) eqn:Elt;
        [ assert (Hsne : s <> c) by (intro Heq; subst; rewrite Hc in Hnth; discriminate);
          rewrite (proj2 (Nat.eqb_neq s c) Hsne)
        | assert (Hsne : s - 1 <> c) by (apply Nat.ltb_ge in Elt; apply Nat.eqb_neq in Es; lia);
          rewrite (proj2 (Nat.eqb_neq (s - 1) c) Hsne) ];
        [ rewrite (IHi1 (S k) (false :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Ho2 Hvalf (S c) ltac:(cbn; exact Hc)),
                  (IHi2 (S k) (false :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Ho3 Hvalf (S c) ltac:(cbn; exact Hc));
          reflexivity
        | rewrite (IHi1 (S k) (false :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Ho2 Hvalf (S c) ltac:(cbn; exact Hc)),
                  (IHi2 (S k) (false :: mask) (lift_cidx 0 1 val) ltac:(cbn; lia) Ho3 Hvalf (S c) ltac:(cbn; exact Hc));
          reflexivity ].
Qed.

Lemma ren_subst_sum_cidx_gen : forall (D : JoinDomain) is_left (i val : cidx D) k mask r1 r2,
  length mask = k ->
  cidx_sum_ok is_left k mask i = true ->
  (forall c, nth c mask false = true -> cidx_uses_kinds true false false false false c val = false) ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cidx r1 (subst_sum_cidx is_left k val i) =
  subst_sum_cidx is_left k (ren_cidx r1 val) (ren_cidx r2 i).
Proof.
  intros D is_left i.
  induction i; intros val k mask r1 r2 Hlen Hok Hval Hlt Heqk Hgt; cbn in *; try reflexivity;
    try (apply andb_true_iff in Hok as [Ho1 Ho2];
         rewrite (IHi1 val k mask r1 r2 Hlen Ho1 Hval Hlt Heqk Hgt),
                 (IHi2 val k mask r1 r2 Hlen Ho2 Hval Hlt Heqk Hgt); reflexivity).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite Nat.eqb_refl in Hok; discriminate |].
    destruct (le_lt_dec k x).
    + destruct (Hgt x ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
    + destruct (Hlt x ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - f_equal. apply IHi with (mask := mask); assumption.
  - apply andb_true_iff in Hok as [Hne _].
    destruct (Nat.eq_dec b k) as [-> | Hne']; [rewrite Nat.eqb_refl in Hne; discriminate |].
    destruct (le_lt_dec k b).
    + destruct (Hgt b ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
    + destruct (Hlt b ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - apply andb_true_iff in Hok as [Hne _].
    destruct (Nat.eq_dec p k) as [-> | Hne']; [rewrite Nat.eqb_refl in Hne; discriminate |].
    destruct (le_lt_dec k p).
    + destruct (Hgt p ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
    + destruct (Hlt p ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - apply andb_true_iff in Hok as [Hne _].
    destruct (Nat.eq_dec p k) as [-> | Hne']; [rewrite Nat.eqb_refl in Hne; discriminate |].
    destruct (le_lt_dec k p).
    + destruct (Hgt p ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
    + destruct (Hlt p ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - assert (Hlt' : forall x, x < S k -> ren_shift r1 x = ren_shift r2 x /\ ren_shift r2 x < S k).
    { intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia]. }
    assert (Heqk' : ren_shift r2 (S k) = S k) by (cbn; f_equal; exact Heqk).
    assert (Hgt' : forall x, x > S k -> ren_shift r2 x > S k /\ ren_shift r1 (x - 1) = ren_shift r2 x - 1).
    { intros [| [| y]] Hx'; [lia | lia | destruct (Hgt (S y) ltac:(lia)) as [Hr2 Hr1]; cbn in *; rewrite Nat.sub_0_r in Hr1; split; lia]. }
    destruct (Nat.eq_dec s k) as [-> | Hne].
    + rewrite Nat.eqb_refl, Heqk, Nat.eqb_refl in *.
      assert (Hval' : forall c, nth c (true :: mask) false = true ->
        cidx_uses_kinds true false false false false c (lift_cidx 0 1 val) = false).
      { intros [| c'] Hc'; [apply cidx_uses_kinds_lift0 | apply cidx_uses_kinds_lift_shift; apply Hval; exact Hc']. }
      assert (Hbr :
        cidx_uses_kinds true false false false false 0
          (subst_sum_cidx is_left (S k) (lift_cidx 0 1 val) (if is_left then i1 else i2)) = false).
      { destruct is_left;
          [eapply cidx_uses_kinds_subst_sum_mask with (mask := true :: mask); [cbn; lia | exact Hok | exact Hval' | cbn; reflexivity]
          |eapply cidx_uses_kinds_subst_sum_mask with (mask := true :: mask); [cbn; lia | exact Hok | exact Hval' | cbn; reflexivity]]. }
      rewrite (ren_subst_cidx_gen D _ val 0 r1 (ren_shift r1) Hbr ltac:(intros; lia) eq_refl
                 ltac:(intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]])).
      f_equal.
      destruct is_left.
      * rewrite (IHi1 (lift_cidx 0 1 val) (S k) (true :: mask) (ren_shift r1) (ren_shift r2) ltac:(cbn; lia) Hok Hval' Hlt' Heqk' Hgt').
        rewrite ren_lift0_cidx. reflexivity.
      * rewrite (IHi2 (lift_cidx 0 1 val) (S k) (true :: mask) (ren_shift r1) (ren_shift r2) ltac:(cbn; lia) Hok Hval' Hlt' Heqk' Hgt').
        rewrite ren_lift0_cidx. reflexivity.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hne) in *.
      apply andb_true_iff in Hok as [H12 Ho3]; apply andb_true_iff in H12 as [_ Ho2].
      assert (Hvalf : forall c, nth c (false :: mask) false = true ->
        cidx_uses_kinds true false false false false c (lift_cidx 0 1 val) = false).
      { intros [| c'] Hc'; [cbn in Hc'; discriminate | apply cidx_uses_kinds_lift_shift; apply Hval; exact Hc']. }
      destruct (le_lt_dec k s).
      * destruct (Hgt s ltac:(lia)) as [Hr2gt Hr1].
        rw_nat_bool. cbn.
        f_equal; [exact Hr1 | |].
        -- rewrite (IHi1 (lift_cidx 0 1 val) (S k) (false :: mask) (ren_shift r1) (ren_shift r2) ltac:(cbn; lia) Ho2 Hvalf Hlt' Heqk' Hgt').
           rewrite ren_lift0_cidx. reflexivity.
        -- rewrite (IHi2 (lift_cidx 0 1 val) (S k) (false :: mask) (ren_shift r1) (ren_shift r2) ltac:(cbn; lia) Ho3 Hvalf Hlt' Heqk' Hgt').
           rewrite ren_lift0_cidx. reflexivity.
      * destruct (Hlt s ltac:(lia)) as [Hr1 Hr2lt].
        rw_nat_bool. cbn.
        f_equal; [exact Hr1 | |].
        -- rewrite (IHi1 (lift_cidx 0 1 val) (S k) (false :: mask) (ren_shift r1) (ren_shift r2) ltac:(cbn; lia) Ho2 Hvalf Hlt' Heqk' Hgt').
           rewrite ren_lift0_cidx. reflexivity.
        -- rewrite (IHi2 (lift_cidx 0 1 val) (S k) (false :: mask) (ren_shift r1) (ren_shift r2) ltac:(cbn; lia) Ho3 Hvalf Hlt' Heqk' Hgt').
           rewrite ren_lift0_cidx. reflexivity.
Qed.

Lemma ren_subst_sum_cty_gen : forall (D : JoinDomain) is_left (T : cty D) (val : cidx D) k mask r1 r2,
  length mask = k ->
  cty_sum_ok is_left k mask T = true ->
  (forall c, nth c mask false = true -> cidx_uses_kinds true false false false false c val = false) ->
  (forall x, x < k -> r1 x = r2 x /\ r2 x < k) ->
  r2 k = k ->
  (forall x, x > k -> r2 x > k /\ r1 (x - 1) = r2 x - 1) ->
  ren_cty r1 (subst_sum_cty is_left k val T) =
  subst_sum_cty is_left k (ren_cidx r1 val) (ren_cty r2 T).
Proof.
  intros D is_left T.
  induction T using cty_ind_nested; intros val k mask r1 r2 Hlen Hok Hval Hlt Heqk Hgt; cbn in *; try reflexivity;
    try (apply andb_true_iff in Hok as [Ho1 Ho2]; f_equal; [apply (IHT1 _ _ mask); assumption | apply (IHT2 _ _ mask); assumption]).
  - apply andb_true_iff in Hok as [Ho1 Ho2].
    rewrite (IHT _ _ mask _ _ Hlen Ho1 Hval Hlt Heqk Hgt),
            (ren_subst_sum_cidx_gen D is_left len val k mask r1 r2 Hlen Ho2 Hval Hlt Heqk Hgt).
    reflexivity.
  - apply andb_true_iff in Hok as [Hne _].
    destruct (Nat.eq_dec x k) as [-> | Hne']; [rewrite Nat.eqb_refl in Hne; discriminate |].
    destruct (le_lt_dec k x).
    + destruct (Hgt x ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
    + destruct (Hlt x ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - f_equal. apply (IHT _ _ mask); assumption.
  - apply andb_true_iff in Hok as [Hne _].
    destruct (Nat.eq_dec b k) as [-> | Hne']; [rewrite Nat.eqb_refl in Hne; discriminate |].
    destruct (le_lt_dec k b).
    + destruct (Hgt b ltac:(lia)) as [Hr2gt Hr1]. rw_nat_bool. cbn. f_equal. exact Hr1.
    + destruct (Hlt b ltac:(lia)) as [Hr1 Hr2lt]. rw_nat_bool. cbn. f_equal. exact Hr1.
  - apply andb_true_iff in Hok as [Ho1 Ho2].
    f_equal; [apply (IHT1 _ _ mask); assumption |].
    assert (Hvalf : forall c, nth c (false :: mask) false = true ->
      cidx_uses_kinds true false false false false c (lift_cidx 0 1 val) = false).
    { intros [| c'] Hc'; [cbn in Hc'; discriminate | apply cidx_uses_kinds_lift_shift; apply Hval; exact Hc']. }
    rewrite (IHT2 (lift_cidx 0 1 val) (S k) (false :: mask) (ren_shift r1) (ren_shift r2));
      [rewrite ren_lift0_cidx; reflexivity | cbn; lia | exact Ho2 | exact Hvalf | | cbn; f_equal; exact Heqk |].
    + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
    + intros [| [| y]] Hx'; [lia | lia | destruct (Hgt (S y) ltac:(lia)) as [Hr2 Hr1]; cbn in *; rewrite Nat.sub_0_r in Hr1; split; lia].
  - apply andb_true_iff in Hok as [Ho1 Ho2].
    f_equal; [apply (IHT1 _ _ mask); assumption |].
    assert (Hvalf : forall c, nth c (false :: mask) false = true ->
      cidx_uses_kinds true false false false false c (lift_cidx 0 1 val) = false).
    { intros [| c'] Hc'; [cbn in Hc'; discriminate | apply cidx_uses_kinds_lift_shift; apply Hval; exact Hc']. }
    rewrite (IHT2 (lift_cidx 0 1 val) (S k) (false :: mask) (ren_shift r1) (ren_shift r2));
      [rewrite ren_lift0_cidx; reflexivity | cbn; lia | exact Ho2 | exact Hvalf | | cbn; f_equal; exact Heqk |].
    + intros [| x'] Hx'; [cbn; split; lia | destruct (Hlt x' ltac:(lia)); cbn; split; lia].
    + intros [| [| y]] Hx'; [lia | lia | destruct (Hgt (S y) ltac:(lia)) as [Hr2 Hr1]; cbn in *; rewrite Nat.sub_0_r in Hr1; split; lia].
  - f_equal. apply (IHT _ _ mask); assumption.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply andb_true_iff in Hok as [Ho1 Ho2].
    rewrite (H2 _ _ mask _ _ eq_refl Ho1 Hval Hlt Heqk Hgt), (IHf H3 Ho2). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply andb_true_iff in Hok as [Ho1 Ho2].
    rewrite (ren_subst_sum_cidx_gen D is_left idx val k mask r1 r2 Hlen Ho1 Hval Hlt Heqk Hgt), (IH Ho2). reflexivity.
Qed.

Definition sum_mask_env {D : JoinDomain} (is_left : bool) (env : cenv D) (k : nat) (mask : list bool) : Prop :=
  length mask = k /\
  (exists ek A B, clookup env k = Some ek /\
    cty_alpha_eq (ren_cty (plus (S k)) (cannotation ek)) (CSum A B) /\
    (if is_left then cty_alpha_eq A CNat else cty_alpha_eq B CNat)) /\
  (forall c, nth c mask false = true ->
    exists ec, clookup env c = Some ec /\ cty_alpha_eq (cannotation ec) CNat).

Lemma sum_mask_env_cons_false : forall (D : JoinDomain) is_left (env : cenv D) k mask hd,
  sum_mask_env is_left env k mask ->
  sum_mask_env is_left (hd :: env) (S k) (false :: mask).
Proof.
  intros D is_left env k mask hd [Hlen [[ek [A [B [Hlk [Hsum Hnat]]]]] Hmask]].
  split; [cbn; lia | split].
  - exists ek, (ren_cty (plus 1) A), (ren_cty (plus 1) B).
    repeat split; [exact Hlk | |].
    + unfold cty_alpha_eq in *.
      replace (ren_cty (plus (S (S k))) (cannotation ek))
         with (ren_cty (plus 1) (ren_cty (plus (S k)) (cannotation ek)))
        by (rewrite ren_cty_comp; apply ren_cty_ext; intro y; lia).
      rewrite erase_hints_ren, Hsum. cbn. rewrite <- !erase_hints_ren. reflexivity.
    + destruct is_left; unfold cty_alpha_eq in *; rewrite erase_hints_ren, Hnat; reflexivity.
  - intros [| c'] Hc'; [cbn in Hc'; discriminate | apply Hmask; exact Hc'].
Qed.

Lemma sum_mask_env_cons_true : forall (D : JoinDomain) is_left (env : cenv D) k mask x A' u',
  sum_mask_env is_left env k mask ->
  (forall ek A B, clookup env k = Some ek ->
    cty_alpha_eq (ren_cty (plus (S k)) (cannotation ek)) (CSum A B) ->
    (if is_left then cty_alpha_eq A' A else cty_alpha_eq A' B)) ->
  sum_mask_env is_left ({| cbinder := x; cannotation := A'; ctype_uses := u' |} :: env) (S k) (true :: mask).
Proof.
  intros D is_left env k mask x A' u' [Hlen [[ek [A [B [Hlk [Hsum Hnat]]]]] Hmask]] Hbr.
  split; [cbn; lia | split].
  - exists ek, (ren_cty (plus 1) A), (ren_cty (plus 1) B).
    repeat split; [exact Hlk | |].
    + unfold cty_alpha_eq in *.
      replace (ren_cty (plus (S (S k))) (cannotation ek))
         with (ren_cty (plus 1) (ren_cty (plus (S k)) (cannotation ek)))
        by (rewrite ren_cty_comp; apply ren_cty_ext; intro y; lia).
      rewrite erase_hints_ren, Hsum. cbn. rewrite <- !erase_hints_ren. reflexivity.
    + destruct is_left; unfold cty_alpha_eq in *; rewrite erase_hints_ren, Hnat; reflexivity.
  - intros [| c'] Hc'.
    + exists {| cbinder := x; cannotation := A'; ctype_uses := u' |}. split; [reflexivity |].
      specialize (Hbr ek A B Hlk Hsum).
      destruct is_left; unfold cty_alpha_eq in *; cbn in *; rewrite Hbr; exact Hnat.
    + apply Hmask; exact Hc'.
Qed.

Lemma cidx_demand_sum_ok : forall (D : JoinDomain) (env : cenv D) i d,
  CIdxDemand env i d ->
  forall is_left k mask,
    sum_mask_env is_left env k mask ->
    cidx_sum_ok is_left k mask i = true.
Proof.
  intros D env i d H.
  induction H; intros is_left k mask Henv; cbn; try reflexivity;
    try (rewrite (IHCIdxDemand1 is_left k mask Henv), (IHCIdxDemand2 is_left k mask Henv); reflexivity);
    try (apply IHCIdxDemand; exact Henv).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [| rewrite (proj2 (Nat.eqb_neq _ _) Hne); reflexivity].
    destruct Henv as [_ [[ek [A [B [Hlk [Hsum _]]]]] _]].
    rewrite H in Hlk; inversion Hlk; subst.
    unfold cty_alpha_eq in H0, Hsum. rewrite erase_hints_ren, H0 in Hsum. discriminate.
  - destruct Henv as [_ [[ek [A [B [Hlk [Hsum _]]]]] Hmask]].
    assert (Hne : b <> k).
    { intro Heq; subst. rewrite H in Hlk; inversion Hlk; subst.
      unfold cty_alpha_eq in H0, Hsum. rewrite erase_hints_ren, H0 in Hsum. discriminate. }
    assert (Hnth : nth b mask false = false).
    { destruct (nth b mask false) eqn:Eb; [| reflexivity].
      destruct (Hmask b Eb) as [ec [Hlkc Hnatc]]. rewrite H in Hlkc; inversion Hlkc; subst.
      unfold cty_alpha_eq in H0, Hnatc. rewrite H0 in Hnatc. discriminate. }
    rewrite (proj2 (Nat.eqb_neq _ _) Hne), Hnth. reflexivity.
  - destruct Henv as [_ [[ek [A [B [Hlk [Hsum _]]]]] Hmask]].
    assert (Hne : p <> k).
    { intro Heq; subst. rewrite H in Hlk; inversion Hlk; subst.
      unfold cty_alpha_eq in H0, Hsum. rewrite erase_hints_ren, H0 in Hsum. discriminate. }
    assert (Hnth : nth p mask false = false).
    { destruct (nth p mask false) eqn:Eb; [| reflexivity].
      destruct (Hmask p Eb) as [ec [Hlkc Hnatc]]. rewrite H in Hlkc; inversion Hlkc; subst.
      unfold cty_alpha_eq in H0, Hnatc. rewrite H0 in Hnatc. discriminate. }
    rewrite (proj2 (Nat.eqb_neq _ _) Hne), Hnth. reflexivity.
  - destruct Henv as [_ [[ek [A [B [Hlk [Hsum _]]]]] Hmask]].
    assert (Hne : p <> k).
    { intro Heq; subst. rewrite H in Hlk; inversion Hlk; subst.
      unfold cty_alpha_eq in H0, Hsum. rewrite erase_hints_ren, H0 in Hsum. discriminate. }
    assert (Hnth : nth p mask false = false).
    { destruct (nth p mask false) eqn:Eb; [| reflexivity].
      destruct (Hmask p Eb) as [ec [Hlkc Hnatc]]. rewrite H in Hlkc; inversion Hlkc; subst.
      unfold cty_alpha_eq in H0, Hnatc. rewrite H0 in Hnatc. discriminate. }
    rewrite (proj2 (Nat.eqb_neq _ _) Hne), Hnth. reflexivity.
  - destruct (Nat.eq_dec s k) as [-> | Hne].
    + rewrite Nat.eqb_refl.
      destruct is_left.
      * eapply IHCIdxDemand1. apply sum_mask_env_cons_true; [exact Henv |].
        intros ek A0 B0 Hlk Hsum. rewrite H in Hlk; inversion Hlk; subst.
        unfold cty_alpha_eq in H0, Hsum. rewrite H0 in Hsum. inversion Hsum; assumption.
      * eapply IHCIdxDemand2. apply sum_mask_env_cons_true; [exact Henv |].
        intros ek A0 B0 Hlk Hsum. rewrite H in Hlk; inversion Hlk; subst.
        unfold cty_alpha_eq in H0, Hsum. rewrite H0 in Hsum. inversion Hsum; assumption.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hne).
      pose proof Henv as [_ [_ Hmask]].
      assert (Hnth : nth s mask false = false).
      { destruct (nth s mask false) eqn:Eb; [| reflexivity].
        destruct (Hmask s Eb) as [ec [Hlkc Hnatc]]. rewrite H in Hlkc; inversion Hlkc; subst.
        unfold cty_alpha_eq in H0, Hnatc. rewrite erase_hints_ren, Hnatc in H0. discriminate. }
      rewrite Hnth.
      rewrite (IHCIdxDemand1 is_left (S k) (false :: mask) (sum_mask_env_cons_false _ _ _ _ _ _ Henv)),
              (IHCIdxDemand2 is_left (S k) (false :: mask) (sum_mask_env_cons_false _ _ _ _ _ _ Henv)).
      reflexivity.
Qed.

Lemma ctype_demand_sum_ok : forall (D : JoinDomain) (env : cenv D) T d,
  CTypeDemand env T d ->
  forall is_left k mask,
    sum_mask_env is_left env k mask ->
    cty_sum_ok is_left k mask T = true.
Proof.
  intros D env T d H.
  induction H using CTypeDemand_ind_mut with
    (P := fun env T d _ => forall is_left k mask, sum_mask_env is_left env k mask -> cty_sum_ok is_left k mask T = true)
    (P0 := fun env fs df _ => forall is_left k mask, sum_mask_env is_left env k mask ->
             (fix go_fs (fs0 : list (nat * grade D * cty D)) : bool :=
                match fs0 with [] => true | (_, _, ft) :: rest => cty_sum_ok is_left k mask ft && go_fs rest end) fs = true)
    (P1 := fun env ls dl _ => forall is_left k mask, sum_mask_env is_left env k mask ->
             (fix go_is (ls0 : list (cidx D)) : bool :=
                match ls0 with [] => true | hd :: rest => cidx_sum_ok is_left k mask hd && go_is rest end) ls = true);
    intros is_left k mask Henv; cbn; try reflexivity.
  - rewrite (IHCTypeDemand is_left k mask Henv).
    match goal with
    | Hc : CIdxDemand _ _ _ |- _ => rewrite (cidx_demand_sum_ok D _ _ _ Hc is_left k mask Henv)
    end. reflexivity.
  - destruct Henv as [_ [[ek [A [B [Hlk [Hsum _]]]]] Hmask]].
    match goal with
    | Hlkx : clookup _ x = Some _, Ha : cty_alpha_eq (cannotation _) (CUniv _) |- _ =>
        assert (Hne : x <> k) by (intro Heq; subst; rewrite Hlkx in Hlk; inversion Hlk; subst; unfold cty_alpha_eq in Ha, Hsum; rewrite erase_hints_ren, Ha in Hsum; discriminate);
        assert (Hnth : nth x mask false = false) by (destruct (nth x mask false) eqn:Eb; [destruct (Hmask x Eb) as [ec [Hlkc Hnatc]]; rewrite Hlkx in Hlkc; inversion Hlkc; subst; unfold cty_alpha_eq in Ha, Hnatc; rewrite Ha in Hnatc; discriminate | reflexivity]);
        rewrite (proj2 (Nat.eqb_neq _ _) Hne), Hnth; reflexivity
    end.
  - apply (IHCTypeDemand is_left k mask Henv).
  - destruct Henv as [_ [[ek [A [B [Hlk [Hsum _]]]]] Hmask]].
    match goal with
    | Hlkb : clookup _ b = Some _, Ha : cty_alpha_eq (cannotation _) (CBox _ (CUniv _)) |- _ =>
        assert (Hne : b <> k) by (intro Heq; subst; rewrite Hlkb in Hlk; inversion Hlk; subst; unfold cty_alpha_eq in Ha, Hsum; rewrite erase_hints_ren, Ha in Hsum; discriminate);
        assert (Hnth : nth b mask false = false) by (destruct (nth b mask false) eqn:Eb; [destruct (Hmask b Eb) as [ec [Hlkc Hnatc]]; rewrite Hlkb in Hlkc; inversion Hlkc; subst; unfold cty_alpha_eq in Ha, Hnatc; rewrite Ha in Hnatc; discriminate | reflexivity]);
        rewrite (proj2 (Nat.eqb_neq _ _) Hne), Hnth; reflexivity
    end.
  - rewrite (IHCTypeDemand1 is_left k mask Henv),
            (IHCTypeDemand2 is_left (S k) (false :: mask) (sum_mask_env_cons_false _ _ _ _ _ _ Henv)). reflexivity.
  - rewrite (IHCTypeDemand1 is_left k mask Henv),
            (IHCTypeDemand2 is_left (S k) (false :: mask) (sum_mask_env_cons_false _ _ _ _ _ _ Henv)). reflexivity.
  - apply (IHCTypeDemand is_left k mask Henv).
  - rewrite (IHCTypeDemand1 is_left k mask Henv), (IHCTypeDemand2 is_left k mask Henv). reflexivity.
  - apply (IHCTypeDemand is_left k mask Henv).
  - apply (IHCTypeDemand is_left k mask Henv).
  - rewrite (IHCTypeDemand is_left k mask Henv), (IHCTypeDemand0 is_left k mask Henv). reflexivity.
  - match goal with
    | Hc : CIdxDemand _ _ _ |- _ => rewrite (cidx_demand_sum_ok D _ _ _ Hc is_left k mask Henv)
    end.
    rewrite (IHCTypeDemand is_left k mask Henv). reflexivity.
Qed.

Lemma cty_uses_var_implies_sum_ok : forall (D : JoinDomain) is_left (T : cty D) k mask,
  Forall (eq false) mask ->
  cty_uses_var k T = false ->
  cty_sum_ok is_left k mask T = true.
Proof.
  intros D is_left T.
  assert (Hcidx : forall (i : cidx D) k mask,
    Forall (eq false) mask -> cidx_uses_var k i = false -> cidx_sum_ok is_left k mask i = true).
  { induction i; intros k mask Hfa Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHi1 k mask Hfa Hu1), (IHi2 k mask Hfa Hu2); reflexivity);
      try (apply IHi; assumption).
    - rewrite Hu; reflexivity.
    - assert (Hnth : nth b mask false = false) by (destruct (le_lt_dec (length mask) b); [apply nth_overflow; lia | rewrite Forall_forall in Hfa; symmetry; apply Hfa, nth_In; exact l]).
      rewrite Hu, Hnth; reflexivity.
    - assert (Hnth : nth p mask false = false) by (destruct (le_lt_dec (length mask) p); [apply nth_overflow; lia | rewrite Forall_forall in Hfa; symmetry; apply Hfa, nth_In; exact l]).
      rewrite Hu, Hnth; reflexivity.
    - assert (Hnth : nth p mask false = false) by (destruct (le_lt_dec (length mask) p); [apply nth_overflow; lia | rewrite Forall_forall in Hfa; symmetry; apply Hfa, nth_In; exact l]).
      rewrite Hu, Hnth; reflexivity.
    - apply orb_false_iff in Hu as [H12 Hu3]; apply orb_false_iff in H12 as [Hu1 Hu2].
      rewrite Hu1.
      assert (Hnth : nth s mask false = false) by (destruct (le_lt_dec (length mask) s); [apply nth_overflow; lia | rewrite Forall_forall in Hfa; symmetry; apply Hfa, nth_In; exact l]).
      rewrite Hnth. cbn.
      rewrite (IHi1 (S k) (false :: mask) (Forall_cons _ eq_refl Hfa) Hu2),
              (IHi2 (S k) (false :: mask) (Forall_cons _ eq_refl Hfa) Hu3). reflexivity. }
  induction T using cty_ind_nested; intros k mask Hfa Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHT1 k mask Hfa Hu1), (IHT2 k mask Hfa Hu2); reflexivity).
  - apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (IHT k mask Hfa Hu1), (Hcidx len k mask Hfa Hu2). reflexivity.
  - assert (Hnth : nth x mask false = false) by (destruct (le_lt_dec (length mask) x); [apply nth_overflow; lia | rewrite Forall_forall in Hfa; symmetry; apply Hfa, nth_In; exact l]).
    rewrite Hu, Hnth; reflexivity.
  - apply IHT; assumption.
  - assert (Hnth : nth b mask false = false) by (destruct (le_lt_dec (length mask) b); [apply nth_overflow; lia | rewrite Forall_forall in Hfa; symmetry; apply Hfa, nth_In; exact l]).
    rewrite Hu, Hnth; reflexivity.
  - apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (IHT1 k mask Hfa Hu1), (IHT2 (S k) (false :: mask) (Forall_cons _ eq_refl Hfa) Hu2). reflexivity.
  - apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (IHT1 k mask Hfa Hu1), (IHT2 (S k) (false :: mask) (Forall_cons _ eq_refl Hfa) Hu2). reflexivity.
  - apply IHT; assumption.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (H2 k mask Hfa Hu1), (IHf H3 Hu2). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (Hcidx idx k mask Hfa Hu1), (IH Hu2). reflexivity.
Qed.

Lemma ren_spec_sum_subj : forall (D : JoinDomain) (scrut : cterm D) (mot : cty D) rho,
  (match scrut with
   | CInl _ v =>
       match term_as_cidx v with
       | Some _ => cty_sum_ok true 0 [] mot = true
       | None => cty_uses_var 0 mot = false
       end
   | CInr _ v =>
       match term_as_cidx v with
       | Some _ => cty_sum_ok false 0 [] mot = true
       | None => cty_uses_var 0 mot = false
       end
   | CVar _ => True
   | _ => cty_uses_var 0 mot = false
   end) ->
  ren_cty rho (spec_sum_subj_cty scrut mot) =
  spec_sum_subj_cty (ren_cterm rho scrut) (ren_cty (ren_shift rho) mot).
Proof.
  intros D scrut mot rho Huse.
  destruct scrut; cbn in *; try (apply ren_unshift_cty; exact Huse).
  - apply ren_subst_var_in_cty.
  - destruct scrut; cbn in *; try (apply ren_unshift_cty; exact Huse);
      (eapply ren_subst_sum_cty_gen with (mask := []);
        [reflexivity | exact Huse | intros c Hc; destruct c; discriminate | intros; lia | reflexivity |
         intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]]]).
  - destruct scrut; cbn in *; try (apply ren_unshift_cty; exact Huse);
      (eapply ren_subst_sum_cty_gen with (mask := []);
        [reflexivity | exact Huse | intros c Hc; destruct c; discriminate | intros; lia | reflexivity |
         intros [| x'] Hx'; [lia | cbn; split; [lia | rewrite !Nat.sub_0_r; reflexivity]]]).
Qed.

Lemma ren_shift_lift_2 : forall k y,
  ren_shift (ren_lift (S k) 2) y = ren_lift (S (S k)) 2 y.
Proof.
  intros k [| y]; unfold ren_lift; cbn; [reflexivity |].
  destruct (y <? S k) eqn:E1; destruct (y <=? k) eqn:E2;
    [ reflexivity
    | apply Nat.ltb_lt in E1; apply Nat.leb_gt in E2; lia
    | apply Nat.ltb_ge in E1; apply Nat.leb_le in E2; lia
    | reflexivity ].
Qed.

Lemma cty_uses_kinds_ren_lift1 : forall (D : JoinDomain) (T : cty D) k,
  cty_uses_kinds true false false false false false false k T = false ->
  cty_uses_kinds true false false false false false false k (ren_cty (ren_lift (S k) 2) T) = false.
Proof.
  intros D T.
  assert (Hcidx : forall (i : cidx D) k,
    cidx_uses_kinds true false false false false k i = false ->
    cidx_uses_kinds true false false false false k (ren_cidx (ren_lift (S k) 2) i) = false).
  { induction i; intros k Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHi1 k Hu1), (IHi2 k Hu2); reflexivity);
      try (apply IHi; exact Hu).
    - unfold ren_lift; destruct (Nat.ltb_spec b (S k)); apply Nat.eqb_neq; apply Nat.eqb_neq in Hu; lia.
    - unfold ren_lift; destruct (Nat.ltb_spec p (S k)); apply Nat.eqb_neq; apply Nat.eqb_neq in Hu; lia.
    - unfold ren_lift; destruct (Nat.ltb_spec p (S k)); apply Nat.eqb_neq; apply Nat.eqb_neq in Hu; lia.
    - apply orb_false_iff in Hu as [H12 Hu3]; apply orb_false_iff in H12 as [Hu1 Hu2].
      assert (Hs : (ren_lift (S k) 2 s =? k) = false) by (unfold ren_lift; destruct (Nat.ltb_spec s (S k)); apply Nat.eqb_neq; apply Nat.eqb_neq in Hu1; lia).
      rewrite Hs.
      replace (ren_cidx (ren_shift (ren_lift (S k) 2)) i1) with (ren_cidx (ren_lift (S (S k)) 2) i1)
        by (symmetry; apply ren_cidx_ext; apply ren_shift_lift_2).
      replace (ren_cidx (ren_shift (ren_lift (S k) 2)) i2) with (ren_cidx (ren_lift (S (S k)) 2) i2)
        by (symmetry; apply ren_cidx_ext; apply ren_shift_lift_2).
      rewrite (IHi1 (S k) Hu2), (IHi2 (S k) Hu3). reflexivity. }
  induction T using cty_ind_nested; intros k Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHT1 k Hu1), (IHT2 k Hu2); reflexivity).
  - apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (IHT k Hu1), (Hcidx len k Hu2). reflexivity.
  - unfold ren_lift; destruct (Nat.ltb_spec x (S k)); apply Nat.eqb_neq; apply Nat.eqb_neq in Hu; lia.
  - apply IHT; exact Hu.
  - unfold ren_lift; destruct (Nat.ltb_spec b (S k)); apply Nat.eqb_neq; apply Nat.eqb_neq in Hu; lia.
  - apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (IHT1 k Hu1).
    replace (ren_cty (ren_shift (ren_lift (S k) 2)) T2) with (ren_cty (ren_lift (S (S k)) 2) T2)
      by (symmetry; apply ren_cty_ext; apply ren_shift_lift_2).
    rewrite (IHT2 (S k) Hu2). reflexivity.
  - apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (IHT1 k Hu1).
    replace (ren_cty (ren_shift (ren_lift (S k) 2)) T2) with (ren_cty (ren_lift (S (S k)) 2) T2)
      by (symmetry; apply ren_cty_ext; apply ren_shift_lift_2).
    rewrite (IHT2 (S k) Hu2). reflexivity.
  - apply IHT; exact Hu.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (H2 k Hu1), (IHf H3 Hu2). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hu as [Hu1 Hu2].
    rewrite (Hcidx idx k Hu1), (IH Hu2). reflexivity.
Qed.

Lemma ren_spec_fix_step : forall (D : JoinDomain) (mot : cty D) rho,
  cty_uses_kinds true false false false false false false 0 mot = false ->
  ren_cty (ren_shift (ren_shift rho)) (spec_fix_step_cty mot) =
  spec_fix_step_cty (ren_cty (ren_shift rho) mot).
Proof.
  intros D mot rho Hu.
  unfold spec_fix_step_cty.
  rewrite ren_subst_cidx_in_cty_0 by (apply cty_uses_kinds_ren_lift1; exact Hu).
  cbn. rewrite !ren_cty_comp.
  f_equal. apply ren_cty_ext. intros [| y]; unfold ren_lift; cbn; [reflexivity | replace (y + 2) with (S (S y)) by lia; cbn; lia].
Qed.

Lemma ren_spec_fix_subj : forall (D : JoinDomain) (scrut : cterm D) (mot : cty D) rho,
  (match term_as_cidx scrut with
   | Some _ => cty_uses_kinds true false false false false false false 0 mot = false
   | None => cty_uses_var 0 mot = false
   end) ->
  ren_cty rho (spec_fix_subj_cty scrut mot) =
  spec_fix_subj_cty (ren_cterm rho scrut) (ren_cty (ren_shift rho) mot).
Proof.
  intros D scrut mot rho Huse.
  unfold spec_fix_subj_cty.
  destruct scrut; cbn in *; try (apply ren_unshift_cty; exact Huse);
    apply ren_subst_cidx_in_cty_0; exact Huse.
Qed.



(* Renaming Specifications & Context Relations *)

Record RenSpec (D : JoinDomain) (rho : nat -> nat) (Tvec : list (grade D) -> list (grade D)) (n1 n2 : nat) : Prop := {
  rs_zero : Tvec (vec_zero n1) = vec_zero n2;
  rs_single : forall x q, x < n1 -> Tvec (vec_single n1 x q) = vec_single n2 (rho x) q;
  rs_add : forall u v, length u = n1 -> length v = n1 -> Tvec (vec_add u v) = vec_add (Tvec u) (Tvec v);
  rs_scale : forall q u, length u = n1 -> Tvec (vec_scale q u) = vec_scale q (Tvec u);
  rs_join : forall j u v, grade_join D = Some j -> length u = n1 -> length v = n1 -> Tvec (vec_join j u v) = vec_join j (Tvec u) (Tvec v);
  rs_allows : forall u v, length u = n1 -> length v = n1 -> vec_allows u v -> vec_allows (Tvec u) (Tvec v);
  rs_len : forall u, length u = n1 -> length (Tvec u) = n2;
  rs_nth : forall u i, length u = n1 -> i < n1 -> nth_grade (Tvec u) (rho i) = nth_grade u i;
  rs_is_zero : forall u, length u = n1 -> vec_is_zero u = true -> vec_is_zero (Tvec u) = true
}.

Definition Tvec_cons {D : JoinDomain} (Tvec : list (grade D) -> list (grade D)) (u : list (grade D)) : list (grade D) :=
  match u with
  | a :: rest => a :: Tvec rest
  | [] => []
  end.

Lemma RenSpec_cons : forall (D : JoinDomain) rho (Tvec : list (grade D) -> list (grade D)) n1 n2,
  RenSpec D rho Tvec n1 n2 ->
  RenSpec D (ren_shift rho) (Tvec_cons Tvec) (S n1) (S n2).
Proof.
  intros D rho Tvec n1 n2 RS. constructor.
  - unfold Tvec_cons. change (vec_zero (S n1)) with (@zero D :: vec_zero n1).
    change (vec_zero (S n2)) with (@zero D :: vec_zero n2).
    cbn. rewrite (rs_zero D _ _ _ _ RS). reflexivity.
  - intros [| x] q Hlt; cbn.
    + unfold Tvec_cons. change (repeat (@zero D) n1) with (vec_zero n1). change (repeat (@zero D) n2) with (vec_zero n2).
      cbn. rewrite (rs_zero D _ _ _ _ RS). reflexivity.
    + rewrite (rs_single D _ _ _ _ RS); [reflexivity | lia].
  - intros [| a u] [| b v] Hu Hv; cbn in *; try lia; f_equal.
    apply (rs_add D _ _ _ _ RS); lia.
  - intros q [| a u] Hu; cbn in *; try lia; f_equal.
    apply (rs_scale D _ _ _ _ RS); lia.
  - intros j [| a u] [| b v] Hj Hu Hv; cbn in *; try lia; f_equal.
    apply (rs_join D _ _ _ _ RS); [exact Hj | lia | lia].
  - intros [| a u] [| b v] Hu Hv Hal; cbn in *; try lia; inversion Hal; subst; constructor;
      [assumption | apply (rs_allows D _ _ _ _ RS); [lia | lia | assumption]].
  - intros [| a u] Hu; cbn in *; try lia; f_equal.
    apply (rs_len D _ _ _ _ RS); lia.
  - intros [| a u] [| i] Hu Hlt; unfold nth_grade in *; cbn in *; try lia; [reflexivity |].
    apply (rs_nth D _ _ _ _ RS); lia.
  - intros [| a u] Hu Hz; cbn in *; try lia.
    unfold vec_is_zero in Hz; cbn in Hz; apply andb_true_iff in Hz as [Ha Hu'].
    unfold vec_is_zero; cbn. rewrite Ha.
    change (forallb (grade_eqb (@zero D)) (Tvec u)) with (vec_is_zero (Tvec u)).
    exact (rs_is_zero D _ _ _ _ RS u ltac:(lia) Hu').
Qed.

Lemma ren_cty_eq_CNat : forall (D : JoinDomain) f (A : cty D),
  cty_alpha_eq (ren_cty f A) CNat -> cty_alpha_eq A CNat.
Proof.
  intros D f A H. unfold cty_alpha_eq in *. rewrite erase_hints_ren in H.
  destruct A; cbn in H; try discriminate; reflexivity.
Qed.

Lemma ren_cty_eq_CUniv : forall (D : JoinDomain) f (A : cty D) lvl,
  cty_alpha_eq (ren_cty f A) (CUniv lvl) -> cty_alpha_eq A (CUniv lvl).
Proof.
  intros D f A lvl H. unfold cty_alpha_eq in *. rewrite erase_hints_ren in H.
  destruct A; cbn in H; try discriminate; exact H.
Qed.

Lemma ren_cty_eq_CBox_Univ : forall (D : JoinDomain) f (A : cty D) q lvl,
  cty_alpha_eq (ren_cty f A) (CBox q (CUniv lvl)) -> cty_alpha_eq A (CBox q (CUniv lvl)).
Proof.
  intros D f A q lvl H. unfold cty_alpha_eq in *. rewrite erase_hints_ren in H.
  destruct A; cbn in H; try discriminate.
  destruct A; cbn in H; try discriminate; exact H.
Qed.

Lemma ren_cty_eq_CBox_Nat : forall (D : JoinDomain) f (A : cty D) q,
  cty_alpha_eq (ren_cty f A) (CBox q CNat) -> cty_alpha_eq A (CBox q CNat).
Proof.
  intros D f A q H. unfold cty_alpha_eq in *. rewrite erase_hints_ren in H.
  destruct A; cbn in H; try discriminate.
  destruct A; cbn in H; try discriminate; exact H.
Qed.

Lemma ren_cty_eq_CSigma_FstNat : forall (D : JoinDomain) f (A : cty D) z r snd_ty,
  cty_alpha_eq (ren_cty f A) (CSigma z r CNat snd_ty) ->
  exists z' snd_ty', cty_alpha_eq A (CSigma z' r CNat snd_ty').
Proof.
  intros D f A z r snd_ty H. unfold cty_alpha_eq in *. rewrite erase_hints_ren in H.
  destruct A; cbn in H; try discriminate.
  destruct A1; cbn in H; try discriminate.
  inversion H; subst. exists 0, A2. reflexivity.
Qed.

Lemma ren_cty_eq_CSigma_SndNat : forall (D : JoinDomain) f (A : cty D) z r fst_ty,
  cty_alpha_eq (ren_cty f A) (CSigma z r fst_ty CNat) ->
  exists z' fst_ty', cty_alpha_eq A (CSigma z' r fst_ty' CNat).
Proof.
  intros D f A z r fst_ty H. unfold cty_alpha_eq in *. rewrite erase_hints_ren in H.
  destruct A; cbn in H; try discriminate.
  destruct A2; cbn in H; try discriminate.
  inversion H; subst. exists 0, A1. reflexivity.
Qed.

Record RenTypeEnv {D : JoinDomain} (env1 env2 : cenv D) (rho : nat -> nat) (Tvec : list (grade D) -> list (grade D)) : Prop := {
  rte_spec : RenSpec D rho Tvec (length env1) (length env2);
  rte_lookup : forall x e, clookup env1 x = Some e ->
    exists e', clookup env2 (rho x) = Some e' /\
      ren_cty (plus (S (rho x))) (cannotation e') = ren_cty rho (ren_cty (plus (S x)) (cannotation e))
}.

Lemma RenTypeEnv_cons : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec x1 x2 T a1 a2,
  RenTypeEnv env1 env2 rho Tvec ->
  RenTypeEnv
    ({| cbinder := x1; cannotation := T; ctype_uses := a1 |} :: env1)
    ({| cbinder := x2; cannotation := ren_cty rho T; ctype_uses := a2 |} :: env2)
    (ren_shift rho) (Tvec_cons Tvec).
Proof.
  intros D env1 env2 rho Tvec x1 x2 T a1 a2 RTE. constructor.
  - apply RenSpec_cons; apply (rte_spec _ _ _ _ RTE).
  - intros [| x'] e Hlkp; cbn in Hlkp.
    + inversion Hlkp; subst; cbn.
      eexists; split; [reflexivity |].
      cbn. rewrite !ren_cty_comp. apply ren_cty_ext; intro y; cbn; reflexivity.
    + destruct (rte_lookup _ _ _ _ RTE x' e Hlkp) as [e' [Hl' Heq]].
      exists e'. split; [exact Hl' |].
      transitivity (ren_cty S (ren_cty (plus (S (rho x'))) (cannotation e')));
        [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
        | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity ].
Qed.

Lemma clookup_lt_length : forall (D : JoinDomain) (env : cenv D) x e,
  clookup env x = Some e -> x < length env.
Proof.
  intros D env x e H. pose proof (nth_error_Some env x) as [Hs _].
  apply Hs. unfold clookup in H. rewrite H. discriminate.
Qed.

Lemma BranchVec_ren : forall (D : JoinDomain) rho Tvec n1 n2 u1 u2 u,
  RenSpec D rho Tvec n1 n2 ->
  length u1 = n1 ->
  length u2 = n1 ->
  BranchVec u1 u2 u ->
  BranchVec (Tvec u1) (Tvec u2) (Tvec u).
Proof.
  intros D rho Tvec n1 n2 u1 u2 u RS H1 H2 Hbr.
  unfold BranchVec in *. destruct (grade_join D) as [j |] eqn:Hj.
  - subst u. apply (rs_join D _ _ _ _ RS); [exact Hj | assumption | assumption].
  - destruct Hbr as [-> ->]. split; reflexivity.
Qed.

Lemma ren_cidx_demand : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec i d,
  RenTypeEnv env1 env2 rho Tvec ->
  CIdxDemand env1 i d ->
  CIdxDemand env2 (ren_cidx rho i) (Tvec d).
Proof.
  intros D env1 env2 rho Tvec i d RTE H.
  revert env2 rho Tvec RTE.
  induction H; intros env2 rho Tvec RTE; cbn.
  - destruct (rte_lookup _ _ _ _ RTE x e H) as [e' [Hl' Heq]].
    assert (Hx : x < length env) by (eapply clookup_lt_length; exact H).
    rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) x one Hx).
    eapply CIdxDemandVar; [exact Hl' |].
    apply (ren_cty_eq_CNat D (plus (S (rho x)))).
    apply (f_equal erase_hints) in Heq.
    change (cty_alpha_eq (ren_cty (plus (S (rho x))) (cannotation e')) (ren_cty rho (ren_cty (plus (S x)) (cannotation e)))) in Heq.
    pose proof (ren_cty_alpha_eq D (plus (S x)) _ _ H0) as Hlift.
    pose proof (ren_cty_alpha_eq D rho _ _ Hlift) as Hrho.
    unfold cty_alpha_eq in *; cbn in *. rewrite Heq. exact Hrho.
  - rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ RTE)). constructor.
  - pose proof (cidx_demand_length D env l dl H) as Hl.
    pose proof (cidx_demand_length D env r dr H0) as Hr.
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) dl dr Hl Hr).
    constructor; [apply IHCIdxDemand1 | apply IHCIdxDemand2]; exact RTE.
  - pose proof (cidx_demand_length D env i di H) as Hi.
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ RTE) q di Hi).
    constructor; apply IHCIdxDemand; exact RTE.
  - destruct (rte_lookup _ _ _ _ RTE b e H) as [e' [Hl' Heq]].
    assert (Hb : b < length env) by (eapply clookup_lt_length; exact H).
    rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) b one Hb).
    assert (Hbox : cty_alpha_eq (ren_cty (plus (S (rho b))) (cannotation e')) (CBox q CNat)).
    { unfold cty_alpha_eq in *. rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S b)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D rho _ _ H1) as H2. exact H2. }
    apply (ren_cty_eq_CBox_Nat D (plus (S (rho b)))) in Hbox.
    eapply CIdxDemandUnbox; [exact Hl' | exact Hbox].
  - destruct (rte_lookup _ _ _ _ RTE p e H) as [e' [Hl' Heq]].
    assert (Hp : p < length env) by (eapply clookup_lt_length; exact H).
    rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) p one Hp).
    assert (Hsig : cty_alpha_eq (ren_cty (plus (S (rho p))) (cannotation e'))
                     (CSigma z r CNat (ren_cty (ren_shift rho) (ren_cty (ren_shift (plus (S p))) snd_ty)))).
    { unfold cty_alpha_eq in *. rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S p)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D rho _ _ H1) as H2. exact H2. }
    destruct (ren_cty_eq_CSigma_FstNat D (plus (S (rho p))) _ _ _ _ Hsig) as [z' [snd_ty' Hsig']].
    eapply CIdxDemandFst; [exact Hl' | exact Hsig'].
  - destruct (rte_lookup _ _ _ _ RTE p e H) as [e' [Hl' Heq]].
    assert (Hp : p < length env) by (eapply clookup_lt_length; exact H).
    rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) p one Hp).
    assert (Hsig : cty_alpha_eq (ren_cty (plus (S (rho p))) (cannotation e'))
                     (CSigma z r (ren_cty rho (ren_cty (plus (S p)) fst_ty)) CNat)).
    { unfold cty_alpha_eq in *. rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S p)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D rho _ _ H1) as H2. exact H2. }
    destruct (ren_cty_eq_CSigma_SndNat D (plus (S (rho p))) _ _ _ _ Hsig) as [z' [fst_ty' Hsig']].
    eapply CIdxDemandSnd; [exact Hl' | exact Hsig'].
  - destruct (rte_lookup _ _ _ _ RTE s e H) as [e' [Hl' Heq]].
    assert (Hs : s < length env) by (eapply clookup_lt_length; exact H).
    pose proof (cidx_demand_length D _ _ _ H1) as Hdl. cbn in Hdl.
    pose proof (cidx_demand_length D _ _ _ H2) as Hdr. cbn in Hdr.
    assert (Hdbr : length d_br = length env).
    { rewrite (BranchVec_length D (tl dl) (tl dr) d_br); [destruct dl; cbn in *; lia | | exact H3].
      destruct dl, dr; cbn in *; lia. }
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) _ d_br (vec_single_length D _ _ _) Hdbr).
    rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) s one Hs).
    eapply CIdxDemandCase with (A := ren_cty rho A) (B := ren_cty rho B)
      (dl := Tvec_cons Tvec dl) (dr := Tvec_cons Tvec dr).
    + exact Hl'.
    + unfold cty_alpha_eq in *. rewrite Heq.
      pose proof (ren_cty_alpha_eq D rho _ _ H0) as Hsum. exact Hsum.
    + apply IHCIdxDemand1. apply RenTypeEnv_cons; exact RTE.
    + apply IHCIdxDemand2. apply RenTypeEnv_cons; exact RTE.
    + destruct dl as [| al dl'], dr as [| ar dr']; cbn in *; try lia.
      eapply BranchVec_ren; [exact (rte_spec _ _ _ _ RTE) | lia | lia | exact H3].
Qed.

Lemma record_field_and_idx_list_demand_length : forall (D : JoinDomain),
  (forall (env : cenv D) fs df, CRecordFieldDemand env fs df -> length df = length env) /\
  (forall (env : cenv D) ls dl, CIdxListDemand env ls dl -> length dl = length env).
Proof.
  intro D. split.
  - intros env fs df H. induction H; [apply vec_zero_length | rewrite vec_add_length; [eapply ctype_demand_length; eassumption | rewrite (ctype_demand_length D _ _ _ H); symmetry; exact IHCRecordFieldDemand]].
  - intros env ls dl H. induction H; [apply vec_zero_length | rewrite vec_add_length; [eapply cidx_demand_length; eassumption | rewrite (cidx_demand_length D _ _ _ H); symmetry; exact IHCIdxListDemand]].
Qed.

Lemma ren_ctype_demand : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec T d,
  RenTypeEnv env1 env2 rho Tvec ->
  CTypeDemand env1 T d ->
  CTypeDemand env2 (ren_cty rho T) (Tvec d).
Proof.
  intros D env1 env2 rho Tvec T d RTE H.
  revert env2 rho Tvec RTE.
  induction H using CTypeDemand_ind_mut with
    (P := fun env1 T d _ => forall env2 rho Tvec, RenTypeEnv env1 env2 rho Tvec -> CTypeDemand env2 (ren_cty rho T) (Tvec d))
    (P0 := fun env1 fs df _ => forall env2 rho Tvec, RenTypeEnv env1 env2 rho Tvec -> CRecordFieldDemand env2 (map (fun '(fn, fg, ft) => (fn, fg, ren_cty rho ft)) fs) (Tvec df))
    (P1 := fun env1 ls dl _ => forall env2 rho Tvec, RenTypeEnv env1 env2 rho Tvec -> CIdxListDemand env2 (map (ren_cidx rho) ls) (Tvec dl));
    intros env2 rho Tvec RTE; cbn.
  - rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ RTE)). constructor.
  - rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ RTE)). constructor.
  - match goal with
    | H1 : CTypeDemand _ ?elem ?de, H2 : CIdxDemand _ ?len ?dl |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hde;
        pose proof (cidx_demand_length D _ _ _ H2) as Hdl;
        rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) de dl Hde Hdl);
        constructor; [apply IHCTypeDemand; exact RTE | eapply ren_cidx_demand; eassumption]
    end.
  - rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ RTE)). constructor.
  - match goal with
    | Hlk : clookup _ ?x = Some ?e, Ha : cty_alpha_eq (cannotation ?e) (CUniv ?lvl) |- _ =>
        destruct (rte_lookup _ _ _ _ RTE x e Hlk) as [e' [Hl' Heq]];
        assert (Hx : x < _) by (eapply clookup_lt_length; exact Hlk);
        rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) x one Hx);
        assert (Hun : cty_alpha_eq (ren_cty (plus (S (rho x))) (cannotation e')) (CUniv lvl))
          by (unfold cty_alpha_eq in *; rewrite Heq; pose proof (ren_cty_alpha_eq D (plus (S x)) _ _ Ha) as H1; exact (ren_cty_alpha_eq D rho _ _ H1));
        apply (ren_cty_eq_CUniv D (plus (S (rho x)))) in Hun;
        eapply CTypeTVar; [exact Hl' | exact Hun]
    end.
  - match goal with
    | H1 : CTypeDemand _ ?inner ?di |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hdi;
        rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ RTE) q di Hdi);
        constructor; apply IHCTypeDemand; exact RTE
    end.
  - match goal with
    | Hlk : clookup _ ?b = Some ?e, Ha : cty_alpha_eq (cannotation ?e) (CBox ?q (CUniv ?lvl)) |- _ =>
        destruct (rte_lookup _ _ _ _ RTE b e Hlk) as [e' [Hl' Heq]];
        assert (Hb : b < _) by (eapply clookup_lt_length; exact Hlk);
        rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ RTE) b one Hb);
        assert (Hbox : cty_alpha_eq (ren_cty (plus (S (rho b))) (cannotation e')) (CBox q (CUniv lvl)))
          by (unfold cty_alpha_eq in *; rewrite Heq; pose proof (ren_cty_alpha_eq D (plus (S b)) _ _ Ha) as H1; exact (ren_cty_alpha_eq D rho _ _ H1));
        apply (ren_cty_eq_CBox_Univ D (plus (S (rho b)))) in Hbox;
        eapply CTypeTUnbox; [exact Hl' | exact Hbox]
    end.
  - match goal with
    | H1 : CTypeDemand _ ?dom ?a, H2 : CTypeDemand (_ :: _) ?cod ?b, Hal : allows _ _ |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Ha;
        pose proof (ctype_demand_length D _ _ _ H2) as Hb; cbn in Hb;
        destruct b as [| b0 b']; cbn in *; [lia |];
        rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) a b' Ha ltac:(lia));
        eapply CTypePi with (a := Tvec a) (b := Tvec_cons Tvec (b0 :: b'));
          [ apply IHCTypeDemand1; exact RTE
          | change (Tvec_cons Tvec (b0 :: b')) with (b0 :: Tvec b');
            apply (IHCTypeDemand2 _ (ren_shift rho) (Tvec_cons Tvec)); apply RenTypeEnv_cons; exact RTE
          | cbn in *; exact Hal ]
    end.
  - match goal with
    | H1 : CTypeDemand _ ?f ?a, H2 : CTypeDemand (_ :: _) ?s ?b, Hal : allows _ _ |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Ha;
        pose proof (ctype_demand_length D _ _ _ H2) as Hb; cbn in Hb;
        destruct b as [| b0 b']; cbn in *; [lia |];
        rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) a b' Ha ltac:(lia));
        eapply CTypeSigma with (a := Tvec a) (b := Tvec_cons Tvec (b0 :: b'));
          [ apply IHCTypeDemand1; exact RTE
          | change (Tvec_cons Tvec (b0 :: b')) with (b0 :: Tvec b');
            apply (IHCTypeDemand2 _ (ren_shift rho) (Tvec_cons Tvec)); apply RenTypeEnv_cons; exact RTE
          | cbn in *; exact Hal ]
    end.
  - constructor; apply IHCTypeDemand; exact RTE.
  - match goal with
    | H1 : CTypeDemand _ ?l ?dl, H2 : CTypeDemand _ ?r ?dr |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hdl;
        pose proof (ctype_demand_length D _ _ _ H2) as Hdr;
        rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) dl dr Hdl Hdr);
        constructor; [apply IHCTypeDemand1 | apply IHCTypeDemand2]; exact RTE
    end.
  - constructor; apply IHCTypeDemand; exact RTE.
  - constructor; apply IHCTypeDemand; exact RTE.
  - rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ RTE)). constructor.
  - match goal with
    | H1 : CTypeDemand _ _ ?dt, Hr : CRecordFieldDemand ?E _ ?drest |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hdt;
        pose proof (proj1 (record_field_and_idx_list_demand_length D) _ _ _ Hr) as Hdr;
        rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) dt drest Hdt Hdr)
    end.
    constructor; [apply IHCTypeDemand | apply IHCTypeDemand0]; exact RTE.
  - rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ RTE)). constructor.
  - match goal with
    | H1 : CIdxDemand _ _ ?di, Hr : CIdxListDemand ?E _ ?drest |- _ =>
        pose proof (cidx_demand_length D _ _ _ H1) as Hdi;
        pose proof (proj2 (record_field_and_idx_list_demand_length D) _ _ _ Hr) as Hdr;
        rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ RTE) di drest Hdi Hdr)
    end.
    constructor; [eapply ren_cidx_demand; eassumption | apply IHCTypeDemand; exact RTE].
Qed.

Lemma ren_cuniverse_level : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec T lvl,
  RenTypeEnv env1 env2 rho Tvec ->
  CUniverseLevel env1 T lvl ->
  CUniverseLevel env2 (ren_cty rho T) lvl.
Proof.
  intros D env1 env2 rho Tvec T lvl RTE H.
  revert env2 rho Tvec RTE.
  induction H using CUniverseLevel_ind_mut with
    (P := fun env1 T lvl _ => forall env2 rho Tvec, RenTypeEnv env1 env2 rho Tvec -> CUniverseLevel env2 (ren_cty rho T) lvl)
    (P0 := fun env1 fs lvl _ => forall env2 rho Tvec, RenTypeEnv env1 env2 rho Tvec -> CRecordFieldLevel env2 (map (fun '(fn, fg, ft) => (fn, fg, ren_cty rho ft)) fs) lvl);
    intros env2 rho Tvec RTE; cbn; try constructor.
  - eapply IHCUniverseLevel; exact RTE.
  - match goal with
    | Hlk : clookup _ ?x = Some ?e, Ha : cty_alpha_eq (cannotation ?e) (CUniv ?lvl) |- _ =>
        destruct (rte_lookup _ _ _ _ RTE x e Hlk) as [e' [Hl' Heq]];
        assert (Hun : cty_alpha_eq (ren_cty (plus (S (rho x))) (cannotation e')) (CUniv lvl))
          by (unfold cty_alpha_eq in *; rewrite Heq; pose proof (ren_cty_alpha_eq D (plus (S x)) _ _ Ha) as H1; exact (ren_cty_alpha_eq D rho _ _ H1));
        apply (ren_cty_eq_CUniv D (plus (S (rho x)))) in Hun;
        eapply CLevelTVar; [exact Hl' | exact Hun]
    end.
  - eapply IHCUniverseLevel; exact RTE.
  - match goal with
    | Hlk : clookup _ ?b = Some ?e, Ha : cty_alpha_eq (cannotation ?e) (CBox ?q (CUniv ?lvl)) |- _ =>
        destruct (rte_lookup _ _ _ _ RTE b e Hlk) as [e' [Hl' Heq]];
        assert (Hbox : cty_alpha_eq (ren_cty (plus (S (rho b))) (cannotation e')) (CBox q (CUniv lvl)))
          by (unfold cty_alpha_eq in *; rewrite Heq; pose proof (ren_cty_alpha_eq D (plus (S b)) _ _ Ha) as H1; exact (ren_cty_alpha_eq D rho _ _ H1));
        apply (ren_cty_eq_CBox_Univ D (plus (S (rho b)))) in Hbox;
        eapply CLevelTUnbox; [exact Hl' | exact Hbox]
    end.
  - eapply IHCUniverseLevel1; exact RTE.
  - apply (IHCUniverseLevel2 _ (ren_shift rho) (Tvec_cons Tvec)).
    apply RenTypeEnv_cons; exact RTE.
  - eapply IHCUniverseLevel1; exact RTE.
  - apply (IHCUniverseLevel2 _ (ren_shift rho) (Tvec_cons Tvec)).
    apply RenTypeEnv_cons; exact RTE.
  - eapply IHCUniverseLevel; exact RTE.
  - eapply IHCUniverseLevel1; exact RTE.
  - eapply IHCUniverseLevel2; exact RTE.
  - eapply IHCUniverseLevel; exact RTE.
  - eapply IHCUniverseLevel; exact RTE.
  - eapply IHCUniverseLevel0; exact RTE.
Qed.

Lemma cidx_eqb_ren : forall (D : JoinDomain) rho (a b : cidx D),
  cidx_eqb a b = true -> cidx_eqb (ren_cidx rho a) (ren_cidx rho b) = true.
Proof.
  intros D rho a. revert rho.
  induction a; intros rho b0 H; destruct b0; cbn in *; try discriminate; try reflexivity.
  - apply Nat.eqb_eq in H. subst. apply Nat.eqb_refl.
  - exact H.
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHa1 _ _ H1), (IHa2 _ _ H2). reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite H1, (IHa _ _ H2). reflexivity.
  - apply Nat.eqb_eq in H. subst. apply Nat.eqb_refl.
  - apply Nat.eqb_eq in H. subst. apply Nat.eqb_refl.
  - apply Nat.eqb_eq in H. subst. apply Nat.eqb_refl.
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [Hs Hl].
    apply Nat.eqb_eq in Hs. rewrite Hs, Nat.eqb_refl, (IHa1 _ _ Hl), (IHa2 _ _ H2). reflexivity.
Qed.

Lemma ren_subty : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec A B,
  RenTypeEnv env1 env2 rho Tvec ->
  Subty env1 A B ->
  Subty env2 (ren_cty rho A) (ren_cty rho B).
Proof.
  intros D env1 env2 rho Tvec A B RTE H.
  revert env2 rho Tvec RTE.
  induction H; intros env2 rho Tvec RTE; cbn.
  - apply SubRefl. apply ren_cty_alpha_eq; exact H.
  - apply SubBox; [exact H | exact (IHSubty _ _ _ RTE)].
  - eapply SubPi; [exact H | exact H0 | exact (IHSubty1 _ _ _ RTE) |].
    apply (IHSubty2 _ (ren_shift rho) (Tvec_cons Tvec)).
    apply RenTypeEnv_cons; exact RTE.
  - eapply SubSigma; [exact H | exact (IHSubty1 _ _ _ RTE) |].
    apply (IHSubty2 _ (ren_shift rho) (Tvec_cons Tvec)).
    apply RenTypeEnv_cons; exact RTE.
  - apply SubSum; [exact (IHSubty1 _ _ _ RTE) | exact (IHSubty2 _ _ _ RTE)].
  - apply SubVec; [apply cidx_eqb_ren; exact H | exact (IHSubty _ _ _ RTE)].
Qed.

Record RenEnv {D : JoinDomain} (env1 env2 : cenv D) (rho : nat -> nat) (Tvec : list (grade D) -> list (grade D)) : Prop := {
  re_type :> RenTypeEnv env1 env2 rho Tvec;
  re_uses : forall x e, clookup env1 x = Some e ->
    exists e', clookup env2 (rho x) = Some e' /\
      ren_cty (plus (S (rho x))) (cannotation e') = ren_cty rho (ren_cty (plus (S x)) (cannotation e)) /\
      vec_zero (S (rho x)) ++ ctype_uses e' = Tvec (vec_zero (S x) ++ ctype_uses e) /\
      (forall row, CTypeDemand (skipn (S x) env1) (cannotation e) row ->
         vec_allows row (ctype_uses e) ->
         exists row', CTypeDemand (skipn (S (rho x)) env2) (cannotation e') row' /\
           vec_allows row' (ctype_uses e'))
}.
Arguments re_type {D env1 env2 rho Tvec} _.
Arguments re_uses {D env1 env2 rho Tvec} _.

Lemma RenEnv_cons_any : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec x T a1 a2,
  RenEnv env1 env2 rho Tvec ->
  a2 = Tvec a1 ->
  RenEnv
    ({| cbinder := x; cannotation := T; ctype_uses := a1 |} :: env1)
    ({| cbinder := x; cannotation := ren_cty rho T; ctype_uses := a2 |} :: env2)
    (ren_shift rho) (Tvec_cons Tvec).
Proof.
  intros D env1 env2 rho Tvec x T a1 a2 RE Ha2. constructor.
  - apply RenTypeEnv_cons; exact (re_type RE).
  - intros [| x'] e Hlkp; cbn in Hlkp.
    + inversion Hlkp; subst; cbn.
      eexists; split; [reflexivity | repeat split].
      * cbn. rewrite !ren_cty_comp. apply ren_cty_ext; intro y; cbn; reflexivity.
      * intros row Hrow Hal. exists (Tvec row). split.
        -- eapply ren_ctype_demand; [exact (re_type RE) | exact Hrow].
        -- apply (rs_allows D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)));
             [eapply ctype_demand_length; eassumption
             |etransitivity; [symmetry; eapply vec_allows_length; exact Hal | eapply ctype_demand_length; exact Hrow]
             |exact Hal].
    + destruct (re_uses RE x' e Hlkp) as [e' [Hl' [Hty [Hvec Htd]]]].
      exists e'. repeat split; [exact Hl' | | | exact Htd].
      * transitivity (ren_cty S (ren_cty (plus (S (rho x'))) (cannotation e')));
          [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
          | rewrite Hty, !ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity ].
      * transitivity (zero :: vec_zero (S (rho x')) ++ ctype_uses e');
          [reflexivity | rewrite Hvec; reflexivity].
Qed.

Lemma iter_ren_shift_S : forall k rho,
  Nat.iter (S k) ren_shift rho = Nat.iter k ren_shift (ren_shift rho).
Proof.
  induction k as [| k IH]; intro rho; cbn; [reflexivity | f_equal; apply IH].
Qed.

Lemma iter_Tvec_cons_S : forall (D : JoinDomain) k (Tvec : list (grade D) -> list (grade D)) u,
  Nat.iter (S k) Tvec_cons Tvec u = Nat.iter k Tvec_cons (Tvec_cons Tvec) u.
Proof.
  intros D k. induction k as [| k IH]; intros Tvec u; cbn; [reflexivity |].
  destruct u as [| a u']; cbn; [reflexivity | f_equal; apply IH].
Qed.

Lemma Tvec_consN_firstn_skipn : forall (D : JoinDomain) k (Tvec : list (grade D) -> list (grade D)) (u : list (grade D)),
  k <= length u ->
  firstn k (Nat.iter k Tvec_cons Tvec u) = firstn k u /\
  skipn k (Nat.iter k Tvec_cons Tvec u) = Tvec (skipn k u).
Proof.
  intros D k. induction k as [| k IH]; intros Tvec u Hle; cbn in *; [split; reflexivity |].
  destruct u as [| a u']; cbn in *; [lia |].
  destruct (IH Tvec u' ltac:(lia)) as [Hf Hs].
  split; [f_equal; exact Hf | exact Hs].
Qed.

Lemma RenSpec_ext_Tvec : forall (D : JoinDomain) rho Tvec1 Tvec2 n1 n2,
  (forall u, Tvec1 u = Tvec2 u) ->
  RenSpec D rho Tvec1 n1 n2 ->
  RenSpec D rho Tvec2 n1 n2.
Proof.
  intros D rho Tvec1 Tvec2 n1 n2 Hext RS. constructor.
  - rewrite <- Hext. exact (rs_zero D _ _ _ _ RS).
  - intros x q Hx. rewrite <- Hext. apply (rs_single D _ _ _ _ RS); assumption.
  - intros u v Hu Hv. rewrite <- !Hext. apply (rs_add D _ _ _ _ RS); assumption.
  - intros q u Hu. rewrite <- !Hext. apply (rs_scale D _ _ _ _ RS); assumption.
  - intros j u v Hj Hu Hv. rewrite <- !Hext. apply (rs_join D _ _ _ _ RS); assumption.
  - intros u v Hu Hv Hal. rewrite <- !Hext. apply (rs_allows D _ _ _ _ RS); assumption.
  - intros u Hu. rewrite <- Hext. apply (rs_len D _ _ _ _ RS); assumption.
  - intros u i Hu Hi. rewrite <- Hext. apply (rs_nth D _ _ _ _ RS); assumption.
  - intros u Hu Hz. rewrite <- Hext. apply (rs_is_zero D _ _ _ _ RS); assumption.
Qed.

Lemma RenTypeEnv_ext_Tvec : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec1 Tvec2,
  (forall u, Tvec1 u = Tvec2 u) ->
  RenTypeEnv env1 env2 rho Tvec1 ->
  RenTypeEnv env1 env2 rho Tvec2.
Proof.
  intros D env1 env2 rho Tvec1 Tvec2 Hext RTE. constructor.
  - eapply RenSpec_ext_Tvec; [exact Hext | exact (rte_spec _ _ _ _ RTE)].
  - exact (rte_lookup _ _ _ _ RTE).
Qed.

Lemma RenEnv_ext_Tvec : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec1 Tvec2,
  (forall u, Tvec1 u = Tvec2 u) ->
  RenEnv env1 env2 rho Tvec1 ->
  RenEnv env1 env2 rho Tvec2.
Proof.
  intros D env1 env2 rho Tvec1 Tvec2 Hext RE. constructor.
  - eapply RenTypeEnv_ext_Tvec; [exact Hext | exact (re_type RE)].
  - intros x e Hlkp. destruct (re_uses RE x e Hlkp) as [e' [Hl' [Hty [Hvec Htd]]]].
    exists e'. repeat split; [exact Hl' | exact Hty | | exact Htd].
    rewrite <- Hext. exact Hvec.
Qed.

Lemma ren_record_extend : forall (D : JoinDomain) (env1 : cenv D) bs fields ext1,
  CRecordExtendEnv env1 bs fields ext1 ->
  forall env2 rho Tvec,
    RenEnv env1 env2 rho Tvec ->
    exists ext2,
      CRecordExtendEnv env2 bs (map (fun '(n0, g0, t0) => (n0, g0, ren_cty rho t0)) fields) ext2 /\
      RenEnv ext1 ext2 (Nat.iter (length fields) ren_shift rho) (Nat.iter (length fields) Tvec_cons Tvec).
Proof.
  intros D env1 bs fields ext1 H.
  induction H; intros env2 rho Tvec RE; cbn.
  - exists env2; split; [constructor | exact RE].
  - pose proof (ren_ctype_demand D _ _ _ _ _ _ (re_type RE) H) as Htd2.
    assert (RE' : RenEnv ({| cbinder := b; cannotation := ft; ctype_uses := row |} :: env)
                         ({| cbinder := b; cannotation := ren_cty rho ft; ctype_uses := Tvec row |} :: env2)
                         (ren_shift rho) (Tvec_cons Tvec)).
    { apply RenEnv_cons_any; [exact RE | reflexivity]. }
    destruct (IHCRecordExtendEnv _ _ _ RE') as [ext2 [Hext RE2]].
    rewrite length_map in *.
    exists ext2; split.
    + econstructor; [exact Htd2 |].
      replace (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0))
                   (map (fun '(n0, g0, t0) => (n0, g0, ren_cty rho t0)) rest))
         with (map (fun '(n0, g0, t0) => (n0, g0, ren_cty (ren_shift rho) t0))
                   (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
      * exact Hext.
      * clear. induction rest as [| [[n0 g0] t0] rest IH]; cbn; [reflexivity |].
        rewrite ren_lift0_cty, IH. reflexivity.
    + rewrite <- iter_ren_shift_S in RE2.
      eapply RenEnv_ext_Tvec; [| exact RE2].
      intro u; symmetry; apply iter_Tvec_cons_S.
Qed.

Lemma ren_record_field_allows : forall (D : JoinDomain) s (fields : list (nat * grade D * cty D)) us rho,
  CRecordFieldAllows s fields us ->
  CRecordFieldAllows s (map (fun '(n0, g0, t0) => (n0, g0, ren_cty rho t0)) fields) us.
Proof.
  intros D s fields us rho H. induction H; cbn; constructor; auto.
Qed.

Lemma ren_lift_iter_cty : forall (D : JoinDomain) k rho (T : cty D),
  ren_cty (Nat.iter k ren_shift rho) (lift_cty 0 k T) = lift_cty 0 k (ren_cty rho T).
Proof.
  intros D k rho T. unfold lift_cty. rewrite !ren_cty_comp. apply ren_cty_ext.
  intro x. clear T. unfold ren_lift.
  destruct (x <? 0) eqn:Ex; [apply Nat.ltb_lt in Ex; lia |].
  destruct (rho x <? 0) eqn:Er; [apply Nat.ltb_lt in Er; lia |].
  induction k as [| k IH]; [cbn; rewrite !Nat.add_0_r; reflexivity |].
  replace (x + S k) with (S (x + k)) by lia.
  change (Nat.iter (S k) ren_shift rho (S (x + k))) with (S (Nat.iter k ren_shift rho (x + k))).
  rewrite IH. lia.
Qed.

Lemma ren_core_derives : forall (D : JoinDomain) (env1 env2 : cenv D) rho Tvec t j,
  RenEnv env1 env2 rho Tvec ->
  CoreDerives env1 t j ->
  CoreDerives env2 (ren_cterm rho t)
    {| cresult_type := ren_cty rho (cresult_type j);
       ccomp_demand := Tvec (ccomp_demand j);
       ctype_demand_row := Tvec (ctype_demand_row j) |}.
Proof.
  intros D env1 env2 rho Tvec t j RE H.
  revert env2 rho Tvec RE.
  induction H using CoreDerives_ind_mut with
    (P := fun env1 t j _ =>
       forall env2 rho Tvec, RenEnv env1 env2 rho Tvec ->
       CoreDerives env2 (ren_cterm rho t)
         {| cresult_type := ren_cty rho (cresult_type j);
            ccomp_demand := Tvec (ccomp_demand j);
            ctype_demand_row := Tvec (ctype_demand_row j) |})
    (P0 := fun env1 fs u v _ =>
       forall env2 rho Tvec, RenEnv env1 env2 rho Tvec ->
       CRecordElemDerives env2
         (map (fun '(fn, fg, ft, fv) => (fn, fg, ren_cty rho ft, ren_cterm rho fv)) fs)
         (Tvec u) (Tvec v));
    intros env2 rho Tvec RE; cbn in *.
  - (* CoreVar *)
    destruct (re_uses RE x e e0) as [e' [Hl' [Heq [Hvec Htd]]]].
    destruct (Htd row c v) as [row' [Hrow' Hal']].
    assert (Hx : x < length env) by (eapply clookup_lt_length; exact e0).
    rewrite (rs_single D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) x one Hx).
    change (zero :: repeat zero x ++ ctype_uses e) with (vec_zero (S x) ++ ctype_uses e).
    change (fun m : nat => S (x + m)) with (plus (S x)).
    rewrite <- Hvec, <- Heq.
    eapply CoreVar; [exact Hl' | exact Hrow' | exact Hal'].
  - (* CoreNatVal *)
    rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE))).
    constructor. eapply ren_cidx_demand; [exact (re_type RE) | exact c].
  - (* CoreBoolVal *)
    rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE))). constructor.
  - (* CoreTypeVal *)
    rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE))).
    constructor; [eapply ren_ctype_demand; [exact (re_type RE) | exact c] |
                  eapply ren_cuniverse_level; [exact (re_type RE) | exact c0]].
  - (* CoreLam *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hu Hv]. cbn in Hu, Hv.
    pose proof (ctype_demand_length D env dom a c) as Ha.
    destruct u as [| u0 u'], v as [| v0 v']; cbn in *; try lia.
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) a v' Ha ltac:(lia)).
    eapply CoreLam with (u := Tvec_cons Tvec (u0 :: u')) (v := Tvec_cons Tvec (v0 :: v')).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + apply (IHCoreDerives _ (ren_shift rho) (Tvec_cons Tvec)).
      apply RenEnv_cons_any; [exact RE | reflexivity].
    + cbn. exact a0.
    + cbn. exact a1.
  - (* CoreApp *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hw Hvf]. cbn in Hw.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hua Hva]. cbn in Hua, Hva.
    pose proof (ctype_demand_length D env dom a_dom c0) as Ha.
    pose proof (ctype_demand_length D _ cod b c1) as Hb. cbn in Hb.
    destruct b as [| b0 b']; cbn in *; [lia |].
    assert (Hz : length z_type = length env).
    { subst z_type. destruct dom; cbn; try exact Hua. destruct arg; cbn; try exact Hua; exact Hva. }
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) w (vec_scale s u_arg) Hw ltac:(rewrite vec_scale_length; exact Hua)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) s u_arg Hua).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) b' (vec_scale r z_type) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hz)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) r z_type Hz).
    eapply CoreApp with (a_dom := Tvec a_dom) (b := Tvec_cons Tvec (b0 :: b')).
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + apply (IHCoreDerives2 _ rho Tvec RE).
    + apply ren_cty_alpha_eq; exact c.
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c0].
    + eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c1].
    + cbn. exact a.
    + intros lvl arg_ty' Hdom Harg.
      destruct dom; cbn in Hdom; try discriminate; inversion Hdom; subst.
      destruct arg; cbn in Harg; destruct Harg as [Harg | [y' [Heqy Heqty]]];
        try discriminate.
      * inversion Heqy; inversion Heqty; subst.
        match goal with
        | |- CUniverseLevel _ (CTVar (rho ?v)) _ =>
            change (CTVar (D := D) (rho v)) with (ren_cty (D := D) rho (CTVar v));
            eapply ren_cuniverse_level; [exact (re_type RE) |];
            apply (c2 lvl (CTVar v)); [reflexivity | right; exists v; split; reflexivity]
        end.
      * inversion Harg; subst. eapply ren_cuniverse_level; [exact (re_type RE) |].
        apply c2 with (lvl := lvl); [reflexivity | left; reflexivity].
    + apply ren_app_result_ty; [| | exact e].
      * intros ->. eapply (ctype_demand_uses_kinds D _ cod (b0 :: b') c1 0); [reflexivity | eapply flags_allow_CNat; reflexivity].
      * intros lvl ->. eapply (ctype_demand_uses_kinds D _ cod (b0 :: b') c1 0); [reflexivity | eapply flags_allow_CUniv; reflexivity].
    + subst z_type. destruct dom; destruct arg; cbn; try reflexivity.
  - (* CoreLet *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hur Hvr]. cbn in Hur, Hvr.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hub Hvb]. cbn in Hub, Hvb.
    destruct u_bod as [| ub0 u_bod'], v_bod as [| vb0 v_bod']; cbn in *; try lia.
    assert (Hza : length (app_type_arg_demand ann rhs u_rhs v_rhs) = length env).
    { destruct ann; cbn; try exact Hur. destruct rhs; cbn; try exact Hur; exact Hvr. }
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_bod' (vec_scale s u_rhs) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hur)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) s u_rhs Hur).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) v_bod' (vec_scale r _) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hza)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) r _ Hza).
    change (ren_cty (fun i : nat => match i with 0 => 0 | S i' => i' end) bod_ty) with (unshift_cty 0 bod_ty).
    rewrite ren_unshift_cty; [| exact e].
    replace (Tvec (app_type_arg_demand ann rhs u_rhs v_rhs))
       with (app_type_arg_demand (ren_cty rho ann) (ren_cterm rho rhs) (Tvec u_rhs) (Tvec v_rhs))
      by (destruct ann; destruct rhs; cbn; reflexivity).
    eapply CoreLet with (a_ann := Tvec a_ann) (u_bod := Tvec_cons Tvec (ub0 :: u_bod')) (v_bod := Tvec_cons Tvec (vb0 :: v_bod')).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + apply ren_cty_alpha_eq; exact c0.
    + apply (IHCoreDerives2 _ (ren_shift rho) (Tvec_cons Tvec)).
      apply RenEnv_cons_any; [exact RE | reflexivity].
    + cbn. exact a.
    + cbn. exact a0.
    + rewrite ren_cty_uses_var_shift; exact e.
  - (* CorePair *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hul Hvl]. cbn in Hul.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hur Hvr]. cbn in Hur.
    pose proof (ctype_demand_length D env fst_ty a c) as Ha.
    pose proof (ctype_demand_length D _ snd_ty b c0) as Hb. cbn in Hb.
    destruct b as [| b0 b']; cbn in *; [lia |].
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_l u_r Hul Hur).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) a b' Ha ltac:(lia)).
    eapply CorePair with (a := Tvec a) (b := Tvec_cons Tvec (b0 :: b'))
                         (exp_snd := ren_cty rho exp_snd).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c0].
    + cbn. exact a0.
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + apply ren_cty_alpha_eq; exact c1.
    + apply (IHCoreDerives2 _ rho Tvec RE).
    + apply ren_app_result_ty; [| | exact e].
      * intros ->. eapply (ctype_demand_uses_kinds D _ snd_ty (b0 :: b') c0 0); [reflexivity | eapply flags_allow_CNat; reflexivity].
      * intros lvl ->. eapply (ctype_demand_uses_kinds D _ snd_ty (b0 :: b') c0 0); [reflexivity | eapply flags_allow_CUniv; reflexivity].
    + apply ren_cty_alpha_eq; exact c2.
  - (* CoreLetPair *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hw Hvp]. cbn in Hw.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hub Hvb]. cbn in Hub.
    pose proof (ctype_demand_length D env A a c) as Ha.
    pose proof (ctype_demand_length D _ B b c0) as Hb. cbn in Hb.
    pose proof (ctype_demand_length D _ mot v_mot c1) as Hvm. cbn in Hvm.
    destruct b as [| b0 b']; cbn in *; [lia |].
    destruct v_mot as [| vm0 v_mot']; cbn in *; [lia |].
    destruct u_b as [| ub0 [| ub1 u_b']]; cbn in *; try lia.
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_b' (vec_scale s w) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hw)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) s w Hw).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) v_mot' (vec_scale kappa w) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hw)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) kappa w Hw).
    subst res_ty. rewrite ren_spec_pair_subj.
    2:{ destruct pr; cbn in *; try exact y0; try exact I.
        destruct (term_as_cidx pr1), (term_as_cidx pr2); try exact y0.
        eapply (ctype_demand_uses_kinds D _ mot (vm0 :: v_mot') c1 0); [reflexivity | eapply flags_allow_CSigma; reflexivity]. }
    eapply CoreLetPair with (a := Tvec a) (b := Tvec_cons Tvec (b0 :: b'))
      (v_mot := Tvec_cons Tvec (vm0 :: v_mot'))
      (u_b := Tvec_cons (Tvec_cons Tvec) (ub0 :: ub1 :: u_b'))
      (v_b := Tvec_cons (Tvec_cons Tvec) v_b)
      (act_mot := ren_cty (ren_shift (ren_shift rho)) act_mot).
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c0].
    + change (tl (Tvec_cons Tvec (b0 :: b'))) with (Tvec b').
      change (CSigma z r (ren_cty rho A) (ren_cty (ren_shift rho) B))
        with (ren_cty rho (CSigma z r A B)).
      rewrite <- (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) a b' Ha ltac:(lia)).
      eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c1].
    + cbn. exact a0.
    + apply (IHCoreDerives2 _ (ren_shift (ren_shift rho)) (Tvec_cons (Tvec_cons Tvec))).
      apply RenEnv_cons_any; [apply RenEnv_cons_any; [exact RE | reflexivity] | reflexivity].
    + reflexivity.
    + subst exp_mot. rewrite <- ren_spec_pair_body. apply ren_cty_alpha_eq; exact c2.
    + cbn. exact a1.
    + cbn. exact a2.
    + destruct pr; cbn in *; try exact I; try (rewrite ren_cty_uses_var_shift; exact y0).
      destruct pr1, pr2; cbn in *; try exact I; rewrite ren_cty_uses_var_shift; exact y0.
    + reflexivity.
  - (* CorePromote *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hu Hv]. cbn in Hu.
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) q u Hu).
    constructor. apply (IHCoreDerives _ rho Tvec RE).
  - (* CoreLetBox *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hzb Hvz]. cbn in Hzb, Hvz.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hw Hbw]. cbn in Hw, Hbw.
    pose proof (ctype_demand_length D _ mot v_mot c0) as Hvm. cbn in Hvm.
    destruct v_mot as [| vm0 v_mot']; cbn in *; [lia |].
    destruct w as [| w0 w']; cbn in *; [lia |].
    destruct bw as [| bw0 bw']; cbn in *; [lia |].
    assert (Hzty : length z_ty = length env).
    { subst z_ty. destruct box_term; cbn; try exact Hzb. destruct box_term; cbn; try exact Hzb.
      rewrite vec_scale_length; exact Hvz. }
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) w' z_b ltac:(lia) Hzb).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) v_mot' (vec_scale kappa z_ty) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hzty)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) kappa z_ty Hzty).
    subst res_ty. rewrite ren_spec_box_subj.
    2:{ destruct box_term; cbn in *; try exact y; try exact I.
        destruct box_term; cbn in *; try exact y; try exact I.
        - inversion H; subst. match goal with | Hsub : CoreDerives _ (CNatVal _) _ |- _ => inversion Hsub; subst end.
          eapply (ctype_demand_uses_kinds D _ mot (vm0 :: v_mot') c0 0); [reflexivity | eapply flags_allow_CBox_Nat; reflexivity].
        - inversion H; subst. match goal with | Hsub : CoreDerives _ (CTypeVal _) _ |- _ => inversion Hsub; subst end.
          eapply (ctype_demand_uses_kinds D _ mot (vm0 :: v_mot') c0 0); [reflexivity | eapply flags_allow_CBox_Univ; reflexivity]. }
    eapply CoreLetBox with (a := Tvec a) (v_mot := Tvec_cons Tvec (vm0 :: v_mot'))
      (w := Tvec_cons Tvec (w0 :: w')) (bw := Tvec_cons Tvec (bw0 :: bw'))
      (act_mot := ren_cty (ren_shift rho) act_mot).
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + change (CBox q (ren_cty rho A)) with (ren_cty rho (CBox q A)).
      eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c0].
    + cbn. exact a0.
    + apply (IHCoreDerives2 _ (ren_shift rho) (Tvec_cons Tvec)).
      apply RenEnv_cons_any; [exact RE | reflexivity].
    + reflexivity.
    + subst exp_mot. rewrite <- ren_spec_box_body. apply ren_cty_alpha_eq; exact c1.
    + cbn. exact a1.
    + cbn. exact a2.
    + destruct box_term; cbn in *; try exact I; try (rewrite ren_cty_uses_var_shift; exact y).
      destruct box_term; cbn in *; try exact I; rewrite ren_cty_uses_var_shift; exact y.
    + reflexivity.
    + subst z_ty. destruct box_term; cbn; try reflexivity.
      destruct box_term; cbn; try reflexivity.
      match goal with
      | |- Tvec (vec_scale ?g0 vz) = vec_scale ?g0 (Tvec vz) =>
          rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) g0 vz Hvz); reflexivity
      end.
  - (* CoreInl *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hu Ha]. cbn in Hu, Ha.
    pose proof (ctype_demand_length D env rhs_ty b c) as Hb.
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) a b Ha Hb).
    constructor; [apply (IHCoreDerives _ rho Tvec RE) | eapply ren_ctype_demand; [exact (re_type RE) | exact c]].
  - (* CoreInr *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hu Hb]. cbn in Hu, Hb.
    pose proof (ctype_demand_length D env lhs_ty a c) as Ha.
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) a b Ha Hb).
    constructor; [eapply ren_ctype_demand; [exact (re_type RE) | exact c] | apply (IHCoreDerives _ rho Tvec RE)].
  - (* CoreMatchSum *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hw Hvs]. cbn in Hw.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hu1 Hb1]. cbn in Hu1.
    pose proof (core_derives_lengths D _ _ _ H1) as [Hu2 Hb2]. cbn in Hu2.
    pose proof (ctype_demand_length D env A a c) as Ha.
    pose proof (ctype_demand_length D env B b c0) as Hb.
    pose proof (ctype_demand_length D _ mot v_mot c1) as Hvm. cbn in Hvm.
    destruct u1 as [| u1_0 u1'], u2 as [| u2_0 u2'], v_mot as [| vm0 v_mot']; cbn in *; try lia.
    assert (Hubr : length u_br = length env)
      by (rewrite (BranchVec_length D u1' u2' u_br); [lia | lia | exact b0]).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) (vec_scale s w) u_br ltac:(rewrite vec_scale_length; exact Hw) Hubr).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) s w Hw).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) v_mot' (vec_scale kappa w) ltac:(lia) ltac:(rewrite vec_scale_length; exact Hw)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) kappa w Hw).
    subst res_ty. rewrite ren_spec_sum_subj.
    2:{ destruct scrut; cbn in *; try exact y0; try exact I.
        - destruct (term_as_cidx scrut) eqn:Hv; [| exact y0].
          destruct A; try (apply cty_uses_var_implies_sum_ok; [constructor | exact y0]).
          eapply (ctype_demand_sum_ok D _ mot (vm0 :: v_mot') c1 true 0 []).
          split; [reflexivity | split; [exists {| cbinder := 0; cannotation := CSum CNat B; ctype_uses := vec_add a b |}, CNat, (ren_cty (plus 1) B); repeat split; reflexivity | intros cc Hc; destruct cc; discriminate]].
        - destruct (term_as_cidx scrut) eqn:Hv; [| exact y0].
          destruct B; try (apply cty_uses_var_implies_sum_ok; [constructor | exact y0]).
          eapply (ctype_demand_sum_ok D _ mot (vm0 :: v_mot') c1 false 0 []).
          split; [reflexivity | split; [exists {| cbinder := 0; cannotation := CSum A CNat; ctype_uses := vec_add a b |}, (ren_cty (plus 1) A), CNat; repeat split; reflexivity | intros cc Hc; destruct cc; discriminate]]. }
    eapply CoreMatchSum with (a := Tvec a) (b := Tvec b)
      (v_mot := Tvec_cons Tvec (vm0 :: v_mot'))
      (u1 := Tvec_cons Tvec (u1_0 :: u1')) (b1 := Tvec_cons Tvec b1)
      (u2 := Tvec_cons Tvec (u2_0 :: u2')) (b2 := Tvec_cons Tvec b2).
    + exact n.
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c0].
    + change (CSum (ren_cty rho A) (ren_cty rho B)) with (ren_cty rho (CSum A B)).
      rewrite <- (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) a b Ha Hb).
      eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c1].
    + cbn. exact a0.
    + apply (IHCoreDerives2 _ (ren_shift rho) (Tvec_cons Tvec)).
      apply RenEnv_cons_any; [exact RE | reflexivity].
    + apply (IHCoreDerives3 _ (ren_shift rho) (Tvec_cons Tvec)).
      apply RenEnv_cons_any; [exact RE | reflexivity].
    + rewrite <- ren_spec_sum_branch. apply ren_cty_alpha_eq; exact c2.
    + rewrite <- ren_spec_sum_branch. apply ren_cty_alpha_eq; exact c3.
    + cbn. exact a1.
    + cbn. exact a2.
    + cbn. eapply BranchVec_ren; [exact (rte_spec _ _ _ _ (re_type RE)) | lia | lia | exact b0].
    + destruct scrut; cbn in *; try exact I; try (rewrite ren_cty_uses_var_shift; exact y0).
      * destruct scrut; cbn in *; try (rewrite ren_cty_uses_var_shift; exact y0);
          (destruct A; cbn in *; try exact I; rewrite ren_cty_uses_var_shift; exact y0).
      * destruct scrut; cbn in *; try (rewrite ren_cty_uses_var_shift; exact y0);
          (destruct B; cbn in *; try exact I; rewrite ren_cty_uses_var_shift; exact y0).
    + reflexivity.
  - (* CoreIf *)
    pose proof (core_derives_lengths D _ _ _ H) as [Huc Hvc]. cbn in Huc.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hu1 Hv1]. cbn in Hu1, Hv1.
    pose proof (core_derives_lengths D _ _ _ H1) as [Hu2 Hv2]. cbn in Hu2, Hv2.
    assert (Hubr : length u_br = length env)
      by (rewrite (BranchVec_length D u1 u2 u_br); [lia | lia | exact b]).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_c u_br Huc Hubr).
    eapply CoreIf.
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + apply (IHCoreDerives2 _ rho Tvec RE).
    + apply (IHCoreDerives3 _ rho Tvec RE).
    + apply ren_cty_alpha_eq; exact c.
    + eapply BranchVec_ren; [exact (rte_spec _ _ _ _ (re_type RE)) | exact Hu1 | exact Hu2 | exact b].
    + eapply BranchVec_ren; [exact (rte_spec _ _ _ _ (re_type RE)) | exact Hv1 | exact Hv2 | exact b0].
  - (* CoreRecordMk *)
    replace (map (fun '(fn, fg, ft) => (fn, fg, ren_cty rho ft))
                 (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields))
       with (map (fun '(fn, fg, ft, _) => (fn, fg, ft))
                 (map (fun '(fn, fg, ft, fv) => (fn, fg, ren_cty rho ft, ren_cterm rho fv)) fields)).
    + constructor. apply IHCoreDerives; exact RE.
    + clear. induction fields as [| [[[fn fg] ft] fv] rest IH]; cbn; [reflexivity | f_equal; exact IH].
  - (* CoreMatchRecord *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hw Hvs]. cbn in Hw.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hub Hvb]. cbn in Hub.
    pose proof (record_extend_length D _ _ _ _ c0) as Hextlen.
    rewrite Hextlen in Hub.
    destruct (ren_record_extend D _ _ _ _ c0 _ _ _ RE) as [ext2 [Hext2 RE2]].
    destruct (Tvec_consN_firstn_skipn D (length fields) Tvec u_b ltac:(lia)) as [Hfirst Hskip].
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) (vec_scale s w) (skipn (length fields) u_b)
              ltac:(rewrite vec_scale_length; exact Hw) ltac:(rewrite length_skipn, Hub; lia)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) s w Hw).
    rewrite <- Hskip.
    replace (skipn (length fields) (Nat.iter (length fields) Tvec_cons Tvec u_b))
       with (skipn (length (map (fun '(n0, g0, t0) => (n0, g0, ren_cty rho t0)) fields))
                   (Nat.iter (length fields) Tvec_cons Tvec u_b))
      by (rewrite length_map; reflexivity).
    eapply CoreMatchRecord with (fields := map (fun '(n0, g0, t0) => (n0, g0, ren_cty rho t0)) fields)
      (body_env := ext2) (v_b := Nat.iter (length fields) Tvec_cons Tvec v_b).
    + exact n.
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
    + rewrite length_map; exact e.
    + exact Hext2.
    + rewrite e. apply (IHCoreDerives2 _ (Nat.iter (length fields) ren_shift rho) (Nat.iter (length fields) Tvec_cons Tvec) RE2).
    + rewrite length_map, <- ren_lift_iter_cty. apply ren_cty_alpha_eq; exact c1.
    + rewrite length_map, Hfirst. apply ren_record_field_allows; exact c2.
  - (* CoreSubgrade *)
    eapply CoreSubgrade.
    + apply (IHCoreDerives _ rho Tvec RE).
    + eapply ren_subty; [exact (re_type RE) | exact s].
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c].
  - (* CoreFix *)
    pose proof (core_derives_lengths D _ _ _ H) as [Hus Hvs]. cbn in Hus.
    pose proof (core_derives_lengths D _ _ _ H0) as [Hub Hvb]. cbn in Hub.
    pose proof (core_derives_lengths D _ _ _ H1) as [Hust Hvst]. cbn in Hust.
    pose proof (ctype_demand_length D _ mot v_mot c) as Hvm. cbn in Hvm.
    destruct v_mot as [| vm0 v_mot']; cbn in Hvm; [lia |].
    destruct u_st as [| us0 [| us1 u_st']]; cbn in Hust; try lia.
    change (tl (vm0 :: v_mot')) with v_mot' in *.
    change (nth_grade (vm0 :: v_mot') 0) with vm0 in *.
    change (tl (tl (us0 :: us1 :: u_st'))) with u_st' in *.
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_s (vec_add u_b (vec_scale s_rec u_st'))
              Hus ltac:(rewrite vec_add_length; [exact Hub | rewrite vec_scale_length; lia])).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_b (vec_scale s_rec u_st')
              Hub ltac:(rewrite vec_scale_length; lia)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) s_rec u_st' ltac:(lia)).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) v_mot' (vec_scale vm0 u_s)
              ltac:(lia) ltac:(rewrite vec_scale_length; exact Hus)).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) vm0 u_s Hus).
    subst res_ty. rewrite ren_spec_fix_subj.
    2:{ destruct (term_as_cidx scrut); [| exact y].
        eapply (ctype_demand_uses_kinds D _ mot (vm0 :: v_mot') c 0); [reflexivity | eapply flags_allow_CNat; reflexivity]. }
    eapply CoreFix with (v_mot := Tvec_cons Tvec (vm0 :: v_mot'))
      (u_st := Tvec_cons (Tvec_cons Tvec) (us0 :: us1 :: u_st'))
      (v_st := Tvec_cons (Tvec_cons Tvec) v_st).
    + apply (IHCoreDerives1 _ rho Tvec RE).
    + change (CNat (D := D)) with (ren_cty (D := D) rho CNat).
      rewrite <- (rs_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE))).
      eapply ren_ctype_demand; [apply RenTypeEnv_cons; exact (re_type RE) | exact c].
    + apply (IHCoreDerives2 _ rho Tvec RE).
    + pose proof (ren_subst_cidx_in_cty_0 D mot (CIdxLit 0) rho) as Hsub0. cbn in Hsub0.
      rewrite <- Hsub0; [apply ren_cty_alpha_eq; exact c0 |].
      eapply (ctype_demand_uses_kinds D _ mot (vm0 :: v_mot') c 0); [reflexivity | eapply flags_allow_CNat; reflexivity].
    + apply (IHCoreDerives3 _ (ren_shift (ren_shift rho)) (Tvec_cons (Tvec_cons Tvec))).
      change (CNat (D := D)) with (ren_cty (D := D) rho CNat).
      apply RenEnv_cons_any; [| reflexivity].
      apply RenEnv_cons_any; [exact RE | symmetry; apply (rs_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)))].
    + rewrite <- ren_spec_fix_step; [apply ren_cty_alpha_eq; exact c1 |].
      eapply (ctype_demand_uses_kinds D _ mot (vm0 :: v_mot') c 0); [reflexivity | eapply flags_allow_CNat; reflexivity].
    + cbn. exact a.
    + cbn. exact a0.
    + cbn. unfold fix_recurrence_ok in *.
      destruct (vec_is_zero u_st') eqn:Hz.
      * rewrite (rs_is_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) u_st' ltac:(lia) Hz). exact I.
      * destruct (vec_is_zero (Tvec u_st')); [exact I | exact f].
    + destruct scrut; cbn; try exact I; rewrite ren_cty_uses_var_shift; exact y.
    + reflexivity.
  - (* CRecordElemNil *)
    rewrite (rs_zero D _ _ _ _ (rte_spec _ _ _ _ (re_type RE))). constructor.
  - (* CRecordElemCons *)
    pose proof (core_derives_lengths D _ _ _ H) as [Huv Hvv]. cbn in Huv.
    pose proof (ctype_demand_length D env ft dt c0) as Hdt.
    assert (Hur : length u_rest = length env /\ length v_rest = length env) by
      (match goal with
       | Hrec : CRecordElemDerives _ _ _ _ |- _ =>
           exact (record_elem_derives_lengths D _ _ _ _ Hrec)
       end).
    destruct Hur as [Hu_r Hv_r].
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) (vec_scale fg u_v) u_rest
              ltac:(rewrite vec_scale_length; exact Huv) Hu_r).
    rewrite (rs_scale D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) fg u_v Huv).
    rewrite (rs_add D _ _ _ _ (rte_spec _ _ _ _ (re_type RE)) dt v_rest Hdt Hv_r).
    econstructor.
    + apply (IHCoreDerives _ rho Tvec RE).
    + apply ren_cty_alpha_eq; exact c.
    + eapply ren_ctype_demand; [exact (re_type RE) | exact c0].
    + apply (IHCoreDerives0 _ rho Tvec RE).
Qed.

(* Concrete Weakening and Exchange *)

Definition weaken_rho (k x : nat) : nat :=
  if x <? k then x else S x.

Fixpoint weaken_cenv {D : JoinDomain} (b : cbinding D) (env_a env_b : cenv D) : cenv D :=
  match env_a with
  | [] => b :: env_b
  | e :: rest =>
      {| cbinder := cbinder e;
         cannotation := lift_cty (length rest) 1 (cannotation e);
         ctype_uses := vec_insert_zero (length rest) (ctype_uses e) |} :: weaken_cenv b rest env_b
  end.

Lemma weaken_cenv_length : forall (D : JoinDomain) (b : cbinding D) env_a env_b,
  length (weaken_cenv b env_a env_b) = S (length env_a + length env_b).
Proof.
  intros D b env_a env_b. induction env_a as [| e rest IH]; cbn; [reflexivity | lia].
Qed.

Lemma vec_insert_zero_spec : forall (D : JoinDomain) k,
  RenSpec D (weaken_rho k) (vec_insert_zero k) (k + 0) (S k) (* helper below *).
Abort.

Lemma vec_insert_zero_length_gen : forall (D : JoinDomain) k (u : list (grade D)),
  k <= length u -> length (vec_insert_zero k u) = S (length u).
Proof.
  intros D k. induction k as [| k IH]; intros u Hle; cbn; [reflexivity |].
  destruct u as [| a u']; cbn in *; [lia | f_equal; apply IH; lia].
Qed.

Lemma vec_insert_zero_zero : forall (D : JoinDomain) k n,
  k <= n -> vec_insert_zero (D := D) k (vec_zero n) = vec_zero (S n).
Proof.
  intros D k. induction k as [| k IH]; intros n Hle; cbn; [reflexivity |].
  destruct n as [| n']; [lia | cbn; f_equal; apply IH; lia].
Qed.

Lemma vec_insert_zero_single : forall (D : JoinDomain) k n x q,
  k <= n -> x < n ->
  vec_insert_zero (D := D) k (vec_single n x q) = vec_single (S n) (weaken_rho k x) q.
Proof.
  intros D k. induction k as [| k IH]; intros n x q Hkn Hxn; unfold weaken_rho in *; cbn.
  - reflexivity.
  - destruct n as [| n']; [lia |].
    destruct x as [| x']; cbn.
    + rewrite vec_insert_zero_zero; [reflexivity | lia].
    + destruct (S x' <? S k) eqn:Hsk; destruct (x' <? k) eqn:Hxk;
        try (apply Nat.ltb_lt in Hsk; apply Nat.ltb_ge in Hxk; lia);
        try (apply Nat.ltb_ge in Hsk; apply Nat.ltb_lt in Hxk; lia);
        cbn; f_equal; rewrite (IH n' x' q ltac:(lia) ltac:(lia));
        unfold weaken_rho; rewrite Hxk; reflexivity.
Qed.

Lemma vec_insert_zero_add : forall (D : JoinDomain) k (u v : list (grade D)),
  k <= length u -> length u = length v ->
  vec_insert_zero k (vec_add u v) = vec_add (vec_insert_zero k u) (vec_insert_zero k v).
Proof.
  intros D k. induction k as [| k IH]; intros u v Hk Hlen; cbn.
  - rewrite (add_zero D). reflexivity.
  - destruct u as [| a u'], v as [| b v']; cbn in *; try lia; f_equal; apply IH; lia.
Qed.

Lemma vec_insert_zero_scale : forall (D : JoinDomain) k (q : grade D) u,
  k <= length u ->
  vec_insert_zero k (vec_scale q u) = vec_scale q (vec_insert_zero k u).
Proof.
  intros D k. induction k as [| k IH]; intros q u Hk; cbn.
  - rewrite (mul_zero_r D). reflexivity.
  - destruct u as [| a u']; cbn in *; [lia | f_equal; apply IH; lia].
Qed.

Lemma vec_insert_zero_join : forall (D : JoinDomain) k (j : grade D -> grade D -> grade D) u v,
  j zero zero = zero ->
  k <= length u -> length u = length v ->
  vec_insert_zero k (vec_join j u v) = vec_join j (vec_insert_zero k u) (vec_insert_zero k v).
Proof.
  intros D k j u v Hzz Hk Hlen. revert u v Hk Hlen.
  induction k as [| k IH]; intros u v Hk Hlen; cbn.
  - rewrite Hzz; reflexivity.
  - destruct u as [| a u'], v as [| b v']; cbn in *; try lia; f_equal; apply IH; lia.
Qed.

Lemma join_zero_zero_of_erasure : forall (D : JoinDomain),
  ErasureDomain D ->
  forall j, grade_join D = Some j -> j zero zero = zero.
Proof.
  intros D ED j Hj.
  apply (erasure_allows_zero_eq D ED).
  apply (join_least D j Hj); apply allows_refl.
Qed.

Lemma vec_insert_zero_allows : forall (D : JoinDomain) k (u v : list (grade D)),
  k <= length u -> length u = length v ->
  vec_allows u v -> vec_allows (vec_insert_zero k u) (vec_insert_zero k v).
Proof.
  intros D k. induction k as [| k IH]; intros u v Hk Hlen Hal; cbn.
  - constructor; [apply allows_refl | exact Hal].
  - destruct Hal; cbn in *; [lia | constructor; [exact H | apply IH; lia || assumption]].
Qed.

Lemma vec_insert_zero_nth : forall (D : JoinDomain) k u i,
  k <= length u -> i < length u ->
  nth_grade (D := D) (vec_insert_zero k u) (weaken_rho k i) = nth_grade u i.
Proof.
  intros D k. induction k as [| k IH]; intros u i Hk Hi; unfold weaken_rho in *; cbn.
  - reflexivity.
  - destruct u as [| a u']; cbn in *; [lia |].
    destruct i as [| i']; cbn; [reflexivity |].
    destruct (S i' <? S k) eqn:Hsk; destruct (i' <? k) eqn:E;
      try (apply Nat.ltb_lt in Hsk; apply Nat.ltb_ge in E; lia);
      try (apply Nat.ltb_ge in Hsk; apply Nat.ltb_lt in E; lia);
      cbn; specialize (IH u' i' ltac:(lia) ltac:(lia));
      unfold weaken_rho in IH; rewrite E in IH; exact IH.
Qed.

Lemma vec_insert_zero_is_zero : forall (D : JoinDomain) k (u : list (grade D)),
  vec_is_zero u = true -> vec_is_zero (vec_insert_zero k u) = true.
Proof.
  intros D k. induction k as [| k IH]; intros u Hz; unfold vec_is_zero in *; cbn in *.
  - rewrite andb_true_iff; split; [destruct (grade_eqb_spec D zero zero) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity] | exact Hz].
  - destruct u as [| a u']; cbn in *;
      [rewrite andb_true_r; destruct (grade_eqb_spec D zero zero) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity] |].
    rewrite andb_true_iff in Hz |- *; destruct Hz as [Ha Hu']; split; [exact Ha | apply IH; exact Hu'].
Qed.

Lemma weaken_RenSpec : forall (D : JoinDomain) k n,
  (forall j, grade_join D = Some j -> j zero zero = zero) ->
  k <= n ->
  RenSpec D (weaken_rho k) (vec_insert_zero k) n (S n).
Proof.
  intros D k n Hjz Hkn. constructor.
  - apply vec_insert_zero_zero; exact Hkn.
  - intros x q Hx. apply vec_insert_zero_single; assumption.
  - intros u v Hu Hv. apply vec_insert_zero_add; lia.
  - intros q u Hu. apply vec_insert_zero_scale; lia.
  - intros j u v Hj Hu Hv. apply vec_insert_zero_join; [apply Hjz; exact Hj | lia | lia].
  - intros u v Hu Hv Hal. apply vec_insert_zero_allows; lia || assumption.
  - intros u Hu. rewrite vec_insert_zero_length_gen; lia.
  - intros u i Hu Hi. apply vec_insert_zero_nth; lia.
  - intros u Hu Hz. apply vec_insert_zero_is_zero; exact Hz.
Qed.

Lemma lift_as_weaken_rho : forall (D : JoinDomain) k (T : cty D),
  lift_cty k 1 T = ren_cty (weaken_rho k) T.
Proof.
  intros D k T. unfold lift_cty. apply ren_cty_ext.
  intro x. unfold ren_lift, weaken_rho. destruct (x <? k); [reflexivity | lia].
Qed.

Lemma weaken_skipn_comm : forall (D : JoinDomain) (b : cbinding D) env_a env_b x,
  skipn (S (weaken_rho (length env_a) x)) (weaken_cenv b env_a env_b) =
  match le_lt_dec (length env_a) x with
  | left _ => skipn (S x) (env_a ++ env_b)
  | right _ =>
      let suffix := skipn (S x) env_a in
      weaken_cenv b suffix env_b
  end.
Proof.
  intros D b env_a. induction env_a as [| e0 rest IH]; intros env_b x.
  - unfold weaken_rho; cbn [length weaken_cenv app].
    destruct (x <? 0) eqn:E; [apply Nat.ltb_lt in E; lia |].
    destruct (le_lt_dec 0 x); [reflexivity | lia].
  - destruct x as [| x'].
    + unfold weaken_rho; cbn [length weaken_cenv skipn].
      destruct (0 <? S (length rest)) eqn:E; [| apply Nat.ltb_ge in E; lia].
      destruct (le_lt_dec (S (length rest)) 0); [lia | reflexivity].
    + unfold weaken_rho in *; cbn [length weaken_cenv].
      destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
        try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
        try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia).
      * destruct (le_lt_dec (S (length rest)) (S x')); [apply Nat.ltb_lt in Hsx; lia |].
        cbn [skipn]. specialize (IH env_b x'). rewrite Hxlt in IH.
        destruct (le_lt_dec (length rest) x'); [lia | exact IH].
      * destruct (le_lt_dec (S (length rest)) (S x')); [| apply Nat.ltb_ge in Hsx; lia].
        cbn [skipn app]. specialize (IH env_b x'). rewrite Hxlt in IH.
        destruct (le_lt_dec (length rest) x'); [exact IH | lia].
Qed.

Lemma weaken_RenEnv : forall (D : JoinDomain) (b : cbinding D) env_a env_b,
  (forall j, grade_join D = Some j -> j zero zero = zero) ->
  RenEnv (env_a ++ env_b) (weaken_cenv b env_a env_b)
    (weaken_rho (length env_a)) (vec_insert_zero (length env_a)).
Proof.
  intros D b env_a env_b Hjz. induction env_a as [| e0 rest IH].
  - cbn. constructor.
    + constructor.
      * apply weaken_RenSpec; [exact Hjz | lia].
      * intros x e Hl. exists e; split; [exact Hl |].
        rewrite ren_cty_comp. apply ren_cty_ext; intro y; unfold weaken_rho; cbn; reflexivity.
    + intros x e Hl. exists e; repeat split; [exact Hl | |].
      * rewrite ren_cty_comp. apply ren_cty_ext; intro y; unfold weaken_rho; cbn; reflexivity.
      * intros row Hrow Hal; exists row; split; assumption.
  - constructor.
    + constructor.
      * rewrite weaken_cenv_length, length_app; apply weaken_RenSpec; [exact Hjz | cbn; lia].
      * intros [| x'] e Hl; cbn in Hl.
        -- inversion Hl; subst; cbn.
           eexists; split; [reflexivity |].
           cbn [cannotation].
           rewrite lift_as_weaken_rho, !ren_cty_comp.
           apply ren_cty_ext; intro y; unfold weaken_rho; cbn.
           destruct (y <? length rest) eqn:E; rw_nat_bool; reflexivity.
        -- destruct (rte_lookup _ _ _ _ (re_type IH) x' e Hl) as [e' [Hl' Heq]].
           unfold weaken_rho in *; cbn.
           destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
             try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
             try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia).
           ++ exists e'; split; [exact Hl' |].
              transitivity (ren_cty S (ren_cty (plus (S x')) (cannotation e')));
                [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
                | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn;
                  destruct (S x' + y <? length rest) eqn:E1; rw_nat_bool; reflexivity ].
           ++ exists e'; split; [exact Hl' |].
              transitivity (ren_cty S (ren_cty (plus (S (S x'))) (cannotation e')));
                [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
                | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn;
                  destruct (S x' + y <? length rest) eqn:E1; rw_nat_bool; reflexivity ].
    + intros [| x'] e Hl; cbn in Hl.
      * inversion Hl; subst; cbn.
        eexists; repeat split.
        -- cbn [cannotation]. rewrite lift_as_weaken_rho, !ren_cty_comp.
           apply ren_cty_ext; intro y; unfold weaken_rho; cbn.
           destruct (y <? length rest) eqn:E; rw_nat_bool; reflexivity.
        -- intros row Hrow Hal. exists (vec_insert_zero (length rest) row). split.
           ++ rewrite lift_as_weaken_rho. eapply ren_ctype_demand; [exact (re_type IH) | exact Hrow].
           ++ apply vec_insert_zero_allows;
                [pose proof (ctype_demand_length D _ _ _ Hrow); rewrite length_app in *; lia
                |pose proof (ctype_demand_length D _ _ _ Hrow); pose proof (vec_allows_length D _ _ Hal); lia
                |exact Hal].
      * destruct (re_uses IH x' e Hl) as [e' [Hl' [Heq [Hvec Htd]]]].
        unfold weaken_rho in *; cbn.
        destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
          try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
          try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia).
        -- exists e'; repeat split; [exact Hl' | | | exact Htd].
           ++ transitivity (ren_cty S (ren_cty (plus (S x')) (cannotation e')));
                [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
                | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn;
                  destruct (S x' + y <? length rest) eqn:E1; rw_nat_bool; reflexivity ].
           ++ transitivity (zero :: vec_zero (S x') ++ ctype_uses e');
                [reflexivity | rewrite Hvec; reflexivity].
        -- exists e'; repeat split; [exact Hl' | | | exact Htd].
           ++ transitivity (ren_cty S (ren_cty (plus (S (S x'))) (cannotation e')));
                [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
                | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn;
                  destruct (S x' + y <? length rest) eqn:E1; rw_nat_bool; reflexivity ].
           ++ transitivity (zero :: vec_zero (S (S x')) ++ ctype_uses e');
                [reflexivity | rewrite Hvec; reflexivity].
Qed.

Theorem core_weakening : forall (D : JoinDomain) (b : cbinding D) env_a env_b t j,
  (forall j0, grade_join D = Some j0 -> j0 zero zero = zero) ->
  CoreDerives (env_a ++ env_b) t j ->
  CoreDerives (weaken_cenv b env_a env_b) (lift_cterm (length env_a) 1 t)
    {| cresult_type := lift_cty (length env_a) 1 (cresult_type j);
       ccomp_demand := vec_insert_zero (length env_a) (ccomp_demand j);
       ctype_demand_row := vec_insert_zero (length env_a) (ctype_demand_row j) |}.
Proof.
  intros D b env_a env_b t j Hjz H.
  rewrite lift_as_weaken_rho.
  replace (lift_cterm (length env_a) 1 t) with (ren_cterm (weaken_rho (length env_a)) t).
  - eapply ren_core_derives; [apply weaken_RenEnv; exact Hjz | exact H].
  - unfold lift_cterm.
    assert (Hext : forall rho1 rho2 (tm : cterm D), (forall x, rho1 x = rho2 x) -> ren_cterm rho1 tm = ren_cterm rho2 tm).
    { intros rho1 rho2 tm. revert rho1 rho2.
      induction tm using cterm_ind_nested; intros r1 r2 Hext; cbn;
        try reflexivity;
        try (rewrite Hext; reflexivity);
        try (rewrite (ren_cidx_ext D _ _ i Hext); reflexivity);
        try (rewrite (ren_cty_ext D _ _ T Hext); reflexivity);
        try solve [f_equal; try (apply ren_cty_ext; exact Hext); try (apply IHtm; exact Hext);
                   try (apply IHtm1; exact Hext); try (apply IHtm2; exact Hext); try (apply IHtm3; exact Hext)].
      - f_equal; [apply ren_cty_ext; exact Hext | apply IHtm; intros [| z]; cbn; auto].
      - f_equal; [apply ren_cty_ext; exact Hext | apply IHtm1; exact Hext | apply IHtm2; intros [| z]; cbn; auto].
      - f_equal; [apply ren_cty_ext; exact Hext | apply ren_cty_ext; intros [| z]; cbn; auto |
                  apply IHtm1; exact Hext | apply IHtm2; exact Hext].
      - f_equal; [apply ren_cty_ext; intros [| z]; cbn; auto | apply IHtm1; exact Hext |
                  apply IHtm2; intros [| [| z]]; cbn; auto].
      - f_equal; [apply ren_cty_ext; intros [| z]; cbn; auto | apply IHtm1; exact Hext |
                  apply IHtm2; intros [| z]; cbn; auto].
      - f_equal; [apply ren_cty_ext; intros [| z]; cbn; auto | apply IHtm1; exact Hext |
                  apply IHtm2; intros [| z]; cbn; auto | apply IHtm3; intros [| z]; cbn; auto].
      - f_equal. induction fields as [| [[[fn fg] ft] fv] rest IHf]; cbn; [reflexivity |].
        inversion H0; subst; cbn in H3.
        rewrite (ren_cty_ext D _ _ ft Hext), (H3 _ _ Hext), (IHf H4). reflexivity.
      - f_equal; [apply ren_cty_ext; exact Hext | apply IHtm1; exact Hext |].
        match goal with
        | |- ren_cterm (Nat.iter ?n ren_shift ?r1) _ = ren_cterm (Nat.iter ?n ren_shift ?r2) _ =>
            apply IHtm2; induction n as [| k IHk];
              [exact Hext
              |intros [| z]; [reflexivity |
                 change (Nat.iter (S k) ren_shift r1 (S z)) with (S (Nat.iter k ren_shift r1 z));
                 change (Nat.iter (S k) ren_shift r2 (S z)) with (S (Nat.iter k ren_shift r2 z));
                 f_equal; apply IHk]]
        end.
      - f_equal; [apply ren_cty_ext; intros [| z]; cbn; auto | apply IHtm1; exact Hext |
                  apply IHtm2; exact Hext | apply IHtm3; intros [| [| z]]; cbn; auto]. }
    apply Hext. intro x. unfold ren_lift, weaken_rho. destruct (x <? length env_a); [reflexivity | lia].
Qed.

Theorem core_weakening_erasure : forall (D : JoinDomain) (b : cbinding D) env_a env_b t j,
  ErasureDomain D ->
  CoreDerives (env_a ++ env_b) t j ->
  CoreDerives (weaken_cenv b env_a env_b) (lift_cterm (length env_a) 1 t)
    {| cresult_type := lift_cty (length env_a) 1 (cresult_type j);
       ccomp_demand := vec_insert_zero (length env_a) (ccomp_demand j);
       ctype_demand_row := vec_insert_zero (length env_a) (ctype_demand_row j) |}.
Proof.
  intros D b env_a env_b t j ED H.
  apply core_weakening; [apply join_zero_zero_of_erasure; exact ED | exact H].
Qed.

(* Exchange *)

Definition swap_rho (k x : nat) : nat :=
  if x =? k then S k else if x =? S k then k else x.

Lemma swap_rho_involutive : forall k x, swap_rho k (swap_rho k x) = x.
Proof.
  intros k x. unfold swap_rho.
  destruct (Nat.eq_dec x k) as [-> | H1].
  - rewrite Nat.eqb_refl.
    destruct (S k =? k) eqn:E1; [apply Nat.eqb_eq in E1; lia |].
    rewrite Nat.eqb_refl. reflexivity.
  - assert (Hne1 : (x =? k) = false) by (apply Nat.eqb_neq; exact H1).
    rewrite Hne1. destruct (Nat.eq_dec x (S k)) as [-> | H2].
    + rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
    + assert (Hne2 : (x =? S k) = false) by (apply Nat.eqb_neq; exact H2).
      rewrite Hne2, Hne1, Hne2. reflexivity.
Qed.

Lemma vec_swap_length : forall (D : JoinDomain) k (u : list (grade D)),
  length (vec_swap k u) = length u.
Proof.
  intros D k. induction k as [| k IH]; intros [| a [| b u']]; cbn; try reflexivity; f_equal; apply IH.
Qed.

Lemma vec_swap_zero : forall (D : JoinDomain) k n,
  vec_swap (D := D) k (vec_zero n) = vec_zero n.
Proof.
  intros D k. induction k as [| k IH]; intros [| [| n']]; cbn; try reflexivity; f_equal; first [exact (IH 0) | exact (IH (S n'))].
Qed.

Lemma vec_swap_single : forall (D : JoinDomain) k n x q,
  S k < n -> x < n ->
  vec_swap (D := D) k (vec_single n x q) = vec_single n (swap_rho k x) q.
Proof.
  intros D k. induction k as [| k IH]; intros n x q Hkn Hxn; unfold swap_rho in *; cbn.
  - destruct n as [| [| n']]; [lia | lia |].
    destruct x as [| [| x']]; cbn; [reflexivity | reflexivity | f_equal; f_equal; reflexivity].
  - destruct n as [| n']; [lia |].
    destruct x as [| x']; cbn; [f_equal; apply vec_swap_zero |].
    destruct n' as [| n'']; [lia |].
    destruct x' as [| x'']; cbn.
    + f_equal. change (q :: vec_zero n'') with (vec_single (S n'') 0 q).
      rewrite (IH (S n'') 0 q ltac:(lia) ltac:(lia)). unfold swap_rho.
      destruct (0 =? k) eqn:E1; [reflexivity | cbn; reflexivity].
    + f_equal. change (zero :: vec_single n'' x'' q) with (vec_single (S n'') (S x'') q).
      rewrite (IH (S n'') (S x'') q ltac:(lia) ltac:(lia)). unfold swap_rho.
      destruct (S x'' =? k) eqn:E1; [reflexivity |].
      destruct (S x'' =? S k) eqn:E2; destruct (x'' =? k) eqn:E3;
        [reflexivity
        |apply Nat.eqb_eq in E2; apply Nat.eqb_neq in E3; lia
        |apply Nat.eqb_neq in E2; apply Nat.eqb_eq in E3; lia
        |reflexivity].
Qed.

Lemma vec_swap_add : forall (D : JoinDomain) k (u v : list (grade D)),
  length u = length v ->
  vec_swap k (vec_add u v) = vec_add (vec_swap k u) (vec_swap k v).
Proof.
  intros D k. induction k as [| k IH]; intros [| a1 u'] [| b1 v'] Hlen;
    cbn in *; try discriminate; try reflexivity.
  - destruct u' as [| a2 u''], v' as [| b2 v'']; cbn in *; try discriminate; reflexivity.
  - destruct u' as [| a2 u''], v' as [| b2 v'']; cbn in *; try discriminate;
      [f_equal; exact (IH [] [] eq_refl) | f_equal; apply (IH (a2 :: u'') (b2 :: v'')); cbn; lia].
Qed.

Lemma vec_swap_scale : forall (D : JoinDomain) k (q : grade D) u,
  vec_swap k (vec_scale q u) = vec_scale q (vec_swap k u).
Proof.
  intros D k. induction k as [| k IH]; intros q [| a u']; cbn; try reflexivity.
  - destruct u' as [| b u'']; cbn; reflexivity.
  - destruct u' as [| b u'']; cbn; f_equal; [exact (IH q []) | exact (IH q (b :: u''))].
Qed.

Lemma vec_swap_join : forall (D : JoinDomain) k (j : grade D -> grade D -> grade D) u v,
  length u = length v ->
  vec_swap k (vec_join j u v) = vec_join j (vec_swap k u) (vec_swap k v).
Proof.
  intros D k j. induction k as [| k IH]; intros [| a1 u'] [| b1 v'] Hlen;
    cbn in *; try discriminate; try reflexivity.
  - destruct u' as [| a2 u''], v' as [| b2 v'']; cbn in *; try discriminate; reflexivity.
  - destruct u' as [| a2 u''], v' as [| b2 v'']; cbn in *; try discriminate;
      [f_equal; exact (IH [] [] eq_refl) | f_equal; apply (IH (a2 :: u'') (b2 :: v'')); cbn; lia].
Qed.

Lemma vec_swap_allows : forall (D : JoinDomain) k (u v : list (grade D)),
  vec_allows u v -> vec_allows (vec_swap k u) (vec_swap k v).
Proof.
  intros D k. induction k as [| k IH]; intros u v Hal.
  - destruct Hal as [| a b u1 v1 Hab Hal1]; [constructor |].
    destruct Hal1 as [| a2 b2 u2 v2 Hab2 Hal2]; cbn; constructor; auto; constructor; auto.
  - destruct Hal as [| a b u1 v1 Hab Hal1]; [constructor |].
    destruct Hal1 as [| a2 b2 u2 v2 Hab2 Hal2]; cbn; constructor;
      [exact Hab | exact (IH [] [] (Forall2_nil _)) | exact Hab | apply (IH (a2 :: u2) (b2 :: v2)); constructor; assumption].
Qed.

Lemma vec_swap_nth : forall (D : JoinDomain) k u i,
  S k < length u -> i < length u ->
  nth_grade (D := D) (vec_swap k u) (swap_rho k i) = nth_grade u i.
Proof.
  intros D k. induction k as [| k IH]; intros [| a [| b u']] i Hku Hi; cbn in *; try lia; unfold swap_rho in *.
  - destruct i as [| [| i']]; cbn; reflexivity.
  - destruct i as [| i']; cbn; [reflexivity |].
    specialize (IH (b :: u') i' ltac:(cbn; lia) ltac:(cbn; lia)).
    unfold swap_rho in IH.
    destruct (i' =? k) eqn:E1; [exact IH |].
    destruct (i' =? S k) eqn:E2; exact IH.
Qed.

Lemma vec_swap_is_zero : forall (D : JoinDomain) k (u : list (grade D)),
  vec_is_zero u = true -> vec_is_zero (vec_swap k u) = true.
Proof.
  intros D k. induction k as [| k IH]; intros u Hz; unfold vec_is_zero in *; cbn in *.
  - destruct u as [| a [| b u']]; cbn in *; [exact Hz | exact Hz |].
    rewrite !andb_true_iff in Hz |- *; tauto.
  - destruct u as [| a [| b u']]; cbn in *; [exact Hz | |].
    + rewrite andb_true_iff in Hz |- *; destruct Hz as [Ha _]; split; [exact Ha | exact (IH [] eq_refl)].
    + rewrite andb_true_iff in Hz |- *; destruct Hz as [Ha Hb]; split; [exact Ha | apply (IH (b :: u')); exact Hb].
Qed.

Lemma swap_RenSpec : forall (D : JoinDomain) k n,
  S k < n ->
  RenSpec D (swap_rho k) (vec_swap k) n n.
Proof.
  intros D k n Hkn. constructor.
  - apply vec_swap_zero.
  - intros x q Hx. apply vec_swap_single; assumption.
  - intros u v Hu Hv. apply vec_swap_add; lia.
  - intros q u Hu. apply vec_swap_scale.
  - intros j u v _ Hu Hv. apply vec_swap_join; lia.
  - intros u v Hu Hv Hal. apply vec_swap_allows; exact Hal.
  - intros u Hu. rewrite vec_swap_length; exact Hu.
  - intros u i Hu Hi. apply vec_swap_nth; lia.
  - intros u Hu Hz. apply vec_swap_is_zero; exact Hz.
Qed.

(* Context alpha-equivalence invariance for CIdxDemand and CTypeDemand *)

Definition cenv_alpha_eq {D : JoinDomain} (env1 env2 : cenv D) : Prop :=
  Forall2 (fun e1 e2 => cty_alpha_eq (cannotation e1) (cannotation e2)) env1 env2.

Lemma cenv_alpha_eq_refl : forall (D : JoinDomain) (env : cenv D),
  cenv_alpha_eq env env.
Proof.
  intros D env. induction env; constructor; [apply cty_alpha_eq_refl | exact IHenv].
Qed.

Lemma cenv_alpha_eq_length : forall (D : JoinDomain) (env1 env2 : cenv D),
  cenv_alpha_eq env1 env2 -> length env1 = length env2.
Proof.
  intros D env1 env2 H. induction H; cbn; congruence.
Qed.

Lemma cenv_alpha_eq_lookup : forall (D : JoinDomain) (env1 env2 : cenv D) x e1,
  cenv_alpha_eq env1 env2 ->
  clookup env1 x = Some e1 ->
  exists e2, clookup env2 x = Some e2 /\ cty_alpha_eq (cannotation e1) (cannotation e2).
Proof.
  intros D env1 env2 x e1 H. revert x e1.
  induction H; intros [| x'] e1 Hl; cbn in Hl; try discriminate.
  - inversion Hl; subst; exists y; split; [reflexivity | exact H].
  - apply IHForall2; exact Hl.
Qed.

Lemma CIdxDemand_alpha_env : forall (D : JoinDomain) (env1 env2 : cenv D) i d,
  cenv_alpha_eq env1 env2 ->
  CIdxDemand env1 i d ->
  CIdxDemand env2 i d.
Proof.
  intros D env1 env2 i d Ha H. revert env2 Ha.
  induction H; intros env2 Ha; try (rewrite (cenv_alpha_eq_length D _ env2 Ha) in *).
  - destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha H) as [e2 [Hl2 He2]].
    eapply CIdxDemandVar; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact H0]].
  - constructor.
  - constructor; [apply IHCIdxDemand1 | apply IHCIdxDemand2]; exact Ha.
  - constructor; apply IHCIdxDemand; exact Ha.
  - destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha H) as [e2 [Hl2 He2]].
    eapply CIdxDemandUnbox; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact H0]].
  - destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha H) as [e2 [Hl2 He2]].
    eapply CIdxDemandFst; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact H0]].
  - destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha H) as [e2 [Hl2 He2]].
    eapply CIdxDemandSnd; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact H0]].
  - destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha H) as [e2 [Hl2 He2]].
    eapply CIdxDemandCase with (A := A) (B := B) (dl := dl) (dr := dr);
      [exact Hl2 | | | | exact H3].
    + eapply cty_alpha_eq_trans; [apply ren_cty_alpha_eq, cty_alpha_eq_sym; exact He2 | exact H0].
    + apply IHCIdxDemand1; constructor; [apply cty_alpha_eq_refl | exact Ha].
    + apply IHCIdxDemand2; constructor; [apply cty_alpha_eq_refl | exact Ha].
Qed.

Lemma CTypeDemand_alpha_env : forall (D : JoinDomain) (env1 env2 : cenv D) T d,
  cenv_alpha_eq env1 env2 ->
  CTypeDemand env1 T d ->
  CTypeDemand env2 T d.
Proof.
  intros D env1 env2 T d Ha H. revert env2 Ha.
  induction H using CTypeDemand_ind_mut with
    (P := fun env1 T d _ => forall env2, cenv_alpha_eq env1 env2 -> CTypeDemand env2 T d)
    (P0 := fun env1 fs df _ => forall env2, cenv_alpha_eq env1 env2 -> CRecordFieldDemand env2 fs df)
    (P1 := fun env1 ls dl _ => forall env2, cenv_alpha_eq env1 env2 -> CIdxListDemand env2 ls dl);
    intros env2 Ha; try (rewrite (cenv_alpha_eq_length D _ _ Ha) in *);
    try solve [constructor; try (eapply CIdxDemand_alpha_env; eassumption);
               try (apply IHCTypeDemand; exact Ha);
               try (apply IHCTypeDemand1; exact Ha);
               try (apply IHCTypeDemand2; exact Ha);
               try (apply IHCTypeDemand0; exact Ha)].
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha Hl) as [e2 [Hl2 He2]];
        eapply CTypeTVar; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact Hc]]
    end.
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha Hl) as [e2 [Hl2 He2]];
        eapply CTypeTUnbox; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact Hc]]
    end.
  - eapply CTypePi; [apply IHCTypeDemand1; exact Ha | | assumption].
    apply IHCTypeDemand2; constructor; [apply cty_alpha_eq_refl | exact Ha].
  - eapply CTypeSigma; [apply IHCTypeDemand1; exact Ha | | assumption].
    apply IHCTypeDemand2; constructor; [apply cty_alpha_eq_refl | exact Ha].
Qed.

(* Strengthening at 0 for CIdxDemand and CTypeDemand when lifting *)

Lemma vec_remove_length : forall (D : JoinDomain) k (u : list (grade D)),
  k < length u -> length (vec_remove k u) = length u - 1.
Proof.
  intros D k. induction k as [| k IH]; intros [| a u'] Hk; cbn in *; try lia; rewrite (IH u' ltac:(lia)); lia.
Qed.

Lemma vec_remove_zero : forall (D : JoinDomain) k n,
  k < S n -> vec_remove (D := D) k (vec_zero (S n)) = vec_zero n.
Proof.
  intros D k. induction k as [| k IH]; intros n Hk; cbn; [reflexivity |].
  destruct n as [| n']; [lia | cbn; f_equal; apply IH; lia].
Qed.

Lemma vec_remove_single_weaken : forall (D : JoinDomain) k n x q,
  k <= n -> x < n ->
  vec_remove (D := D) k (vec_single (S n) (weaken_rho k x) q) = vec_single n x q.
Proof.
  intros D k. induction k as [| k IH]; intros n x q Hkn Hxn; unfold weaken_rho in *; cbn.
  - reflexivity.
  - destruct n as [| n']; [lia |].
    destruct x as [| x'];
      [destruct (0 <? S k) eqn:E; [| apply Nat.ltb_ge in E; lia];
       cbn [vec_single vec_remove]; rewrite vec_remove_zero; [reflexivity | lia] |].
    destruct (S x' <? S k) eqn:Hsk; destruct (x' <? k) eqn:Hxk;
      try (apply Nat.ltb_lt in Hsk; apply Nat.ltb_ge in Hxk; lia);
      try (apply Nat.ltb_ge in Hsk; apply Nat.ltb_lt in Hxk; lia);
      cbn; f_equal;
      (transitivity (vec_remove k (vec_single (S n') (weaken_rho k x') q));
       [unfold weaken_rho; rewrite Hxk; reflexivity | apply IH; lia]).
Qed.

Lemma vec_remove_add : forall (D : JoinDomain) k (u v : list (grade D)),
  k < length u -> length u = length v ->
  vec_remove k (vec_add u v) = vec_add (vec_remove k u) (vec_remove k v).
Proof.
  intros D k. induction k as [| k IH]; intros [| a u'] [| b v'] Hk Hlen; cbn in *; try lia;
    [reflexivity | f_equal; apply IH; lia].
Qed.

Lemma vec_remove_scale : forall (D : JoinDomain) k (q : grade D) u,
  k < length u ->
  vec_remove k (vec_scale q u) = vec_scale q (vec_remove k u).
Proof.
  intros D k. induction k as [| k IH]; intros q [| a u'] Hk; cbn in *; try lia; [reflexivity | f_equal; apply IH; lia].
Qed.

Lemma vec_remove_join : forall (D : JoinDomain) k (j : grade D -> grade D -> grade D) u v,
  k < length u -> length u = length v ->
  vec_remove k (vec_join j u v) = vec_join j (vec_remove k u) (vec_remove k v).
Proof.
  intros D k j. induction k as [| k IH]; intros [| a u'] [| b v'] Hk Hlen; cbn in *; try lia;
    [reflexivity | f_equal; apply IH; lia].
Qed.

Lemma BranchVec_remove : forall (D : JoinDomain) k (u1 u2 u : list (grade D)),
  k < length u1 -> length u1 = length u2 ->
  BranchVec u1 u2 u -> BranchVec (vec_remove k u1) (vec_remove k u2) (vec_remove k u).
Proof.
  intros D k u1 u2 u Hk Hlen Hbr. unfold BranchVec in *.
  destruct (grade_join D) as [j |]; [subst u; apply vec_remove_join; assumption |].
  destruct Hbr as [-> ->]; split; reflexivity.
Qed.

Lemma lift_cidx_as_weaken : forall (D : JoinDomain) k (i : cidx D),
  lift_cidx k 1 i = ren_cidx (weaken_rho k) i.
Proof.
  intros D k i. unfold lift_cidx. apply ren_cidx_ext.
  intro x. unfold ren_lift, weaken_rho. destruct (x <? k); [reflexivity | lia].
Qed.

Lemma lift_cidx_inv_var : forall (D : JoinDomain) k (i0 : cidx D) x,
  ren_cidx (weaken_rho k) i0 = CIdxVar x ->
  exists x0, i0 = CIdxVar x0 /\ x = weaken_rho k x0.
Proof. intros D k i0 x H; destruct i0; cbn in H; try discriminate; inversion H; eauto. Qed.

Lemma strengthen_weaken_cidx_demand : forall (D : JoinDomain) (b : cbinding D) env_a env_b i d,
  CIdxDemand (weaken_cenv b env_a env_b) (ren_cidx (weaken_rho (length env_a)) i) d ->
  CIdxDemand (env_a ++ env_b) i (vec_remove (length env_a) d).
Proof.
  intros D b env_a env_b i. revert b env_a env_b.
  induction i; intros bnd env_a env_b d H; cbn in H.
  - (* CIdxVar *)
    inversion H; subst.
    (* look up x in env_a ++ env_b *)
    assert (Hl : exists e0, clookup (env_a ++ env_b) x = Some e0 /\ cty_alpha_eq (cannotation e0) CNat).
    { clear -H1 H2. revert env_b x e H1 H2.
      induction env_a as [| e0 rest IH]; intros env_b x e H1 H2; cbn in *.
      - unfold weaken_rho in H1; cbn in H1. exists e; split; assumption.
      - destruct x as [| x'].
        + unfold weaken_rho in H1; cbn in H1. inversion H1; subst; cbn in H2.
          rewrite lift_as_weaken_rho in H2. apply ren_cty_eq_CNat in H2. exists e0; split; [reflexivity | exact H2].
        + unfold weaken_rho in H1; cbn in H1.
          destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
            try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
            try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia).
          * destruct (IH env_b x' e) as [e1 [Hl1 Ha1]]; [unfold weaken_rho; rewrite Hxlt; exact H1 | exact H2 |].
            exists e1; split; exact Hl1 || exact Ha1.
          * destruct (IH env_b x' e) as [e1 [Hl1 Ha1]]; [unfold weaken_rho; rewrite Hxlt; exact H1 | exact H2 |].
            exists e1; split; exact Hl1 || exact Ha1. }
    destruct Hl as [e0 [Hl0 Ha0]].
    rewrite weaken_cenv_length.
    rewrite <- length_app, vec_remove_single_weaken;
      [eapply CIdxDemandVar; [exact Hl0 | exact Ha0]
      |(try rewrite length_app in *); lia
      |eapply clookup_lt_length; exact Hl0].
  - (* CIdxLit *)
    inversion H; subst. rewrite weaken_cenv_length. rewrite <- length_app, vec_remove_zero; [constructor | (try rewrite length_app in *); lia].
  - (* CIdxAdd *)
    inversion H; subst.
    pose proof (cidx_demand_length D _ _ _ H2) as Hdl.
    pose proof (cidx_demand_length D _ _ _ H4) as Hdr.
    rewrite weaken_cenv_length in Hdl, Hdr.
    rewrite vec_remove_add; [| lia | lia].
    apply CIdxDemandAdd; [apply (IHi1 bnd _ _ _ H2) | apply (IHi2 bnd _ _ _ H4)].
  - (* CIdxProm *)
    inversion H; subst.
    match goal with
    | Hd : CIdxDemand _ _ _ |- _ =>
        pose proof (cidx_demand_length D _ _ _ Hd) as Hdi;
        rewrite weaken_cenv_length in Hdi;
        rewrite vec_remove_scale; [apply CIdxDemandProm; apply (IHi bnd _ _ _ Hd) | lia]
    end.
  - (* CIdxUnbox *)
    inversion H; subst.
    assert (Hl : exists e0, clookup (env_a ++ env_b) b = Some e0 /\ cty_alpha_eq (cannotation e0) (CBox q CNat)).
    { clear -H1 H2. revert env_b b e H1 H2.
      induction env_a as [| e0 rest IH]; intros env_b b0 e H1 H2; cbn in *.
      - unfold weaken_rho in H1; cbn in H1. exists e; split; assumption.
      - destruct b0 as [| x'].
        + unfold weaken_rho in H1; cbn in H1. inversion H1; subst; cbn in H2.
          rewrite lift_as_weaken_rho in H2. apply ren_cty_eq_CBox_Nat in H2. exists e0; split; [reflexivity | exact H2].
        + unfold weaken_rho in H1; cbn in H1.
          destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
            try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
            try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia);
            destruct (IH env_b x' e) as [e1 [Hl1 Ha1]]; try (unfold weaken_rho; rewrite Hxlt; exact H1); try exact H2;
            exists e1; split; assumption. }
    destruct Hl as [e0 [Hl0 Ha0]].
    rewrite weaken_cenv_length, <- length_app, vec_remove_single_weaken;
      [eapply CIdxDemandUnbox; [exact Hl0 | exact Ha0]
      |(try rewrite length_app in *); lia
      |eapply clookup_lt_length; exact Hl0].
  - (* CIdxFst *)
    inversion H; subst.
    assert (Hl : exists e0 z' snd', clookup (env_a ++ env_b) p = Some e0 /\ cty_alpha_eq (cannotation e0) (CSigma z' r CNat snd')).
    { clear -H1 H2. revert env_b p e z r snd_ty H1 H2.
      induction env_a as [| e0 rest IH]; intros env_b p e z r snd_ty H1 H2; cbn in *.
      - unfold weaken_rho in H1; cbn in H1. exists e, z, snd_ty; split; assumption.
      - destruct p as [| x'].
        + unfold weaken_rho in H1; cbn in H1. inversion H1; subst; cbn in H2.
          rewrite lift_as_weaken_rho in H2.
          destruct (ren_cty_eq_CSigma_FstNat D _ _ _ _ _ H2) as [z' [snd' Hs']].
          exists e0, z', snd'; split; [reflexivity | exact Hs'].
        + unfold weaken_rho in H1; cbn in H1.
          destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
            try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
            try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia);
            destruct (IH env_b x' e z r snd_ty) as [e1 [z' [snd' [Hl1 Ha1]]]];
            try (unfold weaken_rho; rewrite Hxlt; exact H1); try exact H2;
            exists e1, z', snd'; split; assumption. }
    destruct Hl as [e0 [z' [snd' [Hl0 Ha0]]]].
    rewrite weaken_cenv_length, <- length_app, vec_remove_single_weaken;
      [eapply CIdxDemandFst; [exact Hl0 | exact Ha0]
      |(try rewrite length_app in *); lia
      |eapply clookup_lt_length; exact Hl0].
  - (* CIdxSnd *)
    inversion H; subst.
    assert (Hl : exists e0 z' fst', clookup (env_a ++ env_b) p = Some e0 /\ cty_alpha_eq (cannotation e0) (CSigma z' r fst' CNat)).
    { clear -H1 H2. revert env_b p e z r fst_ty H1 H2.
      induction env_a as [| e0 rest IH]; intros env_b p e z r fst_ty H1 H2; cbn in *.
      - unfold weaken_rho in H1; cbn in H1. exists e, z, fst_ty; split; assumption.
      - destruct p as [| x'].
        + unfold weaken_rho in H1; cbn in H1. inversion H1; subst; cbn in H2.
          rewrite lift_as_weaken_rho in H2.
          destruct (ren_cty_eq_CSigma_SndNat D _ _ _ _ _ H2) as [z' [fst' Hs']].
          exists e0, z', fst'; split; [reflexivity | exact Hs'].
        + unfold weaken_rho in H1; cbn in H1.
          destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
            try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
            try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia);
            destruct (IH env_b x' e z r fst_ty) as [e1 [z' [fst' [Hl1 Ha1]]]];
            try (unfold weaken_rho; rewrite Hxlt; exact H1); try exact H2;
            exists e1, z', fst'; split; assumption. }
    destruct Hl as [e0 [z' [fst' [Hl0 Ha0]]]].
    rewrite weaken_cenv_length, <- length_app, vec_remove_single_weaken;
      [eapply CIdxDemandSnd; [exact Hl0 | exact Ha0]
      |(try rewrite length_app in *); lia
      |eapply clookup_lt_length; exact Hl0].
  - (* CIdxCase *)
    inversion H; subst.
    match goal with
    | Hlk : clookup (weaken_cenv _ _ _) _ = Some _,
      Hse : cty_alpha_eq _ (CSum ?A0 ?B0),
      Hd1 : CIdxDemand ({| cbinder := 0; cannotation := ?A0; ctype_uses := _ |} :: _) _ ?dl0,
      Hd2 : CIdxDemand ({| cbinder := 0; cannotation := ?B0; ctype_uses := _ |} :: _) _ ?dr0,
      Hbv : BranchVec (tl ?dl0) (tl ?dr0) _ |- _ =>
        rename Hlk into Hlkp, Hse into Hsum_eq, Hd1 into Hdl0, Hd2 into Hdr0, Hbv into Hbr0
    end.
    assert (Hl : exists e0, clookup (env_a ++ env_b) s = Some e0 /\
                  ren_cty (plus (S (weaken_rho (length env_a) s))) (cannotation e) =
                  ren_cty (weaken_rho (length env_a)) (ren_cty (plus (S s)) (cannotation e0))).
    { clear -Hlkp. revert env_b s e Hlkp.
      induction env_a as [| e0 rest IH]; intros env_b s e Hl; cbn in *.
      - unfold weaken_rho in *; cbn in *. exists e; split; [exact Hl |].
        rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity.
      - destruct s as [| s'].
        + unfold weaken_rho in Hl; cbn in Hl. inversion Hl; subst; cbn.
          exists e0; split; [reflexivity |].
          rewrite lift_as_weaken_rho, !ren_cty_comp; apply ren_cty_ext; intro y; unfold weaken_rho; cbn.
          destruct (y <? length rest) eqn:E; rw_nat_bool; reflexivity.
        + unfold weaken_rho in Hl; cbn in Hl.
          destruct (S s' <? S (length rest)) eqn:Hss; destruct (s' <? length rest) eqn:Hslt;
            try (apply Nat.ltb_lt in Hss; apply Nat.ltb_ge in Hslt; lia);
            try (apply Nat.ltb_ge in Hss; apply Nat.ltb_lt in Hslt; lia).
          * destruct (IH env_b s' e ltac:(unfold weaken_rho; rewrite Hslt; exact Hl)) as [e1 [Hl1 Heq]].
            exists e1; split; [exact Hl1 |].
            transitivity (ren_cty S (ren_cty (fun m : nat => S (weaken_rho (length rest) s' + m)) (cannotation e)));
              [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; unfold weaken_rho; rewrite Hslt, Hss; cbn; reflexivity
              | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; unfold weaken_rho; cbn;
                destruct (S s' + y <? length rest) eqn:E; rw_nat_bool; reflexivity ].
          * destruct (IH env_b s' e ltac:(unfold weaken_rho; rewrite Hslt; exact Hl)) as [e1 [Hl1 Heq]].
            exists e1; split; [exact Hl1 |].
            transitivity (ren_cty S (ren_cty (fun m : nat => S (weaken_rho (length rest) s' + m)) (cannotation e)));
              [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; unfold weaken_rho; rewrite Hslt, Hss; cbn; reflexivity
              | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; unfold weaken_rho; cbn;
                destruct (S s' + y <? length rest) eqn:E; rw_nat_bool; reflexivity ]. }
    destruct Hl as [e0 [Hl0 Heq]].
    unfold cty_alpha_eq in Hsum_eq; rewrite Heq, erase_hints_ren in Hsum_eq.
    destruct (ren_cty (plus (S s)) (cannotation e0)) as [| | | | | | | | | | A0 B0 | |] eqn:Hsum;
      cbn in Hsum_eq; try discriminate.
    inversion Hsum_eq as [[HeqA HeqB]].
    pose proof (cidx_demand_length D _ _ _ Hdl0) as Hdl; cbn in Hdl.
    pose proof (cidx_demand_length D _ _ _ Hdr0) as Hdr; cbn in Hdr.
    rewrite weaken_cenv_length in Hdl, Hdr.
    assert (Hdbr : length d_br = S (length (env_a ++ env_b))) by
      (rewrite (BranchVec_length D (tl dl) (tl dr) d_br); [destruct dl; cbn in *; (try rewrite length_app in *); lia | destruct dl, dr; cbn in *; lia | exact Hbr0]).
    rewrite vec_remove_add; [| rewrite vec_single_length, weaken_cenv_length; lia | rewrite vec_single_length, weaken_cenv_length, <- length_app; symmetry; exact Hdbr].
    rewrite weaken_cenv_length, <- length_app, vec_remove_single_weaken; [| (try rewrite length_app in *); lia | eapply clookup_lt_length; exact Hl0].
    assert (Hdl' : CIdxDemand ({| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_a ++ env_b)) |} :: env_a ++ env_b)
                     i1 (vec_remove (S (length env_a)) dl)).
    { apply (IHi1 bnd ({| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_a ++ env_b)) |} :: env_a) env_b dl).
      cbn; rewrite lift_as_weaken_rho.
      replace (ren_cidx (weaken_rho (S (length env_a))) i1) with (ren_cidx (ren_shift (weaken_rho (length env_a))) i1)
        by (apply ren_cidx_ext; intros [| y]; unfold weaken_rho; cbn;
            [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
            |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]).
      eapply CIdxDemand_alpha_env; [| exact Hdl0].
      constructor; [cbn; apply cty_alpha_eq_sym; unfold cty_alpha_eq; rewrite erase_hints_ren; exact HeqA | apply cenv_alpha_eq_refl]. }
    assert (Hdr' : CIdxDemand ({| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_a ++ env_b)) |} :: env_a ++ env_b)
                     i2 (vec_remove (S (length env_a)) dr)).
    { apply (IHi2 bnd ({| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_a ++ env_b)) |} :: env_a) env_b dr).
      cbn; rewrite lift_as_weaken_rho.
      replace (ren_cidx (weaken_rho (S (length env_a))) i2) with (ren_cidx (ren_shift (weaken_rho (length env_a))) i2)
        by (apply ren_cidx_ext; intros [| y]; unfold weaken_rho; cbn;
            [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
            |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]).
      eapply CIdxDemand_alpha_env; [| exact Hdr0].
      constructor; [cbn; apply cty_alpha_eq_sym; unfold cty_alpha_eq; rewrite erase_hints_ren; exact HeqB | apply cenv_alpha_eq_refl]. }
    destruct dl as [| al dl'], dr as [| ar dr']; cbn in *; try lia.
    eapply CIdxDemandCase with (A := A0) (B := B0)
      (dl := al :: vec_remove (length env_a) dl') (dr := ar :: vec_remove (length env_a) dr');
      [exact Hl0
      |change (ren_cty (plus (S s)) (cannotation e0)) with (ren_cty (fun m : nat => S (s + m)) (cannotation e0));
       rewrite Hsum; apply cty_alpha_eq_refl
      |exact Hdl' | exact Hdr' | cbn; apply BranchVec_remove; [lia | lia | exact Hbr0]].
Qed.

Lemma strengthen_weaken_ctype_demand : forall (D : JoinDomain) (T : cty D) (b : cbinding D) env_a env_b d,
  CTypeDemand (weaken_cenv b env_a env_b) (ren_cty (weaken_rho (length env_a)) T) d ->
  CTypeDemand (env_a ++ env_b) T (vec_remove (length env_a) d).
Proof.
  intros D T. induction T using cty_ind_nested; intros bnd env_a env_b d Htd; cbn in Htd.
  - inversion Htd; subst. rewrite weaken_cenv_length, <- length_app, vec_remove_zero; [constructor | (try rewrite length_app in *); lia].
  - inversion Htd; subst. rewrite weaken_cenv_length, <- length_app, vec_remove_zero; [constructor | (try rewrite length_app in *); lia].
  - inversion Htd; subst.
    match goal with
    | H1 : CTypeDemand _ _ de, H2 : CIdxDemand _ _ dl |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hde;
        pose proof (cidx_demand_length D _ _ _ H2) as Hdl;
        rewrite weaken_cenv_length in Hde, Hdl;
        rewrite vec_remove_add; [| lia | lia];
        constructor; [apply (IHT bnd); exact H1 | apply strengthen_weaken_cidx_demand with (b := bnd); exact H2]
    end.
  - inversion Htd; subst. rewrite weaken_cenv_length, <- length_app, vec_remove_zero; [constructor | (try rewrite length_app in *); lia].
  - inversion Htd; subst.
    match goal with
    | H1 : clookup _ _ = Some ?e, H2 : cty_alpha_eq _ _ |- _ =>
        assert (Hl : exists e0, clookup (env_a ++ env_b) x = Some e0 /\ cty_alpha_eq (cannotation e0) (CUniv lvl));
        [ clear -H1 H2; revert env_b x e H1 H2;
          induction env_a as [| e0 rest IH]; intros env_b x e H1 H2; cbn in *;
          [ unfold weaken_rho in H1; cbn in H1; exists e; split; assumption
          | destruct x as [| x'];
            [ unfold weaken_rho in H1; cbn in H1; inversion H1; subst; cbn in H2;
              rewrite lift_as_weaken_rho in H2; apply ren_cty_eq_CUniv in H2; exists e0; split; [reflexivity | exact H2]
            | unfold weaken_rho in H1; cbn in H1;
              destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
                try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
                try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia);
                destruct (IH env_b x' e) as [e1 [Hl1 Ha1]]; try (unfold weaken_rho; rewrite Hxlt; exact H1); try exact H2;
                exists e1; split; assumption ] ]
        | destruct Hl as [e0 [Hl0 Ha0]];
          rewrite weaken_cenv_length, <- length_app, vec_remove_single_weaken;
            [eapply CTypeTVar; [exact Hl0 | exact Ha0]
            |(try rewrite length_app in *); lia
            |eapply clookup_lt_length; exact Hl0] ]
    end.
  - inversion Htd; subst.
    match goal with
    | H1 : CTypeDemand _ _ _ |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hdi;
        rewrite weaken_cenv_length in Hdi;
        rewrite vec_remove_scale; [constructor; apply (IHT bnd _ _ _ H1) | lia]
    end.
  - inversion Htd; subst.
    match goal with
    | H1 : clookup _ _ = Some ?e, H2 : cty_alpha_eq _ _ |- _ =>
        assert (Hl : exists e0, clookup (env_a ++ env_b) b = Some e0 /\ cty_alpha_eq (cannotation e0) (CBox q (CUniv lvl)));
        [ clear -H1 H2; revert env_b b e H1 H2;
          induction env_a as [| e0 rest IH]; intros env_b b e H1 H2; cbn in *;
          [ unfold weaken_rho in H1; cbn in H1; exists e; split; assumption
          | destruct b as [| x'];
            [ unfold weaken_rho in H1; cbn in H1; inversion H1; subst; cbn in H2;
              rewrite lift_as_weaken_rho in H2; apply ren_cty_eq_CBox_Univ in H2; exists e0; split; [reflexivity | exact H2]
            | unfold weaken_rho in H1; cbn in H1;
              destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
                try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
                try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia);
                destruct (IH env_b x' e) as [e1 [Hl1 Ha1]]; try (unfold weaken_rho; rewrite Hxlt; exact H1); try exact H2;
                exists e1; split; assumption ] ]
        | destruct Hl as [e0 [Hl0 Ha0]];
          rewrite weaken_cenv_length, <- length_app, vec_remove_single_weaken;
            [eapply CTypeTUnbox; [exact Hl0 | exact Ha0]
            |(try rewrite length_app in *); lia
            |eapply clookup_lt_length; exact Hl0] ]
    end.
  - inversion Htd; subst.
    match goal with
    | H1 : CTypeDemand (weaken_cenv _ _ _) (ren_cty _ T1) _,
      H2 : CTypeDemand (_ :: weaken_cenv _ _ _) (ren_cty _ T2) _,
      H3 : allows _ _ |- _ =>
        rename H1 into Hdom; rename H2 into Hcod; rename H3 into Hal
    end.
    pose proof (ctype_demand_length D _ _ _ Hdom) as Ha.
    pose proof (ctype_demand_length D _ _ _ Hcod) as Hb. cbn in Hb.
    rewrite weaken_cenv_length in Ha, Hb.
    match type of Hdom with CTypeDemand _ _ ?va =>
    match type of Hcod with CTypeDemand _ _ ?vb =>
      destruct vb as [| b0' b_rest]; cbn in *; [lia |];
      rewrite vec_remove_add; [| lia | lia];
      pose proof (IHT1 bnd env_a env_b va Hdom) as HT1;
      assert (HT2 : CTypeDemand ({| cbinder := x; cannotation := T1; ctype_uses := vec_remove (length env_a) va |} :: env_a ++ env_b)
                      T2 (b0' :: vec_remove (length env_a) b_rest))
    end end.
    { change (b0' :: vec_remove (length env_a) b_rest) with (vec_remove (S (length env_a)) (b0' :: b_rest)).
      match type of Hdom with CTypeDemand _ _ ?va =>
        apply (IHT2 bnd ({| cbinder := x; cannotation := T1; ctype_uses := vec_remove (length env_a) va |} :: env_a) env_b)
      end.
      cbn. rewrite lift_as_weaken_rho.
      replace (ren_cty (weaken_rho (S (length env_a))) T2) with (ren_cty (ren_shift (weaken_rho (length env_a))) T2).
      - eapply CTypeDemand_alpha_env; [| exact Hcod].
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl].
      - apply ren_cty_ext; intros [| y]; unfold weaken_rho; cbn;
          [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
          |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]. }
    eapply CTypePi with (b := b0' :: vec_remove (length env_a) b_rest); [exact HT1 | exact HT2 | cbn; exact Hal].
  - inversion Htd; subst.
    match goal with
    | H1 : CTypeDemand (weaken_cenv _ _ _) (ren_cty _ T1) _,
      H2 : CTypeDemand (_ :: weaken_cenv _ _ _) (ren_cty _ T2) _,
      H3 : allows _ _ |- _ =>
        rename H1 into Hdom; rename H2 into Hcod; rename H3 into Hal
    end.
    pose proof (ctype_demand_length D _ _ _ Hdom) as Ha.
    pose proof (ctype_demand_length D _ _ _ Hcod) as Hb. cbn in Hb.
    rewrite weaken_cenv_length in Ha, Hb.
    match type of Hdom with CTypeDemand _ _ ?va =>
    match type of Hcod with CTypeDemand _ _ ?vb =>
      destruct vb as [| b0' b_rest]; cbn in *; [lia |];
      rewrite vec_remove_add; [| lia | lia];
      pose proof (IHT1 bnd env_a env_b va Hdom) as HT1;
      assert (HT2 : CTypeDemand ({| cbinder := x; cannotation := T1; ctype_uses := vec_remove (length env_a) va |} :: env_a ++ env_b)
                      T2 (b0' :: vec_remove (length env_a) b_rest))
    end end.
    { change (b0' :: vec_remove (length env_a) b_rest) with (vec_remove (S (length env_a)) (b0' :: b_rest)).
      match type of Hdom with CTypeDemand _ _ ?va =>
        apply (IHT2 bnd ({| cbinder := x; cannotation := T1; ctype_uses := vec_remove (length env_a) va |} :: env_a) env_b)
      end.
      cbn. rewrite lift_as_weaken_rho.
      replace (ren_cty (weaken_rho (S (length env_a))) T2) with (ren_cty (ren_shift (weaken_rho (length env_a))) T2).
      - eapply CTypeDemand_alpha_env; [| exact Hcod].
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl].
      - apply ren_cty_ext; intros [| y]; unfold weaken_rho; cbn;
          [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
          |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]. }
    eapply CTypeSigma with (b := b0' :: vec_remove (length env_a) b_rest); [exact HT1 | exact HT2 | cbn; exact Hal].
  - inversion Htd; subst.
    match goal with
    | H1 : CTypeDemand _ _ _ |- _ => constructor; apply (IHT bnd); exact H1
    end.
  - inversion Htd; subst.
    match goal with
    | H1 : CTypeDemand _ (ren_cty _ T1) ?dl, H2 : CTypeDemand _ (ren_cty _ T2) ?dr |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hdl;
        pose proof (ctype_demand_length D _ _ _ H2) as Hdr;
        rewrite weaken_cenv_length in Hdl, Hdr;
        rewrite vec_remove_add; [| lia | lia];
        constructor; [apply (IHT1 bnd _ _ _ H1) | apply (IHT2 bnd _ _ _ H2)]
    end.
  - inversion Htd; subst. constructor.
    match goal with
    | Hrec_top : CRecordFieldDemand _ _ _ |- _ => rename Hrec_top into Hrec0
    end.
    clear Htd. revert d Hrec0. induction fields as [| [[fn fg] ft] rest IHf]; intros d Hrec; cbn in Hrec.
    + inversion Hrec; subst. rewrite weaken_cenv_length, <- length_app, vec_remove_zero; [constructor | (try rewrite length_app in *); lia].
    + inversion H as [| ? ? HP Hrest]; subst; cbn in HP.
      inversion Hrec; subst.
      match goal with
      | H1 : CTypeDemand (weaken_cenv _ _ _) (ren_cty _ ft) _,
        H2 : CRecordFieldDemand (weaken_cenv _ _ _) (map _ rest) _ |- _ =>
          rename H1 into Hdt_sub; rename H2 into Hrec_sub
      end.
      pose proof (ctype_demand_length D _ _ _ Hdt_sub) as Hdt.
      pose proof (proj1 (record_field_and_idx_list_demand_length D) _ _ _ Hrec_sub) as Hdr.
      rewrite weaken_cenv_length in Hdt, Hdr.
      rewrite vec_remove_add; [| lia | lia].
      constructor; [apply (HP bnd); exact Hdt_sub | apply (IHf Hrest); exact Hrec_sub].
  - inversion Htd; subst. constructor.
    match goal with
    | Hidx_top : CIdxListDemand _ _ _ |- _ => rename Hidx_top into Hidx0
    end.
    clear Htd. revert d Hidx0. induction indices as [| idx rest IH]; intros d Hidx; cbn in Hidx.
    + inversion Hidx; subst. rewrite weaken_cenv_length, <- length_app, vec_remove_zero; [constructor | (try rewrite length_app in *); lia].
    + inversion Hidx; subst.
      match goal with
      | H1 : CIdxDemand (weaken_cenv _ _ _) (ren_cidx _ idx) _,
        H2 : CIdxListDemand (weaken_cenv _ _ _) (map _ rest) _ |- _ =>
          rename H1 into Hdi_sub; rename H2 into Hidx_sub
      end.
      pose proof (cidx_demand_length D _ _ _ Hdi_sub) as Hdi.
      pose proof (proj2 (record_field_and_idx_list_demand_length D) _ _ _ Hidx_sub) as Hdr.
      rewrite weaken_cenv_length in Hdi, Hdr.
      rewrite vec_remove_add; [| lia | lia].
      constructor; [apply strengthen_weaken_cidx_demand with (b := bnd); exact Hdi_sub | apply IH; exact Hidx_sub].
Qed.

Lemma strengthen_0_ctype_demand : forall (D : JoinDomain) (b : cbinding D) env (T : cty D) d,
  CTypeDemand (b :: env) (lift_cty 0 1 T) d ->
  CTypeDemand env T (tl d).
Proof.
  intros D b env T d H.
  change (tl d) with (vec_remove (length (@nil (cbinding D))) d).
  apply strengthen_weaken_ctype_demand with (b := b) (env_a := []) (env_b := env).
  rewrite lift_as_weaken_rho in H. exact H.
Qed.

Fixpoint swap_cenv {D : JoinDomain} (e2' e1' : cbinding D) (env_a env_b : cenv D) : cenv D :=
  match env_a with
  | [] => e2' :: e1' :: env_b
  | e :: rest =>
      {| cbinder := cbinder e;
         cannotation := ren_cty (swap_rho (length rest)) (cannotation e);
         ctype_uses := vec_swap (length rest) (ctype_uses e) |} :: swap_cenv e2' e1' rest env_b
  end.

Lemma swap_cenv_length : forall (D : JoinDomain) (e2' e1' : cbinding D) env_a env_b,
  length (swap_cenv e2' e1' env_a env_b) = length (env_a ++ [e1'; e2'] ++ env_b).
Proof.
  intros D e2' e1' env_a env_b. induction env_a as [| e rest IH]; cbn; [reflexivity | rewrite length_app in *; cbn in *; lia].
Qed.

Lemma swap_rho_S_swap : forall k x,
  swap_rho (S k) (S x) = S (swap_rho k x).
Proof.
  intros k x. unfold swap_rho.
  destruct (x =? k) eqn:E1; destruct (x =? S k) eqn:E2; rw_nat_bool; reflexivity.
Qed.

Lemma vec_allows_tl : forall (D : JoinDomain) (u v : list (grade D)),
  vec_allows u v -> vec_allows (tl u) (tl v).
Proof.
  intros D u v H. inversion H; cbn; [constructor | exact H1].
Qed.

Lemma vec_allows_join_mono : forall (D : JoinDomain) j (u1 u2 v1 v2 : list (grade D)),
  grade_join D = Some j ->
  vec_allows u1 u2 -> vec_allows v1 v2 ->
  vec_allows (vec_join j u1 v1) (vec_join j u2 v2).
Proof.
  intros D j u1 u2 v1 v2 Hj Hu Hv. revert v1 v2 Hv.
  induction Hu; intros v1 v2 Hv; inversion Hv; subst; cbn; constructor;
    [apply (join_least D j Hj); [eapply allows_trans; [exact H | apply (join_left D j Hj)]
                                |eapply allows_trans; [exact H0 | apply (join_right D j Hj)]]
    |apply IHHu; exact H1].
Qed.

Lemma vec_allows_join_insert_zero : forall (D : JoinDomain) j k (u v : list (grade D)),
  grade_join D = Some j ->
  k <= length u -> length u = length v ->
  vec_allows (vec_join j (vec_insert_zero k u) (vec_insert_zero k v))
             (vec_insert_zero k (vec_join j u v)).
Proof.
  intros D j k. induction k as [| k IH]; intros u v Hj Hk Hlen; cbn.
  - constructor; [apply (join_least D j Hj); apply allows_refl |].
    clear -Hj. revert v. induction u; intros []; cbn; constructor; [apply allows_refl | apply IHu].
  - destruct u as [| a u'], v as [| b v']; cbn in *; try lia; constructor;
      [apply allows_refl | apply IH; [exact Hj | lia | lia]].
Qed.

Lemma vec_allows_nth : forall (D : JoinDomain) (u v : list (grade D)) i,
  vec_allows u v -> allows (nth_grade u i) (nth_grade v i).
Proof.
  intros D u v i H. revert i. induction H; intros [| i]; cbn; [apply allows_refl | apply allows_refl | exact H | apply IHForall2].
Qed.

Lemma weaken_lookup_ren : forall (D : JoinDomain) (b : cbinding D) env_a env_b x e,
  clookup (env_a ++ env_b) x = Some e ->
  exists e', clookup (weaken_cenv b env_a env_b) (weaken_rho (length env_a) x) = Some e' /\
    ren_cty (plus (S (weaken_rho (length env_a) x))) (cannotation e') =
    ren_cty (weaken_rho (length env_a)) (ren_cty (plus (S x)) (cannotation e)).
Proof.
  intros D b env_a. induction env_a as [| e0 rest IH]; intros env_b x e Hl; cbn in *.
  - unfold weaken_rho; cbn. exists e; split; [exact Hl |].
    rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity.
  - destruct x as [| x'].
    + unfold weaken_rho; cbn. inversion Hl; subst; cbn.
      exists {| cbinder := cbinder e; cannotation := lift_cty (length rest) 1 (cannotation e);
                ctype_uses := vec_insert_zero (length rest) (ctype_uses e) |}.
      split; [reflexivity |].
      cbn. rewrite lift_as_weaken_rho, !ren_cty_comp.
      apply ren_cty_ext; intro y; unfold weaken_rho; cbn.
      destruct (y <? length rest) eqn:E; rw_nat_bool; reflexivity.
    + destruct (IH env_b x' e Hl) as [e' [Hl' Heq]].
      unfold weaken_rho in *. cbn.
      destruct (S x' <? S (length rest)) eqn:Hsx; destruct (x' <? length rest) eqn:Hxlt;
        try (apply Nat.ltb_lt in Hsx; apply Nat.ltb_ge in Hxlt; lia);
        try (apply Nat.ltb_ge in Hsx; apply Nat.ltb_lt in Hxlt; lia).
      * exists e'; split; [exact Hl' |].
        transitivity (ren_cty S (ren_cty (fun m => S (x' + m)) (cannotation e')));
          [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
          | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn;
            destruct (S x' + y <? length rest) eqn:E; rw_nat_bool; reflexivity ].
      * exists e'; split; [exact Hl' |].
        transitivity (ren_cty S (ren_cty (fun m => S (S x' + m)) (cannotation e')));
          [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
          | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; cbn;
            destruct (S x' + y <? length rest) eqn:E; rw_nat_bool; reflexivity ].
Qed.

Lemma weaken_cidx_demand_join : forall (D : JoinDomain) j (b : cbinding D) env_a env_b (i : cidx D) d,
  grade_join D = Some j ->
  CIdxDemand (env_a ++ env_b) i d ->
  exists d', CIdxDemand (weaken_cenv b env_a env_b) (ren_cidx (weaken_rho (length env_a)) i) d' /\
             vec_allows d' (vec_insert_zero (length env_a) d).
Proof.
  intros D j b env_a env_b i d Hj H.
  (* Wait: CIdxDemandCase replaces env with extended env, so generalize over env1 = env_a ++ env_b *)
  remember (env_a ++ env_b) as env1 eqn:Henv1.
  revert b env_a env_b Henv1.
  induction H; intros b0 env_a env_b0 Henv1; subst env.
  - destruct (weaken_lookup_ren D b0 env_a env_b0 x e H) as [e' [Hl' Heq]].
    assert (Hx : x < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact H).
    eexists; split.
    + eapply CIdxDemandVar; [exact Hl' |].
      apply (ren_cty_eq_CNat D (plus (S (weaken_rho (length env_a) x)))).
      unfold cty_alpha_eq in *; rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S x)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H1) as H2. exact H2.
    + rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hx].
  - eexists; split; [constructor | rewrite weaken_cenv_length, length_app, vec_insert_zero_zero; [apply vec_allows_refl | lia]].
  - destruct (IHCIdxDemand1 b0 env_a env_b0 eq_refl) as [dl' [Hdl' Hal1]].
    destruct (IHCIdxDemand2 b0 env_a env_b0 eq_refl) as [dr' [Hdr' Hal2]].
    pose proof (cidx_demand_length D _ _ _ H) as Hlen1.
    pose proof (cidx_demand_length D _ _ _ H0) as Hlen2.
    exists (vec_add dl' dr'); split; [constructor; assumption |].
    rewrite vec_insert_zero_add; [apply vec_allows_add; assumption | (try rewrite length_app in *); lia | lia].
  - destruct (IHCIdxDemand b0 env_a env_b0 eq_refl) as [d' [Hd' Hal]].
    pose proof (cidx_demand_length D _ _ _ H) as Hlen.
    exists (vec_scale q d'); split; [constructor; assumption |].
    rewrite vec_insert_zero_scale; [apply vec_allows_scale; [apply allows_refl | exact Hal] | (try rewrite length_app in *); lia].
  - destruct (weaken_lookup_ren D b0 env_a env_b0 b e H) as [e' [Hl' Heq]].
    assert (Hb : b < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact H).
    assert (Hbox : cty_alpha_eq (ren_cty (plus (S (weaken_rho (length env_a) b))) (cannotation e')) (CBox q CNat)).
    { unfold cty_alpha_eq in *; rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S b)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H1) as H2. exact H2. }
    apply (ren_cty_eq_CBox_Nat D (plus (S (weaken_rho (length env_a) b)))) in Hbox.
    eexists; split;
      [eapply CIdxDemandUnbox; [exact Hl' | exact Hbox]
      |rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hb]].
  - destruct (weaken_lookup_ren D b0 env_a env_b0 p e H) as [e' [Hl' Heq]].
    assert (Hp : p < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact H).
    assert (Hsig : cty_alpha_eq (ren_cty (plus (S (weaken_rho (length env_a) p))) (cannotation e'))
                     (CSigma z r CNat (ren_cty (ren_shift (weaken_rho (length env_a))) (ren_cty (ren_shift (plus (S p))) snd_ty)))).
    { unfold cty_alpha_eq in *; rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S p)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H1) as H2. exact H2. }
    destruct (ren_cty_eq_CSigma_FstNat D _ _ _ _ _ Hsig) as [z' [snd' Hsig']].
    eexists; split;
      [eapply CIdxDemandFst; [exact Hl' | exact Hsig']
      |rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hp]].
  - destruct (weaken_lookup_ren D b0 env_a env_b0 p e H) as [e' [Hl' Heq]].
    assert (Hp : p < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact H).
    assert (Hsig : cty_alpha_eq (ren_cty (plus (S (weaken_rho (length env_a) p))) (cannotation e'))
                     (CSigma z r (ren_cty (weaken_rho (length env_a)) (ren_cty (plus (S p)) fst_ty)) CNat)).
    { unfold cty_alpha_eq in *; rewrite Heq.
      pose proof (ren_cty_alpha_eq D (plus (S p)) _ _ H0) as H1.
      pose proof (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H1) as H2. exact H2. }
    destruct (ren_cty_eq_CSigma_SndNat D _ _ _ _ _ Hsig) as [z' [fst' Hsig']].
    eexists; split;
      [eapply CIdxDemandSnd; [exact Hl' | exact Hsig']
      |rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hp]].
  - destruct (weaken_lookup_ren D b0 env_a env_b0 s e H) as [e' [Hl' Heq]].
    assert (Hs : s < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact H).
    pose proof (cidx_demand_length D _ _ _ H1) as Hdl. cbn in Hdl.
    pose proof (cidx_demand_length D _ _ _ H2) as Hdr. cbn in Hdr.
    assert (Hdbr : length d_br = length (env_a ++ env_b0)).
    { rewrite (BranchVec_length D (tl dl) (tl dr) d_br); [destruct dl; cbn in *; lia | | exact H3].
      destruct dl, dr; cbn in *; lia. }
    destruct (IHCIdxDemand1 b0 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ env_b0)) |} :: env_a) env_b0 eq_refl)
      as [dl' [Hdl' Hall]].
    destruct (IHCIdxDemand2 b0 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ env_b0)) |} :: env_a) env_b0 eq_refl)
      as [dr' [Hdr' Halr]].
    cbn in Hdl', Hdr', Hall, Halr.
    replace (lift_cty (length env_a) 1 A) with (ren_cty (weaken_rho (length env_a)) A) in Hdl' by (symmetry; apply lift_as_weaken_rho).
    replace (lift_cty (length env_a) 1 B) with (ren_cty (weaken_rho (length env_a)) B) in Hdr' by (symmetry; apply lift_as_weaken_rho).
    replace (ren_cidx (weaken_rho (S (length env_a))) l) with (ren_cidx (ren_shift (weaken_rho (length env_a))) l) in Hdl'
      by (apply ren_cidx_ext; intros [| y]; unfold weaken_rho; cbn;
          [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
          |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]).
    replace (ren_cidx (weaken_rho (S (length env_a))) r) with (ren_cidx (ren_shift (weaken_rho (length env_a))) r) in Hdr'
      by (apply ren_cidx_ext; intros [| y]; unfold weaken_rho; cbn;
          [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
          |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]).
    assert (Hdl'' : CIdxDemand ({| cbinder := 0; cannotation := ren_cty (weaken_rho (length env_a)) A;
                                   ctype_uses := vec_zero (length (weaken_cenv b0 env_a env_b0)) |} :: weaken_cenv b0 env_a env_b0)
                               (ren_cidx (ren_shift (weaken_rho (length env_a))) l) dl').
    { eapply CIdxDemand_alpha_env; [| exact Hdl'].
      constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    assert (Hdr'' : CIdxDemand ({| cbinder := 0; cannotation := ren_cty (weaken_rho (length env_a)) B;
                                   ctype_uses := vec_zero (length (weaken_cenv b0 env_a env_b0)) |} :: weaken_cenv b0 env_a env_b0)
                               (ren_cidx (ren_shift (weaken_rho (length env_a))) r) dr').
    { eapply CIdxDemand_alpha_env; [| exact Hdr'].
      constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    cbn. exists (vec_add (vec_single (length (weaken_cenv b0 env_a env_b0)) (weaken_rho (length env_a) s) one)
                         (vec_join j (tl dl') (tl dr'))).
    split.
    + eapply CIdxDemandCase with (A := ren_cty (weaken_rho (length env_a)) A) (B := ren_cty (weaken_rho (length env_a)) B)
        (dl := dl') (dr := dr').
      * exact Hl'.
      * unfold cty_alpha_eq in *. rewrite Heq.
        pose proof (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H0) as Hsum. exact Hsum.
      * exact Hdl''.
      * exact Hdr''.
      * unfold BranchVec. rewrite Hj. reflexivity.
    + rewrite vec_insert_zero_add; [| rewrite vec_single_length; (try rewrite length_app in *); lia | rewrite vec_single_length; symmetry; exact Hdbr].
      apply vec_allows_add.
      * rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hs].
      * unfold BranchVec in H3. rewrite Hj in H3. subst d_br.
        destruct dl as [| al dl_t], dr as [| ar dr_t]; cbn in *; try lia.
        eapply vec_allows_trans.
        -- eapply vec_allows_join_mono; [exact Hj | apply vec_allows_tl; exact Hall | apply vec_allows_tl; exact Halr].
        -- apply vec_allows_join_insert_zero; [exact Hj | (try rewrite length_app in *); lia | lia].
Qed.

Lemma weaken_ctype_demand_join : forall (D : JoinDomain) j (b : cbinding D) env_a env_b (T : cty D) d,
  grade_join D = Some j ->
  CTypeDemand (env_a ++ env_b) T d ->
  exists d', CTypeDemand (weaken_cenv b env_a env_b) (ren_cty (weaken_rho (length env_a)) T) d' /\
             vec_allows d' (vec_insert_zero (length env_a) d).
Proof.
  intros D j b env_a env_b T d Hj H.
  remember (env_a ++ env_b) as env1 eqn:Henv1.
  revert b env_a env_b Henv1.
  induction H using CTypeDemand_ind_mut with
    (P := fun env1 T d _ => forall b0 env_a env_b0, env1 = env_a ++ env_b0 ->
            exists d', CTypeDemand (weaken_cenv b0 env_a env_b0) (ren_cty (weaken_rho (length env_a)) T) d' /\
                       vec_allows d' (vec_insert_zero (length env_a) d))
    (P0 := fun env1 fs df _ => forall b0 env_a env_b0, env1 = env_a ++ env_b0 ->
             exists df', CRecordFieldDemand (weaken_cenv b0 env_a env_b0) (map (fun '(fn, fg, ft) => (fn, fg, ren_cty (weaken_rho (length env_a)) ft)) fs) df' /\
                         vec_allows df' (vec_insert_zero (length env_a) df))
    (P1 := fun env1 ls dl _ => forall b0 env_a env_b0, env1 = env_a ++ env_b0 ->
             exists dl', CIdxListDemand (weaken_cenv b0 env_a env_b0) (map (ren_cidx (weaken_rho (length env_a))) ls) dl' /\
                         vec_allows dl' (vec_insert_zero (length env_a) dl));
    intros b0 env_a env_b0 Henv1; subst env; cbn.
  - eexists; split; [constructor | rewrite weaken_cenv_length, length_app, vec_insert_zero_zero; [apply vec_allows_refl | lia]].
  - eexists; split; [constructor | rewrite weaken_cenv_length, length_app, vec_insert_zero_zero; [apply vec_allows_refl | lia]].
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [de' [Hde' Hale]].
    match goal with
    | Htd : CTypeDemand _ _ _, Hidx : CIdxDemand _ _ _ |- _ =>
        destruct (weaken_cidx_demand_join D j b0 env_a env_b0 len dl Hj Hidx) as [dl' [Hdl' Hall]];
        pose proof (ctype_demand_length D _ _ _ Htd) as Hlen1;
        pose proof (cidx_demand_length D _ _ _ Hidx) as Hlen2;
        exists (vec_add de' dl'); split; [constructor; assumption |];
        rewrite vec_insert_zero_add; [apply vec_allows_add; assumption | (try rewrite length_app in *); lia | lia]
    end.
  - eexists; split; [constructor | rewrite weaken_cenv_length, length_app, vec_insert_zero_zero; [apply vec_allows_refl | lia]].
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (weaken_lookup_ren D b0 env_a env_b0 x e Hl) as [e' [Hl' Heq]];
        assert (Hx : x < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact Hl);
        assert (Hun : cty_alpha_eq (ren_cty (plus (S (weaken_rho (length env_a) x))) (cannotation e')) (CUniv lvl)) by
          (unfold cty_alpha_eq in *; rewrite Heq;
           pose proof (ren_cty_alpha_eq D (plus (S x)) _ _ Hc) as H1;
           exact (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H1));
        apply (ren_cty_eq_CUniv D (plus (S (weaken_rho (length env_a) x)))) in Hun;
        eexists; split;
          [eapply CTypeTVar; [exact Hl' | exact Hun]
          |rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hx]]
    end.
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [di' [Hdi' Hali]].
    match goal with
    | Htd : CTypeDemand _ _ _ |- _ =>
        pose proof (ctype_demand_length D _ _ _ Htd) as Hlen;
        exists (vec_scale q di'); split; [constructor; assumption |];
        rewrite vec_insert_zero_scale; [apply vec_allows_scale; [apply allows_refl | exact Hali] | (try rewrite length_app in *); lia]
    end.
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (weaken_lookup_ren D b0 env_a env_b0 b e Hl) as [e' [Hl' Heq]];
        assert (Hb : b < length (env_a ++ env_b0)) by (eapply clookup_lt_length; exact Hl);
        assert (Hbox : cty_alpha_eq (ren_cty (plus (S (weaken_rho (length env_a) b))) (cannotation e')) (CBox q (CUniv lvl))) by
          (unfold cty_alpha_eq in *; rewrite Heq;
           pose proof (ren_cty_alpha_eq D (plus (S b)) _ _ Hc) as H1;
           exact (ren_cty_alpha_eq D (weaken_rho (length env_a)) _ _ H1));
        apply (ren_cty_eq_CBox_Univ D (plus (S (weaken_rho (length env_a) b)))) in Hbox;
        eexists; split;
          [eapply CTypeTUnbox; [exact Hl' | exact Hbox]
          |rewrite weaken_cenv_length; rewrite length_app in *; rewrite vec_insert_zero_single; [apply vec_allows_refl | lia | exact Hb]]
    end.
  - destruct (IHCTypeDemand1 b0 env_a env_b0 eq_refl) as [a' [Ha' Hala]].
    destruct (IHCTypeDemand2 b0 ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) env_b0 eq_refl)
      as [b' [Hb' Halb]].
    cbn in Hb', Halb.
    replace (lift_cty (length env_a) 1 dom) with (ren_cty (weaken_rho (length env_a)) dom) in Hb'
      by (symmetry; apply lift_as_weaken_rho).
    replace (ren_cty (weaken_rho (S (length env_a))) cod) with (ren_cty (ren_shift (weaken_rho (length env_a))) cod) in Hb'
      by (apply ren_cty_ext; intros [| y]; unfold weaken_rho; cbn;
          [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
          |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]).
    assert (Hb'' : CTypeDemand ({| cbinder := x; cannotation := ren_cty (weaken_rho (length env_a)) dom; ctype_uses := a' |} :: weaken_cenv b0 env_a env_b0)
                               (ren_cty (ren_shift (weaken_rho (length env_a))) cod) b').
    { eapply CTypeDemand_alpha_env; [| exact Hb'].
      constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    match goal with
    | H1 : CTypeDemand (env_a ++ env_b0) dom _,
      H2 : CTypeDemand (_ :: env_a ++ env_b0) cod _,
      H3 : allows _ r |- _ =>
        rename H1 into Hdom; rename H2 into Hcod; rename H3 into Hal0
    end.
    pose proof (ctype_demand_length D _ _ _ Hdom) as Hla.
    pose proof (ctype_demand_length D _ _ _ Hcod) as Hlb. cbn in Hlb.
    match type of Hcod with CTypeDemand _ _ ?vb =>
      destruct vb as [| bd0 bd']; cbn in *; [lia |]
    end.
    destruct b' as [| bd0' b'_t]; [inversion Halb |].
    exists (vec_add a' b'_t); split.
    + eapply CTypePi with (b := bd0' :: b'_t);
        [exact Ha' | exact Hb'' | cbn; inversion Halb; subst; eapply allows_trans; [eassumption | exact Hal0]].
    + rewrite vec_insert_zero_add; [apply vec_allows_add; [exact Hala | inversion Halb; assumption] | (try rewrite length_app in *); lia | lia].
  - destruct (IHCTypeDemand1 b0 env_a env_b0 eq_refl) as [a' [Ha' Hala]].
    destruct (IHCTypeDemand2 b0 ({| cbinder := x; cannotation := f; ctype_uses := a |} :: env_a) env_b0 eq_refl)
      as [b' [Hb' Halb]].
    cbn in Hb', Halb.
    replace (lift_cty (length env_a) 1 f) with (ren_cty (weaken_rho (length env_a)) f) in Hb'
      by (symmetry; apply lift_as_weaken_rho).
    replace (ren_cty (weaken_rho (S (length env_a))) s) with (ren_cty (ren_shift (weaken_rho (length env_a))) s) in Hb'
      by (apply ren_cty_ext; intros [| y]; unfold weaken_rho; cbn;
          [destruct (0 <? S (length env_a)) eqn:E0; [reflexivity | apply Nat.ltb_ge in E0; lia]
          |destruct (S y <? S (length env_a)) eqn:E1; destruct (y <? length env_a) eqn:E2; nat_bool_hyps; try reflexivity; lia]).
    assert (Hb'' : CTypeDemand ({| cbinder := x; cannotation := ren_cty (weaken_rho (length env_a)) f; ctype_uses := a' |} :: weaken_cenv b0 env_a env_b0)
                               (ren_cty (ren_shift (weaken_rho (length env_a))) s) b').
    { eapply CTypeDemand_alpha_env; [| exact Hb'].
      constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    match goal with
    | H1 : CTypeDemand (env_a ++ env_b0) f _,
      H2 : CTypeDemand (_ :: env_a ++ env_b0) s _,
      H3 : allows _ r |- _ =>
        rename H1 into Hdom; rename H2 into Hcod; rename H3 into Hal0
    end.
    pose proof (ctype_demand_length D _ _ _ Hdom) as Hla.
    pose proof (ctype_demand_length D _ _ _ Hcod) as Hlb. cbn in Hlb.
    match type of Hcod with CTypeDemand _ _ ?vb =>
      destruct vb as [| bd0 bd']; cbn in *; [lia |]
    end.
    destruct b' as [| bd0' b'_t]; [inversion Halb |].
    exists (vec_add a' b'_t); split.
    + eapply CTypeSigma with (b := bd0' :: b'_t);
        [exact Ha' | exact Hb'' | cbn; inversion Halb; subst; eapply allows_trans; [eassumption | exact Hal0]].
    + rewrite vec_insert_zero_add; [apply vec_allows_add; [exact Hala | inversion Halb; assumption] | (try rewrite length_app in *); lia | lia].
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [d' [Hd' Hal]].
    exists d'; split; [constructor; exact Hd' | exact Hal].
  - destruct (IHCTypeDemand1 b0 env_a env_b0 eq_refl) as [dl' [Hdl' Hall]].
    destruct (IHCTypeDemand2 b0 env_a env_b0 eq_refl) as [dr' [Hdr' Halr]].
    match goal with
    | H1 : CTypeDemand _ l _, H2 : CTypeDemand _ r _ |- _ =>
        rename H1 into Htdl; rename H2 into Htdr
    end.
    pose proof (ctype_demand_length D _ _ _ Htdl) as Hlen1.
    pose proof (ctype_demand_length D _ _ _ Htdr) as Hlen2.
    exists (vec_add dl' dr'); split; [constructor; assumption |].
    rewrite vec_insert_zero_add; [apply vec_allows_add; assumption | (try rewrite length_app in *); lia | lia].
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [df' [Hdf' Hal]].
    exists df'; split; [constructor; exact Hdf' | exact Hal].
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [di' [Hdi' Hal]].
    exists di'; split; [constructor; exact Hdi' | exact Hal].
  - eexists; split; [constructor | rewrite weaken_cenv_length, length_app, vec_insert_zero_zero; [apply vec_allows_refl | lia]].
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [dt' [Hdt' Halt]].
    destruct (IHCTypeDemand0 b0 env_a env_b0 eq_refl) as [dr' [Hdr' Halr]].
    match goal with
    | H1 : CTypeDemand _ ft _, H2 : CRecordFieldDemand _ rest _ |- _ =>
        rename H1 into Htd; rename H2 into Hrec
    end.
    pose proof (ctype_demand_length D _ _ _ Htd) as Hlen1.
    pose proof (proj1 (record_field_and_idx_list_demand_length D) _ _ _ Hrec) as Hlen2.
    exists (vec_add dt' dr'); split; [constructor; assumption |].
    rewrite vec_insert_zero_add; [apply vec_allows_add; assumption | (try rewrite length_app in *); lia | lia].
  - eexists; split; [constructor | rewrite weaken_cenv_length, length_app, vec_insert_zero_zero; [apply vec_allows_refl | lia]].
  - destruct (IHCTypeDemand b0 env_a env_b0 eq_refl) as [dr' [Hdr' Halr]].
    match goal with
    | H1 : CIdxDemand _ idx _, H2 : CIdxListDemand _ rest _ |- _ =>
        rename H1 into Hidx; rename H2 into Hrec
    end.
    match type of Hidx with CIdxDemand _ idx ?di0 =>
      destruct (weaken_cidx_demand_join D j b0 env_a env_b0 idx di0 Hj Hidx) as [di' [Hdi' Hali]]
    end.
    pose proof (cidx_demand_length D _ _ _ Hidx) as Hlen1.
    pose proof (proj2 (record_field_and_idx_list_demand_length D) _ _ _ Hrec) as Hlen2.
    exists (vec_add di' dr'); split; [constructor; assumption |].
    rewrite vec_insert_zero_add; [apply vec_allows_add; assumption | (try rewrite length_app in *); lia | lia].
Qed.

Lemma swap_RenEnv : forall (D : JoinDomain) x1 x2 (T1 T2 : cty D) a1 a2 env_a env_b,
  let e1 := {| cbinder := x1; cannotation := lift_cty 0 1 T1; ctype_uses := zero :: a1 |} in
  let e2 := {| cbinder := x2; cannotation := T2; ctype_uses := a2 |} in
  let e2' := {| cbinder := x2; cannotation := lift_cty 0 1 T2; ctype_uses := zero :: a2 |} in
  let e1' := {| cbinder := x1; cannotation := T1; ctype_uses := a1 |} in
  RenEnv (env_a ++ [e1; e2] ++ env_b) (swap_cenv e2' e1' env_a env_b)
    (swap_rho (length env_a)) (vec_swap (length env_a)).
Proof.
  intros D x1 x2 T1 T2 a1 a2 env_a env_b e1 e2 e2' e1'.
  induction env_a as [| e0 rest IH].
  - cbn. unfold e1, e2, e2', e1' in *. constructor.
    + constructor.
      * apply swap_RenSpec; cbn; lia.
      * intros [| [| x']] e Hl; cbn in Hl.
        -- inversion Hl; subst; cbn.
           eexists; split; [reflexivity |].
           cbn [cannotation].
           rewrite lift_as_weaken_rho, !ren_cty_comp.
           apply ren_cty_ext; intros [| y]; unfold swap_rho, weaken_rho; cbn; reflexivity.
        -- inversion Hl; subst; cbn.
           eexists; split; [reflexivity |].
           cbn [cannotation].
           rewrite lift_as_weaken_rho, !ren_cty_comp.
           apply ren_cty_ext; intros [| y]; unfold swap_rho, weaken_rho; cbn; reflexivity.
        -- exists e; split; [exact Hl |].
           rewrite ren_cty_comp. apply ren_cty_ext; intro y; unfold swap_rho; cbn; reflexivity.
    + intros [| [| x']] e Hl; cbn in Hl.
      * inversion Hl; subst; cbn.
        eexists; repeat split.
        -- cbn [cannotation]. rewrite lift_as_weaken_rho, !ren_cty_comp.
           apply ren_cty_ext; intros [| y]; unfold swap_rho, weaken_rho; cbn; reflexivity.
        -- intros row Hrow Hal. exists (tl row). split.
           ++ apply strengthen_0_ctype_demand with (b := e2). exact Hrow.
           ++ apply vec_allows_tl in Hal; exact Hal.
      * inversion Hl; subst; cbn.
        eexists; repeat split.
        -- cbn [cannotation]. rewrite lift_as_weaken_rho, !ren_cty_comp.
           apply ren_cty_ext; intros [| y]; unfold swap_rho, weaken_rho; cbn; reflexivity.
        -- intros row Hrow Hal.
           destruct (grade_join D) as [j |] eqn:Hj.
           ++ destruct (weaken_ctype_demand_join D j e1' [] env_b T2 row Hj Hrow) as [row' [Hrow' Hallow']].
              cbn in Hrow', Hallow'. rewrite <- lift_as_weaken_rho in Hrow'.
              exists row'; split; [exact Hrow' |].
              eapply vec_allows_trans; [exact Hallow' | constructor; [apply allows_refl | exact Hal]].
           ++ exists (zero :: row); split.
              ** rewrite lift_as_weaken_rho.
                 replace (zero :: row) with (vec_insert_zero 0 row) by reflexivity.
                 change (e1' :: env_b) with (weaken_cenv e1' [] env_b).
                 eapply ren_ctype_demand; [exact (re_type (weaken_RenEnv D e1' [] env_b ltac:(intros j0 Hj0; rewrite Hj in Hj0; discriminate))) | exact Hrow].
              ** constructor; [apply allows_refl | exact Hal].
      * exists e; repeat split; [exact Hl | |].
        -- rewrite ren_cty_comp. apply ren_cty_ext; intro y; unfold swap_rho; cbn; reflexivity.
        -- intros row Hrow Hal; exists row; split; assumption.
  - (* inductive step rest *)
    cbn. constructor.
    + constructor.
      * replace (length ({| cbinder := cbinder e0;
                           cannotation := ren_cty (swap_rho (length rest)) (cannotation e0);
                           ctype_uses := vec_swap (length rest) (ctype_uses e0) |} :: swap_cenv e2' e1' rest env_b))
          with (length (e0 :: rest ++ e1 :: e2 :: env_b))
          by (cbn; rewrite swap_cenv_length, !length_app; cbn; lia).
        apply swap_RenSpec. cbn; rewrite length_app; cbn; lia.
      * intros [| x'] e Hl; cbn in Hl.
        -- inversion Hl; subst; cbn.
           eexists; split; [reflexivity |].
           cbn [cannotation].
           rewrite !ren_cty_comp. apply ren_cty_ext; intro y; unfold swap_rho; cbn.
           destruct (y =? length rest) eqn:E1; [rw_nat_bool; reflexivity | destruct (y =? S (length rest)) eqn:E2; rw_nat_bool; reflexivity].
        -- destruct (rte_lookup _ _ _ _ (re_type IH) x' e Hl) as [e' [Hl' Heq]].
           rewrite swap_rho_S_swap. exists e'; split; [exact Hl' |].
           transitivity (ren_cty S (ren_cty (plus (S (swap_rho (length rest) x'))) (cannotation e')));
             [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
             | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; unfold swap_rho; cbn;
               destruct (S x' + y =? length rest) eqn:E1;
                 [rw_nat_bool; destruct (S (S x' + y) =? S (length rest)) eqn:E2;
                    [reflexivity | apply Nat.eqb_neq in E2; apply Nat.eqb_eq in E1; lia]
                 |destruct (S x' + y =? S (length rest)) eqn:E2; rw_nat_bool; reflexivity] ].
    + intros [| x'] e Hl; cbn in Hl.
      * inversion Hl; subst; cbn.
        eexists; repeat split.
        -- cbn [cannotation]. rewrite !ren_cty_comp. apply ren_cty_ext; intro y; unfold swap_rho; cbn.
           destruct (y =? length rest) eqn:E1; [rw_nat_bool; reflexivity | destruct (y =? S (length rest)) eqn:E2; rw_nat_bool; reflexivity].
        -- intros row Hrow Hal. exists (vec_swap (length rest) row). split.
           ++ eapply ren_ctype_demand; [exact (re_type IH) | exact Hrow].
           ++ apply vec_swap_allows; exact Hal.
      * destruct (re_uses IH x' e Hl) as [e' [Hl' [Heq [Hvec Htd]]]].
        rewrite swap_rho_S_swap. exists e'; repeat split; [exact Hl' | | | exact Htd].
        -- transitivity (ren_cty S (ren_cty (plus (S (swap_rho (length rest) x'))) (cannotation e')));
             [ rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
             | rewrite Heq, !ren_cty_comp; apply ren_cty_ext; intro y; unfold swap_rho; cbn;
               destruct (S x' + y =? length rest) eqn:E1;
                 [rw_nat_bool; reflexivity
                 |destruct (S x' + y =? S (length rest)) eqn:E2; rw_nat_bool; reflexivity] ].
        -- transitivity (zero :: vec_zero (S (swap_rho (length rest) x')) ++ ctype_uses e');
             [reflexivity | rewrite Hvec; reflexivity].
Qed.

Theorem core_exchange : forall (D : JoinDomain) x1 x2 (T1 T2 : cty D) a1 a2 env_a env_b t j,
  let e1 := {| cbinder := x1; cannotation := lift_cty 0 1 T1; ctype_uses := zero :: a1 |} in
  let e2 := {| cbinder := x2; cannotation := T2; ctype_uses := a2 |} in
  let e2' := {| cbinder := x2; cannotation := lift_cty 0 1 T2; ctype_uses := zero :: a2 |} in
  let e1' := {| cbinder := x1; cannotation := T1; ctype_uses := a1 |} in
  CoreDerives (env_a ++ [e1; e2] ++ env_b) t j ->
  CoreDerives (swap_cenv e2' e1' env_a env_b) (ren_cterm (swap_rho (length env_a)) t)
    {| cresult_type := ren_cty (swap_rho (length env_a)) (cresult_type j);
       ccomp_demand := vec_swap (length env_a) (ccomp_demand j);
       ctype_demand_row := vec_swap (length env_a) (ctype_demand_row j) |}.
Proof.
  intros D x1 x2 T1 T2 a1 a2 env_a env_b t j e1 e2 e2' e1' H.
  eapply ren_core_derives; [apply swap_RenEnv | exact H].
Qed.

(* ================================================================= *)
(* Part 3: Value Substitution and Type Substitution                  *)
(* ================================================================= *)

Lemma vec_scale_add_l : forall (D : JoinDomain) (q r : grade D) (u : list (grade D)),
  vec_scale (add q r) u = vec_add (vec_scale q u) (vec_scale r u).
Proof.
  intros D q r u. unfold vec_scale. induction u as [| a u IH]; cbn; [reflexivity |].
  rewrite mul_add_r, IH. reflexivity.
Qed.

Lemma vec_allows_join_least : forall (D : JoinDomain) j (u1 u2 w : list (grade D)),
  grade_join D = Some j ->
  vec_allows u1 w ->
  vec_allows u2 w ->
  vec_allows (vec_join j u1 u2) w.
Proof.
  intros D j u1 u2 w Hj H1. revert u2.
  induction H1; intros u2 H2; inversion H2; subst; cbn; constructor;
    [apply (join_least D j Hj); assumption | apply IHForall2; assumption].
Qed.

Lemma vec_allows_join_left : forall (D : JoinDomain) j (u1 u2 : list (grade D)),
  grade_join D = Some j ->
  length u1 = length u2 ->
  vec_allows u1 (vec_join j u1 u2).
Proof.
  intros D j u1. induction u1 as [| a u1 IH]; intros [| b u2] Hj Hlen; cbn in *; try lia;
    constructor; [apply (join_left D j Hj) | apply IH; [exact Hj | lia]].
Qed.

Lemma vec_allows_join_right : forall (D : JoinDomain) j (u1 u2 : list (grade D)),
  grade_join D = Some j ->
  length u1 = length u2 ->
  vec_allows u2 (vec_join j u1 u2).
Proof.
  intros D j u1. induction u1 as [| a u1 IH]; intros [| b u2] Hj Hlen; cbn in *; try lia;
    constructor; [apply (join_right D j Hj) | apply IH; [exact Hj | lia]].
Qed.

Definition branch_rel {D : JoinDomain} (u v : list (grade D)) : Prop :=
  match grade_join D with
  | Some _ => vec_allows u v
  | None => u = v
  end.

Lemma branch_rel_refl : forall (D : JoinDomain) (u : list (grade D)),
  branch_rel u u.
Proof.
  intros D u. unfold branch_rel. destruct (grade_join D); [apply vec_allows_refl | reflexivity].
Qed.

Lemma branch_rel_trans : forall (D : JoinDomain) (u v w : list (grade D)),
  branch_rel u v -> branch_rel v w -> branch_rel u w.
Proof.
  intros D u v w H1 H2. unfold branch_rel in *.
  destruct (grade_join D); [eapply vec_allows_trans; eassumption | congruence].
Qed.

Lemma branch_rel_allows : forall (D : JoinDomain) (u v : list (grade D)),
  branch_rel u v -> vec_allows u v.
Proof.
  intros D u v H. unfold branch_rel in H.
  destruct (grade_join D); [exact H | subst; apply vec_allows_refl].
Qed.

Lemma branch_rel_length : forall (D : JoinDomain) (u v : list (grade D)),
  branch_rel u v -> length u = length v.
Proof.
  intros D u v H. apply branch_rel_allows in H. apply vec_allows_length in H; exact H.
Qed.

Lemma branch_rel_add : forall (D : JoinDomain) (u1 u2 v1 v2 : list (grade D)),
  branch_rel u1 u2 -> branch_rel v1 v2 -> branch_rel (vec_add u1 v1) (vec_add u2 v2).
Proof.
  intros D u1 u2 v1 v2 H1 H2. unfold branch_rel in *.
  destruct (grade_join D); [apply vec_allows_add; assumption | congruence].
Qed.

Lemma branch_rel_scale : forall (D : JoinDomain) (q : grade D) (u1 u2 : list (grade D)),
  branch_rel u1 u2 -> branch_rel (vec_scale q u1) (vec_scale q u2).
Proof.
  intros D q u1 u2 H. unfold branch_rel in *.
  destruct (grade_join D); [apply vec_allows_scale; [apply allows_refl | exact H] | congruence].
Qed.

Lemma branch_rel_tl : forall (D : JoinDomain) (u v : list (grade D)),
  branch_rel u v -> branch_rel (tl u) (tl v).
Proof.
  intros D u v H. unfold branch_rel in *.
  destruct (grade_join D); [apply vec_allows_tl; exact H | congruence].
Qed.

Lemma branch_rel_nth : forall (D : JoinDomain) (u v : list (grade D)) i,
  branch_rel u v -> allows (nth_grade u i) (nth_grade v i).
Proof.
  intros D u v i H. apply vec_allows_nth. apply branch_rel_allows; exact H.
Qed.

Fixpoint vec_subst {D : JoinDomain} (k : nat) (z u : list (grade D)) : list (grade D) :=
  match k, u with
  | 0, q :: u_b => vec_add u_b (vec_scale q z)
  | 0, [] => []
  | S k', a :: u' => a :: vec_subst k' z u'
  | S _, [] => []
  end.

Lemma vec_subst_length : forall (D : JoinDomain) k (z u : list (grade D)) n_b,
  length z = n_b ->
  length u = S (k + n_b) ->
  length (vec_subst k z u) = k + n_b.
Proof.
  intros D k. induction k as [| k IH]; intros z [| a u'] n_b Hz Hu; cbn in *; try lia.
  - rewrite vec_add_length; [lia | rewrite vec_scale_length; lia].
  - f_equal. apply IH; [exact Hz | lia].
Qed.

Lemma vec_subst_zero : forall (D : JoinDomain) k (z : list (grade D)) n_b,
  length z = n_b ->
  vec_subst k z (vec_zero (S (k + n_b))) = vec_zero (k + n_b).
Proof.
  intros D k. induction k as [| k IH]; intros z n_b Hz; unfold vec_zero in *; cbn.
  - rewrite vec_scale_zero, Hz.
    rewrite <- (repeat_length (@zero D) n_b) at 1. apply vec_add_zero_l.
  - f_equal. apply (IH z n_b Hz).
Qed.

Lemma vec_subst_single_lt : forall (D : JoinDomain) k (z : list (grade D)) n_b x q,
  length z = n_b ->
  x < k ->
  vec_subst k z (vec_single (S (k + n_b)) x q) = vec_single (k + n_b) x q.
Proof.
  intros D k. induction k as [| k IH]; intros z n_b [| x'] q Hz Hlt; cbn in *; try lia.
  - f_equal. apply vec_subst_zero; exact Hz.
  - f_equal. apply IH; [exact Hz | lia].
Qed.

Lemma vec_subst_single_eq : forall (D : JoinDomain) k (z : list (grade D)) n_b q,
  length z = n_b ->
  vec_subst k z (vec_single (S (k + n_b)) k q) = vec_zero k ++ vec_scale q z.
Proof.
  intros D k. induction k as [| k IH]; intros z n_b q Hz; cbn.
  - change (repeat (@zero D) n_b) with (vec_zero (D := D) n_b).
    rewrite <- Hz, <- (vec_scale_length D q z) at 1. apply vec_add_zero_l.
  - f_equal. apply IH; exact Hz.
Qed.

Lemma vec_subst_single_gt : forall (D : JoinDomain) k (z : list (grade D)) n_b x q,
  length z = n_b ->
  x > k -> x < S (k + n_b) ->
  vec_subst k z (vec_single (S (k + n_b)) x q) = vec_single (k + n_b) (x - 1) q.
Proof.
  intros D k. induction k as [| k IH]; intros z n_b [| x'] q Hz Hgt Hlt; cbn in *; try lia.
  - rewrite vec_scale_zero, Hz, Nat.sub_0_r.
    change (vec_zero n_b) with (vec_zero (D := D) n_b).
    rewrite <- (vec_single_length D n_b x' q) at 2. apply vec_add_zero_r.
  - rewrite (IH z n_b x' q Hz ltac:(lia) ltac:(lia)).
    destruct x'; [lia | cbn; rewrite !Nat.sub_0_r; reflexivity].
Qed.

Lemma vec_subst_add : forall (D : JoinDomain) k (z u v : list (grade D)) n_b,
  length z = n_b ->
  length u = S (k + n_b) ->
  length v = S (k + n_b) ->
  vec_subst k z (vec_add u v) = vec_add (vec_subst k z u) (vec_subst k z v).
Proof.
  intros D k. induction k as [| k IH]; intros z [| a u'] [| b v'] n_b Hz Hu Hv; cbn in *; try lia.
  - rewrite vec_scale_add_l.
    rewrite !vec_add_assoc. f_equal.
    rewrite <- !vec_add_assoc. f_equal. apply vec_add_comm.
  - f_equal. apply (IH z u' v' n_b Hz ltac:(lia) ltac:(lia)).
Qed.

Lemma vec_subst_scale : forall (D : JoinDomain) k (z u : list (grade D)) q,
  vec_subst k z (vec_scale q u) = vec_scale q (vec_subst k z u).
Proof.
  intros D k. induction k as [| k IH]; intros z [| a u'] q.
  - cbn. unfold vec_scale. cbn. reflexivity.
  - cbn [vec_subst]. unfold vec_scale at 1. cbn [map].
    change (map (mul q) u') with (vec_scale (D := D) q u').
    cbn [vec_subst]. rewrite vec_scale_add, vec_scale_mul. reflexivity.
  - cbn. unfold vec_scale. cbn. reflexivity.
  - unfold vec_scale at 1. cbn [map].
    change (map (mul q) u') with (vec_scale (D := D) q u').
    cbn [vec_subst]. rewrite IH.
    change (vec_scale q (a :: vec_subst k z u')) with (mul q a :: vec_scale (D := D) q (vec_subst k z u')).
    reflexivity.
Qed.

Lemma vec_subst_allows : forall (D : JoinDomain) k (z u v : list (grade D)),
  vec_allows u v ->
  vec_allows (vec_subst k z u) (vec_subst k z v).
Proof.
  intros D k. induction k as [| k IH]; intros z u v H; cbn.
  - inversion H; subst; cbn; [constructor |].
    apply vec_allows_add; [assumption | apply vec_allows_scale; [assumption | apply vec_allows_refl]].
  - inversion H; subst; cbn; [constructor | constructor; [assumption | apply IH; assumption]].
Qed.

Lemma branch_rel_subst : forall (D : JoinDomain) k (z u v : list (grade D)),
  branch_rel u v ->
  branch_rel (vec_subst k z u) (vec_subst k z v).
Proof.
  intros D k z u v H. unfold branch_rel in *.
  destruct (grade_join D); [apply vec_subst_allows; exact H | subst; reflexivity].
Qed.

Lemma vec_subst_tl : forall (D : JoinDomain) k (z u : list (grade D)),
  vec_subst k z (tl u) = tl (vec_subst (S k) z u).
Proof.
  intros D k z [| a u']; [destruct k; reflexivity | cbn; reflexivity].
Qed.

Lemma vec_subst_nth_lt : forall (D : JoinDomain) k (z u : list (grade D)) i,
  i < k -> k < length u ->
  nth_grade (vec_subst k z u) i = nth_grade u i.
Proof.
  intros D k. induction k as [| k IH]; intros z [| a u'] [| i'] Hi Hk;
    unfold nth_grade, nth_default in *; cbn in *; try lia; try reflexivity.
  apply IH; lia.
Qed.

Lemma vec_subst_zero_prefix : forall (D : JoinDomain) k (z a : list (grade D)),
  length z = length a ->
  vec_subst k z (vec_zero (S k) ++ a) = vec_zero k ++ a.
Proof.
  intros D k. induction k as [| k IH]; intros z a Hz; cbn.
  - rewrite vec_scale_zero, Hz. apply vec_add_zero_r.
  - f_equal. apply IH; exact Hz.
Qed.

Lemma vec_subst_zero_app : forall (D : JoinDomain) m k (z a : list (grade D)) n_b,
  length z = n_b ->
  length a = S (k + n_b) ->
  vec_zero m ++ vec_subst k z a = vec_subst (m + k) z (vec_zero m ++ a).
Proof.
  intros D m. induction m as [| m IH]; intros k z a n_b Hz Ha; cbn; [reflexivity |].
  f_equal. apply (IH k z a n_b Hz Ha).
Qed.

Lemma vec_subst_allows_join : forall (D : JoinDomain) j k (z u v : list (grade D)) n_b,
  grade_join D = Some j ->
  length z = n_b ->
  length u = S (k + n_b) ->
  length v = S (k + n_b) ->
  vec_allows (vec_join j (vec_subst k z u) (vec_subst k z v)) (vec_subst k z (vec_join j u v)).
Proof.
  intros D j k z u v n_b Hj Hz Hu Hv.
  eapply vec_allows_join_least; [exact Hj | |].
  - apply vec_subst_allows. apply (vec_allows_join_left D j); [exact Hj | lia].
  - apply vec_subst_allows. apply (vec_allows_join_right D j); [exact Hj | lia].
Qed.

Lemma BranchVec_subst : forall (D : JoinDomain) k (z u1 u2 u u1' u2' : list (grade D)) n_b,
  length z = n_b ->
  length u1 = S (k + n_b) ->
  length u2 = S (k + n_b) ->
  BranchVec u1 u2 u ->
  branch_rel u1' (vec_subst k z u1) ->
  branch_rel u2' (vec_subst k z u2) ->
  exists u', BranchVec u1' u2' u' /\ branch_rel u' (vec_subst k z u).
Proof.
  intros D k z u1 u2 u u1' u2' n_b Hz Hu1 Hu2 Hbr H1 H2.
  unfold BranchVec, branch_rel in *.
  destruct (grade_join D) as [j |] eqn:Hj.
  - subst u. exists (vec_join j u1' u2'). split; [reflexivity |].
    eapply vec_allows_trans.
    + eapply vec_allows_join_mono; [exact Hj | exact H1 | exact H2].
    + apply (vec_subst_allows_join D j k z u1 u2 n_b Hj Hz Hu1 Hu2).
  - destruct Hbr as [-> ->]. subst. exists (vec_subst k z u2). split; [split; reflexivity | reflexivity].
Qed.

Lemma vec_subst_firstn : forall (D : JoinDomain) m k (z u : list (grade D)),
  firstn m (vec_subst (m + k) z u) = firstn m u.
Proof.
  intros D m. induction m as [| m IH]; intros k z [| a u']; cbn; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma vec_subst_skipn : forall (D : JoinDomain) m k (z u : list (grade D)),
  skipn m (vec_subst (m + k) z u) = vec_subst k z (skipn m u).
Proof.
  intros D m. induction m as [| m IH]; intros k z [| a u']; cbn; try reflexivity.
  - destruct k; reflexivity.
  - apply IH.
Qed.

Lemma branch_rel_is_zero : forall (D : JoinDomain),
  (forall a : grade D, allows a zero -> a = zero) ->
  forall (u v : list (grade D)), branch_rel u v -> vec_is_zero v = true -> vec_is_zero u = true.
Proof.
  intros D Haz u v Hbr Hz. apply vec_is_zero_spec. apply vec_is_zero_spec in Hz.
  apply branch_rel_allows in Hbr.
  assert (Hlen : length u = length v) by (apply vec_allows_length in Hbr; exact Hbr).
  rewrite Hz in Hbr.
  rewrite <- Hlen in Hbr. clear Hz Hlen v.
  unfold vec_zero in *. induction u as [| a u IH]; cbn in *; [reflexivity |].
  inversion Hbr as [| ? ? ? ? Ha Hrest]; subst. apply Haz in Ha. subst a. f_equal. apply IH; exact Hrest.
Qed.

(* Uniqueness of CIdxDemand and CTypeDemand up to cenv_alpha_eq *)

Lemma BranchVec_alpha_det : forall (D : JoinDomain) (u1 u2 u v1 v2 v : list (grade D)),
  u1 = v1 -> u2 = v2 -> BranchVec u1 u2 u -> BranchVec v1 v2 v -> u = v.
Proof.
  intros D u1 u2 u v1 v2 v -> -> H1 H2. unfold BranchVec in *.
  destruct (grade_join D); [congruence | destruct H1 as [_ ->]; destruct H2 as [_ ->]; reflexivity].
Qed.

Lemma cidx_demand_unique : forall (D : JoinDomain) (env1 env2 : cenv D) i d1 d2,
  cenv_alpha_eq env1 env2 ->
  CIdxDemand env1 i d1 ->
  CIdxDemand env2 i d2 ->
  d1 = d2.
Proof.
  intros D env1 env2 i d1 d2 Henv H1. revert env2 d2 Henv.
  induction H1; intros env2 d2 Henv H2; inversion H2; subst;
    try rewrite (cenv_alpha_eq_length _ _ _ Henv); try reflexivity.
  - f_equal; [eapply IHCIdxDemand1; eassumption | eapply IHCIdxDemand2; eassumption].
  - f_equal; eapply IHCIdxDemand; eassumption.
  - match goal with
    | Hl : clookup env s = Some e, Hlk2 : clookup env2 s = Some _,
      Ha1 : cty_alpha_eq (ren_cty (plus (S s)) (cannotation e)) (CSum A B),
      Ha2 : cty_alpha_eq (ren_cty (plus (S s)) _) (CSum ?A2 ?B2),
      Hd2 : CIdxDemand ({| cbinder := 0; cannotation := ?A2; ctype_uses := _ |} :: env2) l _,
      Hd4 : CIdxDemand ({| cbinder := 0; cannotation := ?B2; ctype_uses := _ |} :: env2) r _,
      Hb1 : BranchVec (tl dl) (tl dr) d_br, Hb2 : BranchVec (tl _) (tl _) _ |- _ =>
        rename Hl into Hl1; rename Hlk2 into Hlk2';
        rename Ha1 into Ha1'; rename Ha2 into Ha2';
        rename Hd2 into Hd2'; rename Hd4 into Hd4';
        rename Hb1 into Hb1'; rename Hb2 into Hb2'
    end.
    destruct (cenv_alpha_eq_lookup _ _ _ s e Henv Hl1) as [e' [Hl' Heq]].
    rewrite Hlk2' in Hl'; inversion Hl'; subst e'.
    match type of Ha2' with cty_alpha_eq _ (CSum ?A2 ?B2) =>
      assert (Hsum : cty_alpha_eq (CSum A B) (CSum A2 B2)) by
        (eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact Ha1' |];
         eapply cty_alpha_eq_trans; [apply ren_cty_alpha_eq; exact Heq | exact Ha2']);
      unfold cty_alpha_eq in Hsum; cbn in Hsum; inversion Hsum as [[HeqA HeqB]];
      match type of Hd2' with CIdxDemand _ _ ?dl2 =>
      match type of Hd4' with CIdxDemand _ _ ?dr2 =>
        assert (Hdl : dl = dl2) by
          (refine (IHCIdxDemand1 _ _ _ Hd2'); constructor; [cbn; exact HeqA | exact Henv]);
        assert (Hdr : dr = dr2) by
          (refine (IHCIdxDemand2 _ _ _ Hd4'); constructor; [cbn; exact HeqB | exact Henv]);
        subst dl2 dr2
      end end
    end.
    f_equal. eapply BranchVec_alpha_det; [reflexivity | reflexivity | exact Hb1' | exact Hb2'].
Qed.

Lemma ctype_demand_unique : forall (D : JoinDomain) (env1 env2 : cenv D) T d1 d2,
  cenv_alpha_eq env1 env2 ->
  CTypeDemand env1 T d1 ->
  CTypeDemand env2 T d2 ->
  d1 = d2.
Proof.
  intros D env1 env2 T d1 d2 Henv H1. revert env2 d2 Henv.
  induction H1 using CTypeDemand_ind_mut with
    (P := fun env1 T d1 _ => forall env2 d2, cenv_alpha_eq env1 env2 -> CTypeDemand env2 T d2 -> d1 = d2)
    (P0 := fun env1 fs df1 _ => forall env2 df2, cenv_alpha_eq env1 env2 -> CRecordFieldDemand env2 fs df2 -> df1 = df2)
    (P1 := fun env1 ls dl1 _ => forall env2 dl2, cenv_alpha_eq env1 env2 -> CIdxListDemand env2 ls dl2 -> dl1 = dl2);
    intros env2 d2 Henv H2; inversion H2; subst;
    try rewrite (cenv_alpha_eq_length _ _ _ Henv); try reflexivity.
  - f_equal; [eapply IHCTypeDemand; eassumption |].
    match goal with
    | Hc1 : CIdxDemand _ len _, Hc2 : CIdxDemand env2 len _ |- _ =>
        exact (cidx_demand_unique D _ _ _ _ _ Henv Hc1 Hc2)
    end.
  - f_equal; eapply IHCTypeDemand; eassumption.
  - match goal with
    | Hda : CTypeDemand env2 dom _, Hdb : CTypeDemand (_ :: env2) cod _ |- _ =>
        rename Hda into Hda'; rename Hdb into Hdb'
    end.
    match type of Hda' with CTypeDemand _ _ ?a' =>
      assert (Ha : a = a') by (eapply IHCTypeDemand1; eassumption); subst a'
    end.
    match type of Hdb' with CTypeDemand _ _ ?b' =>
      assert (Hb : b = b') by (refine (IHCTypeDemand2 _ _ _ Hdb'); constructor; [cbn; apply cty_alpha_eq_refl | exact Henv]);
      subst b'
    end.
    reflexivity.
  - match goal with
    | Hda : CTypeDemand env2 f _, Hdb : CTypeDemand (_ :: env2) s _ |- _ =>
        rename Hda into Hda'; rename Hdb into Hdb'
    end.
    match type of Hda' with CTypeDemand _ _ ?a' =>
      assert (Ha : a = a') by (eapply IHCTypeDemand1; eassumption); subst a'
    end.
    match type of Hdb' with CTypeDemand _ _ ?b' =>
      assert (Hb : b = b') by (refine (IHCTypeDemand2 _ _ _ Hdb'); constructor; [cbn; apply cty_alpha_eq_refl | exact Henv]);
      subst b'
    end.
    reflexivity.
  - eapply IHCTypeDemand; eassumption.
  - f_equal; [eapply IHCTypeDemand1; eassumption | eapply IHCTypeDemand2; eassumption].
  - eapply IHCTypeDemand; eassumption.
  - eapply IHCTypeDemand; eassumption.
  - f_equal; [eapply IHCTypeDemand; eassumption | eapply IHCTypeDemand0; eassumption].
  - f_equal; [match goal with Hc1 : CIdxDemand _ idx _, Hc2 : CIdxDemand env2 idx _ |- _ => exact (cidx_demand_unique D _ _ _ _ _ Henv Hc1 Hc2) end
             |eapply IHCTypeDemand; eassumption].
Qed.

(* Lifting and Index Substitution Commutation Lemmas *)

Lemma lift_cidx_add : forall (D : JoinDomain) a b (i : cidx D),
  lift_cidx 0 a (lift_cidx 0 b i) = lift_cidx 0 (a + b) i.
Proof.
  intros D a b i. unfold lift_cidx. rewrite ren_cidx_comp.
  apply ren_cidx_ext. intro x. unfold ren_lift. rw_nat_bool. lia.
Qed.

Lemma lift_cty_add : forall (D : JoinDomain) a b (T : cty D),
  lift_cty 0 a (lift_cty 0 b T) = lift_cty 0 (a + b) T.
Proof.
  intros D a b T. unfold lift_cty. rewrite ren_cty_comp.
  apply ren_cty_ext. intro x. unfold ren_lift. rw_nat_bool. lia.
Qed.

Lemma erase_hints_subst_cidx_in_cty : forall (D : JoinDomain) k (val : cidx D) (T : cty D),
  erase_hints (subst_cidx_in_cty k val T) = subst_cidx_in_cty k val (erase_hints T).
Proof.
  intros D k val T. revert k val.
  induction T using cty_ind_nested; intros k val; cbn; f_equal; auto.
  induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
  inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
Qed.

Lemma subst_cidx_alpha_eq : forall (D : JoinDomain) k (val : cidx D) (T1 T2 : cty D),
  cty_alpha_eq T1 T2 ->
  cty_alpha_eq (subst_cidx_in_cty k val T1) (subst_cidx_in_cty k val T2).
Proof.
  intros D k val T1 T2 H. unfold cty_alpha_eq in *.
  rewrite !erase_hints_subst_cidx_in_cty, H. reflexivity.
Qed.

Lemma subst_cidx_eqb : forall (D : JoinDomain) k (val : cidx D) i1 i2,
  cidx_eqb i1 i2 = true ->
  cidx_eqb (subst_cidx k val i1) (subst_cidx k val i2) = true.
Proof.
  intros D k val i1 i2 H. apply cidx_eqb_sound in H. subst i2. apply cidx_eqb_refl.
Qed.

Lemma unshift_cidx_as_ren : forall (D : JoinDomain) (i : cidx D) j,
  unshift_cidx j i = ren_cidx (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end)) i.
Proof. reflexivity. Qed.

Lemma iter_unshift_lt : forall j x,
  x < j -> Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end) x = x.
Proof.
  induction j as [| j IH]; intros [| x] H; try lia.
  - reflexivity.
  - change (Nat.iter (S j) ren_shift (fun n => match n with 0 => 0 | S n' => n' end) (S x))
      with (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end)) (S x)).
    cbn [ren_shift]. f_equal. apply IH; lia.
Qed.

Lemma iter_unshift_gt : forall j x,
  x > j -> Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end) x = x - 1.
Proof.
  induction j as [| j IH]; intros [| x] H; try lia.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - change (Nat.iter (S j) ren_shift (fun n => match n with 0 => 0 | S n' => n' end) (S x))
      with (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end)) (S x)).
    cbn [ren_shift]. rewrite IH by lia. lia.
Qed.

Lemma iter_unshift_eq : forall j,
  Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end) j = j.
Proof.
  induction j as [| j IH]; cbn; [reflexivity |].
  change (Nat.iter (S j) ren_shift (fun n => match n with 0 => 0 | S n' => n' end) (S j))
    with (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end)) (S j)).
  cbn [ren_shift]. f_equal. exact IH.
Qed.

Lemma unshift_lift_cancel : forall (D : JoinDomain) (v : cidx D) j,
  unshift_cidx j (lift_cidx j 1 v) = v.
Proof.
  intros D v j. unfold unshift_cidx, lift_cidx. rewrite ren_cidx_comp.
  transitivity (ren_cidx (fun x => x) v); [| apply ren_cidx_id].
  apply ren_cidx_ext. intro x. unfold ren_lift. destruct (x <? j) eqn:Exj; nat_bool_hyps.
  - apply iter_unshift_lt. exact Exj.
  - rewrite iter_unshift_gt by lia. lia.
Qed.

Lemma ren_lift_comm_0_1 : forall (D : JoinDomain) k (v : cidx D),
  lift_cidx 0 1 (lift_cidx k 1 v) = lift_cidx (S k) 1 (lift_cidx 0 1 v).
Proof.
  intros D k v. unfold lift_cidx. rewrite !ren_cidx_comp.
  apply ren_cidx_ext. intro x. unfold ren_lift.
  destruct (x <? k) eqn:E1; destruct (x <? 0) eqn:E2; nat_bool_hyps; try lia; rw_nat_bool; lia.
Qed.

Lemma subst_cidx_unshift_gen : forall (D : JoinDomain) (i val : cidx D) j k,
  j <= k ->
  cidx_uses_kinds true false false false false (S k) i = false ->
  cidx_uses_kinds false false false false false j i = false ->
  unshift_cidx j (subst_cidx (S k) (lift_cidx j 1 val) i) = subst_cidx k val (unshift_cidx j i).
Proof.
  intros D i. induction i; intros val j k Hjk Huk Hu0; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in Hu0 as [Hu1 Hu2];
         rewrite (IHi1 _ _ _ Hjk Hk1 Hu1), (IHi2 _ _ _ Hjk Hk2 Hu2); reflexivity).
  - nat_bool_hyps.
    destruct (Nat.eq_dec x (S k)) as [-> | Hnek].
    + rw_nat_bool. rewrite unshift_lift_cancel.
      unfold unshift_cidx. cbn [ren_cidx]. rewrite iter_unshift_gt by lia.
      cbn. replace (S k - 1) with k by lia. rw_nat_bool. reflexivity.
    + destruct (le_lt_dec j x) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cidx; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
      destruct (Nat.eq_dec x j) as [-> | Hnej]; [exfalso; lia |].
      destruct (le_lt_dec (S k) x) as [Hkle | Hkgt]; rw_nat_bool;
        unfold unshift_cidx; cbn [ren_cidx]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; f_equal; lia.
  - f_equal; apply IHi; assumption.
  - nat_bool_hyps.
    destruct (le_lt_dec j b) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cidx; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
    destruct (Nat.eq_dec b j) as [-> | Hnej]; [exfalso; lia |].
    destruct (Nat.eq_dec b (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (le_lt_dec (S k) b) as [Hkle | Hkgt]; rw_nat_bool;
      unfold unshift_cidx; cbn [ren_cidx]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps.
    destruct (le_lt_dec j p) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cidx; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
    destruct (Nat.eq_dec p j) as [-> | Hnej]; [exfalso; lia |].
    destruct (Nat.eq_dec p (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (le_lt_dec (S k) p) as [Hkle | Hkgt]; rw_nat_bool;
      unfold unshift_cidx; cbn [ren_cidx]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps.
    destruct (le_lt_dec j p) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cidx; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
    destruct (Nat.eq_dec p j) as [-> | Hnej]; [exfalso; lia |].
    destruct (Nat.eq_dec p (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (le_lt_dec (S k) p) as [Hkle | Hkgt]; rw_nat_bool;
      unfold unshift_cidx; cbn [ren_cidx]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; f_equal; lia.
  - apply orb_false_iff in Huk as [Hk12 Hk3]. apply orb_false_iff in Hk12 as [Hk1 Hk2].
    apply orb_false_iff in Hu0 as [Hu12 Hu3]. apply orb_false_iff in Hu12 as [Hu1 Hu2].
    nat_bool_hyps. f_equal.
    + destruct (le_lt_dec j s) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cidx; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
      destruct (Nat.eq_dec s j) as [-> | Hnej]; [exfalso; lia |].
      destruct (Nat.eq_dec s (S k)) as [-> | Hnek]; [exfalso; lia |].
      destruct (le_lt_dec (S k) s) as [Hkle | Hkgt]; rw_nat_bool;
        unfold unshift_cidx; cbn [ren_cidx]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; lia.
    + change (ren_cidx (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end))) ?e)
        with (unshift_cidx (S j) e).
      rewrite ren_lift_comm_0_1.
      apply (IHi1 (lift_cidx 0 1 val) (S j) (S k) ltac:(lia) Hk2 Hu2).
    + change (ren_cidx (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end))) ?e)
        with (unshift_cidx (S j) e).
      rewrite ren_lift_comm_0_1.
      apply (IHi2 (lift_cidx 0 1 val) (S j) (S k) ltac:(lia) Hk3 Hu3).
Qed.

Lemma subst_cidx_unshift_0 : forall (D : JoinDomain) (i val : cidx D) k,
  cidx_uses_kinds true false false false false (S k) i = false ->
  cidx_uses_kinds false false false false false 0 i = false ->
  unshift_cidx 0 (subst_cidx (S k) (lift_cidx 0 1 val) i) = subst_cidx k val (unshift_cidx 0 i).
Proof.
  intros D i val k Huk Hu0. apply subst_cidx_unshift_gen; [lia | exact Huk | exact Hu0].
Qed.

Lemma subst_cidx_unshift_cty_gen : forall (D : JoinDomain) (T : cty D) (val : cidx D) j k,
  j <= k ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds false false false false false false false j T = false ->
  unshift_cty j (subst_cidx_in_cty (S k) (lift_cidx j 1 val) T) = subst_cidx_in_cty k val (unshift_cty j T).
Proof.
  intros D T. induction T using cty_ind_nested; intros val j k Hjk Huk Hu0; cbn in *; try reflexivity;
    try (f_equal; apply IHT; assumption);
    try (apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in Hu0 as [Hu1 Hu2];
         f_equal; [apply IHT1 | apply IHT2]; assumption).
  - apply orb_false_iff in Huk as [Hk1 Hk2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    f_equal; [apply IHT; assumption | apply subst_cidx_unshift_gen; assumption].
  - nat_bool_hyps.
    destruct (le_lt_dec j x) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cty; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
    destruct (Nat.eq_dec x j) as [-> | Hnej]; [exfalso; lia |].
    destruct (Nat.eq_dec x (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (le_lt_dec (S k) x) as [Hkle | Hkgt]; rw_nat_bool;
      unfold unshift_cty; cbn [ren_cty]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps.
    destruct (le_lt_dec j b) as [Hjle | Hjgt]; [| rw_nat_bool; unfold unshift_cty; cbn; rewrite !iter_unshift_lt by lia; rw_nat_bool; reflexivity].
    destruct (Nat.eq_dec b j) as [-> | Hnej]; [exfalso; lia |].
    destruct (Nat.eq_dec b (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (le_lt_dec (S k) b) as [Hkle | Hkgt]; rw_nat_bool;
      unfold unshift_cty; cbn [ren_cty]; rewrite !iter_unshift_gt by lia; cbn; rw_nat_bool; f_equal; lia.
  - apply orb_false_iff in Huk as [Hk1 Hk2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    change (ren_cty (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end))) ?e)
      with (unshift_cty (S j) e).
    rewrite ren_lift_comm_0_1.
    apply (IHT2 (lift_cidx 0 1 val) (S j) (S k) ltac:(lia) Hk2 Hu2).
  - apply orb_false_iff in Huk as [Hk1 Hk2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    change (ren_cty (ren_shift (Nat.iter j ren_shift (fun n => match n with 0 => 0 | S n' => n' end))) ?e)
      with (unshift_cty (S j) e).
    rewrite ren_lift_comm_0_1.
    apply (IHT2 (lift_cidx 0 1 val) (S j) (S k) ltac:(lia) Hk2 Hu2).
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2.
    apply orb_false_iff in Huk as [Hk1 Hk_r]. apply orb_false_iff in Hu0 as [Hu1 Hu_r].
    rewrite (H2 _ _ _ Hjk Hk1 Hu1), (IHf H3 Hk_r Hu_r). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [Hk1 Hk2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    f_equal; [apply subst_cidx_unshift_gen; assumption | apply IH; assumption].
Qed.

Lemma subst_cidx_unshift_cty_0 : forall (D : JoinDomain) (T : cty D) (val : cidx D) k,
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds false false false false false false false 0 T = false ->
  unshift_cty 0 (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) T) = subst_cidx_in_cty k val (unshift_cty 0 T).
Proof.
  intros D T val k Huk Hu0. apply subst_cidx_unshift_cty_gen; [lia | exact Huk | exact Hu0].
Qed.

Lemma cidx_uses_kinds_ren_gen : forall (D : JoinDomain) (i : cidx D) k k' r,
  (forall x, x <> k -> r x <> k') ->
  cidx_uses_kinds true false false false false k i = false ->
  cidx_uses_kinds true false false false false k' (ren_cidx r i) = false.
Proof.
  intros D i. induction i; intros k k' r Hr Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHi1 _ _ _ Hr H1), (IHi2 _ _ _ Hr H2); reflexivity).
  - apply IHi with (k := k); assumption.
  - nat_bool_hyps. apply Nat.eqb_neq, Hr; exact Hu.
  - nat_bool_hyps. apply Nat.eqb_neq, Hr; exact Hu.
  - nat_bool_hyps. apply Nat.eqb_neq, Hr; exact Hu.
  - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
    nat_bool_hyps. rewrite (proj2 (Nat.eqb_neq _ _) (Hr _ H1)). cbn.
    assert (Hr' : forall x, x <> S k -> ren_shift r x <> S k').
    { intros [| y] Hy; cbn; [lia |]. pose proof (Hr y ltac:(lia)); lia. }
    rewrite (IHi1 _ _ _ Hr' H2), (IHi2 _ _ _ Hr' H3). reflexivity.
Qed.

Lemma cty_uses_kinds_ren_gen : forall (D : JoinDomain) (T : cty D) k k' rn,
  (forall x, x <> k -> rn x <> k') ->
  cty_uses_kinds true false false false false false false k T = false ->
  cty_uses_kinds true false false false false false false k' (ren_cty rn T) = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros k k' rn Hr Hu; cbn in *; try reflexivity;
    try (apply IHT with (k := k); assumption);
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHT1 _ _ _ Hr H1), (IHT2 _ _ _ Hr H2); reflexivity).
  - apply orb_false_iff in Hu as [H1 H2].
    rewrite (IHT _ _ _ Hr H1), (cidx_uses_kinds_ren_gen D len _ _ _ Hr H2). reflexivity.
  - nat_bool_hyps. apply Nat.eqb_neq, Hr; exact Hu.
  - nat_bool_hyps. apply Nat.eqb_neq, Hr; exact Hu.
  - apply orb_false_iff in Hu as [H1 H2]. rewrite (IHT1 _ _ _ Hr H1).
    assert (Hr' : forall x, x <> S k -> ren_shift rn x <> S k').
    { intros [| y] Hy; cbn; [lia |]. pose proof (Hr y ltac:(lia)); lia. }
    rewrite (IHT2 _ _ _ Hr' H2). reflexivity.
  - apply orb_false_iff in Hu as [H1 H2]. rewrite (IHT1 _ _ _ Hr H1).
    assert (Hr' : forall x, x <> S k -> ren_shift rn x <> S k').
    { intros [| y] Hy; cbn; [lia |]. pose proof (Hr y ltac:(lia)); lia. }
    rewrite (IHT2 _ _ _ Hr' H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [H1 H3_r].
    rewrite (H2 _ _ _ Hr H1), (IHf H3 H3_r). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hu as [H1 H2].
    rewrite (cidx_uses_kinds_ren_gen D idx _ _ _ Hr H1), (IH H2). reflexivity.
Qed.

Lemma cty_uses_kinds_lift_shift : forall (D : JoinDomain) (T : cty D) d,
  cty_uses_kinds true false false false false false false d T = false ->
  cty_uses_kinds true false false false false false false (S d) (lift_cty 0 1 T) = false.
Proof.
  intros D T d Hu. unfold lift_cty. eapply cty_uses_kinds_ren_gen; [| exact Hu].
  intros x Hne. unfold ren_lift. destruct (x <? 0) eqn:E; nat_bool_hyps; lia.
Qed.

Lemma subst_cidx_lift_cidx_ge : forall (D : JoinDomain) (i val : cidx D) c k,
  c <= k ->
  cidx_uses_kinds true false false false false k i = false ->
  subst_cidx (S k) (lift_cidx c 1 val) (lift_cidx c 1 i) = lift_cidx c 1 (subst_cidx k val i).
Proof.
  intros D i. induction i; intros val c k Hck Huk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huk as [Hk1 Hk2]; rewrite (IHi1 _ _ _ Hck Hk1), (IHi2 _ _ _ Hck Hk2); reflexivity).
  - unfold ren_lift. destruct (x <? c) eqn:Exc; cbv iota;
      destruct (x =? k) eqn:Exk, (x <? k) eqn:Exlk; cbv iota; nat_bool_hyps; try lia;
      repeat (rw_nat_bool; cbv iota); try reflexivity; unfold lift_cidx, ren_lift; cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - rewrite (IHi _ _ _ Hck Huk). reflexivity.
  - nat_bool_hyps. unfold ren_lift. destruct (b <? c) eqn:Ebc; cbv iota;
      destruct (b =? k) eqn:Ebk, (b <? k) eqn:Eblk; cbv iota; nat_bool_hyps; try lia;
      repeat (rw_nat_bool; cbv iota); unfold lift_cidx, ren_lift; cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - nat_bool_hyps. unfold ren_lift. destruct (p <? c) eqn:Epc; cbv iota;
      destruct (p =? k) eqn:Epk, (p <? k) eqn:Eplk; cbv iota; nat_bool_hyps; try lia;
      repeat (rw_nat_bool; cbv iota); unfold lift_cidx, ren_lift; cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - nat_bool_hyps. unfold ren_lift. destruct (p <? c) eqn:Epc; cbv iota;
      destruct (p =? k) eqn:Epk, (p <? k) eqn:Eplk; cbv iota; nat_bool_hyps; try lia;
      repeat (rw_nat_bool; cbv iota); unfold lift_cidx, ren_lift; cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Huk as [Hk12 Hk3]. apply orb_false_iff in Hk12 as [Hk1 Hk2]. nat_bool_hyps.
    f_equal.
    + unfold ren_lift. destruct (s <? c) eqn:Esc; cbv iota;
        destruct (s =? k) eqn:Esk, (s <? k) eqn:Eslk; cbv iota; nat_bool_hyps; try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); lia.
    + replace (ren_cidx (ren_shift (ren_lift c 1)) i1) with (lift_cidx (S c) 1 i1)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity]).
      rewrite ren_lift_comm_0_1.
      rewrite (IHi1 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2).
      unfold lift_cidx. apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity].
    + replace (ren_cidx (ren_shift (ren_lift c 1)) i2) with (lift_cidx (S c) 1 i2)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity]).
      rewrite ren_lift_comm_0_1.
      rewrite (IHi2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk3).
      unfold lift_cidx. apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity].
Qed.

Lemma subst_cidx_lift_cancel : forall (D : JoinDomain) (v w : cidx D) c,
  subst_cidx c w (lift_cidx c 1 v) = v.
Proof.
  intros D v. induction v; intros w c; cbn; try reflexivity;
    try (rewrite IHv1, IHv2; reflexivity).
  - unfold ren_lift. destruct (x <? c) eqn:Exc; nat_bool_hyps; rw_nat_bool; cbn; f_equal; lia.
  - rewrite IHv; reflexivity.
  - unfold ren_lift. destruct (b <? c) eqn:Ebc; nat_bool_hyps; rw_nat_bool; cbn; f_equal; lia.
  - unfold ren_lift. destruct (p <? c) eqn:Epc; nat_bool_hyps; rw_nat_bool; cbn; f_equal; lia.
  - unfold ren_lift. destruct (p <? c) eqn:Epc; nat_bool_hyps; rw_nat_bool; cbn; f_equal; lia.
  - f_equal.
    + unfold ren_lift. destruct (s <? c) eqn:Esc; nat_bool_hyps; rw_nat_bool; cbn; lia.
    + replace (ren_cidx (ren_shift (ren_lift c 1)) v1) with (lift_cidx (S c) 1 v1)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity]).
      apply IHv1.
    + replace (ren_cidx (ren_shift (ren_lift c 1)) v2) with (lift_cidx (S c) 1 v2)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity]).
      apply IHv2.
Qed.

Lemma subst_cidx_subst_cidx_gen : forall (D : JoinDomain) (i v1 v2 : cidx D) k1 k2,
  k1 <= k2 ->
  cidx_uses_kinds true false false false false k2 v1 = false ->
  cidx_uses_kinds true false false false false (S k2) i = false ->
  subst_cidx k2 v2 (subst_cidx k1 v1 i) =
  subst_cidx k1 (subst_cidx k2 v2 v1) (subst_cidx (S k2) (lift_cidx k1 1 v2) i).
Proof.
  intros D i. induction i; intros v1 v2 k1 k2 Hle Hv1 Huk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huk as [H1 H2];
         rewrite (IHi1 _ _ _ _ Hle Hv1 H1), (IHi2 _ _ _ _ Hle Hv1 H2); reflexivity).
  - destruct (Nat.eq_dec x k1) as [-> | Hne1].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
    + destruct (Nat.eq_dec x (S k2)) as [-> | Hne2].
      * repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); rewrite subst_cidx_lift_cancel; reflexivity.
      * destruct (le_lt_dec k1 x), (le_lt_dec (S k2) x); try lia;
          repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - rewrite (IHi _ _ _ _ Hle Hv1 Huk). reflexivity.
  - destruct (Nat.eq_dec b (S k2)) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Huk; discriminate |].
    destruct (Nat.eq_dec b k1) as [-> | Hne1].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); destruct k1, k2; cbn; reflexivity.
    + destruct (le_lt_dec k1 b), (le_lt_dec (S k2) b); try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Nat.eq_dec p (S k2)) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Huk; discriminate |].
    destruct (Nat.eq_dec p k1) as [-> | Hne1].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); destruct k1, k2; cbn; reflexivity.
    + destruct (le_lt_dec k1 p), (le_lt_dec (S k2) p); try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Nat.eq_dec p (S k2)) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Huk; discriminate |].
    destruct (Nat.eq_dec p k1) as [-> | Hne1].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); destruct k1, k2; cbn; reflexivity.
    + destruct (le_lt_dec k1 p), (le_lt_dec (S k2) p); try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Huk as [H12 H3]. apply orb_false_iff in H12 as [Hs H2].
    f_equal.
    + destruct (Nat.eq_dec s (S k2)) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Hs; discriminate |].
      destruct (Nat.eq_dec s k1) as [-> | Hne1].
      * repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); destruct k1, k2; cbn; reflexivity.
      * destruct (le_lt_dec k1 s), (le_lt_dec (S k2) s); try lia;
          repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); lia.
    + pose proof (cidx_uses_kinds_lift_shift D v1 k2 Hv1) as Hv1'.
      rewrite (IHi1 (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) (S k1) (S k2) ltac:(lia) Hv1' H2).
      rewrite (subst_cidx_lift_cidx_ge D v1 v2 0 k2 ltac:(lia) Hv1).
      rewrite ren_lift_comm_0_1. reflexivity.
    + pose proof (cidx_uses_kinds_lift_shift D v1 k2 Hv1) as Hv1'.
      rewrite (IHi2 (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) (S k1) (S k2) ltac:(lia) Hv1' H3).
      rewrite (subst_cidx_lift_cidx_ge D v1 v2 0 k2 ltac:(lia) Hv1).
      rewrite ren_lift_comm_0_1. reflexivity.
Qed.

Lemma subst_cidx_in_cty_lift_ge : forall (D : JoinDomain) (T : cty D) (val : cidx D) c k,
  c <= k ->
  cty_uses_kinds true false false false false false false k T = false ->
  subst_cidx_in_cty (S k) (lift_cidx c 1 val) (lift_cty c 1 T) = lift_cty c 1 (subst_cidx_in_cty k val T).
Proof.
  intros D T. induction T using cty_ind_nested; intros val c k Hck Huk; cbn in *; try reflexivity;
    try (f_equal; apply IHT; assumption);
    try (apply orb_false_iff in Huk as [Hk1 Hk2]; f_equal; [apply IHT1 | apply IHT2]; assumption).
  - apply orb_false_iff in Huk as [Hk1 Hk2].
    f_equal; [apply IHT; assumption | apply subst_cidx_lift_cidx_ge; assumption].
  - nat_bool_hyps. unfold ren_lift. destruct (x <? c) eqn:Exc; cbv iota;
      destruct (x =? k) eqn:Exk, (x <? k) eqn:Exlk; cbv iota; nat_bool_hyps; try lia;
      repeat (rw_nat_bool; cbv iota); unfold lift_cty, ren_lift; cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - nat_bool_hyps. unfold ren_lift. destruct (b <? c) eqn:Ebc; cbv iota;
      destruct (b =? k) eqn:Ebk, (b <? k) eqn:Eblk; cbv iota; nat_bool_hyps; try lia;
      repeat (rw_nat_bool; cbv iota); unfold lift_cty, ren_lift; cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Huk as [Hk1 Hk2].
    f_equal; [apply IHT1; assumption |].
    replace (ren_cty (ren_shift (ren_lift c 1)) T2) with (lift_cty (S c) 1 T2)
      by (unfold lift_cty; apply ren_cty_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity]).
    rewrite ren_lift_comm_0_1, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2).
    unfold lift_cty. apply ren_cty_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity].
  - apply orb_false_iff in Huk as [Hk1 Hk2].
    f_equal; [apply IHT1; assumption |].
    replace (ren_cty (ren_shift (ren_lift c 1)) T2) with (lift_cty (S c) 1 T2)
      by (unfold lift_cty; apply ren_cty_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity]).
    rewrite ren_lift_comm_0_1, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2).
    unfold lift_cty. apply ren_cty_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (y <? c) eqn:Ey; rw_nat_bool; reflexivity].
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [Hk1 Hkr].
    rewrite (H2 _ _ _ Hck Hk1), (IHf H3 Hkr). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [Hk1 Hk2].
    f_equal; [apply subst_cidx_lift_cidx_ge; assumption | apply IH; assumption].
Qed.

Lemma subst_cidx_in_cty_subst_cidx : forall (D : JoinDomain) (T : cty D) (v1 v2 : cidx D) k1 k2,
  k1 <= k2 ->
  cidx_uses_kinds true false false false false k2 v1 = false ->
  cty_uses_kinds true false false false false false false (S k2) T = false ->
  subst_cidx_in_cty k2 v2 (subst_cidx_in_cty k1 v1 T) =
  subst_cidx_in_cty k1 (subst_cidx k2 v2 v1) (subst_cidx_in_cty (S k2) (lift_cidx k1 1 v2) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros v1 v2 k1 k2 Hle Hv1 Huk; cbn in *; try reflexivity;
    try (f_equal; apply IHT; assumption);
    try (apply orb_false_iff in Huk as [H1 H2]; f_equal; [apply IHT1 | apply IHT2]; assumption).
  - apply orb_false_iff in Huk as [H1 H2].
    rewrite (IHT _ _ _ _ Hle Hv1 H1), (subst_cidx_subst_cidx_gen D len v1 v2 k1 k2 Hle Hv1 H2). reflexivity.
  - destruct (Nat.eq_dec x (S k2)) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Huk; discriminate |].
    destruct (Nat.eq_dec x k1) as [-> | Hne1].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); destruct k1, k2; cbn; reflexivity.
    + destruct (le_lt_dec k1 x), (le_lt_dec (S k2) x); try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Nat.eq_dec b (S k2)) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Huk; discriminate |].
    destruct (Nat.eq_dec b k1) as [-> | Hne1].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); destruct k1, k2; cbn; reflexivity.
    + destruct (le_lt_dec k1 b), (le_lt_dec (S k2) b); try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Huk as [H1 H2]. f_equal; [apply IHT1; assumption |].
    pose proof (cidx_uses_kinds_lift_shift D v1 k2 Hv1) as Hv1'.
    rewrite (IHT2 (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) (S k1) (S k2) ltac:(lia) Hv1' H2).
    rewrite (subst_cidx_lift_cidx_ge D v1 v2 0 k2 ltac:(lia) Hv1), ren_lift_comm_0_1. reflexivity.
  - apply orb_false_iff in Huk as [H1 H2]. f_equal; [apply IHT1; assumption |].
    pose proof (cidx_uses_kinds_lift_shift D v1 k2 Hv1) as Hv1'.
    rewrite (IHT2 (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) (S k1) (S k2) ltac:(lia) Hv1' H2).
    rewrite (subst_cidx_lift_cidx_ge D v1 v2 0 k2 ltac:(lia) Hv1), ren_lift_comm_0_1. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    rewrite (H2 _ _ _ _ Hle Hv1 H1), (IHf H3 H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2].
    rewrite (subst_cidx_subst_cidx_gen D idx v1 v2 k1 k2 Hle Hv1 H1), (IH H2). reflexivity.
Qed.

Lemma subst_tvar_in_cidx_as_unshift : forall (D : JoinDomain) d (j : cidx D),
  cidx_uses_kinds false false false false false d j = false ->
  subst_tvar_in_cidx d j = unshift_cidx d j.
Proof.
  intros D d j. revert d. induction j; intros d Hu; unfold unshift_cidx in *; cbn in *;
    try reflexivity.
  - nat_bool_hyps. destruct (x <? d) eqn:E1; nat_bool_hyps; [rewrite iter_unshift_lt by lia; reflexivity |].
    destruct (x =? d) eqn:E2; nat_bool_hyps; [exfalso; lia | rewrite iter_unshift_gt by lia; reflexivity].
  - apply orb_false_iff in Hu as [Hu1 Hu2]. rewrite (IHj1 _ Hu1), (IHj2 _ Hu2). reflexivity.
  - rewrite (IHj _ Hu). reflexivity.
  - nat_bool_hyps. destruct (b <? d) eqn:E1; nat_bool_hyps; [rewrite iter_unshift_lt by lia; reflexivity |].
    destruct (b =? d) eqn:E2; nat_bool_hyps; [exfalso; lia | rewrite iter_unshift_gt by lia; reflexivity].
  - nat_bool_hyps. destruct (p <? d) eqn:E1; nat_bool_hyps; [rewrite iter_unshift_lt by lia; reflexivity |].
    destruct (p =? d) eqn:E2; nat_bool_hyps; [exfalso; lia | rewrite iter_unshift_gt by lia; reflexivity].
  - nat_bool_hyps. destruct (p <? d) eqn:E1; nat_bool_hyps; [rewrite iter_unshift_lt by lia; reflexivity |].
    destruct (p =? d) eqn:E2; nat_bool_hyps; [exfalso; lia | rewrite iter_unshift_gt by lia; reflexivity].
  - apply orb_false_iff in Hu as [H12 Hu3]; apply orb_false_iff in H12 as [Hu1 Hu2]; nat_bool_hyps.
    f_equal.
    + destruct (s <? d) eqn:E1; nat_bool_hyps; [rewrite iter_unshift_lt by lia; reflexivity |].
      destruct (s =? d) eqn:E2; nat_bool_hyps; [exfalso; lia | rewrite iter_unshift_gt by lia; reflexivity].
    + apply (IHj1 (S d) Hu2).
    + apply (IHj2 (S d) Hu3).
Qed.

Lemma cidx_uses_kinds_0_subst : forall (D : JoinDomain) (j val : cidx D) c k,
  c < k ->
  cidx_uses_kinds true false false false false k j = false ->
  cidx_uses_kinds false false false false false c val = false ->
  cidx_uses_kinds false false false false false c j = false ->
  cidx_uses_kinds false false false false false c (subst_cidx k val j) = false.
Proof.
  intros D j. induction j; intros val c k Hck Hk Hval Hc; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hk as [Hk1 Hk2]; apply orb_false_iff in Hc as [Hc1 Hc2];
         rewrite (IHj1 _ _ _ Hck Hk1 Hval Hc1), (IHj2 _ _ _ Hck Hk2 Hval Hc2); reflexivity).
  - nat_bool_hyps. destruct (x =? k) eqn:Exk; nat_bool_hyps; [exact Hval |].
    destruct (x <? k) eqn:Exlk; nat_bool_hyps; cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - apply (IHj _ _ _ Hck Hk Hval Hc).
  - nat_bool_hyps. destruct (b <? k) eqn:Eblk; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (p <? k) eqn:Eplk; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (p <? k) eqn:Eplk; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Hk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2].
    apply orb_false_iff in Hc as [Hc12 Hc3]; apply orb_false_iff in Hc12 as [Hc1 Hc2].
    nat_bool_hyps.
    assert (Hs : ((if s <? k then s else if s =? k then 0 else s - 1) =? c) = false) by
      (destruct (s <? k) eqn:Eslk; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia).
    rewrite Hs. cbn.
    assert (Hval' : cidx_uses_kinds false false false false false (S c) (lift_cidx 0 1 val) = false).
    { unfold lift_cidx.
      assert (Hren : forall (u : cidx D) d d' rn,
        (forall y, y <> d -> rn y <> d') ->
        cidx_uses_kinds false false false false false d u = false ->
        cidx_uses_kinds false false false false false d' (ren_cidx rn u) = false).
      { clear; induction u; intros d d' rn Hrn Hu; cbn in *; try reflexivity;
          try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHu1 _ _ _ Hrn H1), (IHu2 _ _ _ Hrn H2); reflexivity);
          try (apply IHu with (d := d); assumption);
          try (nat_bool_hyps; apply Nat.eqb_neq, Hrn; exact Hu).
        apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
        rewrite (proj2 (Nat.eqb_neq _ _) (Hrn _ H1)). cbn.
        assert (Hrn' : forall y, y <> S d -> ren_shift rn y <> S d') by (intros [| y] Hy; cbn; [lia |]; pose proof (Hrn y ltac:(lia)); lia).
        rewrite (IHu1 _ _ _ Hrn' H2), (IHu2 _ _ _ Hrn' H3); reflexivity. }
      eapply Hren; [| exact Hval]. intros y Hy; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
    rewrite (IHj1 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2 Hval' Hc2),
            (IHj2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk3 Hval' Hc3). reflexivity.
Qed.

Lemma cidx_uses_kinds_lift_j : forall (D : JoinDomain) (i : cidx D) j,
  cidx_uses_kinds false false false false false j (lift_cidx j 1 i) = false.
Proof.
  intros D i. induction i; intros j; cbn; try reflexivity;
    try (rewrite (IHi1 j), (IHi2 j); reflexivity);
    try (apply (IHi j));
    try (unfold ren_lift; destruct (Nat.ltb_spec x j); apply Nat.eqb_neq; lia);
    try (unfold ren_lift; destruct (Nat.ltb_spec b j); apply Nat.eqb_neq; lia);
    try (unfold ren_lift; destruct (Nat.ltb_spec p j); apply Nat.eqb_neq; lia).
  - assert (Hs : (ren_lift j 1 s =? j) = false) by (unfold ren_lift; destruct (Nat.ltb_spec s j); apply Nat.eqb_neq; lia).
    rewrite Hs.
    replace (ren_cidx (ren_shift (ren_lift j 1)) i1) with (lift_cidx (S j) 1 i1)
      by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y j); rw_nat_bool; lia]).
    replace (ren_cidx (ren_shift (ren_lift j 1)) i2) with (lift_cidx (S j) 1 i2)
      by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y j); rw_nat_bool; lia]).
    rewrite (IHi1 (S j)), (IHi2 (S j)). reflexivity.
Qed.

Lemma subst_cidx_tvar_in_cty_gen : forall (D : JoinDomain) (T U : cty D) (val : cidx D) j k,
  j <= k ->
  cty_uses_kinds true false false false false false false k U = false ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false j T = false ->
  subst_cidx_in_cty k val (subst_tvar_in_cty j U T) =
  subst_tvar_in_cty j (subst_cidx_in_cty k val U) (subst_cidx_in_cty (S k) (lift_cidx j 1 val) T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U val j k Hjk HU Huk Hu0; cbn in *; try reflexivity;
    try (f_equal; apply IHT; assumption);
    try (apply orb_false_iff in Huk as [H1 H2]; apply orb_false_iff in Hu0 as [Hu1 Hu2];
         f_equal; [apply IHT1 | apply IHT2]; assumption).
  - apply orb_false_iff in Huk as [H1 H2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    rewrite (IHT _ _ _ _ Hjk HU H1 Hu1). f_equal.
    assert (Hs0 : cidx_uses_kinds false false false false false j (subst_cidx (S k) (lift_cidx j 1 val) len) = false).
    { apply cidx_uses_kinds_0_subst; [lia | exact H2 | apply cidx_uses_kinds_lift_j | exact Hu2]. }
    rewrite (subst_tvar_in_cidx_as_unshift D j len Hu2), (subst_tvar_in_cidx_as_unshift D j _ Hs0).
    symmetry. apply subst_cidx_unshift_gen; assumption.
  - nat_bool_hyps. destruct (Nat.eq_dec x (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (Nat.eq_dec x j) as [-> | Hnej].
    + repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
    + destruct (le_lt_dec j x), (le_lt_dec (S k) x); try lia;
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - nat_bool_hyps. destruct (Nat.eq_dec b j) as [-> | Hnej]; [exfalso; lia |].
    destruct (Nat.eq_dec b (S k)) as [-> | Hnek]; [exfalso; lia |].
    destruct (le_lt_dec j b), (le_lt_dec (S k) b); try lia;
      repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - apply orb_false_iff in Huk as [H1 H2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    pose proof (cty_uses_kinds_lift_shift D U k HU) as HU'.
    rewrite ren_lift_comm_0_1.
    rewrite (IHT2 (lift_cty 0 1 U) (lift_cidx 0 1 val) (S j) (S k) ltac:(lia) HU' H2 Hu2).
    rewrite (subst_cidx_in_cty_lift_ge D U val 0 k ltac:(lia) HU). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    f_equal; [apply IHT1; assumption |].
    pose proof (cty_uses_kinds_lift_shift D U k HU) as HU'.
    rewrite ren_lift_comm_0_1.
    rewrite (IHT2 (lift_cty 0 1 U) (lift_cidx 0 1 val) (S j) (S k) ltac:(lia) HU' H2 Hu2).
    rewrite (subst_cidx_in_cty_lift_ge D U val 0 k ltac:(lia) HU). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2.
    apply orb_false_iff in Huk as [H1 Hk_r]. apply orb_false_iff in Hu0 as [Hu1 Hu_r].
    rewrite (H2 _ _ _ _ Hjk HU H1 Hu1), (IHf H3 Hk_r Hu_r). reflexivity.
  - f_equal.
    induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2]. apply orb_false_iff in Hu0 as [Hu1 Hu2].
    assert (Hs0 : cidx_uses_kinds false false false false false j (subst_cidx (S k) (lift_cidx j 1 val) idx) = false).
    { apply cidx_uses_kinds_0_subst; [lia | exact H1 | apply cidx_uses_kinds_lift_j | exact Hu1]. }
    rewrite (subst_tvar_in_cidx_as_unshift D j idx Hu1), (subst_tvar_in_cidx_as_unshift D j _ Hs0).
    f_equal; [symmetry; apply subst_cidx_unshift_gen; assumption | apply IH; assumption].
Qed.

Lemma subst_cidx_tvar_in_cty : forall (D : JoinDomain) (T U : cty D) (val : cidx D) k,
  cty_uses_kinds true false false false false false false k U = false ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds false true false false false false false 0 T = false ->
  subst_cidx_in_cty k val (subst_tvar_in_cty 0 U T) =
  subst_tvar_in_cty 0 (subst_cidx_in_cty k val U) (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) T).
Proof.
  intros D T U val k HU Huk Hu0. apply subst_cidx_tvar_in_cty_gen; [lia | exact HU | exact Huk | exact Hu0].
Qed.

Lemma cidx_uses_var_lift_shift : forall (D : JoinDomain) (i : cidx D) c,
  cidx_uses_var c i = false ->
  cidx_uses_var (S c) (lift_cidx 0 1 i) = false.
Proof.
  intros D i c Hi. unfold lift_cidx.
  assert (Hren : forall (u : cidx D) d d' rn,
    (forall y, y <> d -> rn y <> d') ->
    cidx_uses_var d u = false ->
    cidx_uses_var d' (ren_cidx rn u) = false).
  { induction u; intros d d' rn Hrn Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHu1 _ _ _ Hrn H1), (IHu2 _ _ _ Hrn H2); reflexivity);
      try (apply (IHu _ _ _ Hrn Hu));
      try (nat_bool_hyps; apply Nat.eqb_neq, Hrn; exact Hu).
    apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    rewrite (proj2 (Nat.eqb_neq _ _) (Hrn _ H1)). cbn.
    assert (Hrn' : forall y, y <> S d -> ren_shift rn y <> S d') by (intros [| y] Hy; cbn; [lia |]; pose proof (Hrn y ltac:(lia)); lia).
    rewrite (IHu1 _ _ _ Hrn' H2), (IHu2 _ _ _ Hrn' H3); reflexivity. }
  eapply Hren; [| exact Hi]. intros y Hy; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia.
Qed.

Lemma cidx_uses_var_subst_cidx_0 : forall (D : JoinDomain) (i val : cidx D) c k,
  c < k ->
  cidx_uses_kinds true false false false false k i = false ->
  cidx_uses_var c val = false ->
  cidx_uses_var c i = false ->
  cidx_uses_var c (subst_cidx k val i) = false.
Proof.
  intros D i. induction i; intros val c k Hck Huk Hv Hi; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in Hi as [H1 H2];
         rewrite (IHi1 _ _ _ Hck Hk1 Hv H1), (IHi2 _ _ _ Hck Hk2 Hv H2); reflexivity).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rw_nat_bool; exact Hv |].
    destruct (x <? k) eqn:Exk; nat_bool_hyps; cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - apply (IHi _ _ _ Hck Huk Hv Hi).
  - nat_bool_hyps. destruct (b <? k) eqn:E; cbv iota; nat_bool_hyps; cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (p <? k) eqn:E; cbv iota; nat_bool_hyps; cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (p <? k) eqn:E; cbv iota; nat_bool_hyps; cbn; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Huk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2].
    apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]. nat_bool_hyps.
    assert (Hs : ((if s <? k then s else if s =? k then 0 else s - 1) =? c) = false) by
      (destruct (s <? k) eqn:E; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia).
    rewrite Hs.
    pose proof (cidx_uses_var_lift_shift D val c Hv) as Hv'.
    rewrite (IHi1 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2 Hv' H2),
            (IHi2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk3 Hv' H3). reflexivity.
Qed.

Lemma cty_uses_var_subst_cidx_0 : forall (D : JoinDomain) (T : cty D) (val : cidx D) c k,
  c < k ->
  cty_uses_kinds true false false false false false false k T = false ->
  cidx_uses_var c val = false ->
  cty_uses_var c T = false ->
  cty_uses_var c (subst_cidx_in_cty k val T) = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros val c k Hck Huk Hv HT; cbn in *; try reflexivity;
    try (apply (IHT _ _ _ Hck Huk Hv HT));
    try (apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in HT as [H1 H2];
         rewrite (IHT1 _ _ _ Hck Hk1 Hv H1), (IHT2 _ _ _ Hck Hk2 Hv H2); reflexivity).
  - apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT _ _ _ Hck Hk1 Hv H1), (cidx_uses_var_subst_cidx_0 D len val c k Hck Hk2 Hv H2). reflexivity.
  - nat_bool_hyps. destruct (x <? k) eqn:E; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (b <? k) eqn:E; cbv iota; nat_bool_hyps; repeat (rw_nat_bool; cbv iota); try reflexivity; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ Hck Hk1 Hv H1).
    pose proof (cidx_uses_var_lift_shift D val c Hv) as Hv'.
    rewrite (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2 Hv' H2). reflexivity.
  - apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (IHT1 _ _ _ Hck Hk1 Hv H1).
    pose proof (cidx_uses_var_lift_shift D val c Hv) as Hv'.
    rewrite (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2 Hv' H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2.
    apply orb_false_iff in Huk as [Hk1 Hk_r]; apply orb_false_iff in HT as [H1 H3_r].
    rewrite (H2 _ _ _ Hck Hk1 Hv H1), (IHf H3 Hk_r H3_r). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [Hk1 Hk2]; apply orb_false_iff in HT as [H1 H2].
    rewrite (cidx_uses_var_subst_cidx_0 D idx val c k Hck Hk1 Hv H1), (IH Hk2 H2). reflexivity.
Qed.

Lemma lift_cidx_uses_var_0 : forall (D : JoinDomain) (v : cidx D),
  cidx_uses_var 0 (lift_cidx 0 1 v) = false.
Proof.
  intros D v.
  assert (Hgen : forall (i : cidx D) c, cidx_uses_var c (lift_cidx c 1 i) = false).
  { induction i; intros c; cbn; try reflexivity;
      try (rewrite IHi1, IHi2; reflexivity);
      try (apply IHi);
      try (unfold ren_lift; destruct (Nat.ltb_spec x c); apply Nat.eqb_neq; lia);
      try (unfold ren_lift; destruct (Nat.ltb_spec b c); apply Nat.eqb_neq; lia);
      try (unfold ren_lift; destruct (Nat.ltb_spec p c); apply Nat.eqb_neq; lia).
    - assert (Hs : (ren_lift c 1 s =? c) = false) by (unfold ren_lift; destruct (Nat.ltb_spec s c); apply Nat.eqb_neq; lia).
      rewrite Hs.
      replace (ren_cidx (ren_shift (ren_lift c 1)) i1) with (lift_cidx (S c) 1 i1)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y c); rw_nat_bool; lia]).
      replace (ren_cidx (ren_shift (ren_lift c 1)) i2) with (lift_cidx (S c) 1 i2)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity | destruct (Nat.ltb_spec y c); rw_nat_bool; lia]).
      rewrite (IHi1 (S c)), (IHi2 (S c)). reflexivity. }
  apply Hgen.
Qed.

(* Environment and Term Substitution for Dependent Nat Index *)

Fixpoint subst_cidx_cenv {D : JoinDomain} (idx : cidx D) (z : list (grade D)) (env_a : cenv D) : cenv D :=
  match env_a with
  | [] => []
  | e :: rest =>
      {| cbinder := cbinder e;
         cannotation := subst_cidx_in_cty (length rest) (lift_cidx 0 (length rest) idx) (cannotation e);
         ctype_uses := vec_subst (length rest) z (ctype_uses e) |} :: subst_cidx_cenv idx z rest
  end.

Lemma subst_cidx_cenv_length : forall (D : JoinDomain) (idx : cidx D) z env_a,
  length (subst_cidx_cenv idx z env_a) = length env_a.
Proof.
  intros D idx z env_a. induction env_a as [| e rest IH]; cbn; [reflexivity | congruence].
Qed.

Fixpoint subst_cidx_in_cterm {D : JoinDomain} (k : nat) (val : cidx D) (t : cterm D) : cterm D :=
  match t with
  | CVar x =>
      if x =? k then CNatVal val
      else if x <? k then CVar x
      else CVar (x - 1)
  | CNatVal i => CNatVal (subst_cidx k val i)
  | CBoolVal b => CBoolVal b
  | CTypeVal T => CTypeVal (subst_cidx_in_cty k val T)
  | CLam x s r dom body =>
      CLam x s r (subst_cidx_in_cty k val dom) (subst_cidx_in_cterm (S k) (lift_cidx 0 1 val) body)
  | CApp fn arg => CApp (subst_cidx_in_cterm k val fn) (subst_cidx_in_cterm k val arg)
  | CLet x s r ann rhs body =>
      CLet x s r (subst_cidx_in_cty k val ann)
        (subst_cidx_in_cterm k val rhs) (subst_cidx_in_cterm (S k) (lift_cidx 0 1 val) body)
  | CPair x r fst_ty snd_ty fst_val snd_val =>
      CPair x r (subst_cidx_in_cty k val fst_ty) (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) snd_ty)
        (subst_cidx_in_cterm k val fst_val) (subst_cidx_in_cterm k val snd_val)
  | CLetPair x y s kappa mot pr body =>
      CLetPair x y s kappa (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) mot)
        (subst_cidx_in_cterm k val pr) (subst_cidx_in_cterm (S (S k)) (lift_cidx 0 2 val) body)
  | CPromote q v => CPromote q (subst_cidx_in_cterm k val v)
  | CLetBox x kappa mot bx body =>
      CLetBox x kappa (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) mot)
        (subst_cidx_in_cterm k val bx) (subst_cidx_in_cterm (S k) (lift_cidx 0 1 val) body)
  | CInl rt v => CInl (subst_cidx_in_cty k val rt) (subst_cidx_in_cterm k val v)
  | CInr lt v => CInr (subst_cidx_in_cty k val lt) (subst_cidx_in_cterm k val v)
  | CMatchSum x y s kappa mot scrut lb rb =>
      CMatchSum x y s kappa (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) mot)
        (subst_cidx_in_cterm k val scrut)
        (subst_cidx_in_cterm (S k) (lift_cidx 0 1 val) lb)
        (subst_cidx_in_cterm (S k) (lift_cidx 0 1 val) rb)
  | CIf c th el =>
      CIf (subst_cidx_in_cterm k val c) (subst_cidx_in_cterm k val th) (subst_cidx_in_cterm k val el)
  | CRecordMk id fields =>
      CRecordMk id (map (fun '(fn, fg, ft, fv) =>
        (fn, fg, subst_cidx_in_cty k val ft, subst_cidx_in_cterm k val fv)) fields)
  | CMatchRecord id s mot scrut bs body =>
      CMatchRecord id s (subst_cidx_in_cty k val mot) (subst_cidx_in_cterm k val scrut) bs
        (subst_cidx_in_cterm (length bs + k) (lift_cidx 0 (length bs) val) body)
  | CSubgrade target body => CSubgrade (subst_cidx_in_cty k val target) (subst_cidx_in_cterm k val body)
  | CFix xn xr sr mot scrut base step =>
      CFix xn xr sr (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) mot)
        (subst_cidx_in_cterm k val scrut)
        (subst_cidx_in_cterm k val base)
        (subst_cidx_in_cterm (S (S k)) (lift_cidx 0 2 val) step)
  end.

Lemma ren_plus_1_as_lift : forall (D : JoinDomain) (T : cty D),
  ren_cty S T = lift_cty 0 1 T.
Proof.
  intros D T. unfold lift_cty. apply ren_cty_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia.
Qed.

Lemma ren_plus_1_cidx_as_lift : forall (D : JoinDomain) (i : cidx D),
  ren_cidx S i = lift_cidx 0 1 i.
Proof.
  intros D i. unfold lift_cidx. apply ren_cidx_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia.
Qed.

Lemma cidx_uses_kinds_erase_hints : forall (D : JoinDomain) idx tvar tunbox unbox fst snd scase k (T : cty D),
  cty_uses_kinds idx tvar tunbox unbox fst snd scase k (erase_hints T) =
  cty_uses_kinds idx tvar tunbox unbox fst snd scase k T.
Proof.
  intros D idx tvar tunbox unbox fst snd scase k T. revert k.
  induction T using cty_ind_nested; intro k; cbn; try reflexivity;
    try (apply IHT); try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT. reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
Qed.

Lemma cty_uses_kinds_alpha : forall (D : JoinDomain) idx tvar tunbox unbox fst snd scase k (T1 T2 : cty D),
  cty_alpha_eq T1 T2 ->
  cty_uses_kinds idx tvar tunbox unbox fst snd scase k T1 =
  cty_uses_kinds idx tvar tunbox unbox fst snd scase k T2.
Proof.
  intros D idx tvar tunbox unbox fst snd scase k T1 T2 Ha.
  rewrite <- (cidx_uses_kinds_erase_hints D _ _ _ _ _ _ _ k T1).
  rewrite <- (cidx_uses_kinds_erase_hints D _ _ _ _ _ _ _ k T2).
  unfold cty_alpha_eq in Ha; rewrite Ha; reflexivity.
Qed.

Lemma cty_uses_kinds_ren_plus : forall (D : JoinDomain) (T : cty D) d k,
  cty_uses_kinds true false false false false false false k T = false ->
  cty_uses_kinds true false false false false false false (d + k) (ren_cty (plus d) T) = false.
Proof.
  intros D T d k Hu. eapply cty_uses_kinds_ren_gen; [| exact Hu].
  intros x Hne. lia.
Qed.

Lemma cidx_uses_kinds_ren_gt_gen : forall (D : JoinDomain) (j : cidx D) rn k,
  (forall x, rn x <> k) ->
  cidx_uses_kinds true false false false false k (ren_cidx rn j) = false.
Proof.
  intros D j. induction j; intros rn k Hr; cbn; try reflexivity;
    try (rewrite (IHj1 _ _ Hr), (IHj2 _ _ Hr); reflexivity);
    try (apply IHj; exact Hr).
  - apply Nat.eqb_neq; apply Hr.
  - apply Nat.eqb_neq; apply Hr.
  - apply Nat.eqb_neq; apply Hr.
  - assert (Hs : (rn s =? k) = false) by (apply Nat.eqb_neq, Hr).
    rewrite Hs; cbn.
    rewrite (IHj1 (ren_shift rn) (S k)), (IHj2 (ren_shift rn) (S k));
      [reflexivity | intros [| y]; cbn; [lia | pose proof (Hr y); lia]
                   | intros [| y]; cbn; [lia | pose proof (Hr y); lia]].
Qed.

Lemma cty_uses_kinds_ren_gt : forall (D : JoinDomain) (T : cty D) d k,
  k < d ->
  cty_uses_kinds true false false false false false false k (ren_cty (plus d) T) = false.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) rn k,
    (forall x, rn x <> k) ->
    cty_uses_kinds true false false false false false false k (ren_cty rn T0) = false).
  { clear T. intros T0. induction T0 using cty_ind_nested; intros rn k Hr; cbn; try reflexivity;
      try (apply IHT0; exact Hr);
      try (rewrite (IHT0_1 _ _ Hr), (IHT0_2 _ _ Hr); reflexivity).
    - rewrite (IHT0 _ _ Hr), (cidx_uses_kinds_ren_gt_gen D len rn k Hr). reflexivity.
    - apply Nat.eqb_neq; apply Hr.
    - apply Nat.eqb_neq; apply Hr.
    - rewrite (IHT0_1 _ _ Hr), (IHT0_2 (ren_shift rn) (S k)); [reflexivity | intros [| y]; cbn; [lia | pose proof (Hr y); lia]].
    - rewrite (IHT0_1 _ _ Hr), (IHT0_2 (ren_shift rn) (S k)); [reflexivity | intros [| y]; cbn; [lia | pose proof (Hr y); lia]].
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
      inversion H; subst; cbn in H2. rewrite (H2 _ _ Hr), (IHf H3). reflexivity.
    - induction indices as [| idx rest IH]; cbn; [reflexivity |].
      rewrite (cidx_uses_kinds_ren_gt_gen D idx rn k Hr), IH. reflexivity. }
  intros d k Hkd. apply Hgen. intro x; lia.
Qed.

Definition cenv_nat_safe {D : JoinDomain} (env_a : cenv D) (k : nat) : Prop :=
  forall x e, x < length env_a -> clookup env_a x = Some e ->
    cty_uses_kinds true false false false false false false (k - S x) (cannotation e) = false.

Lemma cenv_nat_safe_cons : forall (D : JoinDomain) e0 (env_a : cenv D),
  cty_uses_kinds true false false false false false false (length env_a) (cannotation e0) = false ->
  cenv_nat_safe env_a (length env_a) ->
  cenv_nat_safe (e0 :: env_a) (S (length env_a)).
Proof.
  intros D e0 env_a He0 Hsafe [| x'] e Hlt Hl; cbn in *.
  - inversion Hl; subst. rewrite Nat.sub_0_r. exact He0.
  - apply (Hsafe x' e ltac:(lia) Hl).
Qed.

Lemma subst_cidx_lookup_lt : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b x e,
  x < length env_a ->
  cenv_nat_safe env_a (length env_a) ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_cidx_cenv idx z env_a ++ env_b) x = Some e' /\
    ren_cty (plus (S x)) (cannotation e') =
      subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) (ren_cty (plus (S x)) (cannotation e)) /\
    vec_zero (S x) ++ ctype_uses e' = vec_subst (length env_a) z (vec_zero (S x) ++ ctype_uses e) /\
    skipn (S x) (subst_cidx_cenv idx z env_a ++ env_b) =
      subst_cidx_cenv idx z (skipn (S x) env_a) ++ env_b /\
    skipn (S x) (env_a ++ b :: env_b) = skipn (S x) env_a ++ b :: env_b.
Proof.
  intros D idx z env_a. induction env_a as [| e0 rest IH]; intros b env_b [| x'] e Hlt Hsafe Hl; cbn in *; try lia.
  - inversion Hl; subst; cbn.
    exists {| cbinder := cbinder e;
              cannotation := subst_cidx_in_cty (length rest) (lift_cidx 0 (length rest) idx) (cannotation e);
              ctype_uses := vec_subst (length rest) z (ctype_uses e) |}.
    repeat split; try reflexivity.
    cbn [cannotation].
    pose proof (Hsafe 0 e ltac:(cbn; lia) eq_refl) as He_safe.
    cbn [length] in He_safe. replace (S (length rest) - 1) with (length rest) in He_safe by lia.
    rewrite ren_plus_1_as_lift, <- (subst_cidx_in_cty_lift_ge D (cannotation e) (lift_cidx 0 (length rest) idx) 0 (length rest) ltac:(lia) He_safe).
    rewrite lift_cidx_add, <- ren_plus_1_as_lift. reflexivity.
  - assert (Hsafe_r : cenv_nat_safe rest (length rest)).
    { intros y ey Hy Hly. exact (Hsafe (S y) ey ltac:(cbn; lia) Hly). }
    destruct (IH b env_b x' e ltac:(lia) Hsafe_r Hl) as [e' [Hl' [Heq [Hvec [Hsk1 Hsk2]]]]].
    exists e'. repeat split; [exact Hl' | | | exact Hsk1 | exact Hsk2].
    + assert (He_safe : cty_uses_kinds true false false false false false false (length rest - S x') (cannotation e) = false).
      { apply (Hsafe (S x') e ltac:(cbn; lia)).
        clear -Hlt Hl. unfold clookup in *. rewrite nth_error_app1 in Hl by lia. exact Hl. }
      assert (He_safe_ren : cty_uses_kinds true false false false false false false (length rest) (ren_cty (fun m => S (x' + m)) (cannotation e)) = false).
      { replace (length rest) with (S x' + (length rest - S x')) by lia.
        apply cty_uses_kinds_ren_plus; exact He_safe. }
      transitivity (ren_cty S (ren_cty (fun m => S (x' + m)) (cannotation e')));
        [rewrite ren_cty_comp; apply ren_cty_ext; intro y; cbn; reflexivity
        |rewrite Heq, !ren_plus_1_as_lift, <- (subst_cidx_in_cty_lift_ge D _ _ 0 (length rest) ltac:(lia) He_safe_ren), lift_cidx_add;
         cbn [Nat.add]; rewrite <- ren_plus_1_as_lift, ren_cty_comp; f_equal; apply ren_cty_ext; intro y; cbn; reflexivity].
    + cbn [vec_zero vec_subst repeat app]; f_equal; exact Hvec.
Qed.

Lemma subst_cidx_ren_skip_gen : forall (D : JoinDomain) (i val : cidx D) k r1 r2,
  (forall x, (r1 x < k /\ r2 x = r1 x) \/ (r1 x > k /\ r2 x = r1 x - 1)) ->
  subst_cidx k val (ren_cidx r1 i) = ren_cidx r2 i.
Proof.
  intros D i. induction i; intros val k r1 r2 Hr; cbn; try reflexivity;
    try (rewrite (IHi1 _ _ _ _ Hr), (IHi2 _ _ _ _ Hr); reflexivity).
  - destruct (Hr x) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - rewrite (IHi _ _ _ _ Hr). reflexivity.
  - destruct (Hr b) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Hr p) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Hr p) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - f_equal.
    + destruct (Hr s) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); lia.
    + apply (IHi1 (lift_cidx 0 1 val) (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
    + apply (IHi2 (lift_cidx 0 1 val) (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
Qed.

Lemma subst_cidx_in_cty_ren_skip_gen : forall (D : JoinDomain) (T : cty D) (val : cidx D) k r1 r2,
  (forall x, (r1 x < k /\ r2 x = r1 x) \/ (r1 x > k /\ r2 x = r1 x - 1)) ->
  subst_cidx_in_cty k val (ren_cty r1 T) = ren_cty r2 T.
Proof.
  intros D T. induction T using cty_ind_nested; intros val k r1 r2 Hr; cbn; try reflexivity;
    try (f_equal; apply IHT; exact Hr);
    try (f_equal; [apply IHT1 | apply IHT2]; exact Hr).
  - f_equal; [apply IHT; exact Hr | apply subst_cidx_ren_skip_gen; exact Hr].
  - destruct (Hr x) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - destruct (Hr b) as [[H1 H2] | [H1 H2]]; repeat (rw_nat_bool; cbv iota); f_equal; lia.
  - f_equal; [apply IHT1; exact Hr |].
    apply (IHT2 (lift_cidx 0 1 val) (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
  - f_equal; [apply IHT1; exact Hr |].
    apply (IHT2 (lift_cidx 0 1 val) (S k)). intros [| y]; cbn; [left; lia | destruct (Hr y) as [[H1 H2] | [H1 H2]]; [left; lia | right; lia]].
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite (H2 _ _ _ _ Hr), (IHf H3). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply subst_cidx_ren_skip_gen; exact Hr | exact IH].
Qed.

Lemma vec_add_zero_len_le : forall (D : JoinDomain) (u : list (grade D)) n,
  length u = n ->
  vec_add u (vec_zero n) = u.
Proof.
  intros D u n <-. apply vec_add_zero_r.
Qed.

Lemma subst_cidx_lookup_gt : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b x e,
  x > length env_a ->
  length z = length env_b ->
  length (vec_zero (S x) ++ ctype_uses e) = S (length env_a + length env_b) ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_cidx_cenv idx z env_a ++ env_b) (x - 1) = Some e' /\
    ren_cty (plus (S (x - 1))) (cannotation e') =
      subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) (ren_cty (plus (S x)) (cannotation e)) /\
    vec_zero (S (x - 1)) ++ ctype_uses e' = vec_subst (length env_a) z (vec_zero (S x) ++ ctype_uses e) /\
    skipn (S (x - 1)) (subst_cidx_cenv idx z env_a ++ env_b) = skipn (S x) (env_a ++ b :: env_b).
Proof.
  intros D idx z env_a b env_b x e Hgt Hz Hlen Hl.
  exists e.
  assert (Hl_b : clookup env_b (x - S (length env_a)) = Some e).
  { unfold clookup in *. rewrite nth_error_app2 in Hl by lia.
    destruct (x - length env_a) as [| k'] eqn:Ed; [lia |].
    cbn in Hl. replace (x - S (length env_a)) with k' by lia. exact Hl. }
  repeat split.
  - unfold clookup. rewrite nth_error_app2; [| rewrite subst_cidx_cenv_length; lia].
    rewrite subst_cidx_cenv_length. replace (x - 1 - length env_a) with (x - S (length env_a)) by lia. exact Hl_b.
  - symmetry. apply subst_cidx_in_cty_ren_skip_gen. intro y. right; lia.
  - clear Hl Hl_b. induction env_a as [| e0 rest IH] in x, Hgt, Hlen |- *.
    + destruct x as [| x']; [lia |].
      replace (S x' - 1) with x' by lia.
      change (vec_zero (S (S x'))) with (@zero D :: vec_zero (S x')).
      cbn [length app vec_subst]. rewrite vec_scale_zero, Hz.
      unfold vec_zero in Hlen. rewrite length_app, repeat_length in Hlen.
      symmetry. apply vec_add_zero_len_le. unfold vec_zero; rewrite length_app, repeat_length; cbn in Hlen; lia.
    + destruct x as [| x']; [lia |].
      cbn [length subst_cidx_cenv] in *.
      replace (S x' - 1) with (S (x' - 1)) by lia.
      cbn [app vec_zero vec_subst repeat]. f_equal.
      apply IH; [lia | unfold vec_zero in *; rewrite length_app, repeat_length in *; lia].
  - rewrite !skipn_app, !subst_cidx_cenv_length.
    rewrite (skipn_all2 (subst_cidx_cenv idx z env_a)) by (rewrite subst_cidx_cenv_length; lia).
    rewrite (skipn_all2 env_a) by lia.
    cbn [app]. replace (S (x - 1) - length env_a) with (S x - S (length env_a)) by lia.
    destruct (S x - length env_a) as [| m] eqn:Em; [lia |].
    cbn [skipn]. replace (S x - S (length env_a)) with m by lia. reflexivity.
Qed.

(* Clean helper for lifting env_b demands to env_a' ++ env_b *)

Lemma weaken_cidx_demand_app_left : forall (D : JoinDomain) env_b (i : cidx D) z,
  CIdxDemand env_b i z ->
  forall env_a',
  exists z', CIdxDemand (env_a' ++ env_b) (lift_cidx 0 (length env_a') i) z' /\
             branch_rel z' (vec_zero (length env_a') ++ z).
Proof.
  intros D env_b i z Hi env_a'.
  induction env_a' as [| e0 rest [z' [Hz' Hbr]]].
  - cbn. replace (lift_cidx 0 0 i) with i by (unfold lift_cidx; symmetry; transitivity (ren_cidx (fun x => x) i); [apply ren_cidx_ext; intro x; unfold ren_lift; destruct (x <? 0) eqn:Ex; nat_bool_hyps; lia | apply ren_cidx_id]).
    exists z; split; [exact Hi | apply branch_rel_refl].
  - cbn [app length]. rewrite <- lift_cidx_add with (a := 1) (b := length rest).
    rewrite lift_cidx_as_weaken. change (e0 :: rest ++ env_b) with (weaken_cenv e0 [] (rest ++ env_b)).
    destruct (grade_join D) as [j |] eqn:Hj.
    + destruct (weaken_cidx_demand_join D j e0 [] (rest ++ env_b) _ z' Hj Hz') as [z'' [Hz'' Hallow]].
      exists z''. split; [exact Hz'' |].
      unfold branch_rel in *. rewrite Hj in *.
      eapply vec_allows_trans; [exact Hallow |].
      cbn. constructor; [apply allows_refl | exact Hbr].
    + exists (zero :: z'). split.
      * replace (zero :: z') with (vec_insert_zero 0 z') by reflexivity.
        eapply ren_cidx_demand; [exact (re_type (weaken_RenEnv D e0 [] (rest ++ env_b) ltac:(intros j0 Hj0; rewrite Hj in Hj0; discriminate))) | exact Hz'].
      * unfold branch_rel in *. rewrite Hj in *. subst z'. reflexivity.
Qed.

Lemma weaken_ctype_demand_app_left : forall (D : JoinDomain) env_b (T : cty D) z,
  CTypeDemand env_b T z ->
  forall env_a',
  exists z', CTypeDemand (env_a' ++ env_b) (lift_cty 0 (length env_a') T) z' /\
             branch_rel z' (vec_zero (length env_a') ++ z).
Proof.
  intros D env_b T z HT env_a'.
  induction env_a' as [| e0 rest [z' [Hz' Hbr]]].
  - cbn. replace (lift_cty 0 0 T) with T by (unfold lift_cty; symmetry; transitivity (ren_cty (fun x => x) T); [apply ren_cty_ext; intro x; unfold ren_lift; destruct (x <? 0) eqn:Ex; nat_bool_hyps; lia | apply ren_cty_id]).
    exists z; split; [exact HT | apply branch_rel_refl].
  - cbn [app length]. rewrite <- lift_cty_add with (a := 1) (b := length rest).
    rewrite lift_as_weaken_rho. change (e0 :: rest ++ env_b) with (weaken_cenv e0 [] (rest ++ env_b)).
    destruct (grade_join D) as [j |] eqn:Hj.
    + destruct (weaken_ctype_demand_join D j e0 [] (rest ++ env_b) _ z' Hj Hz') as [z'' [Hz'' Hallow]].
      exists z''. split; [exact Hz'' |].
      unfold branch_rel in *. rewrite Hj in *.
      eapply vec_allows_trans; [exact Hallow |].
      cbn. constructor; [apply allows_refl | exact Hbr].
    + exists (zero :: z'). split.
      * replace (zero :: z') with (vec_insert_zero 0 z') by reflexivity.
        eapply ren_ctype_demand; [exact (re_type (weaken_RenEnv D e0 [] (rest ++ env_b) ltac:(intros j0 Hj0; rewrite Hj in Hj0; discriminate))) | exact Hz'].
      * unfold branch_rel in *. rewrite Hj in *. subst z'. reflexivity.
Qed.

Lemma ren_cuniverse_level_gen : forall (D : JoinDomain) (env1 env2 : cenv D) rho T lvl,
  (forall x e, clookup env1 x = Some e ->
     exists e', clookup env2 (rho x) = Some e' /\
       (forall lvl0, cty_alpha_eq (cannotation e) (CUniv lvl0) -> cty_alpha_eq (cannotation e') (CUniv lvl0)) /\
       (forall q0 lvl0, cty_alpha_eq (cannotation e) (CBox q0 (CUniv lvl0)) -> cty_alpha_eq (cannotation e') (CBox q0 (CUniv lvl0)))) ->
  CUniverseLevel env1 T lvl ->
  CUniverseLevel env2 (ren_cty rho T) lvl.
Proof.
  intros D env1 env2 rho T lvl Hlk H. revert env2 rho Hlk.
  induction H using CUniverseLevel_ind_mut with
    (P := fun env1 T lvl _ => forall env2 rho,
      (forall x e, clookup env1 x = Some e ->
         exists e', clookup env2 (rho x) = Some e' /\
           (forall lvl0, cty_alpha_eq (cannotation e) (CUniv lvl0) -> cty_alpha_eq (cannotation e') (CUniv lvl0)) /\
           (forall q0 lvl0, cty_alpha_eq (cannotation e) (CBox q0 (CUniv lvl0)) -> cty_alpha_eq (cannotation e') (CBox q0 (CUniv lvl0)))) ->
      CUniverseLevel env2 (ren_cty rho T) lvl)
    (P0 := fun env1 fs lvl _ => forall env2 rho,
      (forall x e, clookup env1 x = Some e ->
         exists e', clookup env2 (rho x) = Some e' /\
           (forall lvl0, cty_alpha_eq (cannotation e) (CUniv lvl0) -> cty_alpha_eq (cannotation e') (CUniv lvl0)) /\
           (forall q0 lvl0, cty_alpha_eq (cannotation e) (CBox q0 (CUniv lvl0)) -> cty_alpha_eq (cannotation e') (CBox q0 (CUniv lvl0)))) ->
      CRecordFieldLevel env2 (map (fun '(fn, fg, ft) => (fn, fg, ren_cty rho ft)) fs) lvl);
    intros env2 rho Hlk; cbn; try (constructor; eauto; fail).
  - match goal with
    | Hc : clookup _ _ = Some _, Ha : cty_alpha_eq _ (CUniv _) |- _ =>
        destruct (Hlk _ _ Hc) as [e' [Hl' [Hu _]]]; eapply CLevelTVar; [exact Hl' | exact (Hu _ Ha)]
    end.
  - match goal with
    | Hc : clookup _ _ = Some _, Ha : cty_alpha_eq _ (CBox _ (CUniv _)) |- _ =>
        destruct (Hlk _ _ Hc) as [e' [Hl' [_ Hb]]]; eapply CLevelTUnbox; [exact Hl' | exact (Hb _ _ Ha)]
    end.
  - econstructor; [apply IHCUniverseLevel1; exact Hlk |].
    apply IHCUniverseLevel2. intros [| x'] e0 Hl0; cbn in *.
    + inversion Hl0; subst. eexists; split; [reflexivity |].
      split; [intros lvl0 Ha; cbn [cannotation] in *; unfold cty_alpha_eq in *; rewrite erase_hints_ren, Ha; reflexivity
             |intros q0 lvl0 Ha; cbn [cannotation] in *; unfold cty_alpha_eq in *; rewrite erase_hints_ren, Ha; reflexivity].
    + destruct (Hlk x' e0 Hl0) as [e' [Hl' Hrest]]. exists e'; split; [exact Hl' | exact Hrest].
  - econstructor; [apply IHCUniverseLevel1; exact Hlk |].
    apply IHCUniverseLevel2. intros [| x'] e0 Hl0; cbn in *.
    + inversion Hl0; subst. eexists; split; [reflexivity |].
      split; [intros lvl0 Ha; cbn [cannotation] in *; unfold cty_alpha_eq in *; rewrite erase_hints_ren, Ha; reflexivity
             |intros q0 lvl0 Ha; cbn [cannotation] in *; unfold cty_alpha_eq in *; rewrite erase_hints_ren, Ha; reflexivity].
    + destruct (Hlk x' e0 Hl0) as [e' [Hl' Hrest]]. exists e'; split; [exact Hl' | exact Hrest].
Qed.

Lemma weaken_cuniverse_level_app_left : forall (D : JoinDomain) env_b (T : cty D) lvl,
  CUniverseLevel env_b T lvl ->
  forall env_a',
  CUniverseLevel (env_a' ++ env_b) (lift_cty 0 (length env_a') T) lvl.
Proof.
  intros D env_b T lvl HT env_a'.
  replace (lift_cty 0 (length env_a') T) with (ren_cty (plus (length env_a')) T)
    by (unfold lift_cty; apply ren_cty_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia).
  eapply ren_cuniverse_level_gen; [| exact HT].
  intros x e Hl. exists e; repeat split; auto.
  unfold clookup in *. rewrite nth_error_app2 by lia.
  replace (length env_a' + x - length env_a') with x by lia. exact Hl.
Qed.

Lemma subst_cidx_lookup_lt_ann_raw : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b x e,
  x < length env_a ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_cidx_cenv idx z env_a ++ env_b) x = Some e' /\
    cannotation e' =
      subst_cidx_in_cty (length env_a - S x) (lift_cidx 0 (length env_a - S x) idx) (cannotation e) /\
    vec_zero (S x) ++ ctype_uses e' = vec_subst (length env_a) z (vec_zero (S x) ++ ctype_uses e) /\
    skipn (S x) (subst_cidx_cenv idx z env_a ++ env_b) =
      subst_cidx_cenv idx z (skipn (S x) env_a) ++ env_b /\
    skipn (S x) (env_a ++ b :: env_b) = skipn (S x) env_a ++ b :: env_b.
Proof.
  intros D idx z env_a. induction env_a as [| e0 rest IH]; intros b env_b [| x'] e Hlt Hl; cbn in *; try lia.
  - inversion Hl; subst; cbn.
    exists {| cbinder := cbinder e;
              cannotation := subst_cidx_in_cty (length rest) (lift_cidx 0 (length rest) idx) (cannotation e);
              ctype_uses := vec_subst (length rest) z (ctype_uses e) |}.
    repeat split; try reflexivity. cbn [cannotation]. replace (length rest - 0) with (length rest) by lia. reflexivity.
  - destruct (IH b env_b x' e ltac:(lia) Hl) as [e' [Hl' [Heq [Hvec [Hsk1 Hsk2]]]]].
    exists e'. repeat split; [exact Hl' | exact Heq | | exact Hsk1 | exact Hsk2].
    cbn [vec_zero vec_subst repeat app]; f_equal; exact Hvec.
Qed.

Lemma subst_cidx_lookup_gt_ann : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b x e,
  x > length env_a ->
  clookup (env_a ++ b :: env_b) x = Some e ->
  exists e',
    clookup (subst_cidx_cenv idx z env_a ++ env_b) (x - 1) = Some e' /\
    cannotation e' = cannotation e /\
    ren_cty (plus (S (x - 1))) (cannotation e') =
      subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) (ren_cty (plus (S x)) (cannotation e)) /\
    skipn (S (x - 1)) (subst_cidx_cenv idx z env_a ++ env_b) = skipn (S x) (env_a ++ b :: env_b).
Proof.
  intros D idx z env_a b env_b x e Hgt Hl.
  exists e.
  assert (Hl_b : clookup env_b (x - S (length env_a)) = Some e).
  { unfold clookup in *. rewrite nth_error_app2 in Hl by lia.
    destruct (x - length env_a) as [| k'] eqn:Ed; [lia |].
    cbn in Hl. replace (x - S (length env_a)) with k' by lia. exact Hl. }
  repeat split.
  - unfold clookup. rewrite nth_error_app2; [| rewrite subst_cidx_cenv_length; lia].
    rewrite subst_cidx_cenv_length. replace (x - 1 - length env_a) with (x - S (length env_a)) by lia. exact Hl_b.
  - symmetry. apply subst_cidx_in_cty_ren_skip_gen. intro y. right; lia.
  - rewrite !skipn_app, !subst_cidx_cenv_length.
    rewrite (skipn_all2 (subst_cidx_cenv idx z env_a)) by (rewrite subst_cidx_cenv_length; lia).
    rewrite (skipn_all2 env_a) by lia.
    cbn [app]. replace (S (x - 1) - length env_a) with (S x - S (length env_a)) by lia.
    destruct (S x - length env_a) as [| m] eqn:Em; [lia |].
    cbn [skipn]. replace (S x - S (length env_a)) with m by lia. reflexivity.
Qed.

Lemma subst_cidx_demand : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b i d,
  cannotation b = CNat ->
  cenv_nat_safe env_a (length env_a) ->
  CIdxDemand env_b idx z ->
  CIdxDemand (env_a ++ b :: env_b) i d ->
  exists d',
    CIdxDemand (subst_cidx_cenv idx z env_a ++ env_b) (subst_cidx (length env_a) (lift_cidx 0 (length env_a) idx) i) d' /\
    branch_rel d' (vec_subst (length env_a) z d).
Proof.
  intros D idx z env_a b env_b i d Hb Hsafe Hidx H.
  remember (env_a ++ b :: env_b) as env1 eqn:Henv1.
  revert env_a Henv1 Hsafe.
  induction H; intros env_a Henv1 Hsafe; subst env; cbn.
  - destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt].
    + destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b x e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandVar; [exact Hl' |].
        rewrite Heq. exact (subst_cidx_alpha_eq D (length env_a - S x) (lift_cidx 0 (length env_a - S x) idx) _ _ H0).
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | exact Hlt].
    + subst x. repeat (rw_nat_bool; cbv iota).
      assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2 in H by lia; rewrite Nat.sub_diag in H; inversion H; reflexivity).
      subst e.
      destruct (weaken_cidx_demand_app_left D env_b idx z Hidx (subst_cidx_cenv idx z env_a)) as [z' [Hz' Hbr]].
      rewrite subst_cidx_cenv_length in Hz', Hbr.
      eexists; split; [exact Hz' |].
      rewrite length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_eq; [| eapply cidx_demand_length; exact Hidx].
      cbn [length]. rewrite vec_scale_one. exact Hbr.
    + destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b x e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hx_len; cbn in Hx_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandVar; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | lia | lia].
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero; [eexists; split; [constructor | rewrite !length_app, subst_cidx_cenv_length; apply branch_rel_refl] | eapply cidx_demand_length; exact Hidx].
  - destruct (IHCIdxDemand1 env_a eq_refl Hsafe) as [dl' [Hdl' Hbrl]].
    destruct (IHCIdxDemand2 env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]].
    pose proof (cidx_demand_length D _ _ _ H) as Hlen1.
    pose proof (cidx_demand_length D _ _ _ H0) as Hlen2.
    rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2.
    exists (vec_add dl' dr'); split; [constructor; assumption |].
    rewrite (vec_subst_add D (length env_a) z dl dr (length env_b)); [apply branch_rel_add; assumption | eapply cidx_demand_length; exact Hidx | lia | lia].
  - destruct (IHCIdxDemand env_a eq_refl Hsafe) as [d' [Hd' Hbr]].
    exists (vec_scale q d'); split; [constructor; assumption |].
    rewrite vec_subst_scale; apply branch_rel_scale; exact Hbr.
  - destruct (lt_eq_lt_dec b0 (length env_a)) as [[Hlt | Heq_b] | Hgt].
    + destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b b0 e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandUnbox; [exact Hl' |].
        rewrite Heq. exact (subst_cidx_alpha_eq D (length env_a - S b0) (lift_cidx 0 (length env_a - S b0) idx) _ _ H0).
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | exact Hlt].
    + subst b0.
      assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2 in H by lia; rewrite Nat.sub_diag in H; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b b0 e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hb_len : b0 < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hb_len; cbn in Hb_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandUnbox; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | lia | lia].
  - destruct (lt_eq_lt_dec p (length env_a)) as [[Hlt | Heq_p] | Hgt].
    + destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b p e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandFst; [exact Hl' |].
        rewrite Heq.
        pose proof (subst_cidx_alpha_eq D (length env_a - S p) (lift_cidx 0 (length env_a - S p) idx) _ _ H0) as Ha. cbn in Ha. exact Ha.
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | exact Hlt].
    + subst p.
      assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2 in H by lia; rewrite Nat.sub_diag in H; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b p e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hp_len : p < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hp_len; cbn in Hp_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandFst; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | lia | lia].
  - destruct (lt_eq_lt_dec p (length env_a)) as [[Hlt | Heq_p] | Hgt].
    + destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b p e Hlt H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandSnd; [exact Hl' |].
        rewrite Heq.
        pose proof (subst_cidx_alpha_eq D (length env_a - S p) (lift_cidx 0 (length env_a - S p) idx) _ _ H0) as Ha. cbn in Ha. exact Ha.
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
          [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | exact Hlt].
    + subst p.
      assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2 in H by lia; rewrite Nat.sub_diag in H; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb in H0. cbn in H0. discriminate.
    + destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b p e Hgt H) as [e' [Hl' [Heq _]]].
      assert (Hp_len : p < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hp_len; cbn in Hp_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandSnd; [exact Hl' | rewrite Heq; exact H0].
      * rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | eapply cidx_demand_length; exact Hidx | lia | lia].
  - assert (Hnz : length z = length env_b) by (eapply cidx_demand_length; exact Hidx).
    pose proof (cidx_demand_length D _ _ _ H1) as Hdl. cbn in Hdl. rewrite length_app in Hdl; cbn in Hdl.
    pose proof (cidx_demand_length D _ _ _ H2) as Hdr. cbn in Hdr. rewrite length_app in Hdr; cbn in Hdr.
    assert (HAB_safe : cty_uses_kinds true false false false false false false (length env_a) (CSum A B) = false).
    { rewrite <- (cty_uses_kinds_alpha D _ _ _ _ _ _ _ (length env_a) _ _ H0).
      destruct (lt_eq_lt_dec s (length env_a)) as [[Hslt | Hseq] | Hsgt].
      - assert (Hs_e : clookup env_a s = Some e).
        { unfold clookup in *; rewrite nth_error_app1 in H by exact Hslt; exact H. }
        pose proof (Hsafe s e Hslt Hs_e) as Hes.
        replace (length env_a) with (S s + (length env_a - S s)) by lia.
        apply cty_uses_kinds_ren_plus; exact Hes.
      - subst s.
        assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2 in H by lia; rewrite Nat.sub_diag in H; inversion H; reflexivity).
        subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb, erase_hints_ren in H0. cbn in H0. discriminate.
      - apply cty_uses_kinds_ren_gt; lia. }
    cbn in HAB_safe. apply orb_false_iff in HAB_safe as [HA_safe HB_safe].
    destruct (IHCIdxDemand1 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl (cenv_nat_safe_cons D {| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} env_a HA_safe Hsafe))
      as [dl' [Hdl' Hbrl]].
    destruct (IHCIdxDemand2 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl (cenv_nat_safe_cons D {| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} env_a HB_safe Hsafe))
      as [dr' [Hdr' Hbrr]].
    cbn [length] in Hdl', Hdr', Hbrl, Hbrr.
    destruct (BranchVec_subst D (length env_a) z (tl dl) (tl dr) d_br (tl dl') (tl dr') (length env_b) Hnz)
      as [d_br' [Hbr' Hbrd]]; [destruct dl; cbn in *; lia | destruct dr; cbn in *; lia | exact H3 | rewrite vec_subst_tl; apply branch_rel_tl; exact Hbrl | rewrite vec_subst_tl; apply branch_rel_tl; exact Hbrr |].
    assert (Hdl'_a : CIdxDemand ({| cbinder := 0; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A;
                                    ctype_uses := vec_zero (length (subst_cidx_cenv idx z env_a ++ env_b)) |} :: subst_cidx_cenv idx z env_a ++ env_b)
                                (subst_cidx (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) l) dl').
    { rewrite (lift_cidx_add D 1 (length env_a)).
      eapply CIdxDemand_alpha_env; [| exact Hdl'].
      cbn [subst_cidx_cenv]. constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    assert (Hdr'_a : CIdxDemand ({| cbinder := 0; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) B;
                                    ctype_uses := vec_zero (length (subst_cidx_cenv idx z env_a ++ env_b)) |} :: subst_cidx_cenv idx z env_a ++ env_b)
                                (subst_cidx (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) r) dr').
    { rewrite (lift_cidx_add D 1 (length env_a)).
      eapply CIdxDemand_alpha_env; [| exact Hdr'].
      cbn [subst_cidx_cenv]. constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    assert (Hdbr_len : length d_br = S (length env_a + length env_b)).
    { rewrite (BranchVec_length D (tl dl) (tl dr) d_br); [destruct dl; cbn in *; lia | destruct dl, dr; cbn in *; lia | exact H3]. }
    destruct (lt_eq_lt_dec s (length env_a)) as [[Hlt | Heq_s] | Hgt].
    + destruct (subst_cidx_lookup_lt D idx z env_a b env_b s e Hlt Hsafe H) as [e' [Hl' [Heq _]]].
      repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandCase; [exact Hl' | rewrite Heq; exact (subst_cidx_alpha_eq D (length env_a) (lift_cidx 0 (length env_a) idx) _ _ H0)
                               | exact Hdl'_a | exact Hdr'_a | exact Hbr'].
      * rewrite (vec_subst_add D (length env_a) z _ d_br (length env_b)); [| exact Hnz | rewrite vec_single_length, length_app; cbn; lia | exact Hdbr_len].
        apply branch_rel_add; [| exact Hbrd].
        rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt; [apply branch_rel_refl | exact Hnz | exact Hlt].
    + subst s.
      assert (Heqb : e = b) by (unfold clookup in H; rewrite nth_error_app2 in H by lia; rewrite Nat.sub_diag in H; inversion H; reflexivity).
      subst e. exfalso. unfold cty_alpha_eq in H0. rewrite Hb, erase_hints_ren in H0. cbn in H0. discriminate.
    + destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b s e Hgt H) as [e' [Hl' [_ [Heq _]]]].
      assert (Hs_len : s < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact H).
      rewrite length_app in Hs_len; cbn in Hs_len. repeat (rw_nat_bool; cbv iota).
      eexists; split.
      * eapply CIdxDemandCase; [exact Hl' | rewrite Heq; exact (subst_cidx_alpha_eq D (length env_a) (lift_cidx 0 (length env_a) idx) _ _ H0)
                               | exact Hdl'_a | exact Hdr'_a | exact Hbr'].
      * rewrite (vec_subst_add D (length env_a) z _ d_br (length env_b)); [| exact Hnz | rewrite vec_single_length, length_app; cbn; lia | exact Hdbr_len].
        apply branch_rel_add; [| exact Hbrd].
        rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | exact Hnz | lia | lia].
Qed.

Lemma subst_ctype_demand : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b T d,
  cannotation b = CNat ->
  cenv_nat_safe env_a (length env_a) ->
  CIdxDemand env_b idx z ->
  CTypeDemand (env_a ++ b :: env_b) T d ->
  exists d',
    CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) T) d' /\
    branch_rel d' (vec_subst (length env_a) z d).
Proof.
  intros D idx z env_a b env_b T d Hb Hsafe Hidx H.
  assert (Hnz : length z = length env_b) by (eapply cidx_demand_length; exact Hidx).
  remember (env_a ++ b :: env_b) as env1 eqn:Henv1.
  revert env_a Henv1 Hsafe.
  induction H using CTypeDemand_ind_mut with
    (P := fun env1 T d _ => forall env_a, env1 = env_a ++ b :: env_b ->
            cenv_nat_safe env_a (length env_a) ->
            exists d', CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b)
                         (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) T) d' /\
                       branch_rel d' (vec_subst (length env_a) z d))
    (P0 := fun env1 fs df _ => forall env_a, env1 = env_a ++ b :: env_b ->
             cenv_nat_safe env_a (length env_a) ->
             exists df', CRecordFieldDemand (subst_cidx_cenv idx z env_a ++ env_b)
                           (map (fun '(fn, fg, ft) => (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft)) fs) df' /\
                         branch_rel df' (vec_subst (length env_a) z df))
    (P1 := fun env1 ls dl _ => forall env_a, env1 = env_a ++ b :: env_b ->
             cenv_nat_safe env_a (length env_a) ->
             exists dl', CIdxListDemand (subst_cidx_cenv idx z env_a ++ env_b)
                           (map (subst_cidx (length env_a) (lift_cidx 0 (length env_a) idx)) ls) dl' /\
                         branch_rel dl' (vec_subst (length env_a) z dl));
    intros env_a Henv1 Hsafe; subst env; cbn.
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero; [eexists; split; [constructor | rewrite !length_app, subst_cidx_cenv_length; apply branch_rel_refl] | exact Hnz].
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero; [eexists; split; [constructor | rewrite !length_app, subst_cidx_cenv_length; apply branch_rel_refl] | exact Hnz].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [de' [Hde' Hbre]].
    match goal with
    | Htd : CTypeDemand _ _ de, Hci : CIdxDemand _ _ dl |- _ =>
        destruct (subst_cidx_demand D idx z env_a b env_b len dl Hb Hsafe Hidx Hci) as [dl' [Hdl' Hbrl]];
        pose proof (ctype_demand_length D _ _ _ Htd) as Hlen1;
        pose proof (cidx_demand_length D _ _ _ Hci) as Hlen2;
        rewrite length_app in Hlen1, Hlen2; cbn [length] in Hlen1, Hlen2;
        exists (vec_add de' dl'); split; [constructor; assumption |];
        rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hnz | lia | lia]
    end.
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero; [eexists; split; [constructor | rewrite !length_app, subst_cidx_cenv_length; apply branch_rel_refl] | exact Hnz].
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt];
        [ destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b x e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [eapply CTypeTVar; [exact Hl' | rewrite Heq; exact (subst_cidx_alpha_eq D (length env_a - S x) (lift_cidx 0 (length env_a - S x) idx) _ _ Hc)]
          |rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt; [apply branch_rel_refl | exact Hnz | exact Hlt]]
        | subst x;
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2 in Hl by lia; rewrite Nat.sub_diag in Hl; inversion Hl; reflexivity);
          subst e; exfalso; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; discriminate
        | destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b x e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hx_len; cbn in Hx_len; repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [eapply CTypeTVar; [exact Hl' | rewrite Heq; exact Hc]
          |rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | exact Hnz | lia | lia]] ]
    end.
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [di' [Hdi' Hbr]].
    exists (vec_scale q di'); split; [constructor; assumption |].
    rewrite vec_subst_scale; apply branch_rel_scale; exact Hbr.
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec b0 (length env_a)) as [[Hlt | Heq_b] | Hgt];
        [ destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b b0 e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [eapply CTypeTUnbox; [exact Hl' | rewrite Heq; exact (subst_cidx_alpha_eq D (length env_a - S b0) (lift_cidx 0 (length env_a - S b0) idx) _ _ Hc)]
          |rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt; [apply branch_rel_refl | exact Hnz | exact Hlt]]
        | subst b0;
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2 in Hl by lia; rewrite Nat.sub_diag in Hl; inversion Hl; reflexivity);
          subst e; exfalso; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; discriminate
        | destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b b0 e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hb_len : b0 < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hb_len; cbn in Hb_len; repeat (rw_nat_bool; cbv iota);
          eexists; split;
          [eapply CTypeTUnbox; [exact Hl' | rewrite Heq; exact Hc]
          |rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt; [apply branch_rel_refl | exact Hnz | lia | lia]] ]
    end.
  - destruct (IHCTypeDemand1 env_a eq_refl Hsafe) as [a' [Ha' Hbra]].
    assert (Hdom_safe : cty_uses_kinds true false false false false false false (length env_a) dom = false).
    { match goal with
      | Htd1 : CTypeDemand _ dom a |- _ =>
          eapply ctype_demand_uses_kinds; [exact Htd1 | unfold clookup; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity |];
          unfold flags_allow; rewrite erase_hints_ren, Hb; cbn; reflexivity
      end. }
    destruct (IHCTypeDemand2 ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) eq_refl (cenv_nat_safe_cons D {| cbinder := x; cannotation := dom; ctype_uses := a |} env_a Hdom_safe Hsafe)) as [b' [Hb' Hbrb]].
    cbn [length] in Hb', Hbrb.
    assert (Hb'' : CTypeDemand ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) dom;
                                   ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b)
                               (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) cod) b').
    { rewrite (lift_cidx_add D 1 (length env_a)).
      eapply CTypeDemand_alpha_env; [| exact Hb'].
      cbn [subst_cidx_cenv]. constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    match goal with
    | H1 : CTypeDemand (env_a ++ b :: env_b) dom _,
      H2 : CTypeDemand (_ :: env_a ++ b :: env_b) cod _,
      H3 : allows _ _ |- _ =>
        rename H1 into Htd1; rename H2 into Htd2; rename H3 into Hal
    end.
    pose proof (ctype_demand_length D _ _ _ Htd1) as Hla.
    pose proof (ctype_demand_length D _ _ _ Htd2) as Hlb.
    cbn [length] in Hlb. rewrite length_app in Hla, Hlb.
    match type of Htd2 with CTypeDemand _ _ ?vb =>
      destruct vb as [| b0_hd b0_tl]; cbn in Hla, Hlb; [lia |]
    end.
    cbn in Hal.
    exists (vec_add a' (tl b')); split.
    + eapply CTypePi; [exact Ha' | exact Hb'' | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | cbn; exact Hal]].
    + rewrite (vec_subst_add D (length env_a) z _ b0_tl (length env_b)); [| exact Hnz | lia | lia].
      apply branch_rel_add; [exact Hbra |].
      change b0_tl with (tl (b0_hd :: b0_tl)). rewrite vec_subst_tl. apply branch_rel_tl; exact Hbrb.
  - destruct (IHCTypeDemand1 env_a eq_refl Hsafe) as [a' [Ha' Hbra]].
    assert (Hf_safe : cty_uses_kinds true false false false false false false (length env_a) f = false).
    { match goal with
      | Htd1 : CTypeDemand _ f a |- _ =>
          eapply ctype_demand_uses_kinds; [exact Htd1 | unfold clookup; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity |];
          unfold flags_allow; rewrite erase_hints_ren, Hb; cbn; reflexivity
      end. }
    destruct (IHCTypeDemand2 ({| cbinder := x; cannotation := f; ctype_uses := a |} :: env_a) eq_refl (cenv_nat_safe_cons D {| cbinder := x; cannotation := f; ctype_uses := a |} env_a Hf_safe Hsafe)) as [b' [Hb' Hbrb]].
    cbn [length] in Hb', Hbrb.
    assert (Hb'' : CTypeDemand ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) f;
                                   ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b)
                               (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) s) b').
    { rewrite (lift_cidx_add D 1 (length env_a)).
      eapply CTypeDemand_alpha_env; [| exact Hb'].
      cbn [subst_cidx_cenv]. constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]. }
    match goal with
    | H1 : CTypeDemand (env_a ++ b :: env_b) f _,
      H2 : CTypeDemand (_ :: env_a ++ b :: env_b) s _,
      H3 : allows _ _ |- _ =>
        rename H1 into Htd1; rename H2 into Htd2; rename H3 into Hal
    end.
    pose proof (ctype_demand_length D _ _ _ Htd1) as Hla.
    pose proof (ctype_demand_length D _ _ _ Htd2) as Hlb.
    cbn [length] in Hlb. rewrite length_app in Hla, Hlb.
    match type of Htd2 with CTypeDemand _ _ ?vb =>
      destruct vb as [| b0_hd b0_tl]; cbn in Hla, Hlb; [lia |]
    end.
    cbn in Hal.
    exists (vec_add a' (tl b')); split.
    + eapply CTypeSigma; [exact Ha' | exact Hb'' | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | cbn; exact Hal]].
    + rewrite (vec_subst_add D (length env_a) z _ b0_tl (length env_b)); [| exact Hnz | lia | lia].
      apply branch_rel_add; [exact Hbra |].
      change b0_tl with (tl (b0_hd :: b0_tl)). rewrite vec_subst_tl. apply branch_rel_tl; exact Hbrb.
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [d' [Hd' Hbr]].
    exists d'; split; [constructor; exact Hd' | exact Hbr].
  - destruct (IHCTypeDemand1 env_a eq_refl Hsafe) as [dl' [Hdl' Hbrl]].
    destruct (IHCTypeDemand2 env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]].
    match goal with
    | H1 : CTypeDemand _ _ dl, H2 : CTypeDemand _ _ dr |- _ =>
        pose proof (ctype_demand_length D _ _ _ H1) as Hlen1;
        pose proof (ctype_demand_length D _ _ _ H2) as Hlen2;
        rewrite length_app in Hlen1, Hlen2; cbn in Hlen1, Hlen2;
        exists (vec_add dl' dr'); split; [constructor; assumption |];
        rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hnz | lia | lia]
    end.
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [df' [Hdf' Hbr]].
    exists df'; split; [constructor; exact Hdf' | exact Hbr].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [di' [Hdi' Hbr]].
    exists di'; split; [constructor; exact Hdi' | exact Hbr].
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero; [eexists; split; [constructor | rewrite !length_app, subst_cidx_cenv_length; apply branch_rel_refl] | exact Hnz].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [dt' [Hdt' Hbrt]].
    destruct (IHCTypeDemand0 env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]].
    match goal with
    | Htd : CTypeDemand _ _ dt, Hrec : CRecordFieldDemand _ _ drest |- _ =>
        pose proof (ctype_demand_length D _ _ _ Htd) as Hlen1;
        pose proof (proj1 (record_field_and_idx_list_demand_length D) _ _ _ Hrec) as Hlen2;
        rewrite length_app in Hlen1, Hlen2; cbn in Hlen1, Hlen2;
        exists (vec_add dt' dr'); split; [constructor; assumption |];
        rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hnz | lia | lia]
    end.
  - rewrite !length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero; [eexists; split; [constructor | rewrite !length_app, subst_cidx_cenv_length; apply branch_rel_refl] | exact Hnz].
  - destruct (IHCTypeDemand env_a eq_refl Hsafe) as [dr' [Hdr' Hbrr]].
    match goal with
    | Hci : CIdxDemand _ _ di, Hrec : CIdxListDemand _ _ drest |- _ =>
        destruct (subst_cidx_demand D idx z env_a b env_b idx0 di Hb Hsafe Hidx Hci) as [di' [Hdi' Hbr_i]];
        pose proof (cidx_demand_length D _ _ _ Hci) as Hlen1;
        pose proof (proj2 (record_field_and_idx_list_demand_length D) _ _ _ Hrec) as Hlen2;
        rewrite length_app in Hlen1, Hlen2; cbn in Hlen1, Hlen2;
        exists (vec_add di' dr'); split; [constructor; assumption |];
        rewrite (vec_subst_add D (length env_a) z _ _ (length env_b)); [apply branch_rel_add; assumption | exact Hnz | lia | lia]
    end.
Qed.

(* Part 3B: Dependent Nat-Value Substitution Helpers, CEnv Demand Relation, *)
(* and core_value_substitution                                             *)

Lemma erase_hints_subst_cidx : forall (D : JoinDomain) k (val : cidx D) (T : cty D),
  erase_hints (subst_cidx_in_cty k val T) = subst_cidx_in_cty k val (erase_hints T).
Proof.
  intros D k val T. revert k val.
  induction T using cty_ind_nested; intros k val; cbn; try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity).
  f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
  inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
Qed.

Lemma cty_alpha_eq_subst_cidx_val : forall (D : JoinDomain) k (v1 v2 : cidx D) (T1 T2 : cty D),
  v1 = v2 -> cty_alpha_eq T1 T2 ->
  cty_alpha_eq (subst_cidx_in_cty k v1 T1) (subst_cidx_in_cty k v2 T2).
Proof.
  intros D k v1 v2 T1 T2 -> HT. unfold cty_alpha_eq in *.
  rewrite !erase_hints_subst_cidx, HT. reflexivity.
Qed.

Lemma cty_alpha_eq_unshift : forall (D : JoinDomain) k (T1 T2 : cty D),
  cty_alpha_eq T1 T2 -> cty_alpha_eq (unshift_cty k T1) (unshift_cty k T2).
Proof.
  intros D k T1 T2 H. unfold unshift_cty. apply ren_cty_alpha_eq; exact H.
Qed.

Lemma cty_alpha_eq_subst_tvar : forall (D : JoinDomain) k (U1 U2 T1 T2 : cty D),
  cty_alpha_eq U1 U2 -> cty_alpha_eq T1 T2 ->
  cty_alpha_eq (subst_tvar_in_cty k U1 T1) (subst_tvar_in_cty k U2 T2).
Proof.
  intros D k U1 U2 T1 T2 HU HT.
  assert (Heh : forall (T U : cty D) j, erase_hints (subst_tvar_in_cty j U T) = subst_tvar_in_cty j (erase_hints U) (erase_hints T)).
  { induction T using cty_ind_nested; intros U j; cbn; try reflexivity;
      try (rewrite IHT; reflexivity);
      try (rewrite IHT1, IHT2; reflexivity).
    - destruct (Nat.ltb_spec x j), (Nat.eqb_spec x j); reflexivity.
    - rewrite (IHT1 U j), (IHT2 (lift_cty 0 1 U) (S j)).
      unfold lift_cty. rewrite !erase_hints_ren. reflexivity.
    - rewrite (IHT1 U j), (IHT2 (lift_cty 0 1 U) (S j)).
      unfold lift_cty. rewrite !erase_hints_ren. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
      inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity. }
  unfold cty_alpha_eq in *. rewrite !Heh, HU, HT. reflexivity.
Qed.

Lemma cty_uses_var_alpha_eq : forall (D : JoinDomain) k (T1 T2 : cty D),
  cty_alpha_eq T1 T2 -> cty_uses_var k T1 = cty_uses_var k T2.
Proof.
  intros D k T1 T2 H.
  assert (Hu : forall (T : cty D) c, cty_uses_var c (erase_hints T) = cty_uses_var c T).
  { induction T using cty_ind_nested; intro c; cbn; try reflexivity;
      try (rewrite IHT; reflexivity); try (rewrite IHT1, IHT2; reflexivity).
    induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H0; subst; cbn in H3. rewrite H3, (IHf H4). reflexivity. }
  unfold cty_alpha_eq in H. rewrite <- (Hu T1 k), <- (Hu T2 k), H. reflexivity.
Qed.

Lemma CUniverseLevel_alpha_env : forall (D : JoinDomain) (env1 env2 : cenv D) T lvl,
  cenv_alpha_eq env1 env2 ->
  CUniverseLevel env1 T lvl ->
  CUniverseLevel env2 T lvl.
Proof.
  intros D env1 env2 T lvl Ha H. revert env2 Ha.
  induction H using CUniverseLevel_ind_mut with
    (P := fun env1 T lvl _ => forall env2, cenv_alpha_eq env1 env2 -> CUniverseLevel env2 T lvl)
    (P0 := fun env1 fs lvl _ => forall env2, cenv_alpha_eq env1 env2 -> CRecordFieldLevel env2 fs lvl);
    intros env2 Ha; try solve [constructor; auto].
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha Hl) as [e2 [Hl2 He2]];
        eapply CLevelTVar; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact Hc]]
    end.
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (cenv_alpha_eq_lookup D _ _ _ _ Ha Hl) as [e2 [Hl2 He2]];
        eapply CLevelTUnbox; [exact Hl2 | eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact He2 | exact Hc]]
    end.
  - eapply CLevelPi; [apply IHCUniverseLevel1; exact Ha |].
    apply IHCUniverseLevel2; constructor; [apply cty_alpha_eq_refl | exact Ha].
  - eapply CLevelSigma; [apply IHCUniverseLevel1; exact Ha |].
    apply IHCUniverseLevel2; constructor; [apply cty_alpha_eq_refl | exact Ha].
Qed.

Lemma Subty_alpha_env : forall (D : JoinDomain) (env1 env2 : cenv D) A B,
  cenv_alpha_eq env1 env2 ->
  Subty env1 A B ->
  Subty env2 A B.
Proof.
  intros D env1 env2 A B Ha H. revert env2 Ha.
  induction H; intros env2 Ha; try solve [constructor; auto].
  - eapply SubPi; [exact H | exact H0 | apply IHSubty1; exact Ha |].
    apply IHSubty2; constructor; [apply cty_alpha_eq_refl | exact Ha].
  - eapply SubSigma; [exact H | apply IHSubty1; exact Ha |].
    apply IHSubty2; constructor; [apply cty_alpha_eq_refl | exact Ha].
Qed.

Lemma subst_cuniverse_level : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b T lvl,
  cannotation b = CNat ->
  CUniverseLevel (env_a ++ b :: env_b) T lvl ->
  CUniverseLevel (subst_cidx_cenv idx z env_a ++ env_b)
    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) T) lvl.
Proof.
  intros D idx z env_a b env_b T lvl Hb H.
  remember (env_a ++ b :: env_b) as env1 eqn:Eenv.
  revert env_a Eenv.
  induction H using CUniverseLevel_ind_mut with
    (P := fun env1 T lvl _ => forall env_a, env1 = env_a ++ b :: env_b ->
            CUniverseLevel (subst_cidx_cenv idx z env_a ++ env_b)
              (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) T) lvl)
    (P0 := fun env1 fs lvl _ => forall env_a, env1 = env_a ++ b :: env_b ->
             CRecordFieldLevel (subst_cidx_cenv idx z env_a ++ env_b)
               (map (fun '(fn, fg, ft) => (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft)) fs) lvl);
    intros env_a Eenv; subst env; cbn; try solve [constructor; auto].
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt];
        [ destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b x e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eapply CLevelTVar; [exact Hl' | rewrite Heq; exact (subst_cidx_alpha_eq D (length env_a - S x) (lift_cidx 0 (length env_a - S x) idx) _ _ Hc)]
        | subst x; assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2 in Hl by lia; rewrite Nat.sub_diag in Hl; inversion Hl; reflexivity);
          subst e; exfalso; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; discriminate
        | destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b x e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hx_len; cbn in Hx_len; repeat (rw_nat_bool; cbv iota);
          eapply CLevelTVar; [exact Hl' | rewrite Heq; exact Hc] ]
    end.
  - match goal with
    | Hl : clookup _ _ = Some _, Hc : cty_alpha_eq _ _ |- _ =>
        destruct (lt_eq_lt_dec b0 (length env_a)) as [[Hlt | Heq_b] | Hgt];
        [ destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b b0 e Hlt Hl) as [e' [Hl' [Heq _]]];
          repeat (rw_nat_bool; cbv iota);
          eapply CLevelTUnbox; [exact Hl' | rewrite Heq; exact (subst_cidx_alpha_eq D (length env_a - S b0) (lift_cidx 0 (length env_a - S b0) idx) _ _ Hc)]
        | subst b0; assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2 in Hl by lia; rewrite Nat.sub_diag in Hl; inversion Hl; reflexivity);
          subst e; exfalso; unfold cty_alpha_eq in Hc; rewrite Hb in Hc; cbn in Hc; discriminate
        | destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b b0 e Hgt Hl) as [e' [Hl' [Heq _]]];
          assert (Hb_len : b0 < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hb_len; cbn in Hb_len; repeat (rw_nat_bool; cbv iota);
          eapply CLevelTUnbox; [exact Hl' | rewrite Heq; exact Hc] ]
    end.
  - eapply CLevelPi; [apply IHCUniverseLevel1; reflexivity |].
    match type of IHCUniverseLevel2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHCUniverseLevel2 (hd :: env_a) eq_refl);
        cbn [length subst_cidx_cenv] in IHCUniverseLevel2;
        rewrite (lift_cidx_add D 1 (length env_a));
        eapply CUniverseLevel_alpha_env; [| exact IHCUniverseLevel2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
  - eapply CLevelSigma; [apply IHCUniverseLevel1; reflexivity |].
    match type of IHCUniverseLevel2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHCUniverseLevel2 (hd :: env_a) eq_refl);
        cbn [length subst_cidx_cenv] in IHCUniverseLevel2;
        rewrite (lift_cidx_add D 1 (length env_a));
        eapply CUniverseLevel_alpha_env; [| exact IHCUniverseLevel2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
Qed.

Lemma subst_subty : forall (D : JoinDomain) (idx : cidx D) z env_a (b : cbinding D) env_b A B,
  cannotation b = CNat ->
  Subty (env_a ++ b :: env_b) A B ->
  Subty (subst_cidx_cenv idx z env_a ++ env_b)
    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A)
    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) B).
Proof.
  intros D idx z env_a b env_b A B Hb H.
  remember (env_a ++ b :: env_b) as env1 eqn:Eenv.
  revert env_a Eenv.
  induction H; intros env_a Eenv; subst env; cbn.
  - apply SubRefl. apply cty_alpha_eq_subst_cidx_val; [reflexivity | exact H].
  - apply SubBox; [exact H | apply IHSubty; reflexivity].
  - eapply SubPi; [exact H | exact H0 | apply IHSubty1; reflexivity |].
    match type of IHSubty2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHSubty2 (hd :: env_a) eq_refl);
        cbn [length subst_cidx_cenv] in IHSubty2;
        rewrite (lift_cidx_add D 1 (length env_a));
        eapply Subty_alpha_env; [| exact IHSubty2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
  - eapply SubSigma; [exact H | apply IHSubty1; reflexivity |].
    match type of IHSubty2 with
    | forall _, ?hd :: _ = _ -> _ =>
        specialize (IHSubty2 (hd :: env_a) eq_refl);
        cbn [length subst_cidx_cenv] in IHSubty2;
        rewrite (lift_cidx_add D 1 (length env_a));
        eapply Subty_alpha_env; [| exact IHSubty2];
        constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]
    end.
  - apply SubSum; [apply IHSubty1 | apply IHSubty2]; reflexivity.
  - apply SubVec; [apply subst_cidx_eqb; exact H | apply IHSubty; reflexivity].
Qed.

Lemma cty_uses_var_as_kinds : forall (D : JoinDomain) (T : cty D) c,
  cty_uses_kinds false false false false false false false c T = cty_uses_var c T.
Proof.
  intros D T.
  assert (Hci : forall (i : cidx D) c, cidx_uses_kinds false false false false false c i = cidx_uses_var c i) by
    (induction i; intro c; cbn; try reflexivity; try (rewrite IHi1, IHi2; reflexivity); apply IHi).
  induction T using cty_ind_nested; intro c; cbn; try reflexivity;
    try (apply IHT);
    try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT, Hci; reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn; [reflexivity |].
    inversion H; subst; cbn in H2. rewrite H2, (IHf H3). reflexivity.
  - induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite Hci, IH. reflexivity.
Qed.

Lemma subst_cidx_in_cty_uses_var_0 : forall (D : JoinDomain) (T : cty D) (val : cidx D) k,
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_var 0 T = false ->
  cty_uses_var 0 (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) T) = false /\
  unshift_cty 0 (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) T) = subst_cidx_in_cty k val (unshift_cty 0 T).
Proof.
  intros D T val k Huk Hu0. split.
  - eapply cty_uses_var_subst_cidx_0; [lia | exact Huk | apply lift_cidx_uses_var_0 | exact Hu0].
  - rewrite subst_cidx_unshift_cty_0; [reflexivity | exact Huk | rewrite cty_uses_var_as_kinds; exact Hu0].
Qed.

Lemma lift_cidx_comm_01 : forall {D : JoinDomain} c (v : cidx D),
  lift_cidx 0 1 (lift_cidx c 1 v) = lift_cidx (S c) 1 (lift_cidx 0 1 v).
Proof.
  intros D c v. unfold lift_cidx. rewrite !ren_cidx_comp.
  apply ren_cidx_ext. intro y. unfold ren_lift.
  destruct (Nat.ltb_spec y 0), (Nat.ltb_spec y c); try lia;
    repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
Qed.

Lemma lift_cty_comm_01 : forall {D : JoinDomain} c (T : cty D),
  lift_cty 0 1 (lift_cty c 1 T) = lift_cty (S c) 1 (lift_cty 0 1 T).
Proof.
  intros D c T. unfold lift_cty. rewrite !ren_cty_comp.
  apply ren_cty_ext. intro y. unfold ren_lift.
  destruct (Nat.ltb_spec y 0), (Nat.ltb_spec y c); try lia;
    repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
Qed.

Lemma subst_cidx_lift_1_comm_gen : forall (D : JoinDomain) (i val : cidx D) c k,
  c <= k ->
  cidx_uses_kinds true false false false false k i = false ->
  subst_cidx (S k) (lift_cidx c 1 val) (lift_cidx c 1 i) =
  lift_cidx c 1 (subst_cidx k val i).
Proof.
  intros D i. induction i; intros val c k Hck Hk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hk as [Hk1 Hk2]; rewrite (IHi1 _ _ _ Hck Hk1), (IHi2 _ _ _ Hck Hk2); reflexivity);
    try (f_equal; apply (IHi _ _ _ Hck Hk)).
  - unfold lift_cidx, ren_lift. cbn [ren_cidx]. destruct (Nat.ltb_spec x c).
    + repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; reflexivity.
    + destruct (lt_eq_lt_dec x k) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); try reflexivity;
        cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps. unfold lift_cidx, ren_lift. cbn [ren_cidx].
    destruct (Nat.ltb_spec b c); [repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; reflexivity |].
    destruct (lt_eq_lt_dec b k) as [[Hlt | ->] | Hgt]; [| exfalso; lia |];
      repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps. unfold lift_cidx, ren_lift. cbn [ren_cidx].
    destruct (Nat.ltb_spec p c); [repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; reflexivity |].
    destruct (lt_eq_lt_dec p k) as [[Hlt | ->] | Hgt]; [| exfalso; lia |];
      repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps. unfold lift_cidx, ren_lift. cbn [ren_cidx].
    destruct (Nat.ltb_spec p c); [repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; reflexivity |].
    destruct (lt_eq_lt_dec p k) as [[Hlt | ->] | Hgt]; [| exfalso; lia |];
      repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; f_equal; lia.
  - apply orb_false_iff in Hk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2]; nat_bool_hyps.
    assert (Hren : forall (u : cidx D), ren_cidx (ren_shift (ren_lift c 1)) u = lift_cidx (S c) 1 u).
    { intro u. unfold lift_cidx. apply ren_cidx_ext. intros [| y]; unfold ren_lift; cbn; rw_nat_bool; try reflexivity; destruct (Nat.ltb_spec y c); rw_nat_bool; reflexivity. }
    rewrite !Hren. rewrite lift_cidx_comm_01.
    rewrite (IHi1 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2), (IHi2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk3).
    unfold ren_lift at 1 3. destruct (Nat.ltb_spec s c);
      [repeat (rw_nat_bool; cbv iota); unfold ren_lift; rw_nat_bool; reflexivity |].
    destruct (lt_eq_lt_dec s k) as [[Hlt | ->] | Hgt]; [| exfalso; lia |];
      repeat (rw_nat_bool; cbv iota); unfold ren_lift; repeat (rw_nat_bool; cbv iota); f_equal; lia.
Qed.

Lemma subst_cidx_in_cty_lift_1_comm_gen : forall (D : JoinDomain) (T : cty D) (val : cidx D) c k,
  c <= k ->
  cty_uses_kinds true false false false false false false k T = false ->
  subst_cidx_in_cty (S k) (lift_cidx c 1 val) (lift_cty c 1 T) =
  lift_cty c 1 (subst_cidx_in_cty k val T).
Proof.
  intros D T. induction T using cty_ind_nested; intros val c k Hck Hk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hck Hk));
    try (apply orb_false_iff in Hk as [Hk1 Hk2]; rewrite (IHT1 _ _ _ Hck Hk1), (IHT2 _ _ _ Hck Hk2); reflexivity).
  - apply orb_false_iff in Hk as [Hk1 Hk2].
    repeat match goal with |- context [ren_cidx (ren_lift c 1) ?u] => change (ren_cidx (ren_lift c 1) u) with (lift_cidx c 1 u) end.
    rewrite (IHT _ _ _ Hck Hk1), (subst_cidx_lift_1_comm_gen D len val c k Hck Hk2). reflexivity.
  - nat_bool_hyps. try unfold lift_cty; unfold ren_lift. cbn [ren_cty].
    destruct (Nat.ltb_spec x c); [repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; reflexivity |].
    destruct (lt_eq_lt_dec x k) as [[Hlt | ->] | Hgt]; [| exfalso; lia |];
      repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; f_equal; lia.
  - nat_bool_hyps. try unfold lift_cty; unfold ren_lift. cbn [ren_cty].
    destruct (Nat.ltb_spec b c); [repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; reflexivity |].
    destruct (lt_eq_lt_dec b k) as [[Hlt | ->] | Hgt]; [| exfalso; lia |];
      repeat (rw_nat_bool; cbv iota); cbn; rw_nat_bool; f_equal; lia.
  - apply orb_false_iff in Hk as [Hk1 Hk2]. rewrite (IHT1 _ _ _ Hck Hk1).
    assert (Hren : forall (U : cty D), ren_cty (ren_shift (ren_lift c 1)) U = lift_cty (S c) 1 U).
    { intro U. unfold lift_cty. apply ren_cty_ext. intros [| y]; unfold ren_lift; cbn; rw_nat_bool; try reflexivity; destruct (Nat.ltb_spec y c); rw_nat_bool; reflexivity. }
    rewrite !Hren, lift_cidx_comm_01.
    rewrite (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2). reflexivity.
  - apply orb_false_iff in Hk as [Hk1 Hk2]. rewrite (IHT1 _ _ _ Hck Hk1).
    assert (Hren : forall (U : cty D), ren_cty (ren_shift (ren_lift c 1)) U = lift_cty (S c) 1 U).
    { intro U. unfold lift_cty. apply ren_cty_ext. intros [| y]; unfold ren_lift; cbn; rw_nat_bool; try reflexivity; destruct (Nat.ltb_spec y c); rw_nat_bool; reflexivity. }
    rewrite !Hren, lift_cidx_comm_01.
    rewrite (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hk2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hk as [Hk1 Hkr].
    rewrite (H2 _ _ _ Hck Hk1), (IHf H3 Hkr). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hk as [Hk1 Hk2].
    repeat match goal with |- context [ren_cidx (ren_lift c 1) ?u] => change (ren_cidx (ren_lift c 1) u) with (lift_cidx c 1 u) end.
    rewrite (subst_cidx_lift_1_comm_gen D idx val c k Hck Hk1), (IH Hk2). reflexivity.
Qed.

Lemma lift_cidx_0_0 : forall {D : JoinDomain} (i : cidx D), lift_cidx 0 0 i = i.
Proof.
  intros D i. unfold lift_cidx. transitivity (ren_cidx (fun x => x) i);
    [apply ren_cidx_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:E; nat_bool_hyps; lia | apply ren_cidx_id].
Qed.

Lemma lift_cty_0_0 : forall {D : JoinDomain} (T : cty D), lift_cty 0 0 T = T.
Proof.
  intros D T. unfold lift_cty. transitivity (ren_cty (fun x => x) T);
    [apply ren_cty_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:E; nat_bool_hyps; lia | apply ren_cty_id].
Qed.

Lemma subst_cidx_lift_cty_comm : forall (D : JoinDomain) m k (val : cidx D) (T : cty D),
  cty_uses_kinds true false false false false false false k T = false ->
  subst_cidx_in_cty (m + k) (lift_cidx 0 m val) (lift_cty 0 m T) =
  lift_cty 0 m (subst_cidx_in_cty k val T).
Proof.
  intros D m. induction m as [| m IH]; intros k val T HT.
  - cbn. rewrite !lift_cidx_0_0, !lift_cty_0_0. reflexivity.
  - change (S m + k) with (S (m + k)).
    rewrite <- lift_cidx_add with (a := 1) (b := m).
    rewrite <- lift_cty_add with (a := 1) (b := m).
    assert (HTm : cty_uses_kinds true false false false false false false (m + k) (lift_cty 0 m T) = false).
    { unfold lift_cty. eapply cty_uses_kinds_ren_gen; [| exact HT].
      intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
    rewrite (subst_cidx_in_cty_lift_1_comm_gen D (lift_cty 0 m T) (lift_cidx 0 m val) 0 (m + k) ltac:(lia) HTm).
    rewrite (IH k val T HT), lift_cty_add. reflexivity.
Qed.

(* Commutation of subst_cidx with dependent specialization functions *)

Lemma spec_pair_body_cidx_as_lift : forall (D : JoinDomain) (u : cidx D) c,
  cidx_uses_kinds true true false false true c u = false ->
  spec_pair_body_cidx c u = lift_cidx c 1 u.
Proof.
  intros D u. induction u; intros c Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHu1 _ H1), (IHu2 _ H2); reflexivity);
    try (f_equal; apply (IHu _ Hu)).
  - unfold lift_cidx, ren_lift. cbn. destruct (x <? c); [reflexivity | f_equal; lia].
  - unfold lift_cidx, ren_lift. cbn. destruct (b <? c); [reflexivity | f_equal; lia].
  - nat_bool_hyps. unfold lift_cidx, ren_lift. cbn. rewrite (proj2 (Nat.eqb_neq _ _) Hu). destruct (p <? c); [reflexivity | f_equal; lia].
  - nat_bool_hyps. unfold lift_cidx, ren_lift. cbn. rewrite (proj2 (Nat.eqb_neq _ _) Hu). destruct (p <? c); [reflexivity | f_equal; lia].
  - apply orb_false_iff in Hu as [H2 H3].
    assert (Hren : forall (w : cidx D), ren_cidx (ren_shift (ren_lift c 1)) w = lift_cidx (S c) 1 w).
    { intro w. unfold lift_cidx. apply ren_cidx_ext. intros [| y]; unfold ren_lift; cbn; rw_nat_bool; try reflexivity;
        destruct (Nat.ltb_spec y c); rw_nat_bool; reflexivity. }
    unfold lift_cidx; cbn. rewrite !Hren, (IHu1 (S c) H2), (IHu2 (S c) H3).
    f_equal; unfold ren_lift; destruct (s <? c); [reflexivity | lia].
Qed.

Lemma cidx_uses_kinds_ren_any : forall (D : JoinDomain) b1 b2 b3 b4 b5 (i : cidx D) k k' r,
  (forall x, r x = k' -> x = k) ->
  cidx_uses_kinds b1 b2 b3 b4 b5 k i = false ->
  cidx_uses_kinds b1 b2 b3 b4 b5 k' (ren_cidx r i) = false.
Proof.
  intros D b1 b2 b3 b4 b5 i.
  induction i; intros k k' r Hr Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHi1 _ _ _ Hr H1), (IHi2 _ _ _ Hr H2); reflexivity);
    try (apply IHi with (k := k); [exact Hr | exact Hu]).
  - destruct b1; [reflexivity |]. destruct (r x =? k') eqn:Heq; [apply Nat.eqb_eq, Hr in Heq; nat_bool_hyps; contradiction | reflexivity].
  - destruct b2; [reflexivity |]. destruct (r b =? k') eqn:Heq; [apply Nat.eqb_eq, Hr in Heq; nat_bool_hyps; contradiction | reflexivity].
  - destruct b3; [reflexivity |]. destruct (r p =? k') eqn:Heq; [apply Nat.eqb_eq, Hr in Heq; nat_bool_hyps; contradiction | reflexivity].
  - destruct b4; [reflexivity |]. destruct (r p =? k') eqn:Heq; [apply Nat.eqb_eq, Hr in Heq; nat_bool_hyps; contradiction | reflexivity].
  - apply orb_false_iff in Hu as [Hu12 Hu3]. apply orb_false_iff in Hu12 as [Hu1 Hu2].
    assert (Hs : (if b5 then false else r s =? k') = false).
    { destruct b5; [reflexivity |]. destruct (r s =? k') eqn:Heq; [apply Nat.eqb_eq, Hr in Heq; nat_bool_hyps; contradiction | reflexivity]. }
    assert (Hrs : forall x, ren_shift r x = S k' -> x = S k).
    { intros [| y] Hy; cbn in Hy; [discriminate | f_equal; apply Hr; lia]. }
    rewrite Hs, (IHi1 _ _ _ Hrs Hu2), (IHi2 _ _ _ Hrs Hu3). reflexivity.
Qed.

Lemma subst_cidx_spec_pair_body : forall (D : JoinDomain) (T : cty D) (val : cidx D) c k,
  S c <= k ->
  cidx_uses_kinds true true false false true c val = false ->
  cty_uses_kinds true false false false false false false k T = false ->
  subst_cidx_in_cty (S k) (lift_cidx c 1 val) (spec_pair_body_cty c T) =
  spec_pair_body_cty c (subst_cidx_in_cty k val T).
Proof.
  intros D T.
  assert (Hci : forall (i : cidx D) val c k, S c <= k ->
    cidx_uses_kinds true true false false true c val = false ->
    cidx_uses_kinds true false false false false k i = false ->
    subst_cidx (S k) (lift_cidx c 1 val) (spec_pair_body_cidx c i) =
    spec_pair_body_cidx c (subst_cidx k val i)).
  { induction i; intros val c k Hck Hv Hk; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hk as [Hk1 Hk2]; rewrite (IHi1 _ _ _ Hck Hv Hk1), (IHi2 _ _ _ Hck Hv Hk2); reflexivity);
      try (f_equal; apply (IHi _ _ _ Hck Hv Hk)).
    - destruct (Nat.ltb_spec x c), (lt_eq_lt_dec x k) as [[Hlt | ->] | Hgt];
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
        try reflexivity; try (symmetry; apply spec_pair_body_cidx_as_lift; exact Hv);
        try (exfalso; lia); unfold lift_cidx, ren_lift; rw_nat_bool; f_equal; lia.
    - nat_bool_hyps. destruct (Nat.ltb_spec b c), (lt_eq_lt_dec b k) as [[Hlt | ->] | Hgt];
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
        try (destruct (Nat.ltb_spec (_ - 1) c); [lia |]);
        try (destruct (Nat.eqb_spec (_ - 1) c); [lia |]);
        repeat (rw_nat_bool; cbv iota);
        try reflexivity; try (exfalso; lia); f_equal; lia.
    - nat_bool_hyps. destruct (Nat.eq_dec p c) as [-> | Hne];
        [repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity |].
      destruct (Nat.ltb_spec p c), (lt_eq_lt_dec p k) as [[Hlt | ->] | Hgt];
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
        try (destruct (Nat.ltb_spec (_ - 1) c); [lia |]);
        try (destruct (Nat.eqb_spec (_ - 1) c); [lia |]);
        repeat (rw_nat_bool; cbv iota);
        try reflexivity; try (exfalso; lia); f_equal; lia.
    - nat_bool_hyps. destruct (Nat.eq_dec p c) as [-> | Hne];
        [repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity |].
      destruct (Nat.ltb_spec p c), (lt_eq_lt_dec p k) as [[Hlt | ->] | Hgt];
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
        try (destruct (Nat.ltb_spec (_ - 1) c); [lia |]);
        try (destruct (Nat.eqb_spec (_ - 1) c); [lia |]);
        repeat (rw_nat_bool; cbv iota);
        try reflexivity; try (exfalso; lia); f_equal; lia.
    - apply orb_false_iff in Hk as [Hk12 Hk3]; apply orb_false_iff in Hk12 as [Hk1 Hk2]; nat_bool_hyps.
      rewrite lift_cidx_comm_01.
      assert (Hv' : cidx_uses_kinds true true false false true (S c) (lift_cidx 0 1 val) = false).
      { unfold lift_cidx. eapply cidx_uses_kinds_ren_any; [| exact Hv].
        intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
      rewrite (IHi1 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hv' Hk2),
              (IHi2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hv' Hk3).
      destruct (Nat.ltb_spec s c), (lt_eq_lt_dec s k) as [[Hlt | ->] | Hgt];
        repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
        try (destruct (Nat.ltb_spec (_ - 1) c); [lia |]);
        try (destruct (Nat.eqb_spec (_ - 1) c); [lia |]);
        repeat (rw_nat_bool; cbv iota);
        try reflexivity; try (exfalso; lia); f_equal; lia. }
  induction T using cty_ind_nested; intros val c k Hck Hv Hk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hck Hv Hk));
    try (apply orb_false_iff in Hk as [Hk1 Hk2]; rewrite (IHT1 _ _ _ Hck Hv Hk1), (IHT2 _ _ _ Hck Hv Hk2); reflexivity).
  - apply orb_false_iff in Hk as [Hk1 Hk2]. rewrite (IHT _ _ _ Hck Hv Hk1), (Hci len val c k Hck Hv Hk2). reflexivity.
  - nat_bool_hyps. destruct (Nat.ltb_spec x c), (lt_eq_lt_dec x k) as [[Hlt | ->] | Hgt];
      repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
      try (destruct (Nat.ltb_spec (_ - 1) c); [lia |]);
      try (destruct (Nat.eqb_spec (_ - 1) c); [lia |]);
      repeat (rw_nat_bool; cbv iota);
      try reflexivity; try (exfalso; lia); f_equal; lia.
  - nat_bool_hyps. destruct (Nat.ltb_spec b c), (lt_eq_lt_dec b k) as [[Hlt | ->] | Hgt];
      repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota);
      try (destruct (Nat.ltb_spec (_ - 1) c); [lia |]);
      try (destruct (Nat.eqb_spec (_ - 1) c); [lia |]);
      repeat (rw_nat_bool; cbv iota);
      try reflexivity; try (exfalso; lia); f_equal; lia.
  - apply orb_false_iff in Hk as [Hk1 Hk2].
    assert (Hv' : cidx_uses_kinds true true false false true (S c) (lift_cidx 0 1 val) = false).
    { unfold lift_cidx. eapply cidx_uses_kinds_ren_any; [| exact Hv].
      intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
    rewrite (IHT1 _ _ _ Hck Hv Hk1), lift_cidx_comm_01, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hv' Hk2). reflexivity.
  - apply orb_false_iff in Hk as [Hk1 Hk2].
    assert (Hv' : cidx_uses_kinds true true false false true (S c) (lift_cidx 0 1 val) = false).
    { unfold lift_cidx. eapply cidx_uses_kinds_ren_any; [| exact Hv].
      intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
    rewrite (IHT1 _ _ _ Hck Hv Hk1), lift_cidx_comm_01, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) Hv' Hk2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hk as [Hk1 Hkr]. rewrite (H2 _ _ _ Hck Hv Hk1), (IHf H3 Hkr). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hk as [Hk1 Hk2]. rewrite (Hci idx val c k Hck Hv Hk1), (IH Hk2). reflexivity.
Qed.

Definition r_var (c y x : nat) : nat :=
  Nat.iter c ren_shift (fun i => match i with 0 => y | S i' => i' end) x.

Lemma r_var_spec : forall c y x,
  (x < c -> r_var c y x = x) /\
  (x = c -> r_var c y x = c + y) /\
  (x > c -> r_var c y x = x - 1).
Proof.
  intros c y. induction c as [| c IH]; intros x; unfold r_var in *.
  - cbn. repeat split; [lia | intros ->; reflexivity | destruct x; lia].
  - change (Nat.iter (S c) ren_shift (fun i => match i with 0 => y | S i' => i' end) x)
      with (ren_shift (Nat.iter c ren_shift (fun i => match i with 0 => y | S i' => i' end)) x).
    destruct x as [| x']; cbn; [repeat split; lia |].
    destruct (IH x') as [H1 [H2 H3]].
    repeat split; intro H; [f_equal; apply H1; lia | rewrite H2; lia | pose proof (H3 ltac:(lia)); lia].
Qed.

Lemma r_var_lt : forall c y x, x < c -> r_var c y x = x.
Proof. intros c y x H. exact (proj1 (r_var_spec c y x) H). Qed.

Lemma r_var_eq : forall c y, r_var c y c = c + y.
Proof. intros c y. exact (proj1 (proj2 (r_var_spec c y c)) eq_refl). Qed.

Lemma r_var_gt : forall c y x, x > c -> r_var c y x = x - 1.
Proof. intros c y x H. exact (proj2 (proj2 (r_var_spec c y x)) H). Qed.

Lemma subst_cidx_r_var_comm_gen : forall (D : JoinDomain) (i val : cidx D) c y k,
  y <> k ->
  cidx_uses_kinds true false false false false (c + S k) i = false ->
  subst_cidx (c + k) (lift_cidx 0 c val) (ren_cidx (r_var c y) i) =
  ren_cidx (r_var c (if y <? k then y else y - 1)) (subst_cidx (c + S k) (lift_cidx 0 (S c) val) i).
Proof.
  intros D i. induction i; intros val c y k Hne Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHi1 _ _ _ _ Hne Hu1), (IHi2 _ _ _ _ Hne Hu2); reflexivity);
    try (f_equal; apply (IHi _ _ _ _ Hne Hu)).
  - destruct (lt_eq_lt_dec x c) as [[Hlt | ->] | Hgt].
    + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt. reflexivity.
    + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
      destruct (Nat.ltb_spec y k); rw_nat_bool; [reflexivity | f_equal; lia].
    + rewrite r_var_gt by exact Hgt.
      destruct (lt_eq_lt_dec x (c + S k)) as [[Hlt' | ->] | Hgt'].
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_gt by exact Hgt. reflexivity.
      * replace (c + S k - 1) with (c + k) by lia. repeat (rw_nat_bool; cbv iota).
        unfold lift_cidx. rewrite ren_cidx_comp. apply ren_cidx_ext.
        intro w. unfold ren_lift. destruct (w <? 0) eqn:Ew; nat_bool_hyps; [lia |].
        rewrite r_var_gt by lia. lia.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite !r_var_gt by lia. f_equal; lia.
  - nat_bool_hyps. destruct (lt_eq_lt_dec b c) as [[Hlt | ->] | Hgt].
    + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt. reflexivity.
    + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
      destruct (Nat.ltb_spec y k); rw_nat_bool; [reflexivity | f_equal; lia].
    + rewrite r_var_gt by exact Hgt.
      destruct (lt_eq_lt_dec b (c + S k)) as [[Hlt' | ->] | Hgt']; try lia.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_gt by exact Hgt. reflexivity.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite !r_var_gt by lia. f_equal; lia.
  - nat_bool_hyps. destruct (lt_eq_lt_dec p c) as [[Hlt | ->] | Hgt].
    + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt. reflexivity.
    + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
      destruct (Nat.ltb_spec y k); rw_nat_bool; [reflexivity | f_equal; lia].
    + rewrite r_var_gt by exact Hgt.
      destruct (lt_eq_lt_dec p (c + S k)) as [[Hlt' | ->] | Hgt']; try lia.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_gt by exact Hgt. reflexivity.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite !r_var_gt by lia. f_equal; lia.
  - nat_bool_hyps. destruct (lt_eq_lt_dec p c) as [[Hlt | ->] | Hgt].
    + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt. reflexivity.
    + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
      destruct (Nat.ltb_spec y k); rw_nat_bool; [reflexivity | f_equal; lia].
    + rewrite r_var_gt by exact Hgt.
      destruct (lt_eq_lt_dec p (c + S k)) as [[Hlt' | ->] | Hgt']; try lia.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_gt by exact Hgt. reflexivity.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite !r_var_gt by lia. f_equal; lia.
  - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hc1 : lift_cidx 0 1 (lift_cidx 0 c val) = lift_cidx 0 (S c) val) by (rewrite lift_cidx_add; reflexivity).
    assert (Hc2 : lift_cidx 0 1 (lift_cidx 0 (S c) val) = lift_cidx 0 (S (S c)) val) by (rewrite lift_cidx_add; reflexivity).
    change (ren_shift (r_var c y)) with (r_var (S c) y).
    change (ren_shift (r_var c (if y <? k then y else y - 1))) with (r_var (S c) (if y <? k then y else y - 1)).
    replace (S (c + S k)) with (S c + S k) in H2, H3 by lia.
    destruct (lt_eq_lt_dec s c) as [[Hlt | ->] | Hgt].
    + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt.
      f_equal; [rewrite Hc1, Hc2; apply (IHi1 val (S c) y k Hne H2) | rewrite Hc1, Hc2; apply (IHi2 val (S c) y k Hne H3)].
    + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
      f_equal; [destruct (Nat.eqb_spec (c + y) (c + k)); [lia |];
                destruct (Nat.ltb_spec (c + y) (c + k)), (Nat.ltb_spec y k);
                repeat (rw_nat_bool; cbv iota); try reflexivity; lia |
                rewrite Hc1, Hc2; apply (IHi1 val (S c) y k Hne H2) |
                rewrite Hc1, Hc2; apply (IHi2 val (S c) y k Hne H3)].
    + rewrite r_var_gt by exact Hgt.
      destruct (lt_eq_lt_dec s (c + S k)) as [[Hlt' | ->] | Hgt']; try lia.
      * repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_gt by exact Hgt.
        f_equal; [rewrite Hc1, Hc2; apply (IHi1 val (S c) y k Hne H2) | rewrite Hc1, Hc2; apply (IHi2 val (S c) y k Hne H3)].
      * destruct (Nat.ltb_spec s (c + S k)), (Nat.eqb_spec s (c + S k)); [lia | lia | lia |].
        destruct (Nat.ltb_spec (s - 1) (c + k)), (Nat.eqb_spec (s - 1) (c + k)); [lia | lia | lia |].
        repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_gt by lia.
        f_equal; [rewrite Hc1, Hc2; apply (IHi1 val (S c) y k Hne H2) | rewrite Hc1, Hc2; apply (IHi2 val (S c) y k Hne H3)].
Qed.

Lemma subst_cidx_ren_var_comm : forall (D : JoinDomain) (T : cty D) (val : cidx D) y k,
  y <> k ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  subst_cidx_in_cty k val (subst_var_in_cty 0 y T) =
  subst_var_in_cty 0 (if y <? k then y else y - 1) (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) T).
Proof.
  intros D T val y k Hne Hu.
  assert (Hgen : forall (T0 : cty D) c val0 y0 k0, y0 <> k0 ->
    cty_uses_kinds true false false false false false false (c + S k0) T0 = false ->
    subst_cidx_in_cty (c + k0) (lift_cidx 0 c val0) (ren_cty (r_var c y0) T0) =
    ren_cty (r_var c (if y0 <? k0 then y0 else y0 - 1))
            (subst_cidx_in_cty (c + S k0) (lift_cidx 0 (S c) val0) T0)).
  { induction T0 using cty_ind_nested; intros c val0 y0 k0 Hnk Htk; cbn in *; try reflexivity;
      try (f_equal; apply (IHT0 _ _ _ _ Hnk Htk));
      try (apply orb_false_iff in Htk as [H1 H2]; rewrite (IHT0_1 _ _ _ _ Hnk H1), (IHT0_2 _ _ _ _ Hnk H2); reflexivity).
    - apply orb_false_iff in Htk as [H1 H2].
      rewrite (IHT0 _ _ _ _ Hnk H1), (subst_cidx_r_var_comm_gen D len val0 c y0 k0 Hnk H2). reflexivity.
    - nat_bool_hyps. destruct (lt_eq_lt_dec x c) as [[Hlt | ->] | Hgt].
      + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt. reflexivity.
      + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
        destruct (Nat.ltb_spec y0 k0); rw_nat_bool; [reflexivity | f_equal; lia].
      + rewrite r_var_gt by exact Hgt.
        destruct (lt_eq_lt_dec x (c + S k0)) as [[Hlt' | ->] | Hgt']; try lia;
          repeat (rw_nat_bool; cbv iota); cbn; rewrite !r_var_gt by lia; f_equal; lia.
    - nat_bool_hyps. destruct (lt_eq_lt_dec b c) as [[Hlt | ->] | Hgt].
      + rewrite r_var_lt by exact Hlt. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_lt by exact Hlt. reflexivity.
      + rewrite r_var_eq. repeat (rw_nat_bool; cbv iota). cbn. rewrite r_var_eq.
        destruct (Nat.ltb_spec y0 k0); rw_nat_bool; [reflexivity | f_equal; lia].
      + rewrite r_var_gt by exact Hgt.
        destruct (lt_eq_lt_dec b (c + S k0)) as [[Hlt' | ->] | Hgt']; try lia;
          repeat (rw_nat_bool; cbv iota); cbn; rewrite !r_var_gt by lia; f_equal; lia.
    - apply orb_false_iff in Htk as [H1 H2]. rewrite (IHT0_1 _ _ _ _ Hnk H1).
      change (ren_shift (r_var c y0)) with (r_var (S c) y0).
      change (ren_shift (r_var c (if y0 <? k0 then y0 else y0 - 1))) with (r_var (S c) (if y0 <? k0 then y0 else y0 - 1)).
      rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
      replace (S (c + k0)) with (S c + k0) by lia.
      replace (S (c + S k0)) with (S c + S k0) in H2 |- * by lia.
      rewrite (IHT0_2 (S c) val0 y0 k0 Hnk H2). reflexivity.
    - apply orb_false_iff in Htk as [H1 H2]. rewrite (IHT0_1 _ _ _ _ Hnk H1).
      change (ren_shift (r_var c y0)) with (r_var (S c) y0).
      change (ren_shift (r_var c (if y0 <? k0 then y0 else y0 - 1))) with (r_var (S c) (if y0 <? k0 then y0 else y0 - 1)).
      rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
      replace (S (c + k0)) with (S c + k0) by lia.
      replace (S (c + S k0)) with (S c + S k0) in H2 |- * by lia.
      rewrite (IHT0_2 (S c) val0 y0 k0 Hnk H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Htk as [H1 Hkr]. rewrite (H2 _ _ _ _ Hnk H1), (IHf H3 Hkr). reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Htk as [H1 H2]. rewrite (subst_cidx_r_var_comm_gen D idx val0 c y0 k0 Hnk H1), (IH H2). reflexivity. }
  pose proof (Hgen T 0 val y k Hne Hu) as Hres.
  cbn in Hres. rewrite lift_cidx_0_0 in Hres. exact Hres.
Qed.

Lemma subst_cidx_lift_cidx_comm : forall (D : JoinDomain) m k (val i : cidx D),
  cidx_uses_kinds true false false false false k i = false ->
  subst_cidx (m + k) (lift_cidx 0 m val) (lift_cidx 0 m i) =
  lift_cidx 0 m (subst_cidx k val i).
Proof.
  intros D m. induction m as [| m IH]; intros k val i Hi.
  - cbn. rewrite !lift_cidx_0_0. reflexivity.
  - change (S m + k) with (S (m + k)).
    do 2 rewrite <- lift_cidx_add with (a := 1) (b := m).
    assert (Him : cidx_uses_kinds true false false false false (m + k) (lift_cidx 0 m i) = false).
    { unfold lift_cidx. eapply cidx_uses_kinds_ren_gen; [| exact Hi].
      intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
    rewrite (subst_cidx_lift_1_comm_gen D (lift_cidx 0 m i) (lift_cidx 0 m val) 0 (m + k) ltac:(lia) Him).
    rewrite (IH k val i Hi), lift_cidx_add. reflexivity.
Qed.

Lemma cidx_ren_above_rel : forall c0 (r1 r2 : nat -> nat),
  (forall y, (r1 y < c0 /\ r2 y = r1 y) \/ (r1 y > c0 /\ r2 y = r1 y - 1)) ->
  forall y, (ren_shift r1 y < S c0 /\ ren_shift r2 y = ren_shift r1 y) \/ (ren_shift r1 y > S c0 /\ ren_shift r2 y = ren_shift r1 y - 1).
Proof.
  intros c0 r1 r2 H [| y]; cbn; [left; split; lia |].
  destruct (H y) as [[Hlt Heq] | [Hgt Heq]]; [left; split; lia | right; split; lia].
Qed.

Lemma ren_lift_S_shift : forall c0 y,
  (ren_lift 0 (S c0) y < c0 /\ ren_lift 0 c0 y = ren_lift 0 (S c0) y) \/
  (ren_lift 0 (S c0) y > c0 /\ ren_lift 0 c0 y = ren_lift 0 (S c0) y - 1).
Proof.
  intros c0 y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; [lia | right; split; lia].
Qed.

Lemma subst_pair_cidx_lift_cancel : forall (D : JoinDomain) c0 (fi si v : cidx D),
  subst_pair_cidx c0 fi si (lift_cidx 0 (S c0) v) = lift_cidx 0 c0 v.
Proof.
  intros D c0 fi si v.
  assert (Hgen : forall (u fi0 si0 : cidx D) c r1 r2,
    (forall y, (r1 y < c /\ r2 y = r1 y) \/ (r1 y > c /\ r2 y = r1 y - 1)) ->
    subst_pair_cidx c fi0 si0 (ren_cidx r1 u) = ren_cidx r2 u).
  { induction u; intros fi0 si0 c r1 r2 H; cbn in *; try reflexivity;
      try (rewrite (IHu1 _ _ _ _ _ H), (IHu2 _ _ _ _ _ H); reflexivity);
      try (f_equal; apply (IHu _ _ _ _ _ H));
      try (destruct (H x) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H b) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H p) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia).
    destruct (H s) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHu1 (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0) (S c) _ _ (cidx_ren_above_rel c r1 r2 H)),
              (IHu2 (lift_cidx 0 1 fi0) (lift_cidx 0 1 si0) (S c) _ _ (cidx_ren_above_rel c r1 r2 H));
      f_equal; lia. }
  apply (Hgen v fi si c0 _ _ (ren_lift_S_shift c0)).
Qed.

Lemma subst_box_nat_cidx_lift_cancel : forall (D : JoinDomain) c0 q (bi v : cidx D),
  subst_box_nat_cidx c0 q bi (lift_cidx 0 (S c0) v) = lift_cidx 0 c0 v.
Proof.
  intros D c0 q bi v.
  assert (Hgen : forall (u bi0 : cidx D) c r1 r2,
    (forall y, (r1 y < c /\ r2 y = r1 y) \/ (r1 y > c /\ r2 y = r1 y - 1)) ->
    subst_box_nat_cidx c q bi0 (ren_cidx r1 u) = ren_cidx r2 u).
  { induction u; intros bi0 c r1 r2 H; cbn in *; try reflexivity;
      try (rewrite (IHu1 _ _ _ _ H), (IHu2 _ _ _ _ H); reflexivity);
      try (f_equal; apply (IHu _ _ _ _ H));
      try (destruct (H x) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H b) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H p) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia).
    destruct (H s) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHu1 (lift_cidx 0 1 bi0) (S c) _ _ (cidx_ren_above_rel c r1 r2 H)),
              (IHu2 (lift_cidx 0 1 bi0) (S c) _ _ (cidx_ren_above_rel c r1 r2 H));
      f_equal; lia. }
  apply (Hgen v bi c0 _ _ (ren_lift_S_shift c0)).
Qed.

Lemma subst_tvar_in_cidx_lift_cancel : forall (D : JoinDomain) c0 (v : cidx D),
  subst_tvar_in_cidx c0 (lift_cidx 0 (S c0) v) = lift_cidx 0 c0 v.
Proof.
  intros D c0 v.
  assert (Hgen : forall (u : cidx D) c r1 r2,
    (forall y, (r1 y < c /\ r2 y = r1 y) \/ (r1 y > c /\ r2 y = r1 y - 1)) ->
    subst_tvar_in_cidx c (ren_cidx r1 u) = ren_cidx r2 u).
  { induction u; intros c r1 r2 H; cbn in *; try reflexivity;
      try (rewrite (IHu1 _ _ _ H), (IHu2 _ _ _ H); reflexivity);
      try (f_equal; apply (IHu _ _ _ H));
      try (destruct (H x) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H b) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H p) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia).
    destruct (H s) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHu1 (S c) _ _ (cidx_ren_above_rel c r1 r2 H)),
              (IHu2 (S c) _ _ (cidx_ren_above_rel c r1 r2 H));
      f_equal; lia. }
  apply (Hgen v c0 _ _ (ren_lift_S_shift c0)).
Qed.

Lemma subst_sum_cidx_lift_cancel : forall (D : JoinDomain) is_left c0 (vi v : cidx D),
  subst_sum_cidx is_left c0 vi (lift_cidx 0 (S c0) v) = lift_cidx 0 c0 v.
Proof.
  intros D is_left c0 vi v.
  assert (Hgen : forall (u vi0 : cidx D) c r1 r2,
    (forall y, (r1 y < c /\ r2 y = r1 y) \/ (r1 y > c /\ r2 y = r1 y - 1)) ->
    subst_sum_cidx is_left c vi0 (ren_cidx r1 u) = ren_cidx r2 u).
  { induction u; intros vi0 c r1 r2 H; cbn in *; try reflexivity;
      try (rewrite (IHu1 _ _ _ _ H), (IHu2 _ _ _ _ H); reflexivity);
      try (f_equal; apply (IHu _ _ _ _ H));
      try (destruct (H x) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H b) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia);
      try (destruct (H p) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota); f_equal; lia).
    destruct (H s) as [[Hlt Heq] | [Hgt Heq]]; repeat (rw_nat_bool; cbv iota);
      rewrite (IHu1 (lift_cidx 0 1 vi0) (S c) _ _ (cidx_ren_above_rel c r1 r2 H)),
              (IHu2 (lift_cidx 0 1 vi0) (S c) _ _ (cidx_ren_above_rel c r1 r2 H));
      f_equal; lia. }
  apply (Hgen v vi c0 _ _ (ren_lift_S_shift c0)).
Qed.

Lemma subst_sum_cidx_ext_scase : forall (D : JoinDomain) is_left b1 b2 b3 b4 (w vi1 vi2 : cidx D) c,
  cidx_uses_kinds b1 b2 b3 b4 false c w = false ->
  subst_sum_cidx is_left c vi1 w = subst_sum_cidx is_left c vi2 w.
Proof.
  intros D is_left b1 b2 b3 b4 w. induction w; intros vi1 vi2 c Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHw1 vi1 vi2 c H1), (IHw2 vi1 vi2 c H2); reflexivity);
    try (f_equal; apply (IHw vi1 vi2 c Hu)).
  apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
  destruct (Nat.eq_dec s c) as [-> | Hne]; [exfalso; lia |].
  rw_nat_bool. rewrite (IHw1 (lift_cidx 0 1 vi1) (lift_cidx 0 1 vi2) (S c) H2), (IHw2 (lift_cidx 0 1 vi1) (lift_cidx 0 1 vi2) (S c) H3). reflexivity.
Qed.

Lemma spec_sum_branch_cidx_no_scase : forall (D : JoinDomain) is_left c0 (w : cidx D),
  cidx_uses_kinds true true true true false c0 w = false ->
  spec_sum_branch_cidx is_left c0 w = w.
Proof.
  intros D is_left c0 w. revert c0. induction w; intros c0 Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHw1 _ H1), (IHw2 _ H2); reflexivity);
    try (f_equal; apply (IHw _ Hu)).
  apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
  destruct (Nat.eq_dec s c0) as [-> | Hne]; [exfalso; lia |].
  rw_nat_bool. rewrite (IHw1 _ H2), (IHw2 _ H3). reflexivity.
Qed.

Ltac no_if t :=
  match t with
  | context [if _ then _ else _] => fail 1
  | _ => idtac
  end.

Ltac split_nat_cmp :=
  repeat (
    cbv iota in *;
    match goal with
    | |- context [?a <? ?b] => no_if a; no_if b; destruct (Nat.ltb_spec a b); [try lia | try lia]
    | |- context [?a =? ?b] => no_if a; no_if b; destruct (Nat.eqb_spec a b); [try lia | try lia]
    end
  ).

Ltac solve_pair_var v c k :=
  destruct (lt_eq_lt_dec v c) as [[Hlt | Heq] | Hgt];
  [ repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
    repeat (rw_nat_bool; cbv iota); try lia; try reflexivity; f_equal; lia
  | try (subst v || rewrite Heq in * );
    repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
    repeat (rw_nat_bool; cbv iota); try lia; try reflexivity; f_equal; lia
  | repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
    repeat (rw_nat_bool; cbv iota); try lia; try reflexivity; f_equal; lia ].

Lemma subst_cidx_subst_pair_comm_gen : forall (D : JoinDomain) (T : cty D) (fi si val : cidx D) c k,
  (c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false) ->
  cidx_uses_kinds true false false false false k fi = false ->
  cidx_uses_kinds true false false false false k si = false ->
  cty_uses_kinds true false false false false false false (c + S k) T = false ->
  subst_cidx_in_cty (c + k) (lift_cidx 0 c val) (subst_pair_cty c (lift_cidx 0 c fi) (lift_cidx 0 c si) T) =
  subst_pair_cty c (lift_cidx 0 c (subst_cidx k val fi)) (lift_cidx 0 c (subst_cidx k val si))
    (subst_cidx_in_cty (c + S k) (lift_cidx 0 (S c) val) T).
Proof.
  intros D T fi si val c k Hpos Hfi Hsi Huk.
  assert (Hci : forall (i : cidx D) fi0 si0 val0 c0 k0,
    (c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i = false) ->
    cidx_uses_kinds true false false false false k0 fi0 = false ->
    cidx_uses_kinds true false false false false k0 si0 = false ->
    cidx_uses_kinds true false false false false (c0 + S k0) i = false ->
    subst_cidx (c0 + k0) (lift_cidx 0 c0 val0) (subst_pair_cidx c0 (lift_cidx 0 c0 fi0) (lift_cidx 0 c0 si0) i) =
    subst_pair_cidx c0 (lift_cidx 0 c0 (subst_cidx k0 val0 fi0)) (lift_cidx 0 c0 (subst_cidx k0 val0 si0))
      (subst_cidx (c0 + S k0) (lift_cidx 0 (S c0) val0) i)).
  { induction i; intros fi0 si0 val0 c0 k0 Hnz Hf Hs Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [Hu1 Hu2];
           assert (Hnz1 : c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i1 = false)
             by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
           assert (Hnz2 : c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i2 = false)
             by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
           rewrite (IHi1 _ _ _ _ _ Hnz1 Hf Hs Hu1), (IHi2 _ _ _ _ _ Hnz2 Hf Hs Hu2); reflexivity);
      try (rewrite (IHi _ _ _ _ _ Hnz Hf Hs Hu); reflexivity).
    - destruct (Nat.eq_dec x (c0 + S k0)) as [-> | Hne];
        [repeat (rw_nat_bool; cbv iota); symmetry; apply subst_pair_cidx_lift_cancel |].
      destruct (Nat.eq_dec x c0) as [-> | Hnec].
      + destruct Hnz as [Hnz | H0]; [| rewrite Nat.eqb_refl in H0; discriminate].
        repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
          repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
      + solve_pair_var x c0 k0.
    - nat_bool_hyps; solve_pair_var b c0 k0.
    - nat_bool_hyps. destruct (Nat.eq_dec p c0) as [-> | Hne].
      + repeat (rw_nat_bool; cbv iota). apply subst_cidx_lift_cidx_comm; exact Hf.
      + solve_pair_var p c0 k0.
    - nat_bool_hyps. destruct (Nat.eq_dec p c0) as [-> | Hne].
      + repeat (rw_nat_bool; cbv iota). apply subst_cidx_lift_cidx_comm; exact Hs.
      + solve_pair_var p c0 k0.
    - apply orb_false_iff in Hu as [Hu12 Hu3]; apply orb_false_iff in Hu12 as [Hu1 Hu2]; nat_bool_hyps.
      rewrite !lift_cidx_add. replace (1 + c0) with (S c0) by lia. replace (1 + S c0) with (S (S c0)) by lia.
      replace (S (c0 + k0)) with (S c0 + k0) by lia.
      replace (S (c0 + S k0)) with (S c0 + S k0) in Hu2, Hu3 |- * by lia.
      rewrite (IHi1 fi0 si0 val0 (S c0) k0 ltac:(left; lia) Hf Hs Hu2),
              (IHi2 fi0 si0 val0 (S c0) k0 ltac:(left; lia) Hf Hs Hu3).
      solve_pair_var s c0 k0. }
  revert fi si val c k Hpos Hfi Hsi Huk.
  induction T using cty_ind_nested; intros fi si val c k Hpos Hfi Hsi Huk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ _ Hpos Hfi Hsi Huk));
    try (apply orb_false_iff in Huk as [H1 H2];
         assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         assert (Hp2 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T2 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         rewrite (IHT1 _ _ _ _ _ Hp1 Hfi Hsi H1), (IHT2 _ _ _ _ _ Hp2 Hfi Hsi H2); reflexivity).
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hp2 : c + k > 0 \/ cidx_uses_kinds false true true true true c len = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT _ _ _ _ _ Hp1 Hfi Hsi H1), (Hci len fi si val c k Hp2 Hfi Hsi H2). reflexivity.
  - nat_bool_hyps. solve_pair_var x c k.
  - nat_bool_hyps. solve_pair_var b c k.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 _ _ _ _ _ Hp1 Hfi Hsi H1).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 fi si val (S c) k ltac:(left; lia) Hfi Hsi H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 _ _ _ _ _ Hp1 Hfi Hsi H1).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 fi si val (S c) k ltac:(left; lia) Hfi Hsi H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c ft = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CRecord id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (H2 _ _ _ _ _ Hp1 Hfi Hsi H1).
    rewrite (IHf H3 Hpr H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cidx_uses_kinds false true true true true c idx = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CInd id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (Hci idx fi si val c k Hp1 Hfi Hsi H1), (IH Hpr H2). reflexivity.
Qed.

Lemma spec_box_body_cidx_no_unbox : forall (D : JoinDomain) q c0 (w : cidx D),
  cidx_uses_kinds true false true true true c0 w = false ->
  spec_box_body_cidx q c0 w = w.
Proof.
  intros D q c0 w. revert c0. induction w; intros c0 Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHw1 _ H1), (IHw2 _ H2); reflexivity);
    try (f_equal; apply (IHw _ Hu)).
  - nat_bool_hyps. destruct (Nat.eq_dec b c0) as [-> | Hne]; [exfalso; lia | rw_nat_bool; reflexivity].
Qed.

Lemma subst_cidx_spec_box_body : forall (D : JoinDomain) (T : cty D) q (val : cidx D) c k,
  c <= k ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  subst_cidx_in_cty (S k) (lift_cidx c 1 val) (spec_box_body_cty q c T) =
  spec_box_body_cty q c (subst_cidx_in_cty (S k) (lift_cidx c 1 val) T).
Proof.
  intros D T q val c k Hck Huk.
  assert (Hci : forall (i : cidx D) val0 c0 k0, c0 <= k0 ->
    cidx_uses_kinds true false false false false (S k0) i = false ->
    subst_cidx (S k0) (lift_cidx c0 1 val0) (spec_box_body_cidx q c0 i) =
    spec_box_body_cidx q c0 (subst_cidx (S k0) (lift_cidx c0 1 val0) i)).
  { induction i; intros val0 c0 k0 Hle Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHi1 _ _ _ Hle H1), (IHi2 _ _ _ Hle H2); reflexivity);
      try (f_equal; apply (IHi _ _ _ Hle Hu)).
    - destruct (lt_eq_lt_dec x (S k0)) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); try reflexivity.
      symmetry; apply spec_box_body_cidx_no_unbox; apply cidx_uses_kinds_lift_c.
    - nat_bool_hyps. destruct (Nat.eq_dec b c0) as [-> | Hne].
      + destruct (Nat.ltb_spec c0 (S k0)), (Nat.eqb_spec c0 (S k0)); try lia; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
      + destruct (lt_eq_lt_dec b (S k0)) as [[Hlt | ?] | Hgt]; try lia; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
    - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
      rewrite lift_cidx_comm_01.
      rewrite (IHi1 (lift_cidx 0 1 val0) (S c0) (S k0) ltac:(lia) H2),
              (IHi2 (lift_cidx 0 1 val0) (S c0) (S k0) ltac:(lia) H3). reflexivity. }
  revert val c k Hck Huk.
  induction T using cty_ind_nested; intros val c k Hck Huk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hck Huk));
    try (apply orb_false_iff in Huk as [H1 H2]; rewrite (IHT1 _ _ _ Hck H1), (IHT2 _ _ _ Hck H2); reflexivity).
  - apply orb_false_iff in Huk as [H1 H2]. rewrite (IHT _ _ _ Hck H1), (Hci len val c k Hck H2). reflexivity.
  - nat_bool_hyps. destruct (Nat.eq_dec b c) as [-> | Hne].
    + destruct (Nat.ltb_spec c (S k)), (Nat.eqb_spec c (S k)); try lia; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
    + destruct (lt_eq_lt_dec b (S k)) as [[Hlt | ?] | Hgt]; try lia; repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
  - apply orb_false_iff in Huk as [H1 H2]. rewrite (IHT1 _ _ _ Hck H1), lift_cidx_comm_01, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2]. rewrite (IHT1 _ _ _ Hck H1), lift_cidx_comm_01, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    rewrite (H2 _ _ _ Hck H1), (IHf H3 H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2]. rewrite (Hci idx val c k Hck H1), (IH H2). reflexivity.
Qed.

Lemma subst_cidx_subst_box_nat_comm_gen : forall (D : JoinDomain) (T : cty D) q (bi val : cidx D) c k,
  (c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false) ->
  cidx_uses_kinds true false false false false k bi = false ->
  cty_uses_kinds true false false false false false false (c + S k) T = false ->
  subst_cidx_in_cty (c + k) (lift_cidx 0 c val) (subst_box_nat_cty c q (lift_cidx 0 c bi) T) =
  subst_box_nat_cty c q (lift_cidx 0 c (subst_cidx k val bi))
    (subst_cidx_in_cty (c + S k) (lift_cidx 0 (S c) val) T).
Proof.
  intros D T q bi val c k Hpos Hbi Huk.
  assert (Hci : forall (i : cidx D) bi0 val0 c0 k0,
    (c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i = false) ->
    cidx_uses_kinds true false false false false k0 bi0 = false ->
    cidx_uses_kinds true false false false false (c0 + S k0) i = false ->
    subst_cidx (c0 + k0) (lift_cidx 0 c0 val0) (subst_box_nat_cidx c0 q (lift_cidx 0 c0 bi0) i) =
    subst_box_nat_cidx c0 q (lift_cidx 0 c0 (subst_cidx k0 val0 bi0))
      (subst_cidx (c0 + S k0) (lift_cidx 0 (S c0) val0) i)).
  { induction i; intros bi0 val0 c0 k0 Hnz Hb Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [H1 H2];
           assert (Hnz1 : c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i1 = false)
             by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
           assert (Hnz2 : c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i2 = false)
             by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
           rewrite (IHi1 _ _ _ _ Hnz1 Hb H1), (IHi2 _ _ _ _ Hnz2 Hb H2); reflexivity);
      try (f_equal; apply (IHi _ _ _ _ Hnz Hb Hu)).
    - destruct (Nat.eq_dec x (c0 + S k0)) as [-> | Hne];
        [repeat (rw_nat_bool; cbv iota); symmetry; apply subst_box_nat_cidx_lift_cancel |].
      destruct (Nat.eq_dec x c0) as [-> | Hnec].
      + destruct Hnz as [Hnz | H0]; [| rewrite Nat.eqb_refl in H0; discriminate].
        repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
          repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
      + solve_pair_var x c0 k0.
    - nat_bool_hyps. destruct (Nat.eq_dec b c0) as [-> | Hne]; repeat (rw_nat_bool; cbv iota);
        [cbn; f_equal; apply subst_cidx_lift_cidx_comm; exact Hb |].
      solve_pair_var b c0 k0.
    - nat_bool_hyps; solve_pair_var p c0 k0.
    - nat_bool_hyps; solve_pair_var p c0 k0.
    - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
      rewrite !lift_cidx_add. replace (1 + c0) with (S c0) by lia. replace (1 + S c0) with (S (S c0)) by lia.
      replace (S (c0 + k0)) with (S c0 + k0) by lia.
      replace (S (c0 + S k0)) with (S c0 + S k0) in H2, H3 |- * by lia.
      rewrite (IHi1 bi0 val0 (S c0) k0 ltac:(left; lia) Hb H2),
              (IHi2 bi0 val0 (S c0) k0 ltac:(left; lia) Hb H3).
      solve_pair_var s c0 k0. }
  revert bi val c k Hpos Hbi Huk.
  induction T using cty_ind_nested; intros bi val c k Hpos Hbi Huk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ Hpos Hbi Huk));
    try (apply orb_false_iff in Huk as [H1 H2];
         assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         assert (Hp2 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T2 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         rewrite (IHT1 _ _ _ _ Hp1 Hbi H1), (IHT2 _ _ _ _ Hp2 Hbi H2); reflexivity).
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hp2 : c + k > 0 \/ cidx_uses_kinds false true true true true c len = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT _ _ _ _ Hp1 Hbi H1), (Hci len bi val c k Hp2 Hbi H2). reflexivity.
  - nat_bool_hyps; solve_pair_var x c k.
  - nat_bool_hyps; solve_pair_var b c k.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 _ _ _ _ Hp1 Hbi H1).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 bi val (S c) k ltac:(left; lia) Hbi H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 _ _ _ _ Hp1 Hbi H1).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 bi val (S c) k ltac:(left; lia) Hbi H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c ft = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CRecord id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (H2 _ _ _ _ Hp1 Hbi H1).
    rewrite (IHf H3 Hpr H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cidx_uses_kinds false true true true true c idx = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CInd id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (Hci idx bi val c k Hp1 Hbi H1), (IH Hpr H2). reflexivity.
Qed.

Lemma subst_cidx_subst_box_ty_comm_gen : forall (D : JoinDomain) (T U : cty D) q (val : cidx D) c k,
  (c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false) ->
  cty_uses_kinds true false false false false false false k U = false ->
  cty_uses_kinds true false false false false false false (c + S k) T = false ->
  subst_cidx_in_cty (c + k) (lift_cidx 0 c val) (subst_box_ty_cty c q (lift_cty 0 c U) T) =
  subst_box_ty_cty c q (lift_cty 0 c (subst_cidx_in_cty k val U))
    (subst_cidx_in_cty (c + S k) (lift_cidx 0 (S c) val) T).
Proof.
  intros D T U q val c k Hpos HU Huk.
  assert (Hci : forall (i : cidx D) val0 c0 k0,
    (c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i = false) ->
    cidx_uses_kinds true false false false false (c0 + S k0) i = false ->
    subst_cidx (c0 + k0) (lift_cidx 0 c0 val0) (subst_tvar_in_cidx c0 i) =
    subst_tvar_in_cidx c0 (subst_cidx (c0 + S k0) (lift_cidx 0 (S c0) val0) i)).
  { induction i; intros val0 c0 k0 Hnz Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [H1 H2];
           assert (Hnz1 : c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i1 = false)
             by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
           assert (Hnz2 : c0 + k0 > 0 \/ cidx_uses_kinds false true true true true c0 i2 = false)
             by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
           rewrite (IHi1 _ _ _ Hnz1 H1), (IHi2 _ _ _ Hnz2 H2); reflexivity);
      try (f_equal; apply (IHi _ _ _ Hnz Hu)).
    - destruct (Nat.eq_dec x (c0 + S k0)) as [-> | Hne];
        [repeat (rw_nat_bool; cbv iota); symmetry; apply subst_tvar_in_cidx_lift_cancel |].
      destruct (Nat.eq_dec x c0) as [-> | Hnec].
      + destruct Hnz as [Hnz | H0]; [| rewrite Nat.eqb_refl in H0; discriminate].
        repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
          repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
      + solve_pair_var x c0 k0.
    - nat_bool_hyps; solve_pair_var b c0 k0.
    - nat_bool_hyps; solve_pair_var p c0 k0.
    - nat_bool_hyps; solve_pair_var p c0 k0.
    - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
      rewrite !lift_cidx_add. replace (1 + c0) with (S c0) by lia. replace (1 + S c0) with (S (S c0)) by lia.
      replace (S (c0 + k0)) with (S c0 + k0) by lia.
      replace (S (c0 + S k0)) with (S c0 + S k0) in H2, H3 |- * by lia.
      rewrite (IHi1 val0 (S c0) k0 ltac:(left; lia) H2), (IHi2 val0 (S c0) k0 ltac:(left; lia) H3).
      solve_pair_var s c0 k0. }
  revert U val c k Hpos HU Huk.
  induction T using cty_ind_nested; intros U val c k Hpos HU Huk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ _ Hpos HU Huk));
    try (apply orb_false_iff in Huk as [H1 H2];
         assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         assert (Hp2 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T2 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         rewrite (IHT1 _ _ _ _ Hp1 HU H1), (IHT2 _ _ _ _ Hp2 HU H2); reflexivity).
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hp2 : c + k > 0 \/ cidx_uses_kinds false true true true true c len = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT _ _ _ _ Hp1 HU H1), (Hci len val c k Hp2 H2). reflexivity.
  - nat_bool_hyps; solve_pair_var x c k.
  - nat_bool_hyps. destruct (Nat.eq_dec b c) as [-> | Hne]; repeat (rw_nat_bool; cbv iota);
      [cbn; f_equal; rewrite (subst_cidx_lift_cty_comm D c k val U HU); reflexivity |].
    solve_pair_var b c k.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 _ _ _ _ Hp1 HU H1).
    rewrite !lift_cidx_add, !lift_cty_add.
    replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 U val (S c) k ltac:(left; lia) HU H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 _ _ _ _ Hp1 HU H1).
    rewrite !lift_cidx_add, !lift_cty_add.
    replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 U val (S c) k ltac:(left; lia) HU H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c ft = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CRecord id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (H2 _ _ _ _ Hp1 HU H1).
    rewrite (IHf H3 Hpr H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cidx_uses_kinds false true true true true c idx = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CInd id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (Hci idx val c k Hp1 H1), (IH Hpr H2). reflexivity.
Qed.

Ltac solve_rvar_box v c k :=
  repeat (rw_nat_bool; cbv iota); cbn [ren_cidx ren_cty];
  destruct (lt_eq_lt_dec v c) as [[Hlt_v | Heq_v] | Hgt_v]; try lia;
  [ rewrite r_var_lt by exact Hlt_v;
    repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
    repeat (rw_nat_bool; cbv iota); try lia; reflexivity
  | rewrite r_var_gt by exact Hgt_v;
    repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
    repeat (rw_nat_bool; cbv iota); try lia; try reflexivity; f_equal; lia ].

Lemma subst_cidx_box_var_to_nat_gen : forall (D : JoinDomain) (T : cty D) q (val : cidx D) c k,
  cty_uses_kinds false false false true false false false c T = false ->
  cty_uses_kinds true false false false false false false (c + S k) T = false ->
  subst_cidx_in_cty (c + k) (lift_cidx 0 c val) (ren_cty (r_var c k) (spec_box_body_cty q c T)) =
  subst_box_nat_cty c q (lift_cidx 0 c val) (subst_cidx_in_cty (c + S k) (lift_cidx 0 (S c) val) T).
Proof.
  intros D T q val c k Hc Hk.
  assert (Hci : forall (i : cidx D) val0 c0 k0,
    cidx_uses_kinds false true false false false c0 i = false ->
    cidx_uses_kinds true false false false false (c0 + S k0) i = false ->
    subst_cidx (c0 + k0) (lift_cidx 0 c0 val0) (ren_cidx (r_var c0 k0) (spec_box_body_cidx q c0 i)) =
    subst_box_nat_cidx c0 q (lift_cidx 0 c0 val0) (subst_cidx (c0 + S k0) (lift_cidx 0 (S c0) val0) i)).
  { induction i; intros val0 c0 k0 H0 Hsk; cbn in *; try reflexivity;
      try (apply orb_false_iff in H0 as [H01 H02]; apply orb_false_iff in Hsk as [Hs1 Hs2];
           rewrite (IHi1 _ _ _ H01 Hs1), (IHi2 _ _ _ H02 Hs2); reflexivity);
      try (f_equal; apply (IHi _ _ _ H0 Hsk)).
    - destruct (Nat.eq_dec x c0) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in H0; discriminate |].
      destruct (Nat.eq_dec x (c0 + S k0)) as [-> | Hne'];
        [repeat (rw_nat_bool; cbv iota); rewrite r_var_gt by lia;
         replace (c0 + S k0 - 1) with (c0 + k0) by lia; repeat (rw_nat_bool; cbv iota);
         symmetry; apply subst_box_nat_cidx_lift_cancel |].
      solve_rvar_box x c0 k0.
    - destruct (Nat.eq_dec b c0) as [-> | Hne].
      + destruct (Nat.ltb_spec c0 (c0 + S k0)), (Nat.eqb_spec c0 (c0 + S k0)); try lia.
        repeat (rw_nat_bool; cbv iota); cbn [ren_cidx]; rewrite r_var_eq; cbn; repeat (rw_nat_bool; cbv iota); reflexivity.
      + apply Nat.eqb_neq in Hsk; solve_rvar_box b c0 k0.
    - destruct (Nat.eq_dec p c0) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in H0; discriminate |].
      apply Nat.eqb_neq in Hsk; solve_rvar_box p c0 k0.
    - destruct (Nat.eq_dec p c0) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in H0; discriminate |].
      apply Nat.eqb_neq in Hsk; solve_rvar_box p c0 k0.
    - apply orb_false_iff in H0 as [H012 H03]; apply orb_false_iff in H012 as [H01 H02]; nat_bool_hyps.
      apply orb_false_iff in Hsk as [Hs12 Hs3]; apply orb_false_iff in Hs12 as [Hs1 Hs2]; nat_bool_hyps.
      change (ren_shift (r_var c0 k0)) with (r_var (S c0) k0).
      rewrite !lift_cidx_add. replace (1 + c0) with (S c0) by lia. replace (1 + S c0) with (S (S c0)) by lia.
      replace (S (c0 + k0)) with (S c0 + k0) by lia.
      replace (S (c0 + S k0)) with (S c0 + S k0) in Hs2, Hs3 |- * by lia.
      rewrite (IHi1 val0 (S c0) k0 H02 Hs2), (IHi2 val0 (S c0) k0 H03 Hs3).
      solve_rvar_box s c0 k0. }
  revert val c k Hc Hk.
  induction T using cty_ind_nested; intros val c k Hc Hk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hc Hk));
    try (apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2];
         rewrite (IHT1 _ _ _ H01 Hs1), (IHT2 _ _ _ H02 Hs2); reflexivity).
  - apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2].
    rewrite (IHT _ _ _ H01 Hs1), (Hci len val c k H02 Hs2). reflexivity.
  - nat_bool_hyps; solve_rvar_box x c k.
  - nat_bool_hyps; solve_rvar_box b c k.
  - apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2].
    rewrite (IHT1 _ _ _ H01 Hs1).
    change (ren_shift (r_var c k)) with (r_var (S c) k).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in Hs2 |- * by lia.
    rewrite (IHT2 val (S c) k H02 Hs2). reflexivity.
  - apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2].
    rewrite (IHT1 _ _ _ H01 Hs1).
    change (ren_shift (r_var c k)) with (r_var (S c) k).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in Hs2 |- * by lia.
    rewrite (IHT2 val (S c) k H02 Hs2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hc as [Hc1 Hcr]; apply orb_false_iff in Hk as [Hk1 Hkr].
    rewrite (H2 _ _ _ Hc1 Hk1), (IHf H3 Hcr Hkr). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    rewrite (Hci idx val c k Hc1 Hk1), (IH Hc2 Hk2). reflexivity.
Qed.

Lemma cidx_uses_kinds_subst_sum_cidx : forall (D : JoinDomain) is_left (i vi : cidx D) c k,
  c + k > 0 ->
  cidx_uses_kinds true false false false false (c + k) vi = false ->
  cidx_uses_kinds true false false false false (c + S k) i = false ->
  cidx_uses_kinds true false false false false (c + k) (subst_sum_cidx is_left c vi i) = false.
Proof.
  intros D is_left i. induction i; intros vi c k Hpos Hvi Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHi1 _ _ _ Hpos Hvi Hu1), (IHi2 _ _ _ Hpos Hvi Hu2); reflexivity);
    try (apply (IHi _ _ _ Hpos Hvi Hu)).
  - nat_bool_hyps. destruct (Nat.ltb_spec b c), (Nat.eqb_spec b c); cbn; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (Nat.ltb_spec p c), (Nat.eqb_spec p c); cbn; apply Nat.eqb_neq; lia.
  - nat_bool_hyps. destruct (Nat.ltb_spec p c), (Nat.eqb_spec p c); cbn; apply Nat.eqb_neq; lia.
  - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    pose proof (cidx_uses_kinds_lift_shift D vi (c + k) Hvi) as Hvi'.
    destruct (Nat.eq_dec s c) as [-> | Hne].
    + rw_nat_bool.
      assert (Hbr : cidx_uses_kinds true false false false false (S (c + k))
                      (subst_sum_cidx is_left (S c) (lift_cidx 0 1 vi) (if is_left then i1 else i2)) = false).
      { replace (S (c + k)) with (S c + k) by lia.
        replace (S (c + S k)) with (S c + S k) in H2, H3 by lia.
        destruct is_left; [apply (IHi1 (lift_cidx 0 1 vi) (S c) k ltac:(lia) Hvi' H2) | apply (IHi2 (lift_cidx 0 1 vi) (S c) k ltac:(lia) Hvi' H3)]. }
      clear IHi1 IHi2.
      (* subst_cidx c0 vi' preserves non-occurrence at S (c + k) *)
      assert (Hsub : forall (u : cidx D) v' c0 m,
        c0 <= m -> m > 0 ->
        cidx_uses_kinds true false false false false m v' = false ->
        cidx_uses_kinds true false false false false (S m) u = false ->
        cidx_uses_kinds true false false false false m (subst_cidx c0 v' u) = false).
      { induction u; intros v' c0 m Hcm Hm Hv' Hu'; cbn in *; try reflexivity;
          try (apply orb_false_iff in Hu' as [Ua Ub]; rewrite (IHu1 _ _ _ Hcm Hm Hv' Ua), (IHu2 _ _ _ Hcm Hm Hv' Ub); reflexivity);
          try (apply (IHu _ _ _ Hcm Hm Hv' Hu')).
        - destruct (Nat.eqb_spec x c0); [exact Hv' | destruct (Nat.ltb_spec x c0); reflexivity].
        - nat_bool_hyps. destruct (Nat.ltb_spec b c0), (Nat.eqb_spec b c0); cbn; apply Nat.eqb_neq; lia.
        - nat_bool_hyps. destruct (Nat.ltb_spec p c0), (Nat.eqb_spec p c0); cbn; apply Nat.eqb_neq; lia.
        - nat_bool_hyps. destruct (Nat.ltb_spec p c0), (Nat.eqb_spec p c0); cbn; apply Nat.eqb_neq; lia.
        - apply orb_false_iff in Hu' as [Ua12 Ua3]; apply orb_false_iff in Ua12 as [Ua1 Ua2]; nat_bool_hyps.
          destruct (Nat.ltb_spec s c0), (Nat.eqb_spec s c0); cbn;
            try (rewrite (proj2 (Nat.eqb_neq _ m)) by lia); cbn;
            rewrite (IHu1 (lift_cidx 0 1 v') (S c0) (S m) ltac:(lia) ltac:(lia) (cidx_uses_kinds_lift_shift D v' m Hv') Ua2),
                    (IHu2 (lift_cidx 0 1 v') (S c0) (S m) ltac:(lia) ltac:(lia) (cidx_uses_kinds_lift_shift D v' m Hv') Ua3); reflexivity. }
      exact (Hsub _ _ 0 (c + k) ltac:(lia) Hpos Hvi Hbr).
    + rw_nat_bool. cbn.
      try (rewrite (proj2 (Nat.eqb_neq _ (c + k))) by (destruct (Nat.ltb_spec s c); lia)). cbn.
      replace (S (c + k)) with (S c + k) by lia.
      replace (S (c + S k)) with (S c + S k) in H2, H3 by lia.
      rewrite (IHi1 (lift_cidx 0 1 vi) (S c) k ltac:(lia) Hvi' H2), (IHi2 (lift_cidx 0 1 vi) (S c) k ltac:(lia) Hvi' H3). reflexivity.
Qed.

Lemma cidx_uses_kinds_subst_sum_cidx_all : forall (D : JoinDomain) is_left (i vi : cidx D) c k,
  c + k > 0 ->
  cidx_uses_kinds true false false false false (c + k) vi = false ->
  cidx_uses_kinds true false false false false (c + S k) i = false ->
  cidx_uses_kinds true false false false false (c + k) (subst_sum_cidx is_left c vi i) = false.
Proof.
  exact cidx_uses_kinds_subst_sum_cidx.
Qed.

Lemma subst_cidx_ren_above : forall (D : JoinDomain) (u w1 w2 : cidx D) rn k,
  (forall x, x < k -> rn x < k) ->
  (forall x, x >= k -> rn x = x) ->
  ren_cidx rn w2 = w1 ->
  cidx_uses_kinds true false false false false k u = false ->
  subst_cidx k w1 (ren_cidx rn u) = ren_cidx rn (subst_cidx k w2 u).
Proof.
  intros D u. induction u; intros w1 w2 rn k Hlt Hge Hw Hu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHu1 _ _ _ _ Hlt Hge Hw Hu1), (IHu2 _ _ _ _ Hlt Hge Hw Hu2); reflexivity);
    try (f_equal; apply (IHu _ _ _ _ Hlt Hge Hw Hu)).
  - destruct (lt_eq_lt_dec x k) as [[Hxlt | ->] | Hxgt].
    + pose proof (Hlt x Hxlt). repeat (rw_nat_bool; cbv iota); reflexivity.
    + rewrite Hge by lia. repeat (rw_nat_bool; cbv iota). symmetry; exact Hw.
    + rewrite Hge by lia. repeat (rw_nat_bool; cbv iota); cbn; rewrite Hge by lia; reflexivity.
  - nat_bool_hyps. destruct (Nat.ltb_spec b k); [pose proof (Hlt b ltac:(lia)) | rewrite Hge by lia];
      repeat (rw_nat_bool; cbv iota); cbn; try rewrite Hge by lia; reflexivity.
  - nat_bool_hyps. destruct (Nat.ltb_spec p k); [pose proof (Hlt p ltac:(lia)) | rewrite Hge by lia];
      repeat (rw_nat_bool; cbv iota); cbn; try rewrite Hge by lia; reflexivity.
  - nat_bool_hyps. destruct (Nat.ltb_spec p k); [pose proof (Hlt p ltac:(lia)) | rewrite Hge by lia];
      repeat (rw_nat_bool; cbv iota); cbn; try rewrite Hge by lia; reflexivity.
  - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hlt' : forall y, y < S k -> ren_shift rn y < S k) by (intros [| y] Hy; cbn; [lia | pose proof (Hlt y ltac:(lia)); lia]).
    assert (Hge' : forall y, y >= S k -> ren_shift rn y = y) by (intros [| y] Hy; cbn; [lia | rewrite Hge by lia; reflexivity]).
    assert (Hw' : ren_cidx (ren_shift rn) (lift_cidx 0 1 w2) = lift_cidx 0 1 w1).
    { unfold lift_cidx. rewrite <- Hw, !ren_cidx_comp.
      apply ren_cidx_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:Ey, (rn y <? 0) eqn:Ery; nat_bool_hyps; try lia; replace (y + 1) with (S y) by lia; cbn; lia. }
    rewrite (IHu1 _ _ _ _ Hlt' Hge' Hw' H2), (IHu2 _ _ _ _ Hlt' Hge' Hw' H3).
    destruct (Nat.ltb_spec s k); [pose proof (Hlt s ltac:(lia)) | rewrite Hge by lia];
      repeat (rw_nat_bool; cbv iota); cbn; try rewrite Hge by lia; reflexivity.
Qed.

Lemma cidx_uses_kinds_ren_shift_preserve : forall (D : JoinDomain) (w : cidx D) c,
  cidx_uses_kinds true false false false false c w = false ->
  cidx_uses_kinds true false false false false (S c) (lift_cidx 0 1 w) = false.
Proof.
  intros D w c H. apply cidx_uses_kinds_lift_shift; exact H.
Qed.

Lemma subst_sum_cidx_lift_m1 : forall (D : JoinDomain) is_left (w vi : cidx D) m c,
  m <= c ->
  cidx_uses_kinds false false false false false c w = false ->
  subst_sum_cidx is_left (S c) (lift_cidx m 1 vi) (lift_cidx m 1 w) =
  lift_cidx m 1 (subst_sum_cidx is_left c vi w).
Proof.
  intros D is_left w. induction w; intros vi m c Hmc Hw; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hw as [H1 H2]; rewrite (IHw1 _ _ _ Hmc H1), (IHw2 _ _ _ Hmc H2); reflexivity);
    try (f_equal; apply (IHw _ _ _ Hmc Hw)).
  - nat_bool_hyps. unfold lift_cidx, ren_lift. destruct (Nat.ltb_spec x m), (Nat.ltb_spec x c), (Nat.eqb_spec x c);
      repeat (rw_nat_bool; cbv iota); cbn; try lia; try reflexivity; f_equal; lia.
  - nat_bool_hyps. unfold lift_cidx, ren_lift. destruct (Nat.ltb_spec b m), (Nat.ltb_spec b c);
      repeat (rw_nat_bool; cbv iota); cbn; try lia; try reflexivity; f_equal; lia.
  - nat_bool_hyps. unfold lift_cidx, ren_lift. destruct (Nat.ltb_spec p m), (Nat.ltb_spec p c);
      repeat (rw_nat_bool; cbv iota); cbn; try lia; try reflexivity; f_equal; lia.
  - nat_bool_hyps. unfold lift_cidx, ren_lift. destruct (Nat.ltb_spec p m), (Nat.ltb_spec p c);
      repeat (rw_nat_bool; cbv iota); cbn; try lia; try reflexivity; f_equal; lia.
  - apply orb_false_iff in Hw as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    assert (Hren : forall (u : cidx D), ren_cidx (ren_shift (ren_lift m 1)) u = lift_cidx (S m) 1 u).
    { intro u. unfold lift_cidx. apply ren_cidx_ext. intros [| y]; unfold ren_lift; cbn; rw_nat_bool; try reflexivity; destruct (Nat.ltb_spec y m); rw_nat_bool; reflexivity. }
    assert (Hlift_case : forall s' a b,
      lift_cidx m 1 (@CIdxCase D s' a b) = CIdxCase (ren_lift m 1 s') (lift_cidx (S m) 1 a) (lift_cidx (S m) 1 b))
      by (intros; unfold lift_cidx at 1; cbn [ren_cidx]; rewrite !Hren; reflexivity).
    rewrite !Hren, lift_cidx_comm_01. rw_nat_bool. rewrite Hlift_case.
    rewrite (IHw1 (lift_cidx 0 1 vi) (S m) (S c) ltac:(lia) H2), (IHw2 (lift_cidx 0 1 vi) (S m) (S c) ltac:(lia) H3).
    destruct (Nat.ltb_spec s m), (Nat.ltb_spec s c); unfold ren_lift; repeat (rw_nat_bool; cbv iota); try lia.
    + destruct (Nat.ltb_spec s (S c)), (Nat.eqb_spec s (S c)); repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
    + destruct (Nat.ltb_spec (s + 1) (S c)), (Nat.eqb_spec (s + 1) (S c)); repeat (rw_nat_bool; cbv iota); try lia; f_equal; lia.
    + destruct (Nat.ltb_spec (s + 1) (S c)), (Nat.eqb_spec (s + 1) (S c)), (Nat.ltb_spec (s - 1) m);
        repeat (rw_nat_bool; cbv iota); try lia; f_equal; lia.
Qed.

Lemma subst_sum_cidx_lift_01 : forall (D : JoinDomain) is_left (w vi : cidx D) c,
  cidx_uses_kinds false false false false false c w = false ->
  subst_sum_cidx is_left (S c) (lift_cidx 0 1 vi) (lift_cidx 0 1 w) =
  lift_cidx 0 1 (subst_sum_cidx is_left c vi w).
Proof.
  intros D is_left w vi c Hw. apply subst_sum_cidx_lift_m1; [lia | exact Hw].
Qed.

Lemma subst_cidx_subst_sum_w : forall (D : JoinDomain) is_left (i vi w1 w2 : cidx D) c k,
  (c + k > 0 \/ cidx_uses_kinds false true true true true c i = false) ->
  cidx_uses_kinds true false false false false (c + k) vi = false ->
  cidx_uses_kinds true false false false false (c + S k) i = false ->
  cidx_uses_kinds false false false false false c w2 = false ->
  subst_sum_cidx is_left c vi w2 = w1 ->
  subst_cidx (c + k) w1 (subst_sum_cidx is_left c vi i) =
  subst_sum_cidx is_left c (subst_cidx (c + k) w1 vi) (subst_cidx (c + S k) w2 i).
Proof.
  intros D is_left i. induction i; intros vi w1 w2 c k Hnz Hvi Hu Hw2 Hw1; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hu as [Hu1 Hu2];
         assert (Hnz1 : c + k > 0 \/ cidx_uses_kinds false true true true true c i1 = false)
           by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
         assert (Hnz2 : c + k > 0 \/ cidx_uses_kinds false true true true true c i2 = false)
           by (destruct Hnz as [Hgt | H0]; [left; exact Hgt | right; apply orb_false_iff in H0 as [? ?]; assumption]);
         rewrite (IHi1 _ _ _ _ _ Hnz1 Hvi Hu1 Hw2 Hw1), (IHi2 _ _ _ _ _ Hnz2 Hvi Hu2 Hw2 Hw1); reflexivity);
    try (f_equal; apply (IHi _ _ _ _ _ Hnz Hvi Hu Hw2 Hw1)).
  - destruct (Nat.eq_dec x (c + S k)) as [-> | Hne].
    + repeat (rw_nat_bool; cbv iota). rewrite (subst_sum_cidx_ext_scase D is_left false false false false w2 (subst_cidx (c + k) w1 vi) vi c Hw2).
      symmetry; exact Hw1.
    + destruct (Nat.eq_dec x c) as [-> | Hnec].
      * destruct Hnz as [Hnz | H0]; [| rewrite Nat.eqb_refl in H0; discriminate].
        repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
          repeat (rw_nat_bool; cbv iota); try lia; reflexivity.
      * solve_pair_var x c k.
  - nat_bool_hyps; solve_pair_var b c k.
  - nat_bool_hyps; solve_pair_var p c k.
  - nat_bool_hyps; solve_pair_var p c k.
  - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
    pose proof (cidx_uses_kinds_lift_shift D vi (c + k) Hvi) as Hvi'.
    assert (Hw2' : cidx_uses_kinds false false false false false (S c) (lift_cidx 0 1 w2) = false).
    { unfold lift_cidx. eapply cidx_uses_kinds_ren_any; [| exact Hw2].
      intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
    assert (Hw1' : subst_sum_cidx is_left (S c) (lift_cidx 0 1 vi) (lift_cidx 0 1 w2) = lift_cidx 0 1 w1)
      by (rewrite subst_sum_cidx_lift_01, Hw1; [reflexivity | exact Hw2]).
    destruct (Nat.eq_dec s c) as [-> | Hne].
    + repeat (rw_nat_bool; cbv iota).
      assert (Hbr : cidx_uses_kinds true false false false false (S (c + k))
                      (subst_sum_cidx is_left (S c) (lift_cidx 0 1 vi) (if is_left then i1 else i2)) = false).
      { replace (S (c + k)) with (S c + k) by lia.
        replace (S (c + S k)) with (S c + S k) in H2, H3 by lia.
        destruct is_left; [apply (cidx_uses_kinds_subst_sum_cidx D true i1 (lift_cidx 0 1 vi) (S c) k ltac:(lia) Hvi' H2)
                           | apply (cidx_uses_kinds_subst_sum_cidx D false i2 (lift_cidx 0 1 vi) (S c) k ltac:(lia) Hvi' H3)]. }
      rewrite (subst_cidx_subst_cidx_gen D _ vi w1 0 (c + k) ltac:(lia) Hvi Hbr).
      rewrite <- (subst_cidx_lift_1_comm_gen D vi w1 0 (c + k) ltac:(lia) Hvi).
      destruct is_left.
      * replace (S (c + k)) with (S c + k) by lia. replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
        rewrite (IHi1 (lift_cidx 0 1 vi) (lift_cidx 0 1 w1) (lift_cidx 0 1 w2) (S c) k ltac:(left; lia) Hvi' H2 Hw2' Hw1'). reflexivity.
      * replace (S (c + k)) with (S c + k) by lia. replace (S (c + S k)) with (S c + S k) in H3 |- * by lia.
        rewrite (IHi2 (lift_cidx 0 1 vi) (lift_cidx 0 1 w1) (lift_cidx 0 1 w2) (S c) k ltac:(left; lia) Hvi' H3 Hw2' Hw1'). reflexivity.
    + repeat (rw_nat_bool; cbv iota). cbn.
      rewrite <- (subst_cidx_lift_1_comm_gen D vi w1 0 (c + k) ltac:(lia) Hvi).
      replace (S (c + k)) with (S c + k) by lia.
      replace (S (c + S k)) with (S c + S k) in H2, H3 |- * by lia.
      rewrite (IHi1 (lift_cidx 0 1 vi) (lift_cidx 0 1 w1) (lift_cidx 0 1 w2) (S c) k ltac:(left; lia) Hvi' H2 Hw2' Hw1'),
              (IHi2 (lift_cidx 0 1 vi) (lift_cidx 0 1 w1) (lift_cidx 0 1 w2) (S c) k ltac:(left; lia) Hvi' H3 Hw2' Hw1').
      solve_pair_var s c k.
Qed.

Lemma cidx_uses_var_as_kinds : forall (D : JoinDomain) (i : cidx D) c,
  cidx_uses_kinds false false false false false c i = cidx_uses_var c i.
Proof.
  intros D i. induction i; intro c; cbn; try reflexivity;
    try (rewrite IHi1, IHi2; reflexivity); apply IHi.
Qed.

Lemma subst_sum_cidx_no_use : forall (D : JoinDomain) is_left (u v : cidx D) m,
  cidx_uses_kinds false false false false false m u = false ->
  subst_sum_cidx is_left m v u = ren_cidx (fun x => if x <? m then x else x - 1) u.
Proof.
  intros D is_left u. induction u; intros v m Hmu; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hmu as [Ha Hb]; rewrite (IHu1 _ _ Ha), (IHu2 _ _ Hb); reflexivity);
    try (f_equal; apply (IHu _ _ Hmu)).
  - nat_bool_hyps. destruct (Nat.ltb_spec x m), (Nat.eqb_spec x m); reflexivity || lia.
  - nat_bool_hyps. destruct (Nat.ltb_spec b m), (Nat.eqb_spec b m); reflexivity || lia.
  - nat_bool_hyps. destruct (Nat.ltb_spec p m), (Nat.eqb_spec p m); reflexivity || lia.
  - nat_bool_hyps. destruct (Nat.ltb_spec p m), (Nat.eqb_spec p m); reflexivity || lia.
  - apply orb_false_iff in Hmu as [Ha12 Ha3]; apply orb_false_iff in Ha12 as [Ha1 Ha2]; nat_bool_hyps.
    destruct (Nat.eqb_spec s m); [lia |].
    rewrite (IHu1 _ _ Ha2), (IHu2 _ _ Ha3).
    assert (Hext1 : ren_cidx (fun x => if x <? S m then x else x - 1) u1 =
                    ren_cidx (ren_shift (fun x => if x <? m then x else x - 1)) u1).
    { apply ren_cidx_ext_except with (k := S m); [rewrite <- cidx_uses_var_as_kinds; exact Ha2 |].
      intros [| y] Hne; cbn; [reflexivity |].
      destruct (Nat.ltb_spec (S y) (S m)), (Nat.ltb_spec y m); lia. }
    assert (Hext2 : ren_cidx (fun x => if x <? S m then x else x - 1) u2 =
                    ren_cidx (ren_shift (fun x => if x <? m then x else x - 1)) u2).
    { apply ren_cidx_ext_except with (k := S m); [rewrite <- cidx_uses_var_as_kinds; exact Ha3 |].
      intros [| y] Hne; cbn; [reflexivity |].
      destruct (Nat.ltb_spec (S y) (S m)), (Nat.ltb_spec y m); lia. }
    destruct (Nat.ltb_spec s m); f_equal; assumption.
Qed.

Lemma subst_cidx_spec_sum_branch : forall (D : JoinDomain) (T : cty D) is_left (val : cidx D) c k,
  c <= k ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  subst_cidx_in_cty (S k) (lift_cidx c 1 val) (spec_sum_branch_cty is_left c T) =
  spec_sum_branch_cty is_left c (subst_cidx_in_cty (S k) (lift_cidx c 1 val) T).
Proof.
  intros D T is_left val c k Hck Huk.
  assert (Hsum_rot : forall (i : cidx D) (val0 : cidx D) c0 k0,
    c0 <= k0 ->
    cidx_uses_kinds true false false false false (S (S k0)) i = false ->
    subst_cidx (S k0) (lift_cidx c0 1 val0)
      (ren_cidx (sum_branch_rot c0) (subst_sum_cidx is_left (S c0) (CIdxVar 0) i)) =
    ren_cidx (sum_branch_rot c0)
      (subst_sum_cidx is_left (S c0) (CIdxVar 0)
        (subst_cidx (S (S k0)) (lift_cidx 0 1 (lift_cidx c0 1 val0)) i))).
  { intros i val0 c0 k0 Hle Hu.
    assert (Hk_eq : S c0 + (k0 - c0) = S k0) by lia.
    assert (Hci0 : cidx_uses_kinds true false false false false (S c0 + (k0 - c0)) (@CIdxVar D 0) = false) by (cbn; lia || reflexivity).
    assert (Hbr : cidx_uses_kinds true false false false false (S k0) (subst_sum_cidx is_left (S c0) (CIdxVar 0) i) = false).
    { replace (S k0) with (S c0 + (k0 - c0)) by exact Hk_eq.
      apply cidx_uses_kinds_subst_sum_cidx; [lia | exact Hci0 | replace (S c0 + S (k0 - c0)) with (S (S k0)) by lia; exact Hu]. }
    assert (Hlt : forall x, x < S k0 -> sum_branch_rot c0 x < S k0).
    { intros x Hx. unfold sum_branch_rot. destruct (Nat.eqb_spec x 0), (Nat.leb_spec x c0); lia. }
    assert (Hge : forall x, x >= S k0 -> sum_branch_rot c0 x = x).
    { intros x Hx. unfold sum_branch_rot. destruct (Nat.eqb_spec x 0), (Nat.leb_spec x c0); try lia; reflexivity. }
    assert (Hrot_w : ren_cidx (sum_branch_rot c0) (lift_cidx 0 1 val0) = lift_cidx c0 1 val0).
    { unfold lift_cidx. rewrite ren_cidx_comp. apply ren_cidx_ext. intro y.
      unfold ren_lift, sum_branch_rot. destruct (y <? 0) eqn:Ey; nat_bool_hyps; [lia |].
      destruct (Nat.ltb_spec y c0), (Nat.eqb_spec (y + 1) 0), (Nat.leb_spec (y + 1) c0);
        repeat (rw_nat_bool; cbv iota); lia. }
    rewrite (subst_cidx_ren_above D _ (lift_cidx c0 1 val0) (lift_cidx 0 1 val0) (sum_branch_rot c0) (S k0) Hlt Hge Hrot_w Hbr).
    f_equal.
    assert (Hw2_no : cidx_uses_kinds false false false false false (S c0) (lift_cidx 0 1 (lift_cidx c0 1 val0)) = false).
    { unfold lift_cidx. eapply cidx_uses_kinds_ren_any; [| apply cidx_uses_kinds_lift_c].
      intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; [lia |].
      destruct (Nat.ltb_spec y c0); lia. }
    assert (Hw2_sub : subst_sum_cidx is_left (S c0) (CIdxVar 0) (lift_cidx 0 1 (lift_cidx c0 1 val0)) = lift_cidx 0 1 val0).
    { rewrite (subst_sum_cidx_no_use D is_left _ (CIdxVar 0) (S c0) Hw2_no). unfold lift_cidx. rewrite !ren_cidx_comp.
      apply ren_cidx_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; [lia |].
      destruct (Nat.ltb_spec y c0), (Nat.ltb_spec (y + 1) (S c0)), (Nat.ltb_spec (y + 1 + 1) (S c0));
        repeat (rw_nat_bool; cbv iota); try lia; f_equal; lia. }
    replace (S k0) with (S c0 + (k0 - c0)) by exact Hk_eq.
    replace (S (S k0)) with (S c0 + S (k0 - c0)) by lia.
    rewrite (subst_cidx_subst_sum_w D is_left i (CIdxVar 0) (lift_cidx 0 1 val0) (lift_cidx 0 1 (lift_cidx c0 1 val0)) (S c0) (k0 - c0)
               ltac:(left; lia) Hci0 ltac:(replace (S c0 + S (k0 - c0)) with (S (S k0)) by lia; exact Hu) Hw2_no Hw2_sub).
    replace (subst_cidx (S c0 + (k0 - c0)) (lift_cidx 0 1 val0) (CIdxVar 0)) with (@CIdxVar D 0) by (cbn; rw_nat_bool; reflexivity).
    replace (S c0 + S (k0 - c0)) with (S (S c0 + (k0 - c0))) by lia.
    reflexivity. }
  assert (Hci : forall (i : cidx D) val0 c0 k0, c0 <= k0 ->
    cidx_uses_kinds true false false false false (S k0) i = false ->
    subst_cidx (S k0) (lift_cidx c0 1 val0) (spec_sum_branch_cidx is_left c0 i) =
    spec_sum_branch_cidx is_left c0 (subst_cidx (S k0) (lift_cidx c0 1 val0) i)).
  { induction i; intros val0 c0 k0 Hle Hu; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hu as [H1 H2]; rewrite (IHi1 _ _ _ Hle H1), (IHi2 _ _ _ Hle H2); reflexivity);
      try (f_equal; apply (IHi _ _ _ Hle Hu)).
    - destruct (Nat.eq_dec x (S k0)) as [-> | Hne];
        [repeat (rw_nat_bool; cbv iota); symmetry; apply spec_sum_branch_cidx_no_scase;
         apply cidx_uses_kinds_lift_c
        | destruct (Nat.ltb_spec x (S k0)); repeat (rw_nat_bool; cbv iota); cbn; reflexivity].
    - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
      destruct (Nat.eq_dec s c0) as [-> | Hne].
      + repeat (rw_nat_bool; cbv iota).
        destruct is_left; [apply (Hsum_rot i1 val0 c0 k0 Hle H2) | apply (Hsum_rot i2 val0 c0 k0 Hle H3)].
      + repeat (rw_nat_bool; cbv iota).
        destruct (lt_eq_lt_dec s (S k0)) as [[Hlt | ?] | Hgt]; try lia;
          repeat (rw_nat_bool; cbv iota); cbn;
          destruct (Nat.ltb_spec s (S k0)), (Nat.eqb_spec s (S k0)); try lia;
          repeat (rw_nat_bool; cbv iota); cbn;
          try (destruct (Nat.eqb_spec (s - 1) c0); [lia |]);
          repeat (rw_nat_bool; cbv iota); cbn;
          rewrite lift_cidx_comm_01, (IHi1 (lift_cidx 0 1 val0) (S c0) (S k0) ltac:(lia) H2),
                  (IHi2 (lift_cidx 0 1 val0) (S c0) (S k0) ltac:(lia) H3); reflexivity. }
  revert val c k Hck Huk.
  induction T using cty_ind_nested; intros val c k Hck Huk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hck Huk));
    try (apply orb_false_iff in Huk as [H1 H2]; rewrite (IHT1 _ _ _ Hck H1), (IHT2 _ _ _ Hck H2); reflexivity).
  - apply orb_false_iff in Huk as [H1 H2]. rewrite (IHT _ _ _ Hck H1), (Hci len val c k Hck H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2]. rewrite (IHT1 _ _ _ Hck H1), lift_cidx_comm_01, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2]. rewrite (IHT1 _ _ _ Hck H1), lift_cidx_comm_01, (IHT2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    rewrite (H2 _ _ _ Hck H1), (IHf H3 H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2]. rewrite (Hci idx val c k Hck H1), (IH H2). reflexivity.
Qed.

Lemma subst_cidx_subst_sum_comm_gen : forall (D : JoinDomain) (T : cty D) is_left (vi val : cidx D) c k,
  (c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false) ->
  cidx_uses_kinds true false false false false k vi = false ->
  cty_uses_kinds true false false false false false false (c + S k) T = false ->
  subst_cidx_in_cty (c + k) (lift_cidx 0 c val) (subst_sum_cty is_left c (lift_cidx 0 c vi) T) =
  subst_sum_cty is_left c (lift_cidx 0 c (subst_cidx k val vi))
    (subst_cidx_in_cty (c + S k) (lift_cidx 0 (S c) val) T).
Proof.
  intros D T is_left vi val c k Hpos Hvi Huk.
  assert (Hvi_c : forall c0, cidx_uses_kinds true false false false false (c0 + k) (lift_cidx 0 c0 vi) = false).
  { induction c0 as [| c0 IH]; cbn; [rewrite lift_cidx_0_0; exact Hvi |].
    replace (S c0 + k) with (S (c0 + k)) by lia.
    rewrite <- lift_cidx_add with (a := 1) (b := c0). apply cidx_uses_kinds_lift_shift; exact IH. }
  assert (Hval_no : forall c0, cidx_uses_kinds false false false false false c0 (lift_cidx 0 (S c0) val) = false).
  { assert (Hgen : forall (u : cidx D) r c0, (forall y, r y <> c0) ->
      cidx_uses_kinds false false false false false c0 (ren_cidx r u) = false).
    { induction u; intros r c0 Hr; cbn; try reflexivity;
        try (rewrite (IHu1 _ _ Hr), (IHu2 _ _ Hr); reflexivity);
        try (apply (IHu _ _ Hr));
        try (apply Nat.eqb_neq; apply Hr).
      - assert (Hs : (r s =? c0) = false) by (apply Nat.eqb_neq, Hr).
        assert (Hrs : forall y, ren_shift r y <> S c0)
          by (intros [| y]; cbn; [discriminate | pose proof (Hr y); lia]).
        rewrite Hs, (IHu1 _ _ Hrs), (IHu2 _ _ Hrs). reflexivity. }
    intro c0; unfold lift_cidx; apply Hgen; intro y; unfold ren_lift; destruct (y <? 0) eqn:Ey; nat_bool_hyps; lia. }
  assert (Hci : forall (i : cidx D) c0,
    (c0 + k > 0 \/ cidx_uses_kinds false true true true true c0 i = false) ->
    cidx_uses_kinds true false false false false (c0 + S k) i = false ->
    subst_cidx (c0 + k) (lift_cidx 0 c0 val) (subst_sum_cidx is_left c0 (lift_cidx 0 c0 vi) i) =
    subst_sum_cidx is_left c0 (lift_cidx 0 c0 (subst_cidx k val vi))
      (subst_cidx (c0 + S k) (lift_cidx 0 (S c0) val) i)).
  { intros i c0 Hnz Hu.
    rewrite <- (subst_cidx_lift_cidx_comm D c0 k val vi Hvi).
    rewrite (subst_cidx_subst_sum_w D is_left i (lift_cidx 0 c0 vi) (lift_cidx 0 c0 val) (lift_cidx 0 (S c0) val) c0 k Hnz (Hvi_c c0) Hu (Hval_no c0)).
    - reflexivity.
    - rewrite (subst_sum_cidx_no_use D is_left _ (lift_cidx 0 c0 vi) c0 (Hval_no c0)). unfold lift_cidx. rewrite ren_cidx_comp.
      apply ren_cidx_ext. intro y. unfold ren_lift. destruct (y <? 0) eqn:Ey; nat_bool_hyps; [lia |].
      destruct (Nat.ltb_spec (y + S c0) c0); repeat (rw_nat_bool; cbv iota); try lia; f_equal; lia. }
  revert c Hpos Huk.
  induction T using cty_ind_nested; intros c Hpos Huk; cbn in *; try reflexivity;
    try (f_equal; apply (IHT c Hpos Huk));
    try (apply orb_false_iff in Huk as [H1 H2];
         assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         assert (Hp2 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T2 = false)
           by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]);
         rewrite (IHT1 c Hp1 H1), (IHT2 c Hp2 H2); reflexivity).
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hp2 : c + k > 0 \/ cidx_uses_kinds false true true true true c len = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT c Hp1 H1), (Hci len c Hp2 H2). reflexivity.
  - nat_bool_hyps; solve_pair_var x c k.
  - nat_bool_hyps; solve_pair_var b c k.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 c Hp1 H1).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 (S c) ltac:(left; lia) H2). reflexivity.
  - apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c T1 = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (IHT1 c Hp1 H1).
    rewrite !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in H2 |- * by lia.
    rewrite (IHT2 (S c) ltac:(left; lia) H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Huk as [H1 H3_k].
    assert (Hp1 : c + k > 0 \/ cty_uses_kinds false true true true true true true c ft = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CRecord id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (H2 c Hp1 H1).
    rewrite (IHf H3 Hpr H3_k). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huk as [H1 H2].
    assert (Hp1 : c + k > 0 \/ cidx_uses_kinds false true true true true c idx = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    assert (Hpr : c + k > 0 \/ cty_uses_kinds false true true true true true true c (CInd id rest) = false)
      by (destruct Hpos as [? | H0]; [left; lia | right; cbn in H0; apply orb_false_iff in H0 as [? ?]; assumption]).
    rewrite (Hci idx c Hp1 H1), (IH Hpr H2). reflexivity.
Qed.

Lemma subst_cidx_sum_var_to_nat_gen : forall (D : JoinDomain) (T : cty D) is_left (val : cidx D) c k,
  cty_uses_kinds false false false false false false true c T = false ->
  cty_uses_kinds true false false false false false false (c + S k) T = false ->
  subst_cidx_in_cty (c + k) (lift_cidx 0 c val) (subst_sum_cty is_left c (CIdxVar (c + k)) T) =
  subst_sum_cty is_left c (lift_cidx 0 c val) (subst_cidx_in_cty (c + S k) (lift_cidx 0 (S c) val) T).
Proof.
  intros D T is_left val c k Hc Hk.
  Ltac solve_h0k_var v d m j :=
    repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn; split_nat_cmp;
      repeat (rw_nat_bool; cbv iota);
      try lia; try reflexivity; f_equal; lia.
  assert (H0k : forall (u : cidx D) v0 d m j,
    d <= m ->
    subst_cidx (m + j) (lift_cidx 0 m v0) (subst_cidx d (CIdxVar (m + j)) u) =
    subst_cidx d (lift_cidx 0 m v0) (subst_cidx (m + S j) (lift_cidx 0 (S m) v0) u)).
  { induction u; intros v0 d m j Hdm; cbn [subst_cidx] in *; try reflexivity;
      try (rewrite (IHu1 v0 d m j Hdm), (IHu2 v0 d m j Hdm); reflexivity);
      try (f_equal; apply (IHu v0 d m j Hdm)).
    - destruct (Nat.eq_dec x (m + S j)) as [-> | Hne].
      + repeat (rw_nat_bool; cbv iota). replace (m + S j - 1) with (m + j) by lia.
        cbn. rw_nat_bool.
        unfold lift_cidx. rewrite (subst_cidx_ren_skip_gen D v0 _ d (ren_lift 0 (S m)) (ren_lift 0 m));
          [reflexivity | intro y; unfold ren_lift; rw_nat_bool; right; lia].
      + destruct (Nat.eq_dec x d) as [-> | Hxd].
        * repeat (rw_nat_bool; cbv iota). cbn. rw_nat_bool. reflexivity.
        * destruct (Nat.ltb_spec x d).
          { repeat (rw_nat_bool; cbv iota); cbn; repeat (rw_nat_bool; cbv iota); try lia; reflexivity. }
          { destruct (Nat.ltb_spec x (m + S j)); repeat (rw_nat_bool; cbv iota); split_nat_cmp; cbn;
              split_nat_cmp;
              repeat (rw_nat_bool; cbv iota); try lia; f_equal; lia. }
    - solve_h0k_var b d m j.
    - solve_h0k_var p d m j.
    - solve_h0k_var p d m j.
    - assert (Hlv : lift_cidx 0 1 (CIdxVar (m + j)) = @CIdxVar D (S m + j))
        by (unfold lift_cidx; cbn; unfold ren_lift; rw_nat_bool; f_equal; lia).
      rewrite Hlv.
      rewrite !lift_cidx_add. replace (1 + m) with (S m) by lia. replace (1 + S m) with (S (S m)) by lia.
      replace (S (m + S j)) with (S m + S j) by lia.
      replace (S (m + j)) with (S m + j) by lia.
      rewrite (IHu1 v0 (S d) (S m) j ltac:(lia)), (IHu2 v0 (S d) (S m) j ltac:(lia)).
      solve_h0k_var s d m j. }
  assert (Hci : forall (i : cidx D) v0 c0 k0,
    cidx_uses_kinds false false false false true c0 i = false ->
    cidx_uses_kinds true false false false false (c0 + S k0) i = false ->
    subst_cidx (c0 + k0) (lift_cidx 0 c0 v0) (subst_sum_cidx is_left c0 (CIdxVar (c0 + k0)) i) =
    subst_sum_cidx is_left c0 (lift_cidx 0 c0 v0) (subst_cidx (c0 + S k0) (lift_cidx 0 (S c0) v0) i)).
  { induction i; intros v0 c0 k0 Hc0 Hsk0; cbn [subst_cidx subst_sum_cidx cidx_uses_kinds orb] in *; try reflexivity;
      try (apply orb_false_iff in Hc0 as [H01 H02]; apply orb_false_iff in Hsk0 as [Hs1 Hs2];
           rewrite (IHi1 _ _ _ H01 Hs1), (IHi2 _ _ _ H02 Hs2); reflexivity);
      try (f_equal; apply (IHi _ _ _ Hc0 Hsk0)).
    - destruct (Nat.eq_dec x c0) as [-> | Hne]; [exfalso; rewrite Nat.eqb_refl in Hc0; discriminate |].
      destruct (Nat.eq_dec x (c0 + S k0)) as [-> | Hne'];
        [repeat (rw_nat_bool; cbv iota); symmetry; apply subst_sum_cidx_lift_cancel |].
      solve_pair_var x c0 k0.
    - nat_bool_hyps. destruct (Nat.eq_dec b c0) as [-> | Hne]; [exfalso; lia |].
      solve_pair_var b c0 k0.
    - nat_bool_hyps. destruct (Nat.eq_dec p c0) as [-> | Hne]; [exfalso; lia |].
      solve_pair_var p c0 k0.
    - nat_bool_hyps. destruct (Nat.eq_dec p c0) as [-> | Hne]; [exfalso; lia |].
      solve_pair_var p c0 k0.
    - apply orb_false_iff in Hc0 as [H02 H03].
      apply orb_false_iff in Hsk0 as [Hs12 Hs3]; apply orb_false_iff in Hs12 as [Hs1 Hs2]; nat_bool_hyps.
      rewrite !lift_cidx_add. replace (1 + c0) with (S c0) by lia. replace (1 + S c0) with (S (S c0)) by lia.
      replace (S (c0 + S k0)) with (S c0 + S k0) in Hs2, Hs3 by lia.
      assert (Hlv : lift_cidx 0 1 (CIdxVar (c0 + k0)) = @CIdxVar D (S c0 + k0))
        by (unfold lift_cidx; cbn; unfold ren_lift; rw_nat_bool; f_equal; lia).
      destruct (Nat.eq_dec s c0) as [-> | Hne].
      + repeat (rw_nat_bool; cbv iota). cbn [subst_cidx subst_sum_cidx].
        rewrite Hlv.
        rewrite (H0k _ v0 0 c0 k0 ltac:(lia)).
        replace (c0 + S k0) with (S c0 + k0) by lia.
        replace (S (c0 + S k0)) with (S c0 + S k0) in Hs2, Hs3 |- * by lia.
        replace (S (S c0 + k0)) with (S c0 + S k0) by lia.
        destruct is_left;
          [rewrite (IHi1 v0 (S c0) k0 H02 Hs2); reflexivity
          | rewrite (IHi2 v0 (S c0) k0 H03 Hs3); reflexivity].
      + repeat (rw_nat_bool; cbv iota).
        try (rewrite (proj2 (Nat.eqb_neq _ c0)) by (destruct (Nat.ltb_spec s (c0 + S k0)); repeat (rw_nat_bool; cbv iota); lia)).
        cbn [subst_cidx subst_sum_cidx].
        rewrite Hlv. rewrite ?lift_cidx_add.
        try replace (1 + c0) with (S c0) by lia.
        try replace (1 + S c0) with (S (S c0)) by lia.
        replace (S (c0 + k0)) with (S c0 + k0) by lia.
        replace (S (c0 + S k0)) with (S c0 + S k0) in Hs2, Hs3 |- * by lia.
        try replace (S (S c0 + k0)) with (S c0 + S k0) by lia.
        rewrite (IHi1 v0 (S c0) k0 H02 Hs2), (IHi2 v0 (S c0) k0 H03 Hs3).
        destruct (Nat.ltb_spec s c0), (Nat.ltb_spec s (c0 + S k0));
          repeat (rw_nat_bool; cbv iota); try lia;
          destruct (Nat.ltb_spec (s - 1) (c0 + k0)), (Nat.eqb_spec (s - 1) (c0 + k0)), (Nat.ltb_spec (s - 1) c0);
          repeat (rw_nat_bool; cbv iota); try lia; f_equal; lia. }
  revert val c k Hc Hk.
  induction T using cty_ind_nested; intros val c k Hc Hk; cbn [subst_cidx_in_cty subst_sum_cty cty_uses_kinds] in *; try reflexivity;
    try (f_equal; apply (IHT _ _ _ Hc Hk));
    try (apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2];
         rewrite (IHT1 _ _ _ H01 Hs1), (IHT2 _ _ _ H02 Hs2); reflexivity).
  - apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2].
    rewrite (IHT _ _ _ H01 Hs1), (Hci len val c k H02 Hs2). reflexivity.
  - nat_bool_hyps; destruct (Nat.eq_dec x c) as [-> | Hne]; [exfalso; lia | solve_pair_var x c k].
  - nat_bool_hyps; destruct (Nat.eq_dec b c) as [-> | Hne]; [exfalso; lia | solve_pair_var b c k].
  - apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2].
    assert (Hlv : lift_cidx 0 1 (CIdxVar (c + k)) = @CIdxVar D (S c + k))
      by (unfold lift_cidx; cbn; unfold ren_lift; rw_nat_bool; f_equal; lia).
    rewrite (IHT1 _ _ _ H01 Hs1), Hlv, !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in Hs2 |- * by lia. rewrite (IHT2 val (S c) k H02 Hs2). reflexivity.
  - apply orb_false_iff in Hc as [H01 H02]; apply orb_false_iff in Hk as [Hs1 Hs2].
    assert (Hlv : lift_cidx 0 1 (CIdxVar (c + k)) = @CIdxVar D (S c + k))
      by (unfold lift_cidx; cbn; unfold ren_lift; rw_nat_bool; f_equal; lia).
    rewrite (IHT1 _ _ _ H01 Hs1), Hlv, !lift_cidx_add. replace (1 + c) with (S c) by lia. replace (1 + S c) with (S (S c)) by lia.
    replace (S (c + k)) with (S c + k) by lia.
    replace (S (c + S k)) with (S c + S k) in Hs2 |- * by lia. rewrite (IHT2 val (S c) k H02 Hs2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in Hc as [Hc1 Hcr]; apply orb_false_iff in Hk as [Hk1 Hkr].
    rewrite (H2 _ _ _ Hc1 Hk1), (IHf H3 Hcr Hkr). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Hc as [Hc1 Hc2]; apply orb_false_iff in Hk as [Hk1 Hk2].
    rewrite (Hci idx val c k Hc1 Hk1), (IH Hc2 Hk2). reflexivity.
Qed.

Lemma subst_cidx_spec_fix_step : forall (D : JoinDomain) (mot : cty D) (val : cidx D) k,
  cty_uses_kinds true false false false false false false (S k) mot = false ->
  subst_cidx_in_cty (S (S k)) (lift_cidx 0 2 val) (spec_fix_step_cty mot) =
  spec_fix_step_cty (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) mot).
Proof.
  intros D mot val k Hmot. unfold spec_fix_step_cty.
  assert (Hren : forall (T : cty D) k0 (v0 : cidx D),
    cty_uses_kinds true false false false false false false (S k0) T = false ->
    subst_cidx_in_cty (S (S (S k0))) (lift_cidx 0 3 v0) (ren_cty (ren_lift 1 2) T) =
    ren_cty (ren_lift 1 2) (subst_cidx_in_cty (S k0) (lift_cidx 0 1 v0) T)).
  { Ltac solve_fix_ren v c k0 :=
      unfold ren_lift; cbn [subst_cidx subst_cidx_in_cty ren_cidx ren_cty];
      destruct (Nat.ltb_spec v (S c)); repeat (cbn [subst_cidx subst_cidx_in_cty ren_cidx ren_cty]; repeat (rw_nat_bool; cbv iota));
      [ destruct (Nat.ltb_spec v (S (c + k0))),
                 (Nat.ltb_spec v (S (S (S (c + k0))))), (Nat.eqb_spec v (S (S (S (c + k0)))));
          repeat (cbn [subst_cidx subst_cidx_in_cty ren_cidx ren_cty]; repeat (rw_nat_bool; cbv iota));
          try reflexivity; f_equal; lia
      | destruct (Nat.ltb_spec v (S (c + k0))), (Nat.eqb_spec v (S (c + k0)));
          repeat (cbn [subst_cidx subst_cidx_in_cty ren_cidx ren_cty]; repeat (rw_nat_bool; cbv iota)); try lia;
          destruct (Nat.ltb_spec (v + 2) (S (S (S (c + k0))))), (Nat.eqb_spec (v + 2) (S (S (S (c + k0)))));
          repeat (cbn [subst_cidx subst_cidx_in_cty ren_cidx ren_cty]; repeat (rw_nat_bool; cbv iota));
          try lia; try reflexivity;
          destruct (Nat.ltb_spec (v - 1) (S c));
          repeat (cbn [subst_cidx subst_cidx_in_cty ren_cidx ren_cty]; repeat (rw_nat_bool; cbv iota));
          try lia; try reflexivity; f_equal; lia ].
    assert (Hci : forall (i : cidx D) c k0 (v0 : cidx D),
      cidx_uses_kinds true false false false false (S (c + k0)) i = false ->
      subst_cidx (S (S (S (c + k0)))) (lift_cidx 0 (S (S (S c))) v0) (ren_cidx (ren_lift (S c) 2) i) =
      ren_cidx (ren_lift (S c) 2) (subst_cidx (S (c + k0)) (lift_cidx 0 (S c) v0) i)).
    { induction i; intros c k0 v0 Hu; cbn [subst_cidx ren_cidx cidx_uses_kinds orb] in *; try reflexivity;
        try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHi1 _ _ _ Hu1), (IHi2 _ _ _ Hu2); reflexivity);
        try (f_equal; apply (IHi _ _ _ Hu)).
      - destruct (Nat.eq_dec x (S (c + k0))) as [-> | Hne].
        + unfold ren_lift at 1 3. rw_nat_bool.
          destruct (Nat.ltb_spec (S (c + k0)) (S c)); [lia |].
          repeat (rw_nat_bool; cbv iota).
          destruct (Nat.ltb_spec (S (c + k0) + 2) (S (S (S (c + k0))))); [lia |].
          destruct (Nat.eqb_spec (S (c + k0) + 2) (S (S (S (c + k0))))); [| lia].
          unfold lift_cidx. rewrite ren_cidx_comp. apply ren_cidx_ext.
          intro y. unfold ren_lift. rw_nat_bool.
          destruct (Nat.ltb_spec (y + S c) (S c)); lia.
        + solve_fix_ren x c k0.
      - nat_bool_hyps; destruct (Nat.eqb_spec b (S (c + k0))) as [Heq | Hne];
          [lia | solve_fix_ren b c k0].
      - nat_bool_hyps; destruct (Nat.eqb_spec p (S (c + k0))) as [Heq | Hne];
          [lia | solve_fix_ren p c k0].
      - nat_bool_hyps; destruct (Nat.eqb_spec p (S (c + k0))) as [Heq | Hne];
          [lia | solve_fix_ren p c k0].
      - apply orb_false_iff in Hu as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
        assert (Hsh : forall y, ren_shift (ren_lift (S c) 2) y = ren_lift (S (S c)) 2 y).
        { intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity |].
          destruct (Nat.leb_spec y c), (Nat.leb_spec y (S c)); repeat (rw_nat_bool; cbv iota); lia. }
        repeat erewrite (ren_cidx_ext _ (ren_shift (ren_lift (S c) 2)) (ren_lift (S (S c)) 2) _ Hsh).
        rewrite !lift_cidx_add.
        replace (1 + S (S (S c))) with (S (S (S (S c)))) by lia.
        replace (1 + S c) with (S (S c)) by lia.
        replace (S (S (S (S (c + k0))))) with (S (S (S (S c + k0)))) by lia.
        replace (S (S (c + k0))) with (S (S c + k0)) by lia.
        replace (S (S (c + k0))) with (S (S c + k0)) in H2, H3 by lia.
        rewrite (IHi1 (S c) k0 v0 H2), (IHi2 (S c) k0 v0 H3).
        destruct (Nat.eqb_spec s (S (c + k0))) as [Heq | Hne];
          [lia | solve_fix_ren s c k0]. }
    assert (Hct : forall (T0 : cty D) c k0 (v0 : cidx D),
      cty_uses_kinds true false false false false false false (S (c + k0)) T0 = false ->
      subst_cidx_in_cty (S (S (S (c + k0)))) (lift_cidx 0 (S (S (S c))) v0) (ren_cty (ren_lift (S c) 2) T0) =
      ren_cty (ren_lift (S c) 2) (subst_cidx_in_cty (S (c + k0)) (lift_cidx 0 (S c) v0) T0)).
    { induction T0 using cty_ind_nested; intros c k0 v0 Hu; cbn [subst_cidx_in_cty ren_cty cty_uses_kinds map orb] in *; try reflexivity;
        try (f_equal; apply (IHT0 _ _ _ Hu));
        try (apply orb_false_iff in Hu as [Hu1 Hu2]; rewrite (IHT0_1 _ _ _ Hu1), (IHT0_2 _ _ _ Hu2); reflexivity).
      - apply orb_false_iff in Hu as [Hu1 Hu2]. rewrite (IHT0 _ _ _ Hu1), (Hci _ _ _ _ Hu2). reflexivity.
      - nat_bool_hyps; destruct (Nat.eqb_spec x (S (c + k0))) as [Heq | Hne];
          [lia | solve_fix_ren x c k0].
      - nat_bool_hyps; destruct (Nat.eqb_spec b (S (c + k0))) as [Heq | Hne];
          [lia | solve_fix_ren b c k0].
      - apply orb_false_iff in Hu as [Hu1 Hu2]. rewrite (IHT0_1 _ _ _ Hu1).
        assert (Hsh : forall y, ren_shift (ren_lift (S c) 2) y = ren_lift (S (S c)) 2 y).
        { intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity |].
          destruct (Nat.leb_spec y c), (Nat.leb_spec y (S c)); repeat (rw_nat_bool; cbv iota); lia. }
        erewrite (ren_cty_ext _ (ren_shift (ren_lift (S c) 2)) (ren_lift (S (S c)) 2) _ Hsh).
        erewrite (ren_cty_ext _ (ren_shift (ren_lift (S c) 2)) (ren_lift (S (S c)) 2) _ Hsh).
        rewrite !lift_cidx_add.
        replace (1 + S (S (S c))) with (S (S (S (S c)))) by lia.
        replace (1 + S c) with (S (S c)) by lia.
        replace (S (S (S (S (c + k0))))) with (S (S (S (S c + k0)))) by lia.
        replace (S (S (c + k0))) with (S (S c + k0)) by lia.
        replace (S (S (c + k0))) with (S (S c + k0)) in Hu2 by lia.
        rewrite (IHT0_2 (S c) k0 v0 Hu2). reflexivity.
      - apply orb_false_iff in Hu as [Hu1 Hu2]. rewrite (IHT0_1 _ _ _ Hu1).
        assert (Hsh : forall y, ren_shift (ren_lift (S c) 2) y = ren_lift (S (S c)) 2 y).
        { intros [| y]; unfold ren_lift; cbn; [rw_nat_bool; reflexivity |].
          destruct (Nat.leb_spec y c), (Nat.leb_spec y (S c)); repeat (rw_nat_bool; cbv iota); lia. }
        erewrite (ren_cty_ext _ (ren_shift (ren_lift (S c) 2)) (ren_lift (S (S c)) 2) _ Hsh).
        erewrite (ren_cty_ext _ (ren_shift (ren_lift (S c) 2)) (ren_lift (S (S c)) 2) _ Hsh).
        rewrite !lift_cidx_add.
        replace (1 + S (S (S c))) with (S (S (S (S c)))) by lia.
        replace (1 + S c) with (S (S c)) by lia.
        replace (S (S (S (S (c + k0))))) with (S (S (S (S c + k0)))) by lia.
        replace (S (S (c + k0))) with (S (S c + k0)) by lia.
        replace (S (S (c + k0))) with (S (S c + k0)) in Hu2 by lia.
        rewrite (IHT0_2 (S c) k0 v0 Hu2). reflexivity.
      - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
        inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [Hu1 Hur]. rewrite (H2 _ _ _ Hu1), (IHf H3 Hur). reflexivity.
      - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
        apply orb_false_iff in Hu as [Hu1 Hu2]. rewrite (Hci _ _ _ _ Hu1), (IH Hu2). reflexivity. }
    intros T k0 v0 HT. exact (Hct T 0 k0 v0 HT). }
  assert (Hren_use : cty_uses_kinds true false false false false false false (S (S (S k))) (ren_cty (ren_lift 1 2) mot) = false).
  { eapply cty_uses_kinds_ren_gen; [| exact Hmot].
    intro y. unfold ren_lift. destruct (Nat.ltb_spec y 1); lia. }
  assert (Hlift_23 : lift_cidx 0 1 (lift_cidx 0 2 val) = lift_cidx 0 3 val) by (rewrite lift_cidx_add; reflexivity).
  rewrite (subst_cidx_in_cty_subst_cidx D (ren_cty (ren_lift 1 2) mot) (CIdxAdd (CIdxVar 1) (CIdxLit 1)) (lift_cidx 0 2 val) 0 (S (S k)) ltac:(lia) ltac:(cbn; reflexivity) Hren_use).
  rewrite Hlift_23, (Hren mot k val Hmot). cbn [subst_cidx]. rw_nat_bool. reflexivity.
Qed.

(* Environment demand relation for shrinking ctype_uses along branch_rel *)

Definition cbinding_demand_rel {D : JoinDomain} (env1 : cenv D) (x : nat) (e1 e2 : cbinding D) : Prop :=
  cbinder e1 = cbinder e2 /\
  cty_alpha_eq (cannotation e1) (cannotation e2) /\
  branch_rel (ctype_uses e1) (ctype_uses e2) /\
  (forall row, CTypeDemand (skipn (S x) env1) (cannotation e1) row -> vec_allows row (ctype_uses e2) -> vec_allows row (ctype_uses e1)).

Definition cenv_demand_rel {D : JoinDomain} (env1 env2 : cenv D) : Prop :=
  length env1 = length env2 /\
  forall x e2, clookup env2 x = Some e2 ->
    exists e1, clookup env1 x = Some e1 /\ cbinding_demand_rel env1 x e1 e2.

Lemma cenv_demand_rel_alpha : forall (D : JoinDomain) (env1 env2 : cenv D),
  cenv_demand_rel env1 env2 -> cenv_alpha_eq env1 env2.
Proof.
  intros D env1. induction env1 as [| e1 rest1 IH]; intros [| e2 rest2] [Hlen Hlk];
    cbn in Hlen; try discriminate; [constructor |].
  destruct (Hlk 0 e2 eq_refl) as [e1' [He1' [_ [Ha _]]]].
  cbn in He1'; inversion He1'; subst e1'. constructor; [exact Ha |].
  apply IH; split; [lia |].
  intros x e' Hl. destruct (Hlk (S x) e' Hl) as [e1'' [Hl1 Hbd]].
  exists e1''; split; [exact Hl1 | exact Hbd].
Qed.

Lemma cenv_demand_rel_cons : forall (D : JoinDomain) (env1 env2 : cenv D) xb ann1 ann2 a1 a2,
  cenv_demand_rel env1 env2 ->
  cty_alpha_eq ann1 ann2 ->
  CTypeDemand env1 ann1 a1 ->
  branch_rel a1 a2 ->
  cenv_demand_rel
    ({| cbinder := xb; cannotation := ann1; ctype_uses := a1 |} :: env1)
    ({| cbinder := xb; cannotation := ann2; ctype_uses := a2 |} :: env2).
Proof.
  intros D env1 env2 xb ann1 ann2 a1 a2 [Hlen Hlk] Hann Ha1 Hbr.
  split; [cbn; congruence |].
  intros [| x'] e2 Hl; cbn in Hl.
  - inversion Hl; subst e2.
    eexists; split; [reflexivity |].
    cbn. repeat split; [exact Hann | exact Hbr |].
    intros row Hrow _.
    rewrite (ctype_demand_unique D _ _ _ row a1 (cenv_alpha_eq_refl D env1) Hrow Ha1).
    apply vec_allows_refl.
  - destruct (Hlk x' e2 Hl) as [e1 [Hl1 [Hb [Ha [Hbr' Hrow]]]]].
    exists e1; split; [exact Hl1 |].
    repeat split; [exact Hb | exact Ha | exact Hbr' | exact Hrow].
Qed.

Lemma cenv_demand_rel_cons_same : forall (D : JoinDomain) (env1 env2 : cenv D) xb ann1 ann2 a,
  cenv_demand_rel env1 env2 ->
  cty_alpha_eq ann1 ann2 ->
  CTypeDemand env1 ann1 a ->
  cenv_demand_rel
    ({| cbinder := xb; cannotation := ann1; ctype_uses := a |} :: env1)
    ({| cbinder := xb; cannotation := ann2; ctype_uses := a |} :: env2).
Proof.
  intros D env1 env2 xb ann1 ann2 a Hrel Hann Ha.
  apply cenv_demand_rel_cons; [exact Hrel | exact Hann | exact Ha | apply branch_rel_refl].
Qed.

Lemma cenv_demand_rel_refl : forall (D : JoinDomain) (env : cenv D),
  cenv_demand_rel env env.
Proof.
  intros D env. split; [reflexivity |].
  intros x e Hl. exists e; split; [exact Hl |].
  split; [reflexivity | split; [apply cty_alpha_eq_refl | split; [apply branch_rel_refl | intros row _ Hva; exact Hva]]].
Qed.

Lemma CTypeDemand_alpha_ty : forall (D : JoinDomain) (env : cenv D) (T1 : cty D) d,
  CTypeDemand env T1 d ->
  forall T2, cty_alpha_eq T1 T2 -> CTypeDemand env T2 d.
Proof.
  intros D env T1 d H.
  induction H using CTypeDemand_ind_mut with
    (P := fun env T1 d _ => forall T2, cty_alpha_eq T1 T2 -> CTypeDemand env T2 d)
    (P0 := fun env fs1 df _ => forall fs2,
             Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2) fs1 fs2 ->
             CRecordFieldDemand env fs2 df)
    (P1 := fun env ls1 dl _ => forall ls2, ls1 = ls2 -> CIdxListDemand env ls2 dl);
    intros T2 Halpha;
    try solve [destruct T2; unfold cty_alpha_eq in Halpha; cbn in Halpha; try discriminate;
               inversion Halpha; subst; constructor;
               try (apply IHCTypeDemand; assumption);
               try (apply IHCTypeDemand1; assumption);
               try (apply IHCTypeDemand2; assumption);
               try assumption].
  - destruct T2; unfold cty_alpha_eq in Halpha; cbn in Halpha; try discriminate.
    inversion Halpha; subst. eapply CTypeTVar; eassumption.
  - destruct T2; unfold cty_alpha_eq in Halpha; cbn in Halpha; try discriminate.
    inversion Halpha; subst. eapply CTypeTUnbox; eassumption.
  - destruct T2; unfold cty_alpha_eq in Halpha; cbn in Halpha; try discriminate.
    inversion Halpha as [[Hs Hr Hdom Hcod]]. subst.
    eapply CTypePi; [apply IHCTypeDemand1; exact Hdom | | assumption].
    eapply CTypeDemand_alpha_env;
      [| apply IHCTypeDemand2; exact Hcod]; constructor; [cbn; exact Hdom | apply cenv_alpha_eq_refl].
  - destruct T2; unfold cty_alpha_eq in Halpha; cbn in Halpha; try discriminate.
    inversion Halpha as [[Hr Hf Hs]]. subst.
    eapply CTypeSigma; [apply IHCTypeDemand1; exact Hf | | assumption].
    eapply CTypeDemand_alpha_env;
      [| apply IHCTypeDemand2; exact Hs]; constructor; [cbn; exact Hf | apply cenv_alpha_eq_refl].
  - destruct T2; unfold cty_alpha_eq in Halpha; cbn in Halpha; try discriminate.
    inversion Halpha as [[Hid Hfs]]. subst.
    constructor. apply IHCTypeDemand.
    clear - Hfs. revert fields0 Hfs.
    induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs; cbn in *;
      try discriminate; [constructor |].
    inversion Hfs; constructor; [repeat split; unfold cty_alpha_eq; congruence | apply IH; congruence].
  - inversion Halpha as [| ? y ? lrest Hy Hrest]; subst.
    destruct y as [[n2 g2] t2], Hy as [<- [<- Hft]].
    constructor; [apply IHCTypeDemand; exact Hft | apply IHCTypeDemand0; exact Hrest].
Qed.

Lemma CTypeDemand_alpha : forall (D : JoinDomain) (T1 T2 : cty D) (env1 env2 : cenv D) d,
  cty_alpha_eq T1 T2 ->
  cenv_alpha_eq env1 env2 ->
  CTypeDemand env1 T1 d ->
  CTypeDemand env2 T2 d.
Proof.
  intros D T1 T2 env1 env2 d HT He H.
  eapply CTypeDemand_alpha_env; [exact He | eapply CTypeDemand_alpha_ty; [exact H | exact HT]].
Qed.

Lemma cenv_alpha_eq_sym : forall (D : JoinDomain) (env1 env2 : cenv D),
  cenv_alpha_eq env1 env2 -> cenv_alpha_eq env2 env1.
Proof.
  intros D env1 env2 H. induction H; constructor; [apply cty_alpha_eq_sym; exact H | exact IHForall2].
Qed.

Lemma record_extend_demand_rel : forall (D : JoinDomain) (env2 : cenv D) bs fields ext2 env1 fields1,
  CRecordExtendEnv env2 bs fields ext2 ->
  cenv_demand_rel env1 env2 ->
  Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2) fields1 fields ->
  exists ext1, CRecordExtendEnv env1 bs fields1 ext1 /\ cenv_demand_rel ext1 ext2.
Proof.
  intros D env2 bs fields ext2 env1 fields1 Hext. revert env1 fields1.
  induction Hext; intros env1 fields1 Hrel Hfs; inversion Hfs as [| [[fn1 fg1] ft1] [[fn2 fg2] ft2] fs1' fs2' [Hn [Hg Hft]] Hrest]; subst.
  - exists env1; split; [constructor | exact Hrel].
  - assert (Hrow : CTypeDemand env1 ft1 row) by
      (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact Hft | apply cenv_alpha_eq_sym, cenv_demand_rel_alpha; exact Hrel | exact H]).
    assert (Hrel' : cenv_demand_rel ({| cbinder := b; cannotation := ft1; ctype_uses := row |} :: env1)
                                    ({| cbinder := b; cannotation := ft; ctype_uses := row |} :: env)).
    { apply cenv_demand_rel_cons_same; [exact Hrel | exact Hft | exact Hrow]. }
    assert (Hfs' : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2)
                     (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')
                     (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
    { clear - Hrest. induction Hrest; constructor; [| exact IHHrest].
      destruct x as [[n1 g1] t1], y as [[n2 g2] t2], H as [-> [-> Ht]].
      repeat split; apply ren_cty_alpha_eq; exact Ht. }
    destruct (IHHext _ _ Hrel' Hfs') as [ext1 [Hext1 Hrel_ext]].
    exists ext1; split; [eapply CRecordExtCons; [exact Hrow | exact Hext1] | exact Hrel_ext].
Qed.

Lemma branch_vec_mono : forall (D : JoinDomain) (u1 u2 u v1 v2 : list (grade D)),
  BranchVec u1 u2 u ->
  branch_rel v1 u1 ->
  branch_rel v2 u2 ->
  exists v, BranchVec v1 v2 v /\ branch_rel v u.
Proof.
  intros D u1 u2 u v1 v2 Hbr H1 H2. unfold BranchVec, branch_rel in *.
  destruct (grade_join D) as [j |] eqn:Hj.
  - subst u. exists (vec_join j v1 v2); split; [reflexivity |].
    apply vec_allows_join_mono; [exact Hj | exact H1 | exact H2].
  - destruct Hbr as [-> ->]. subst. exists u2; split; [split; reflexivity | reflexivity].
Qed.

Lemma app_result_ty_alpha : forall (D : JoinDomain) (dom1 dom2 cod1 cod2 : cty D) arg res,
  cty_alpha_eq dom1 dom2 ->
  cty_alpha_eq cod1 cod2 ->
  app_result_ty dom2 cod2 arg = Some res ->
  exists res1, app_result_ty dom1 cod1 arg = Some res1 /\ cty_alpha_eq res1 res.
Proof.
  intros D dom1 dom2 cod1 cod2 arg res Hdom Hcod Happ.
  unfold app_result_ty in *.
  assert (Heq_dom : erase_hints dom1 = erase_hints dom2) by exact Hdom.
  destruct dom1, dom2; cbn in Heq_dom; try discriminate;
    try (destruct (cty_uses_var 0 cod2) eqn:E2; [discriminate |];
         rewrite (cty_uses_var_alpha_eq D 0 cod1 cod2 Hcod), E2;
         inversion Happ; subst; eexists; split; [reflexivity | apply cty_alpha_eq_unshift; exact Hcod]).
  - destruct (term_as_cidx arg) as [idx |].
    + inversion Happ; subst. eexists; split; [reflexivity | apply subst_cidx_alpha_eq; exact Hcod].
    + destruct (cty_uses_var 0 cod2) eqn:E2; [discriminate |].
      rewrite (cty_uses_var_alpha_eq D 0 cod1 cod2 Hcod), E2.
      inversion Happ; subst. eexists; split; [reflexivity | apply cty_alpha_eq_unshift; exact Hcod].
  - destruct (term_as_cidx arg), arg;
      try (inversion Happ; subst; eexists; split;
           [reflexivity | apply cty_alpha_eq_subst_tvar; [apply cty_alpha_eq_refl | exact Hcod]]).
    all: destruct (cty_uses_var 0 cod2) eqn:E2; [discriminate |];
         rewrite (cty_uses_var_alpha_eq D 0 cod1 cod2 Hcod), E2;
         inversion Happ; subst; eexists; split; [reflexivity | apply cty_alpha_eq_unshift; exact Hcod].
Qed.

Lemma branch_rel_scale_grade : forall (D : JoinDomain) (q1 q2 : grade D) (u1 u2 : list (grade D)),
  allows q1 q2 ->
  (grade_join D = None -> q1 = q2) ->
  branch_rel u1 u2 ->
  branch_rel (vec_scale q1 u1) (vec_scale q2 u2).
Proof.
  intros D q1 q2 u1 u2 Hq Hnone Hu. unfold branch_rel in *.
  destruct (grade_join D).
  - apply vec_allows_scale; assumption.
  - rewrite (Hnone eq_refl), Hu. reflexivity.
Qed.

Lemma cenv_alpha_eq_skipn : forall (D : JoinDomain) (env1 env2 : cenv D) n,
  cenv_alpha_eq env1 env2 -> cenv_alpha_eq (skipn n env1) (skipn n env2).
Proof.
  intros D env1 env2 n H. revert n.
  induction H; intros [| n]; cbn; try apply Forall2_nil; try exact H; try apply IHForall2.
  constructor; [exact H | exact H0].
Qed.

Lemma record_allows_mono : forall (D : JoinDomain) (s : grade D) fields fields1 us1 us2,
  CRecordFieldAllows s fields us2 ->
  Forall2 (@allows D) us1 us2 ->
  Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2) fields1 fields ->
  CRecordFieldAllows s fields1 us1.
Proof.
  intros D s fields fields1 us1 us2 Hfa_rec Hfa Hfs_a.
  revert fields1 us1 Hfa Hfs_a.
  induction Hfa_rec; intros [| [[n1 g1] t1] r1] [| u1 us1] Hfa Hfs; inversion Hfs; subst;
    [ apply CRecordAllowsNil
    | inversion Hfa
    | inversion Hfa
    | inversion Hfa; subst;
      match goal with
      | Ha1 : allows ?a ?b, Ha2 : allows ?b ?c, Hn : context [cty_alpha_eq] |- _ =>
          cbn in Hn; destruct Hn as [<- [<- _]]; apply CRecordAllowsCons;
          [ eapply allows_trans; [exact Ha1 | exact Ha2] | eapply IHHfa_rec; eassumption ]
      end ].
Qed.

Lemma Subty_alpha : forall (D : JoinDomain) (env1 : cenv D) A1 B1,
  Subty env1 A1 B1 ->
  forall env2 A2 B2,
  cenv_alpha_eq env1 env2 ->
  cty_alpha_eq A1 A2 ->
  cty_alpha_eq B1 B2 ->
  Subty env2 A2 B2.
Proof.
  intros D env1 A1 B1 H.
  induction H; intros env2 A2 B2 He HA HB.
  - apply SubRefl. eapply cty_alpha_eq_trans; [apply cty_alpha_eq_sym; exact HA | eapply cty_alpha_eq_trans; [exact H | exact HB]].
  - destruct A2, B2; unfold cty_alpha_eq in HA, HB; cbn in HA, HB; try discriminate;
      inversion HA as [[Hq1 HA1]]; inversion HB as [[Hq2 HB1]]; subst;
      apply SubBox; [assumption | apply IHSubty; [exact He | exact HA1 | exact HB1]].
  - destruct A2, B2; unfold cty_alpha_eq in HA, HB; cbn in HA, HB; try discriminate;
      inversion HA as [[Hs1 Hr1 HA1 HB1]]; inversion HB as [[Hs2 Hr2 HA2 HB2]]; subst;
      eapply SubPi; [assumption | assumption | apply IHSubty1; [exact He | exact HA2 | exact HA1] |].
    apply IHSubty2; [constructor; [cbn; exact HA2 | exact He] | exact HB1 | exact HB2].
  - destruct A2, B2; unfold cty_alpha_eq in HA, HB; cbn in HA, HB; try discriminate;
      inversion HA as [[Hr1 HA1 HB1]]; inversion HB as [[Hr2 HA2 HB2]]; subst;
      eapply SubSigma; [assumption | apply IHSubty1; [exact He | exact HA1 | exact HA2] |].
    apply IHSubty2; [constructor; [cbn; exact HA1 | exact He] | exact HB1 | exact HB2].
  - destruct A2, B2; unfold cty_alpha_eq in HA, HB; cbn in HA, HB; try discriminate;
      inversion HA as [[HA1 HB1]]; inversion HB as [[HA2 HB2]]; subst;
      apply SubSum; [apply IHSubty1; [exact He | exact HA1 | exact HA2] | apply IHSubty2; [exact He | exact HB1 | exact HB2]].
  - destruct A2, B2; unfold cty_alpha_eq in HA, HB; cbn in HA, HB; try discriminate;
      inversion HA as [[HA1 Hl1]]; inversion HB as [[HA2 Hl2]]; subst;
      apply SubVec; [assumption | apply IHSubty; [exact He | exact HA1 | exact HA2]].
Qed.

Lemma core_derives_cenv_rel : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (env2 : cenv D) t j2,
  CoreDerives env2 t j2 ->
  forall env1, cenv_demand_rel env1 env2 ->
  exists j1,
    CoreDerives env1 t j1 /\
    cty_alpha_eq (cresult_type j1) (cresult_type j2) /\
    branch_rel (ccomp_demand j1) (ccomp_demand j2) /\
    branch_rel (ctype_demand_row j1) (ctype_demand_row j2).
Proof.
  intros D ED env2 t j2 H.
  induction H using CoreDerives_ind_mut with
    (P := fun env2 t j2 _ => forall env1, cenv_demand_rel env1 env2 ->
            exists j1, CoreDerives env1 t j1 /\
              cty_alpha_eq (cresult_type j1) (cresult_type j2) /\
              branch_rel (ccomp_demand j1) (ccomp_demand j2) /\
              branch_rel (ctype_demand_row j1) (ctype_demand_row j2))
    (P0 := fun env2 fs u2 v2 _ => forall env1, cenv_demand_rel env1 env2 ->
             exists u1 v1, CRecordElemDerives env1 fs u1 v1 /\
               branch_rel u1 u2 /\ branch_rel v1 v2);
    intros env1 Hrel; pose proof (cenv_demand_rel_alpha D env1 _ Hrel) as Halpha;
    pose proof (proj1 Hrel) as Hlen.
  - (* CoreVar *)
    lazymatch goal with
    | Hl : clookup _ x = Some e, Htd : CTypeDemand _ _ row, Hva : vec_allows row _ |- _ =>
        destruct Hrel as [Hl_len Hlk];
        destruct (Hlk x e Hl) as [e1 [Hl1 [Hb [Ha [Hbr Hrow_fn]]]]];
        assert (Hsk_alpha : cenv_alpha_eq (skipn (S x) env1) (skipn (S x) env)) by
          (apply cenv_alpha_eq_skipn; exact Halpha);
        assert (Hrow1 : CTypeDemand (skipn (S x) env1) (cannotation e1) row) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact Ha | apply cenv_alpha_eq_sym; exact Hsk_alpha | exact Htd]);
        eexists; split; [| split; [| split]]; cbn [cresult_type ccomp_demand ctype_demand_row];
        [ eapply CoreVar; [exact Hl1 | exact Hrow1 | exact (Hrow_fn row Hrow1 Hva)]
        | apply ren_cty_alpha_eq; exact Ha
        | rewrite Hl_len; apply branch_rel_refl
        | unfold branch_rel in *; destruct (grade_join D); [| cbn [ctype_demand_row]; rewrite Hbr; reflexivity];
          cbn [ctype_demand_row]; apply Forall2_app; [apply vec_allows_refl | exact Hbr] ]
    end.
  - (* CoreNatVal *)
    lazymatch goal with
    | Hd : CIdxDemand env i d |- _ =>
        assert (Hd1 : CIdxDemand env1 i d) by (eapply CIdxDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hd]);
        eexists; split; [| split; [| split]];
        [ apply CoreNatVal; exact Hd1
        | apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_refl
        | cbn [ctype_demand_row]; rewrite Hlen; apply branch_rel_refl ]
    end.
  - (* CoreBoolVal *)
    eexists; split; [| split; [| split]];
    [ apply CoreBoolVal
    | apply cty_alpha_eq_refl
    | cbn [ccomp_demand]; rewrite Hlen; apply branch_rel_refl
    | cbn [ctype_demand_row]; rewrite Hlen; apply branch_rel_refl ].
  - (* CoreTypeVal *)
    lazymatch goal with
    | Hd : CTypeDemand env T v, Hlv : CUniverseLevel env T lvl |- _ =>
        assert (Hv1 : CTypeDemand env1 T v) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hd]);
        assert (Hlv1 : CUniverseLevel env1 T lvl) by (eapply CUniverseLevel_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hlv]);
        eexists; split; [| split; [| split]];
        [ eapply CoreTypeVal; [exact Hv1 | exact Hlv1]
        | apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; rewrite Hlen; apply branch_rel_refl
        | cbn [ctype_demand_row]; apply branch_rel_refl ]
    end.
  - (* CoreLam *)
    lazymatch goal with
    | Ha : CTypeDemand env dom a, Hs : allows (nth_grade u 0) s, Hr : allows (nth_grade v 0) r |- _ =>
        assert (Ha1 : CTypeDemand env1 dom a) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        destruct (IHCoreDerives _ (cenv_demand_rel_cons_same D env1 env x dom dom a Hrel (cty_alpha_eq_refl D dom) Ha1))
          as [[cod1 u1 v1] [Hb1 [Hcod [Hu Hv]]]];
        cbn in Hcod, Hu, Hv;
        eexists; split; [| split; [| split]];
        [ eapply CoreLam; [exact Ha1 | exact Hb1 | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu) | exact Hs]
                          | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hv) | exact Hr]]
        | cbn [cresult_type]; unfold cty_alpha_eq in *; cbn; congruence
        | cbn [ccomp_demand]; apply branch_rel_tl; exact Hu
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | apply branch_rel_tl; exact Hv] ]
    end.
  - (* CoreApp *)
    lazymatch goal with
    | Hka_eq : cty_alpha_eq kind dom,
      Ha_dom : CTypeDemand env dom a_dom,
      Hb_cod : CTypeDemand _ cod b,
      Hnb : allows (nth_grade b 0) r,
      Huniv : forall lvl arg_ty, dom = CUniv lvl -> _,
      Hres : app_result_ty dom cod arg = Some res_ty,
      Hz_eq : z_type = app_type_arg_demand dom arg u_arg v_arg |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[tf1 w1 v_fn1] [Hfn1 [Htf [Hw Hvfn]]]];
        destruct (IHCoreDerives2 _ Hrel) as [[ka1 u_arg1 v_arg1] [Harg1 [Hka [Huarg Hvarg]]]];
        cbn in Htf, Hka, Hw, Hvfn, Huarg, Hvarg;
        destruct tf1 as [| | | | | | | x1 s1 r1 dom1 cod1 | | | | |]; unfold cty_alpha_eq in Htf; cbn in Htf; try discriminate;
        inversion Htf as [[Hs_eq Hr_eq Hdom_eq Hcod_eq]]; subst s1 r1;
        assert (Hdom_a : cty_alpha_eq dom1 dom) by exact Hdom_eq;
        assert (Hcod_a : cty_alpha_eq cod1 cod) by exact Hcod_eq;
        assert (Ha_dom1 : CTypeDemand env1 dom1 a_dom) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact Hdom_a | apply cenv_alpha_eq_sym; exact Halpha | exact Ha_dom]);
        assert (Hb1 : CTypeDemand ({| cbinder := x1; cannotation := dom1; ctype_uses := a_dom |} :: env1) cod1 b) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact Hcod_a | | exact Hb_cod]; constructor; [cbn; apply cty_alpha_eq_sym; exact Hdom_a | apply cenv_alpha_eq_sym; exact Halpha]);
        assert (Hka1 : cty_alpha_eq ka1 dom1) by (eapply cty_alpha_eq_trans; [exact Hka | eapply cty_alpha_eq_trans; [exact Hka_eq | apply cty_alpha_eq_sym; exact Hdom_a]]);
        assert (Huniv1 : forall lvl arg_ty, dom1 = CUniv lvl ->
                  (arg = CTypeVal arg_ty \/ (exists y, arg = CVar y /\ arg_ty = CTVar y)) ->
                  CUniverseLevel env1 arg_ty lvl) by
          (intros lvl arg_ty Hdom1 Hcase;
           assert (Hdom_u : dom = CUniv lvl) by
             (unfold cty_alpha_eq in Hdom_a; rewrite Hdom1 in Hdom_a; cbn in Hdom_a; destruct dom; cbn in Hdom_a; try discriminate; congruence);
           eapply CUniverseLevel_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact (Huniv lvl arg_ty Hdom_u Hcase)]);
        destruct (app_result_ty_alpha D dom1 dom cod1 cod arg res_ty Hdom_a Hcod_a Hres) as [res1 [Hres1 Hres_a]];
        assert (Hz1 : branch_rel (app_type_arg_demand dom1 arg u_arg1 v_arg1) z_type) by
          (rewrite Hz_eq; unfold app_type_arg_demand;
           assert (Heq_u : erase_hints dom1 = erase_hints dom) by exact Hdom_a;
           destruct dom1, dom; cbn in Heq_u; try discriminate; try exact Huarg;
           destruct arg; try exact Huarg; exact Hvarg);
        eexists; split; [| split; [| split]];
        [ eapply CoreApp; [exact Hfn1 | exact Harg1 | exact Hka1 | exact Ha_dom1 | exact Hb1 | exact Hnb | exact Huniv1 | exact Hres1 | reflexivity]
        | cbn [cresult_type]; exact Hres_a
        | cbn [ccomp_demand]; apply branch_rel_add; [exact Hw | apply branch_rel_scale; exact Huarg]
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | apply branch_rel_scale; exact Hz1] ]
    end.
  - (* CoreLet *)
    lazymatch goal with
    | Ha : CTypeDemand env ann a_ann,
      Hrt_eq : cty_alpha_eq rhs_ty ann,
      Hs : allows (nth_grade u_bod 0) s,
      Hr : allows (nth_grade v_bod 0) r,
      Hu_free : cty_uses_var 0 bod_ty = false |- _ =>
        assert (Ha1 : CTypeDemand env1 ann a_ann) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        destruct (IHCoreDerives1 _ Hrel) as [[rt1 ur1 vr1] [Hrhs1 [Hrt [Hur Hvr]]]];
        destruct (IHCoreDerives2 _ (cenv_demand_rel_cons_same D env1 env x ann ann a_ann Hrel (cty_alpha_eq_refl D ann) Ha1))
          as [[bt1 ub1 vb1] [Hbod1 [Hbt [Hub Hvb]]]];
        cbn in Hrt, Hur, Hvr, Hbt, Hub, Hvb;
        eexists; split; [| split; [| split]];
        [ eapply CoreLet; [exact Ha1 | exact Hrhs1 | eapply cty_alpha_eq_trans; [exact Hrt | exact Hrt_eq] | exact Hbod1
                          | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hub) | exact Hs]
                          | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hvb) | exact Hr]
                          | rewrite (cty_uses_var_alpha_eq D 0 bt1 bod_ty Hbt); exact Hu_free]
        | cbn [cresult_type]; apply cty_alpha_eq_unshift; exact Hbt
        | cbn [ccomp_demand]; apply branch_rel_add; [apply branch_rel_tl; exact Hub | apply branch_rel_scale; exact Hur]
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_tl; exact Hvb | apply branch_rel_scale; unfold app_type_arg_demand; destruct ann, rhs; try exact Hur; exact Hvr] ]
    end.
  - (* CorePair *)
    lazymatch goal with
    | Ha : CTypeDemand env fst_ty a,
      Hb : CTypeDemand _ snd_ty b,
      Hnb : allows (nth_grade b 0) r,
      Hfa_eq : cty_alpha_eq fst_act fst_ty,
      Hexp : app_result_ty fst_ty snd_ty fst_val = Some exp_snd,
      Hsa_eq : cty_alpha_eq snd_act exp_snd |- _ =>
        assert (Ha1 : CTypeDemand env1 fst_ty a) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        assert (Hb1 : CTypeDemand ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env1) snd_ty b) by
          (eapply CTypeDemand_alpha_env; [constructor; [apply cty_alpha_eq_refl | apply cenv_alpha_eq_sym; exact Halpha] | exact Hb]);
        destruct (IHCoreDerives1 _ Hrel) as [[fa1 ul1 vl1] [Hfst1 [Hfa [Hul Hvl]]]];
        destruct (IHCoreDerives2 _ Hrel) as [[sa1 ur1 vr1] [Hsnd1 [Hsa [Hur Hvr]]]];
        cbn in Hfa, Hul, Hvl, Hsa, Hur, Hvr;
        eexists; split; [| split; [| split]];
        [ eapply CorePair; [exact Ha1 | exact Hb1 | exact Hnb | exact Hfst1 | eapply cty_alpha_eq_trans; [exact Hfa | exact Hfa_eq]
                           | exact Hsnd1 | exact Hexp | eapply cty_alpha_eq_trans; [exact Hsa | exact Hsa_eq]]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_add; [exact Hul | exact Hur]
        | cbn [ctype_demand_row]; apply branch_rel_refl ]
    end.
  - (* CoreLetPair *)
    lazymatch goal with
    | Ha : CTypeDemand env A a,
      Hb : CTypeDemand _ B b,
      Hmot : CTypeDemand _ mot v_mot,
      Hkap : allows (nth_grade v_mot 0) kappa,
      Hexp : exp_mot = spec_pair_body_cty 0 mot,
      Hact_eq : cty_alpha_eq act_mot exp_mot,
      Hx_s : allows (nth_grade u_b 1) s,
      Hy_s : allows (nth_grade u_b 0) s,
      Hcond : match pr with | CPair _ _ _ _ fv sv => _ | CVar _ => True | _ => _ end,
      Hres : res_ty = spec_pair_subj_cty pr mot |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[tp1 w1 vp1] [Hpr1 [Htp [Hw Hvp]]]];
        cbn in Htp, Hw, Hvp;
        destruct tp1 as [| | | | | | | | z1 r1 A1 B1 | | | |]; unfold cty_alpha_eq in Htp; cbn in Htp; try discriminate;
        inversion Htp as [[Hr_eq HA_eq HB_eq]]; subst r1;
        assert (HA_a : cty_alpha_eq A1 A) by exact HA_eq;
        assert (HB_a : cty_alpha_eq B1 B) by exact HB_eq;
        assert (Ha1 : CTypeDemand env1 A1 a) by (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact HA_a | apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        assert (Hb1 : CTypeDemand ({| cbinder := x; cannotation := A1; ctype_uses := a |} :: env1) B1 b) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact HB_a | | exact Hb]; constructor; [cbn; apply cty_alpha_eq_sym; exact HA_a | apply cenv_alpha_eq_sym; exact Halpha]);
        assert (Hmot1 : CTypeDemand ({| cbinder := 0; cannotation := CSigma z1 r A1 B1; ctype_uses := vec_add a (tl b) |} :: env1) mot v_mot) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_refl | | exact Hmot]; constructor; [cbn; unfold cty_alpha_eq; cbn; rewrite HA_eq, HB_eq; reflexivity | apply cenv_alpha_eq_sym; exact Halpha]);
        assert (Hrel_x : cenv_demand_rel ({| cbinder := x; cannotation := A1; ctype_uses := a |} :: env1)
                                         ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env)) by
          (apply cenv_demand_rel_cons_same; [exact Hrel | exact HA_a | exact Ha1]);
        assert (Hrel_xy : cenv_demand_rel ({| cbinder := y; cannotation := B1; ctype_uses := b |} :: {| cbinder := x; cannotation := A1; ctype_uses := a |} :: env1)
                                          ({| cbinder := y; cannotation := B; ctype_uses := b |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env)) by
          (apply cenv_demand_rel_cons_same; [exact Hrel_x | exact HB_a | exact Hb1]);
        destruct (IHCoreDerives2 _ Hrel_xy) as [[am1 ub1 vb1] [Hbod1 [Ham [Hub Hvb]]]];
        cbn in Ham, Hub, Hvb;
        eexists; split; [| split; [| split]];
        [ eapply CoreLetPair; [exact Hpr1 | exact Ha1 | exact Hb1 | exact Hmot1 | exact Hkap | exact Hbod1 | exact Hexp
                              | eapply cty_alpha_eq_trans; [exact Ham | exact Hact_eq]
                              | eapply allows_trans; [exact (branch_rel_nth D _ _ 1 Hub) | exact Hx_s]
                              | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hub) | exact Hy_s]
                              | exact Hcond | exact Hres]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_add; [apply branch_rel_tl, branch_rel_tl; exact Hub | apply branch_rel_scale; exact Hw]
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | apply branch_rel_scale; exact Hw] ]
    end.
  - (* CorePromote *)
    destruct (IHCoreDerives _ Hrel) as [[A1 u1 v1] [Hval1 [HA [Hu Hv]]]].
    cbn in HA, Hu, Hv.
    eexists; split; [| split; [| split]];
    [ apply CorePromote; exact Hval1
    | cbn [cresult_type]; unfold cty_alpha_eq in *; cbn; congruence
    | cbn [ccomp_demand]; apply branch_rel_scale; exact Hu
    | cbn [ctype_demand_row]; exact Hv ].
  - (* CoreLetBox *)
    lazymatch goal with
    | Ha : CTypeDemand env A a,
      Hmot : CTypeDemand _ mot v_mot,
      Hkap : allows (nth_grade v_mot 0) kappa,
      Hexp : exp_mot = spec_box_body_cty q 0 mot,
      Hact_eq : cty_alpha_eq act_mot exp_mot,
      Hq_w : allows (nth_grade w 0) q,
      Hqk : allows (nth_grade bw 0) (mul q kappa),
      Hres : res_ty = spec_box_subj_cty box_term mot,
      Hz_eq : z_ty = _ |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[tb1 zb1 vz1] [Hbt1 [Htb [Hzb Hvz]]]];
        cbn in Htb, Hzb, Hvz;
        destruct tb1 as [| | | | | | | | | q1 A1 | | |]; unfold cty_alpha_eq in Htb; cbn in Htb; try discriminate;
        inversion Htb as [[Hq_eq HA_eq]]; subst q1;
        assert (HA_a : cty_alpha_eq A1 A) by exact HA_eq;
        assert (Ha1 : CTypeDemand env1 A1 a) by (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact HA_a | apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        assert (Hmot1 : CTypeDemand ({| cbinder := 0; cannotation := CBox q A1; ctype_uses := a |} :: env1) mot v_mot) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_refl | | exact Hmot]; constructor; [cbn; unfold cty_alpha_eq; cbn; rewrite HA_eq; reflexivity | apply cenv_alpha_eq_sym; exact Halpha]);
        destruct (IHCoreDerives2 _ (cenv_demand_rel_cons_same D env1 env x A1 A a Hrel HA_a Ha1))
          as [[am1 w1 bw1] [Hbod1 [Ham [Hw Hbw]]]];
        cbn in Ham, Hw, Hbw;
        eexists; split; [| split; [| split]];
        [ eapply CoreLetBox; [exact Hbt1 | exact Ha1 | exact Hmot1 | exact Hkap | exact Hbod1 | exact Hexp
                             | eapply cty_alpha_eq_trans; [exact Ham | exact Hact_eq]
                             | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hw) | exact Hq_w]
                             | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbw) | exact Hqk]
                             | assumption | exact Hres | reflexivity]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_add; [apply branch_rel_tl; exact Hw | exact Hzb]
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | apply branch_rel_scale; rewrite Hz_eq; destruct box_term; try exact Hzb; match goal with | |- branch_rel (match ?t0 with _ => _ end) _ => destruct t0; try exact Hzb; apply branch_rel_scale; exact Hvz end] ]
    end.
  - (* CoreInl *)
    lazymatch goal with
    | Hb : CTypeDemand env rhs_ty b |- _ =>
        destruct (IHCoreDerives _ Hrel) as [[A1 u1 a1] [Hv1 [HA [Hu Ha]]]];
        assert (Hb1 : CTypeDemand env1 rhs_ty b) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hb]);
        cbn in HA, Hu, Ha;
        eexists; split; [| split; [| split]];
        [ eapply CoreInl; [exact Hv1 | exact Hb1]
        | cbn [cresult_type]; unfold cty_alpha_eq in *; cbn; congruence
        | cbn [ccomp_demand]; exact Hu
        | cbn [ctype_demand_row]; apply branch_rel_add; [exact Ha | apply branch_rel_refl] ]
    end.
  - (* CoreInr *)
    lazymatch goal with
    | Ha : CTypeDemand env lhs_ty a |- _ =>
        assert (Ha1 : CTypeDemand env1 lhs_ty a) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        destruct (IHCoreDerives _ Hrel) as [[B1 u1 b1] [Hv1 [HB [Hu Hb]]]];
        cbn in HB, Hu, Hb;
        eexists; split; [| split; [| split]];
        [ eapply CoreInr; [exact Ha1 | exact Hv1]
        | cbn [cresult_type]; unfold cty_alpha_eq in *; cbn; congruence
        | cbn [ccomp_demand]; exact Hu
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | exact Hb] ]
    end.
  - (* CoreMatchSum *)
    lazymatch goal with
    | Hsne : s <> zero,
      Ha : CTypeDemand env A a,
      Hb : CTypeDemand env B b,
      Hmot : CTypeDemand _ mot v_mot,
      Hkap : allows (nth_grade v_mot 0) kappa,
      Ht1_eq : cty_alpha_eq t1 (spec_sum_branch_cty true 0 mot),
      Ht2_eq : cty_alpha_eq t2 (spec_sum_branch_cty false 0 mot),
      Hs1 : allows (nth_grade u1 0) s,
      Hs2 : allows (nth_grade u2 0) s,
      Hbr : BranchVec (tl u1) (tl u2) u_br,
      Hres : res_ty = spec_sum_subj_cty scrut mot |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[ts1 w1 vs1] [Hscr1 [Hts [Hw Hvs]]]];
        cbn in Hts, Hw, Hvs;
        destruct ts1 as [| | | | | | | | | | A1 B1 | |]; unfold cty_alpha_eq in Hts; cbn in Hts; try discriminate;
        inversion Hts as [[HA_eq HB_eq]];
        assert (HA_a : cty_alpha_eq A1 A) by exact HA_eq;
        assert (HB_a : cty_alpha_eq B1 B) by exact HB_eq;
        assert (Ha1 : CTypeDemand env1 A1 a) by (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact HA_a | apply cenv_alpha_eq_sym; exact Halpha | exact Ha]);
        assert (Hb1 : CTypeDemand env1 B1 b) by (eapply CTypeDemand_alpha; [apply cty_alpha_eq_sym; exact HB_a | apply cenv_alpha_eq_sym; exact Halpha | exact Hb]);
        assert (Hmot1 : CTypeDemand ({| cbinder := 0; cannotation := CSum A1 B1; ctype_uses := vec_add a b |} :: env1) mot v_mot) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_refl | | exact Hmot]; constructor; [cbn; unfold cty_alpha_eq; cbn; rewrite HA_eq, HB_eq; reflexivity | apply cenv_alpha_eq_sym; exact Halpha]);
        destruct (IHCoreDerives2 _ (cenv_demand_rel_cons_same D env1 env x A1 A a Hrel HA_a Ha1)) as [[tl1 u1' b1'] [Hlb1 [Htl [Hu1 Hb1']]]];
        destruct (IHCoreDerives3 _ (cenv_demand_rel_cons_same D env1 env y B1 B b Hrel HB_a Hb1)) as [[tr1 u2' b2'] [Hrb1 [Htr [Hu2 Hb2']]]];
        cbn in Htl, Hu1, Hb1', Htr, Hu2, Hb2';
        destruct (branch_vec_mono D (tl u1) (tl u2) u_br (tl u1') (tl u2') Hbr (branch_rel_tl D _ _ Hu1) (branch_rel_tl D _ _ Hu2)) as [ubr1 [Hubr1 Hbru]];
        assert (Hcond1 : match scrut with
                         | CInl _ v => match term_as_cidx v, A1 with Some _, CNat => True | _, _ => cty_uses_var 0 mot = false end
                         | CInr _ v => match term_as_cidx v, B1 with Some _, CNat => True | _, _ => cty_uses_var 0 mot = false end
                         | CVar _ => True
                         | _ => cty_uses_var 0 mot = false
                         end) by
          (destruct scrut; try assumption;
           [ match goal with | |- context [term_as_cidx ?v0] => destruct (term_as_cidx v0) end; try assumption;
             assert (Ha' : erase_hints A1 = erase_hints A) by exact HA_a;
             destruct A1, A; cbn in Ha'; try discriminate; assumption
           | match goal with | |- context [term_as_cidx ?v0] => destruct (term_as_cidx v0) end; try assumption;
             assert (Hb' : erase_hints B1 = erase_hints B) by exact HB_a;
             destruct B1, B; cbn in Hb'; try discriminate; assumption ]);
        eexists; split; [| split; [| split]];
        [ eapply CoreMatchSum; [exact Hsne | exact Hscr1 | exact Ha1 | exact Hb1 | exact Hmot1 | exact Hkap | exact Hlb1 | exact Hrb1
                               | eapply cty_alpha_eq_trans; [exact Htl | exact Ht1_eq]
                               | eapply cty_alpha_eq_trans; [exact Htr | exact Ht2_eq]
                               | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu1) | exact Hs1]
                               | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu2) | exact Hs2]
                               | exact Hubr1 | exact Hcond1 | exact Hres]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_add; [apply branch_rel_scale; exact Hw | exact Hbru]
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | apply branch_rel_scale; exact Hw] ]
    end.
  - (* CoreIf *)
    lazymatch goal with
    | Heq : cty_alpha_eq t1 t2, Hbru_bv : BranchVec u1 u2 u_br, Hbrv_bv : BranchVec v1 v2 v_br |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[tc1 uc1 vc1] [Hc1 [Htc [Huc Hvc]]]];
        destruct (IHCoreDerives2 _ Hrel) as [[t1' u1' v1'] [Hth1 [Ht1 [Hu1 Hv1]]]];
        destruct (IHCoreDerives3 _ Hrel) as [[t2' u2' v2'] [Hel1 [Ht2 [Hu2 Hv2]]]];
        cbn in Htc, Huc, Hvc, Ht1, Hu1, Hv1, Ht2, Hu2, Hv2;
        destruct tc1; unfold cty_alpha_eq in Htc; cbn in Htc; try discriminate;
        destruct (branch_vec_mono D u1 u2 u_br u1' u2' Hbru_bv Hu1 Hu2) as [ubr1 [Hubr1 Hbru]];
        destruct (branch_vec_mono D v1 v2 v_br v1' v2' Hbrv_bv Hv1 Hv2) as [vbr1 [Hvbr1 Hbrv]];
        eexists; split; [| split; [| split]];
        [ eapply CoreIf; [exact Hc1 | exact Hth1 | exact Hel1
                         | eapply cty_alpha_eq_trans; [exact Ht1 | eapply cty_alpha_eq_trans; [exact Heq | apply cty_alpha_eq_sym; exact Ht2]]
                         | exact Hubr1 | exact Hvbr1]
        | cbn [cresult_type]; exact Ht1
        | cbn [ccomp_demand]; apply branch_rel_add; [exact Huc | exact Hbru]
        | cbn [ctype_demand_row]; exact Hbrv ]
    end.
  - (* CoreRecordMk *)
    destruct (IHCoreDerives _ Hrel) as [u1 [v1 [Helems [Hu Hv]]]].
    eexists; split; [| split; [| split]];
    [ apply CoreRecordMk; exact Helems
    | apply cty_alpha_eq_refl
    | cbn [ccomp_demand]; exact Hu
    | cbn [ctype_demand_row]; exact Hv ].
  - (* CoreMatchRecord *)
    lazymatch goal with
    | Hsne : s <> zero,
      Hmot : CTypeDemand env mot v_mot,
      Hlen_fs_eq : length bs = length fields,
      Hext : CRecordExtendEnv env bs fields body_env,
      Htb_eq : cty_alpha_eq t_b (lift_cty 0 (length fields) mot),
      Hfa_rec : CRecordFieldAllows s fields (firstn (length fields) u_b) |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[tr1 w1 vs1] [Hscr1 [Htr [Hw Hvs]]]];
        cbn in Htr, Hw, Hvs;
        destruct tr1 as [| | | | | | | | | | | id1 fields1 |]; unfold cty_alpha_eq in Htr; cbn in Htr; try discriminate;
        inversion Htr as [[Hid Hfs]]; subst id1;
        assert (Hfs_a : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2) fields1 fields) by
          (clear - Hfs; revert fields Hfs; induction fields1 as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs; cbn in *; try discriminate;
           [apply Forall2_nil | inversion Hfs; apply Forall2_cons; [repeat split; unfold cty_alpha_eq; congruence | apply IH; congruence]]);
        assert (Hlen_fs : length bs = length fields1) by (rewrite Hlen_fs_eq; symmetry; apply Forall2_length in Hfs_a; exact Hfs_a);
        assert (Hmot1 : CTypeDemand env1 mot v_mot) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hmot]);
        destruct (record_extend_demand_rel D env bs fields body_env env1 fields1 Hext Hrel Hfs_a) as [body_env1 [Hext1 Hrel_ext]];
        destruct (IHCoreDerives2 _ Hrel_ext) as [[tb1 ub1 vb1] [Hbod1 [Htb [Hub Hvb]]]];
        cbn in Htb, Hub, Hvb;
        assert (Hallows1 : CRecordFieldAllows s fields1 (firstn (length fields1) ub1)) by
          (assert (Hfa : Forall2 (@allows D) (firstn (length fields) ub1) (firstn (length fields) u_b)) by
             (apply branch_rel_allows in Hub; clear - Hub; revert ub1 u_b Hub;
              induction (length fields) as [| n IH]; intros [| a u1] [| b u2] H; cbn;
              try apply Forall2_nil; inversion H; subst; apply Forall2_cons; [assumption | apply IH; assumption]);
           rewrite (Forall2_length Hfs_a);
           eapply record_allows_mono; [exact Hfa_rec | exact Hfa | exact Hfs_a]);
        eexists; split; [| split; [| split]];
        [ eapply CoreMatchRecord; [exact Hsne | exact Hscr1 | exact Hmot1 | exact Hlen_fs | exact Hext1 | exact Hbod1
                                  | eapply cty_alpha_eq_trans; [exact Htb | rewrite (Forall2_length Hfs_a); exact Htb_eq]
                                  | exact Hallows1]
        | apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_add; [apply branch_rel_scale; exact Hw |];
          rewrite (Forall2_length Hfs_a); unfold branch_rel in *;
          destruct (grade_join D); [| rewrite Hub; reflexivity];
          (clear - Hub; revert ub1 u_b Hub; induction (length fields) as [| n IH]; intros [| a u1] [| b u2] H; cbn;
           try exact H; try apply Forall2_nil; inversion H; subst; apply IH; assumption)
        | cbn [ctype_demand_row]; apply branch_rel_refl ]
    end.
  - (* CoreSubgrade *)
    lazymatch goal with
    | Hsub : Subty env actual target, Hvt : CTypeDemand env target vt |- _ =>
        destruct (IHCoreDerives _ Hrel) as [[act1 u1 v1] [Hbod1 [Hact [Hu Hv]]]];
        cbn in Hact, Hu, Hv;
        assert (Hvt1 : CTypeDemand env1 target vt) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hvt]);
        assert (Hsub1 : Subty env1 act1 target) by
          (eapply Subty_alpha; [exact Hsub | apply cenv_alpha_eq_sym; exact Halpha | apply cty_alpha_eq_sym; exact Hact | apply cty_alpha_eq_refl]);
        eexists; split; [| split; [| split]];
        [ eapply CoreSubgrade; [exact Hbod1 | exact Hsub1 | exact Hvt1]
        | apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; exact Hu
        | cbn [ctype_demand_row]; apply branch_rel_refl ]
    end.
  - (* CoreFix *)
    lazymatch goal with
    | Hvmot : CTypeDemand _ mot v_mot,
      Htb_eq : cty_alpha_eq t_b (subst_cidx_in_cty 0 (CIdxLit 0) mot),
      Htst_eq : cty_alpha_eq t_st (spec_fix_step_cty mot),
      Hs0 : allows (nth_grade u_st 0) s_rec,
      Hs1 : allows (nth_grade u_st 1) s_rec,
      Hfix : fix_recurrence_ok s_rec (tl (tl u_st)),
      Hres : res_ty = spec_fix_subj_cty scrut mot |- _ =>
        destruct (IHCoreDerives1 _ Hrel) as [[ts1 us1 vs1] [Hscr1 [Hts [Hus Hvs]]]];
        cbn in Hts, Hus, Hvs; destruct ts1; unfold cty_alpha_eq in Hts; cbn in Hts; try discriminate;
        assert (Hvmot1 : CTypeDemand ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env1) |} :: env1) mot v_mot) by
          (eapply CTypeDemand_alpha; [apply cty_alpha_eq_refl | | exact Hvmot]; constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_sym; exact Halpha]);
        destruct (IHCoreDerives2 _ Hrel) as [[tb1 ub1 vb1] [Hbas1 [Htb [Hub Hvb]]]];
        cbn in Htb, Hub, Hvb;
        assert (Hrel_n : cenv_demand_rel
                           ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env1) |} :: env1)
                           ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env)) by
          (rewrite Hlen; apply cenv_demand_rel_cons_same; [exact Hrel | apply cty_alpha_eq_refl | rewrite <- Hlen; apply CTypeNat]);
        assert (Hrel_nr : cenv_demand_rel
                            ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
                             {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env1) |} :: env1)
                            ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
                             {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env)) by
          (apply cenv_demand_rel_cons_same; [exact Hrel_n | apply cty_alpha_eq_refl | exact Hvmot1]);
        destruct (IHCoreDerives3 _ Hrel_nr) as [[tst1 ust1 vst1] [Hst1 [Htst [Hust Hvst]]]];
        cbn in Htst, Hust, Hvst;
        assert (Hfix1 : fix_recurrence_ok s_rec (tl (tl ust1))) by
          (unfold fix_recurrence_ok in *;
           destruct (vec_is_zero (tl (tl u_st))) eqn:Ez;
           [ rewrite (branch_rel_is_zero D (erasure_allows_zero_eq D ED) (tl (tl ust1)) (tl (tl u_st)) (branch_rel_tl D _ _ (branch_rel_tl D _ _ Hust)) Ez); exact I
           | destruct (vec_is_zero (tl (tl ust1))); [exact I | exact Hfix] ]);
        eexists; split; [| split; [| split]];
        [ eapply CoreFix; [exact Hscr1 | exact Hvmot1 | exact Hbas1 | eapply cty_alpha_eq_trans; [exact Htb | exact Htb_eq]
                          | exact Hst1 | eapply cty_alpha_eq_trans; [exact Htst | exact Htst_eq]
                          | eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hust) | exact Hs0]
                          | eapply allows_trans; [exact (branch_rel_nth D _ _ 1 Hust) | exact Hs1]
                          | exact Hfix1 | assumption | exact Hres]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; apply branch_rel_add; [exact Hus | apply branch_rel_add; [exact Hub | apply branch_rel_scale; apply branch_rel_tl, branch_rel_tl; exact Hust]]
        | cbn [ctype_demand_row]; apply branch_rel_add; [apply branch_rel_refl | apply branch_rel_scale; exact Hus] ]
    end.
  - (* CRecordElemNil *)
    exists (vec_zero (length env1)), (vec_zero (length env1)); split; [| split];
    [ apply CRecordElemNil | rewrite Hlen; apply branch_rel_refl | rewrite Hlen; apply branch_rel_refl ].
  - (* CRecordElemCons *)
    lazymatch goal with
    | Htv_eq : cty_alpha_eq t_v ft, Hdt : CTypeDemand env ft dt |- _ =>
        destruct (IHCoreDerives _ Hrel) as [[tv1 uv1 vv1] [Hv1 [Htv [Huv Hvv]]]];
        assert (Hdt1 : CTypeDemand env1 ft dt) by (eapply CTypeDemand_alpha_env; [apply cenv_alpha_eq_sym; exact Halpha | exact Hdt]);
        destruct (IHCoreDerives0 _ Hrel) as [ur1 [vr1 [Hrest [Hur Hvr]]]];
        cbn in Htv, Huv, Hvv;
        eexists (vec_add (vec_scale fg uv1) ur1), (vec_add dt vr1); split; [| split];
        [ eapply CRecordElemCons; [exact Hv1 | eapply cty_alpha_eq_trans; [exact Htv | exact Htv_eq] | exact Hdt1 | exact Hrest]
        | apply branch_rel_add; [apply branch_rel_scale; exact Huv | exact Hur]
        | apply branch_rel_add; [apply branch_rel_refl | exact Hvr] ]
    end.
Qed.

Local Arguments Nat.ltb !_ !_ : simpl nomatch.
Local Arguments Nat.eqb !_ !_ : simpl nomatch.

Lemma cenv_nat_safe_tl : forall (D : JoinDomain) e (env_a : cenv D),
  cenv_nat_safe (e :: env_a) (S (length env_a)) ->
  cenv_nat_safe env_a (length env_a).
Proof.
  intros D e env_a H x ex Hlt Hl.
  exact (H (S x) ex ltac:(cbn; lia) Hl).
Qed.

Lemma cenv_nat_safe_skipn : forall (D : JoinDomain) n (env_a : cenv D),
  cenv_nat_safe env_a (length env_a) ->
  cenv_nat_safe (skipn n env_a) (length (skipn n env_a)).
Proof.
  intros D n. induction n as [| n IH]; intros [| e rest] Hsafe; cbn; try exact Hsafe.
  apply IH. apply cenv_nat_safe_tl in Hsafe. exact Hsafe.
Qed.

Lemma cdemand_nat_safe_erase : forall (D : JoinDomain) (b : cbinding D) env_b,
  erase_hints (cannotation b) = CNat ->
  (forall env i d, CIdxDemand env i d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cidx_uses_kinds true false false false false (length env_a) i = false) /\
  (forall env T d, CTypeDemand env T d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cty_uses_kinds true false false false false false false (length env_a) T = false).
Proof.
  intros D b env_b Hb.
  assert (Hidx : forall env i d, CIdxDemand env i d ->
    forall env_a, env = env_a ++ b :: env_b ->
      cidx_uses_kinds true false false false false (length env_a) i = false).
  { intros env i d H. induction H; intros env_a Henv; subst env; cbn; try reflexivity;
      try (rewrite (IHCIdxDemand1 _ eq_refl), (IHCIdxDemand2 _ eq_refl); reflexivity);
      try (apply (IHCIdxDemand _ eq_refl)).
    - destruct (Nat.eq_dec b0 (length env_a)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec p (length env_a)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec p (length env_a)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite Hb in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec s (length env_a)) as [-> | Hne].
      + unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
        inversion H; subst e. unfold cty_alpha_eq in H0; rewrite erase_hints_ren, Hb in H0; cbn in H0; discriminate.
      + apply Nat.eqb_neq in Hne. rewrite Hne.
        pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hl1.
        pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hr1.
        cbn [length] in Hl1, Hr1. rewrite Hl1, Hr1. reflexivity. }
  split; [exact Hidx |].
  intros env T d HT.
  induction HT using CTypeDemand_ind_mut with
    (P := fun env T d _ => forall env_a, env = env_a ++ b :: env_b ->
      cty_uses_kinds true false false false false false false (length env_a) T = false)
    (P0 := fun env fs df _ => forall env_a, env = env_a ++ b :: env_b ->
      Forall (fun '(_, _, ft) => cty_uses_kinds true false false false false false false (length env_a) ft = false) fs)
    (P1 := fun env ls dl _ => forall env_a, env = env_a ++ b :: env_b ->
      Forall (fun i => cidx_uses_kinds true false false false false (length env_a) i = false) ls);
    intros env_a Henv; subst env; cbn; try reflexivity;
    try (apply IHHT; reflexivity);
    try (rewrite (IHHT1 _ eq_refl), (IHHT2 _ eq_refl); reflexivity);
    try apply Forall_nil.
  - rewrite (IHHT _ eq_refl), (Hidx _ _ _ c _ eq_refl). reflexivity.
  - destruct (Nat.eq_dec x (length env_a)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    lazymatch goal with
    | Hlk : clookup _ _ = Some _, Ha : cty_alpha_eq _ _ |- _ =>
        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
        inversion Hlk; subst; unfold cty_alpha_eq in Ha; try rewrite erase_hints_ren in Ha; rewrite Hb in Ha; cbn in Ha; discriminate
    end.
  - destruct (Nat.eq_dec b0 (length env_a)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    lazymatch goal with
    | Hlk : clookup _ _ = Some _, Ha : cty_alpha_eq _ _ |- _ =>
        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
        inversion Hlk; subst; unfold cty_alpha_eq in Ha; try rewrite erase_hints_ren in Ha; rewrite Hb in Ha; cbn in Ha; discriminate
    end.
  - rewrite (IHHT1 _ eq_refl).
    exact (IHHT2 (_ :: env_a) eq_refl).
  - rewrite (IHHT1 _ eq_refl).
    exact (IHHT2 (_ :: env_a) eq_refl).
  - pose proof (IHHT _ eq_refl) as Hf. clear - Hf. induction fields as [| [[? ?] ?] ? IH]; cbn; inversion Hf; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
  - pose proof (IHHT _ eq_refl) as Hl. clear - Hl. induction indices as [| ? ? IH]; cbn; inversion Hl; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
  - apply Forall_cons; [exact (IHHT _ eq_refl) | exact (IHHT0 _ eq_refl)].
  - apply Forall_cons; [exact (Hidx _ _ _ c _ eq_refl) | exact (IHHT _ eq_refl)].
Qed.

Lemma cdemand_nat_safe : forall (D : JoinDomain) (b : cbinding D) env_b,
  cannotation b = CNat ->
  (forall env i d, CIdxDemand env i d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cidx_uses_kinds true false false false false (length env_a) i = false) /\
  (forall env T d, CTypeDemand env T d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cty_uses_kinds true false false false false false false (length env_a) T = false).
Proof.
  intros D b env_b Hb. apply cdemand_nat_safe_erase. rewrite Hb. reflexivity.
Qed.

Lemma ren_cty_r_var_no_use : forall (D : JoinDomain) (T : cty D) c y1 y2,
  cty_uses_var c T = false ->
  ren_cty (r_var c y1) T = ren_cty (r_var c y2) T.
Proof.
  intros D T.
  Ltac solve_r_var_ne c :=
    nat_bool_hyps;
    lazymatch goal with
    | H : (?v =? c) = false |- _ =>
        apply Nat.eqb_neq in H; destruct (lt_eq_lt_dec v c) as [[Hlt | ->] | Hgt];
        [rewrite !r_var_lt by exact Hlt | contradiction | rewrite !r_var_gt by exact Hgt]; reflexivity
    | H : ?v <> c |- _ =>
        destruct (lt_eq_lt_dec v c) as [[Hlt | ->] | Hgt];
        [rewrite !r_var_lt by exact Hlt | contradiction | rewrite !r_var_gt by exact Hgt]; reflexivity
    end.
  assert (Hci : forall (i : cidx D) c y1 y2, cidx_uses_var c i = false -> ren_cidx (r_var c y1) i = ren_cidx (r_var c y2) i).
  { induction i; intros c y1 y2 Hi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 c y1 y2 H1), (IHi2 c y1 y2 H2); reflexivity);
      try (f_equal; apply (IHi c y1 y2 Hi));
      try solve_r_var_ne c.
    - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2]; nat_bool_hyps.
      change (ren_shift (r_var c y1)) with (r_var (S c) y1).
      change (ren_shift (r_var c y2)) with (r_var (S c) y2).
      rewrite (IHi1 (S c) y1 y2 H2), (IHi2 (S c) y1 y2 H3).
      f_equal; solve_r_var_ne c. }
  induction T using cty_ind_nested; intros c y1 y2 HT; cbn in *; try reflexivity;
    try (f_equal; apply (IHT c y1 y2 HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 c y1 y2 H1), (IHT2 c y1 y2 H2); reflexivity);
    try (f_equal; solve_r_var_ne c).
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT c y1 y2 H1), (Hci len c y1 y2 H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 c y1 y2 H1).
    change (ren_shift (r_var c y1)) with (r_var (S c) y1).
    change (ren_shift (r_var c y2)) with (r_var (S c) y2).
    rewrite (IHT2 (S c) y1 y2 H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 c y1 y2 H1).
    change (ren_shift (r_var c y1)) with (r_var (S c) y1).
    change (ren_shift (r_var c y2)) with (r_var (S c) y2).
    rewrite (IHT2 (S c) y1 y2 H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 Hr]. rewrite (H2 c y1 y2 H1), (IHf H3 Hr). reflexivity.
  - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 Hr]. rewrite (Hci idx c y1 y2 H1), (IH Hr). reflexivity.
Qed.

Lemma cty_uses_kinds_subst_var_0 : forall (D : JoinDomain) (T : cty D) y k,
  y <> k ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_var_in_cty 0 y T) = false.
Proof.
  intros D T y k Hne H. unfold subst_var_in_cty. eapply cty_uses_kinds_ren_gen; [| exact H].
  intros [| z] Hz; cbn; lia.
Qed.

Lemma cty_uses_kinds_unshift_0 : forall (D : JoinDomain) (T : cty D) k,
  cty_uses_var 0 T = false ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (unshift_cty 0 T) = false.
Proof.
  intros D T k H0 H. unfold unshift_cty.
  change (ren_cty (Nat.iter 0 ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) T) with (ren_cty (r_var 0 0) T).
  rewrite (ren_cty_r_var_no_use D T 0 0 (S k) H0).
  exact (cty_uses_kinds_subst_var_0 D T (S k) k ltac:(lia) H).
Qed.

Ltac solve_elim_var v c k Hceq Hsk :=
  destruct (v <? c) eqn:Elt; [apply Nat.ltb_lt in Elt; apply Nat.eqb_neq; lia |];
  destruct (Nat.eq_dec v c) as [Heq_vc | Hne];
  [ rewrite Heq_vc, Nat.eqb_refl; cbn;
    destruct (Nat.eq_dec k 0) as [Hk0 | Hknz];
    [ assert (Hceq' : c = k) by lia;
      exfalso; pose proof (Hceq Hceq') as Hbad; rewrite Heq_vc, Nat.eqb_refl in Hbad; discriminate
    | apply Nat.eqb_neq; lia ]
  | rewrite (proj2 (Nat.eqb_neq _ _) Hne); apply Nat.eqb_neq;
    apply Nat.eqb_neq in Hsk; apply Nat.ltb_ge in Elt; lia ].

Lemma cty_uses_kinds_subst_cidx_0 : forall (D : JoinDomain) (T : cty D) (val : cidx D) k,
  cidx_uses_kinds true false false false false k val = false ->
  (k = 0 -> cty_uses_kinds true false false false false false false 0 T = false) ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_cidx_in_cty 0 val T) = false.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) (val : cidx D) c k,
    c <= k ->
    (c = k -> cty_uses_kinds true false false false false false false c T0 = false) ->
    cty_uses_kinds true false false false false false false (S k) T0 = false ->
    cidx_uses_kinds true false false false false k val = false ->
    cty_uses_kinds true false false false false false false k (subst_cidx_in_cty c val T0) = false).
  { induction T0 using cty_ind_nested; intros val c k Hck Hceq Hsk Hval; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hck Hceq Hsk Hval));
      try (apply orb_false_iff in Hsk as [Hsk1 Hsk2];
           rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk1 Hval),
                   (IHT0_2 _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk2 Hval); reflexivity).
    - apply orb_false_iff in Hsk as [Hsk1 Hsk2].
      rewrite (IHT0 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk1 Hval).
      rewrite (cidx_uses_kinds_subst_cidx_ge D len val c k Hck (fun Heq => match Heq in (_ = k') return cidx_uses_kinds true false false false false k' len = false with eq_refl => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq)) end) Hsk2 Hval).
      reflexivity.
    - solve_elim_var x c k Hceq Hsk.
    - solve_elim_var b c k Hceq Hsk.
    - apply orb_false_iff in Hsk as [Hsk1 Hsk2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk1 Hval).
      rewrite (IHT0_2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) Hsk2 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity.
    - apply orb_false_iff in Hsk as [Hsk1 Hsk2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk1 Hval).
      rewrite (IHT0_2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia) (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) Hsk2 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hsk as [Hsk1 Hsk2].
      rewrite (H2 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk1 Hval),
              (IHf H3 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk2). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [Hsk1 Hsk2].
      rewrite (cidx_uses_kinds_subst_cidx_ge D idx val c k Hck (fun Heq => match Heq in (_ = k') return cidx_uses_kinds true false false false false k' idx = false with eq_refl => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq)) end) Hsk1 Hval),
              (IH (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) Hsk2). reflexivity. }
  intros val k Hval H0 Hsk. exact (Hgen T val 0 k ltac:(lia) (fun Heq => H0 (eq_sym Heq)) Hsk Hval).
Qed.

Lemma cidx_uses_kinds_idx_true : forall (D : JoinDomain) (i : cidx D) u f s sc k,
  cidx_uses_kinds false u f s sc k i = false ->
  cidx_uses_kinds true u f s sc k i = false.
Proof.
  intros D i u f s sc. induction i; intros k H; cbn in *; try reflexivity; try assumption;
    try (apply orb_false_iff in H as [H1 H2]; rewrite (IHi1 _ H1), (IHi2 _ H2); reflexivity);
    try (apply (IHi _ H)).
  apply orb_false_iff in H as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
  rewrite H1, (IHi1 _ H2), (IHi2 _ H3). reflexivity.
Qed.

Lemma cidx_uses_kinds_subst_tvar_ge : forall (D : JoinDomain) (i : cidx D) c k,
  c <= k ->
  (c = k -> cidx_uses_kinds true false false false false c i = false) ->
  cidx_uses_kinds true false false false false (S k) i = false ->
  cidx_uses_kinds true false false false false k (subst_tvar_in_cidx c i) = false.
Proof.
  intros D i. induction i; intros c k Hck Hceq Hsk; cbn in *; try reflexivity;
    try (apply orb_false_iff in Hsk as [H1 H2];
         rewrite (IHi1 _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1),
                 (IHi2 _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2); reflexivity);
    try (apply (IHi _ _ Hck Hceq Hsk));
    try solve_elim_var b c k Hceq Hsk;
    try solve_elim_var p c k Hceq Hsk.
  apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
  assert (Hs : ((if s <? c then s else if s =? c then 0 else s - 1) =? k) = false) by
    solve_elim_var s c k (fun Heq => proj1 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))))) H1.
  rewrite Hs.
  rewrite (IHi1 (S c) (S k) ltac:(lia) (fun Heq => proj2 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))))) H2),
          (IHi2 (S c) (S k) ltac:(lia) (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H3).
  reflexivity.
Qed.

Lemma cty_uses_kinds_subst_tvar_0 : forall (D : JoinDomain) (T U : cty D) k,
  cty_uses_kinds true false false false false false false k U = false ->
  (k = 0 -> cty_uses_kinds false true false false false false false 0 T = false) ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_tvar_in_cty 0 U T) = false.
Proof.
  intros D T.
  assert (Hgen : forall (T0 U : cty D) c k,
    c <= k ->
    (c = k -> cty_uses_kinds false true false false false false false c T0 = false) ->
    cty_uses_kinds true false false false false false false (S k) T0 = false ->
    cty_uses_kinds true false false false false false false k U = false ->
    cty_uses_kinds true false false false false false false k (subst_tvar_in_cty c U T0) = false).
  { induction T0 using cty_ind_nested; intros U c k Hck Hceq Hsk HU; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hck Hceq Hsk HU));
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
                   (IHT0_2 _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 HU); reflexivity).
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
              (cidx_uses_kinds_subst_tvar_ge D len c k Hck (fun Heq => cidx_uses_kinds_idx_true _ _ _ _ _ _ _ (proj2 (proj1 (orb_false_iff _ _) (Hceq Heq)))) H2).
      reflexivity.
    - destruct (Nat.eq_dec x c) as [-> | Hne]; [rewrite Nat.eqb_refl; exact HU |].
      rewrite (proj2 (Nat.eqb_neq _ _) Hne).
      destruct (x <? c) eqn:Elt; [apply Nat.ltb_lt in Elt; apply Nat.eqb_neq; lia |].
      apply Nat.ltb_ge in Elt; apply Nat.eqb_neq; apply Nat.eqb_neq in Hsk; lia.
    - solve_elim_var b c k Hceq Hsk.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU).
      rewrite (IHT0_2 (lift_cty 0 1 U) (S c) (S k) ltac:(lia) (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2 (cty_uses_kinds_lift_shift D U k HU)).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU).
      rewrite (IHT0_2 (lift_cty 0 1 U) (S c) (S k) ltac:(lia) (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2 (cty_uses_kinds_lift_shift D U k HU)).
      reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hsk as [H1 H2'].
      rewrite (H2 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
              (IHf H3 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2'). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [H1 H2].
      rewrite (cidx_uses_kinds_subst_tvar_ge D idx c k Hck (fun Heq => cidx_uses_kinds_idx_true _ _ _ _ _ _ _ (proj1 (proj1 (orb_false_iff _ _) (Hceq Heq)))) H1),
              (IH (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2). reflexivity. }
  intros U k HU H0 Hsk. exact (Hgen T U 0 k ltac:(lia) (fun Heq => H0 (eq_sym Heq)) Hsk HU).
Qed.

Lemma cty_uses_kinds_subst_pair_0 : forall (D : JoinDomain) (T : cty D) (fi si : cidx D) k,
  cidx_uses_kinds true false false false false k fi = false ->
  cidx_uses_kinds true false false false false k si = false ->
  (k = 0 -> cty_uses_kinds true false false false true true false 0 T = false) ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_pair_cty 0 fi si T) = false.
Proof.
  intros D T.
  assert (Hci : forall (i fi si : cidx D) c k,
    c <= k ->
    (c = k -> cidx_uses_kinds true false true true false c i = false) ->
    cidx_uses_kinds true false false false false (S k) i = false ->
    cidx_uses_kinds true false false false false k fi = false ->
    cidx_uses_kinds true false false false false k si = false ->
    cidx_uses_kinds true false false false false k (subst_pair_cidx c fi si i) = false).
  { induction i; intros fi si c k Hck Hceq Hsk Hfi Hsi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHi1 _ _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
                   (IHi2 _ _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 Hfi Hsi); reflexivity);
      try (apply (IHi _ _ _ _ Hck Hceq Hsk Hfi Hsi));
      try solve_elim_var b c k Hceq Hsk.
    - destruct (Nat.eq_dec p c) as [-> | Hne]; [rewrite Nat.eqb_refl; exact Hfi |].
      rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn.
      destruct (p <? c) eqn:Elt; [apply Nat.ltb_lt in Elt; apply Nat.eqb_neq; lia |].
      apply Nat.ltb_ge in Elt; apply Nat.eqb_neq; apply Nat.eqb_neq in Hsk; lia.
    - destruct (Nat.eq_dec p c) as [-> | Hne]; [rewrite Nat.eqb_refl; exact Hsi |].
      rewrite (proj2 (Nat.eqb_neq _ _) Hne). cbn.
      destruct (p <? c) eqn:Elt; [apply Nat.ltb_lt in Elt; apply Nat.eqb_neq; lia |].
      apply Nat.ltb_ge in Elt; apply Nat.eqb_neq; apply Nat.eqb_neq in Hsk; lia.
    - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
      assert (Hs : ((if s <? c then s else if s =? c then 0 else s - 1) =? k) = false) by
        solve_elim_var s c k (fun Heq => proj1 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))))) H1.
      rewrite Hs.
      rewrite (IHi1 (lift_cidx 0 1 fi) (lift_cidx 0 1 si) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))))) H2
                 (cidx_uses_kinds_lift_shift D fi k Hfi) (cidx_uses_kinds_lift_shift D si k Hsi)),
              (IHi2 (lift_cidx 0 1 fi) (lift_cidx 0 1 si) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H3
                 (cidx_uses_kinds_lift_shift D fi k Hfi) (cidx_uses_kinds_lift_shift D si k Hsi)).
      reflexivity. }
  assert (Hgen : forall (T0 : cty D) (fi si : cidx D) c k,
    c <= k ->
    (c = k -> cty_uses_kinds true false false false true true false c T0 = false) ->
    cty_uses_kinds true false false false false false false (S k) T0 = false ->
    cidx_uses_kinds true false false false false k fi = false ->
    cidx_uses_kinds true false false false false k si = false ->
    cty_uses_kinds true false false false false false false k (subst_pair_cty c fi si T0) = false).
  { induction T0 using cty_ind_nested; intros fi si c k Hck Hceq Hsk Hfi Hsi; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ _ Hck Hceq Hsk Hfi Hsi));
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHT0_1 _ _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
                   (IHT0_2 _ _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 Hfi Hsi); reflexivity);
      try solve_elim_var x c k Hceq Hsk;
      try solve_elim_var b c k Hceq Hsk.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0 _ _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
              (Hci len fi si c k Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 Hfi Hsi).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
              (IHT0_2 (lift_cidx 0 1 fi) (lift_cidx 0 1 si) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2
                 (cidx_uses_kinds_lift_shift D fi k Hfi) (cidx_uses_kinds_lift_shift D si k Hsi)).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
              (IHT0_2 (lift_cidx 0 1 fi) (lift_cidx 0 1 si) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2
                 (cidx_uses_kinds_lift_shift D fi k Hfi) (cidx_uses_kinds_lift_shift D si k Hsi)).
      reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hsk as [H1 H2'].
      rewrite (H2 _ _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
              (IHf H3 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2'). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [H1 H2].
      rewrite (Hci idx fi si c k Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hfi Hsi),
              (IH (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2). reflexivity. }
  intros fi si k Hfi Hsi H0 Hsk. exact (Hgen T fi si 0 k ltac:(lia) (fun Heq => H0 (eq_sym Heq)) Hsk Hfi Hsi).
Qed.

Lemma cty_uses_kinds_subst_box_nat_0 : forall (D : JoinDomain) (T : cty D) q (val : cidx D) k,
  cidx_uses_kinds true false false false false k val = false ->
  (k = 0 -> cty_uses_kinds true false false true false false false 0 T = false) ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_box_nat_cty 0 q val T) = false.
Proof.
  intros D T q.
  assert (Hci : forall (i val : cidx D) c k,
    c <= k ->
    (c = k -> cidx_uses_kinds true true false false false c i = false) ->
    cidx_uses_kinds true false false false false (S k) i = false ->
    cidx_uses_kinds true false false false false k val = false ->
    cidx_uses_kinds true false false false false k (subst_box_nat_cidx c q val i) = false).
  { induction i; intros val c k Hck Hceq Hsk Hval; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHi1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
                   (IHi2 _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 Hval); reflexivity);
      try (apply (IHi _ _ _ Hck Hceq Hsk Hval));
      try solve_elim_var p c k Hceq Hsk.
    - destruct (Nat.eq_dec b c) as [-> | Hne]; [rewrite Nat.eqb_refl; cbn; exact Hval |].
      rewrite (proj2 (Nat.eqb_neq _ _) Hne).
      destruct (b <? c) eqn:Elt; cbn; [apply Nat.ltb_lt in Elt; apply Nat.eqb_neq; lia |].
      apply Nat.ltb_ge in Elt; apply Nat.eqb_neq; apply Nat.eqb_neq in Hsk; lia.
    - apply orb_false_iff in Hsk as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
      assert (Hs : ((if s <? c then s else if s =? c then 0 else s - 1) =? k) = false) by
        solve_elim_var s c k (fun Heq => proj1 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))))) H1.
      rewrite Hs.
      rewrite (IHi1 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (proj1 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))))) H2
                 (cidx_uses_kinds_lift_shift D val k Hval)),
              (IHi2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H3
                 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity. }
  assert (Hgen : forall (T0 : cty D) (val : cidx D) c k,
    c <= k ->
    (c = k -> cty_uses_kinds true false false true false false false c T0 = false) ->
    cty_uses_kinds true false false false false false false (S k) T0 = false ->
    cidx_uses_kinds true false false false false k val = false ->
    cty_uses_kinds true false false false false false false k (subst_box_nat_cty c q val T0) = false).
  { induction T0 using cty_ind_nested; intros val c k Hck Hceq Hsk Hval; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hck Hceq Hsk Hval));
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
                   (IHT0_2 _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 Hval); reflexivity);
      try solve_elim_var x c k Hceq Hsk;
      try solve_elim_var b c k Hceq Hsk.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
              (Hci len val c k Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 Hval).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
              (IHT0_2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2
                 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
              (IHT0_2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2
                 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hsk as [H1 H2'].
      rewrite (H2 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
              (IHf H3 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2'). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [H1 H2].
      rewrite (Hci idx val c k Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 Hval),
              (IH (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2). reflexivity. }
  intros val k Hval H0 Hsk. exact (Hgen T val 0 k ltac:(lia) (fun Heq => H0 (eq_sym Heq)) Hsk Hval).
Qed.

Lemma cty_uses_kinds_subst_box_ty_0 : forall (D : JoinDomain) (T U : cty D) q k,
  cty_uses_kinds true false false false false false false k U = false ->
  (k = 0 -> cty_uses_kinds true false true false false false false 0 T = false) ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_box_ty_cty 0 q U T) = false.
Proof.
  intros D T U q.
  assert (Hgen : forall (T0 U0 : cty D) c k,
    c <= k ->
    (c = k -> cty_uses_kinds true false true false false false false c T0 = false) ->
    cty_uses_kinds true false false false false false false (S k) T0 = false ->
    cty_uses_kinds true false false false false false false k U0 = false ->
    cty_uses_kinds true false false false false false false k (subst_box_ty_cty c q U0 T0) = false).
  { induction T0 using cty_ind_nested; intros U0 c k Hck Hceq Hsk HU; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hck Hceq Hsk HU));
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
                   (IHT0_2 _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2 HU); reflexivity);
      try solve_elim_var x c k Hceq Hsk.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
              (cidx_uses_kinds_subst_tvar_ge D len c k Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2).
      reflexivity.
    - destruct (Nat.eq_dec b c) as [-> | Hne]; [rewrite Nat.eqb_refl; cbn; exact HU |].
      rewrite (proj2 (Nat.eqb_neq _ _) Hne).
      destruct (b <? c) eqn:Elt; cbn; [apply Nat.ltb_lt in Elt; apply Nat.eqb_neq; lia |].
      apply Nat.ltb_ge in Elt; apply Nat.eqb_neq; apply Nat.eqb_neq in Hsk; lia.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
              (IHT0_2 (lift_cty 0 1 U0) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2
                 (cty_uses_kinds_lift_shift D U0 k HU)).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
              (IHT0_2 (lift_cty 0 1 U0) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia)))) H2
                 (cty_uses_kinds_lift_shift D U0 k HU)).
      reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hsk as [H1 H2'].
      rewrite (H2 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1 HU),
              (IHf H3 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2'). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [H1 H2].
      rewrite (cidx_uses_kinds_subst_tvar_ge D idx c k Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) H1),
              (IH (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) H2). reflexivity. }
  intros k HU H0 Hsk. exact (Hgen T U 0 k ltac:(lia) (fun Heq => H0 (eq_sym Heq)) Hsk HU).
Qed.

Fixpoint cidx_case_branch_nat {D : JoinDomain} (is_left : bool) (k : nat) (i : cidx D) : bool :=
  match i with
  | CIdxVar _ | CIdxLit _ | CIdxUnbox _ | CIdxFst _ | CIdxSnd _ => true
  | CIdxAdd l r => cidx_case_branch_nat is_left k l && cidx_case_branch_nat is_left k r
  | CIdxProm _ i' => cidx_case_branch_nat is_left k i'
  | CIdxCase s l r =>
      (if s =? k then negb (cidx_uses_kinds true false false false false 0 (if is_left then l else r)) else true)
      && cidx_case_branch_nat is_left (S k) l && cidx_case_branch_nat is_left (S k) r
  end.

Fixpoint cty_case_branch_nat {D : JoinDomain} (is_left : bool) (k : nat) (T : cty D) : bool :=
  match T with
  | CNat | CBool | CUniv _ | CTVar _ | CTUnbox _ => true
  | CVec elem len => cty_case_branch_nat is_left k elem && cidx_case_branch_nat is_left k len
  | CTProm _ inner | CBox _ inner => cty_case_branch_nat is_left k inner
  | CPi _ _ _ dom cod | CSigma _ _ dom cod =>
      cty_case_branch_nat is_left k dom && cty_case_branch_nat is_left (S k) cod
  | CSum l r => cty_case_branch_nat is_left k l && cty_case_branch_nat is_left k r
  | CRecord _ fields =>
      (fix go_fs (fs : list (nat * grade D * cty D)) : bool :=
         match fs with
         | [] => true
         | (_, _, ft) :: rest => cty_case_branch_nat is_left k ft && go_fs rest
         end) fields
  | CInd _ indices =>
      (fix go_is (ls : list (cidx D)) : bool :=
         match ls with
         | [] => true
         | hd :: rest => cidx_case_branch_nat is_left k hd && go_is rest
         end) indices
  end.

Lemma cty_uses_var_case_branch_nat : forall (D : JoinDomain) (T : cty D) is_left k,
  cty_uses_var k T = false ->
  cty_case_branch_nat is_left k T = true.
Proof.
  intros D T is_left.
  assert (Hci : forall (i : cidx D) k, cidx_uses_var k i = false -> cidx_case_branch_nat is_left k i = true).
  { induction i; intros k Hi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ H1), (IHi2 _ H2); reflexivity);
      try (apply (IHi _ Hi)).
    apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
    rewrite H1, (IHi1 _ H2), (IHi2 _ H3). reflexivity. }
  induction T using cty_ind_nested; intros k HT; cbn in *; try reflexivity;
    try (apply (IHT _ HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ H1), (IHT2 _ H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT _ H1), (Hci len _ H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 Hr].
    rewrite (H2 _ H1), (IHf H3 Hr). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 Hr].
    rewrite (Hci idx _ H1), (IH Hr). reflexivity.
Qed.

Lemma cdemand_case_branch_nat : forall (D : JoinDomain) (b : cbinding D) env_b (is_left : bool) A B,
  cty_alpha_eq (cannotation b) (CSum A B) ->
  (if is_left then erase_hints A = CNat else erase_hints B = CNat) ->
  (forall env i d, CIdxDemand env i d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cidx_case_branch_nat is_left (length env_a) i = true) /\
  (forall env T d, CTypeDemand env T d ->
     forall env_a, env = env_a ++ b :: env_b ->
       cty_case_branch_nat is_left (length env_a) T = true).
Proof.
  intros D b env_b is_left A B Hb Hab.
  assert (Hidx : forall env i d, CIdxDemand env i d ->
    forall env_a, env = env_a ++ b :: env_b ->
      cidx_case_branch_nat is_left (length env_a) i = true).
  { intros env i d H. induction H; intros env_a Henv; subst env; cbn; try reflexivity;
      try (rewrite (IHCIdxDemand1 _ eq_refl), (IHCIdxDemand2 _ eq_refl); reflexivity);
      try (apply (IHCIdxDemand _ eq_refl)).
    destruct (Nat.eq_dec s (length env_a)) as [-> | Hne].
    - rewrite Nat.eqb_refl.
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0, Hb.
      rewrite erase_hints_ren, Hb in H0; cbn in H0. inversion H0 as [[Ha_eq Hb_eq]].
      destruct is_left.
      + assert (Hc : cidx_uses_kinds true false false false false 0 l = false).
        { refine (proj1 (cdemand_nat_safe_erase D {| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} (env_a ++ b :: env_b) _) _ _ _ H1 [] eq_refl).
          cbn. rewrite <- Ha_eq, Hab. reflexivity. }
        rewrite Hc; cbn [negb andb].
        pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hl1.
        pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hr1.
        cbn [length] in Hl1, Hr1; rewrite Hl1, Hr1; reflexivity.
      + assert (Hc : cidx_uses_kinds true false false false false 0 r = false).
        { refine (proj1 (cdemand_nat_safe_erase D {| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} (env_a ++ b :: env_b) _) _ _ _ H2 [] eq_refl).
          cbn. rewrite <- Hb_eq, Hab. reflexivity. }
        rewrite Hc; cbn [negb andb].
        pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hl1.
        pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hr1.
        cbn [length] in Hl1, Hr1; rewrite Hl1, Hr1; reflexivity.
    - rewrite (proj2 (Nat.eqb_neq _ _) Hne).
      pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hl1.
      pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hr1.
      cbn [length] in Hl1, Hr1; rewrite Hl1, Hr1; reflexivity. }
  split; [exact Hidx |].
  intros env T d HT.
  induction HT using CTypeDemand_ind_mut with
    (P := fun env T d _ => forall env_a, env = env_a ++ b :: env_b ->
      cty_case_branch_nat is_left (length env_a) T = true)
    (P0 := fun env fs df _ => forall env_a, env = env_a ++ b :: env_b ->
      Forall (fun '(_, _, ft) => cty_case_branch_nat is_left (length env_a) ft = true) fs)
    (P1 := fun env ls dl _ => forall env_a, env = env_a ++ b :: env_b ->
      Forall (fun i => cidx_case_branch_nat is_left (length env_a) i = true) ls);
    intros env_a Henv; subst env; cbn; try reflexivity;
    try (apply IHHT; reflexivity);
    try (rewrite (IHHT1 _ eq_refl), (IHHT2 _ eq_refl); reflexivity);
    try apply Forall_nil.
  - rewrite (IHHT _ eq_refl), (Hidx _ _ _ c _ eq_refl); reflexivity.
  - rewrite (IHHT1 _ eq_refl); exact (IHHT2 (_ :: env_a) eq_refl).
  - rewrite (IHHT1 _ eq_refl); exact (IHHT2 (_ :: env_a) eq_refl).
  - pose proof (IHHT _ eq_refl) as Hf; clear - Hf; induction fields as [| [[? ?] ?] ? IH]; cbn; inversion Hf; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
  - pose proof (IHHT _ eq_refl) as Hl; clear - Hl; induction indices as [| ? ? IH]; cbn; inversion Hl; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
  - apply Forall_cons; [exact (IHHT _ eq_refl) | exact (IHHT0 _ eq_refl)].
  - apply Forall_cons; [exact (Hidx _ _ _ c _ eq_refl) | exact (IHHT _ eq_refl)].
Qed.

Lemma cty_uses_kinds_subst_sum_0 : forall (D : JoinDomain) (T : cty D) is_left (val : cidx D) k,
  cidx_uses_kinds true false false false false k val = false ->
  (k = 0 -> cty_uses_kinds true false false false false false true 0 T = false) ->
  (k = 0 -> cty_case_branch_nat is_left 0 T = true) ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_sum_cty is_left 0 val T) = false.
Proof.
  intros D T is_left.
  assert (Hci : forall (i val : cidx D) c k,
    c <= k ->
    (c = k -> cidx_uses_kinds true false false false true c i = false) ->
    (c = k -> cidx_case_branch_nat is_left c i = true) ->
    cidx_uses_kinds true false false false false (S k) i = false ->
    cidx_uses_kinds true false false false false k val = false ->
    cidx_uses_kinds true false false false false k (subst_sum_cidx is_left c val i) = false).
  { intros i val c k Hck Hceq Hbr0 Hsk Hval.
    destruct (Nat.eq_dec (c + (k - c)) 0) as [Hz | Hnz].
    - assert (Hc0 : c = 0) by lia; assert (Hk0 : k = 0) by lia; subst c k.
      specialize (Hceq eq_refl); specialize (Hbr0 eq_refl). revert val Hceq Hbr0 Hsk Hval.
      induction i; intros val Hceq Hbr0 Hsk Hval; cbn in *; try reflexivity;
        try (apply orb_false_iff in Hceq as [Ha Hb]; apply andb_true_iff in Hbr0 as [Ba Bb];
             apply orb_false_iff in Hsk as [Sa Sb];
             rewrite (IHi1 val Ha Ba Sa Hval), (IHi2 val Hb Bb Sb Hval); reflexivity);
        try (apply (IHi val Hceq Hbr0 Hsk Hval));
        try (destruct (Nat.eqb_spec b 0) as [-> | Hne]; [cbn in Hceq; discriminate | rewrite (proj2 (Nat.ltb_ge b 0) ltac:(lia)); cbn; apply Nat.eqb_neq in Hsk; apply Nat.eqb_neq; lia]);
        try (destruct (Nat.eqb_spec p 0) as [-> | Hne]; [cbn in Hceq; discriminate | rewrite (proj2 (Nat.ltb_ge p 0) ltac:(lia)); cbn; apply Nat.eqb_neq in Hsk; apply Nat.eqb_neq; lia]).
      + apply orb_false_iff in Hceq as [H2 H3].
        apply andb_true_iff in Hbr0 as [B12 B3]; apply andb_true_iff in B12 as [B0 B2].
        apply orb_false_iff in Hsk as [S12 S3]; apply orb_false_iff in S12 as [S1 S2].
        destruct s; cbn in *.
        * assert (Hbr : cidx_uses_kinds true false false false false 1
                          (subst_sum_cidx is_left 1 (lift_cidx 0 1 val) (if is_left then i1 else i2)) = false).
          { destruct is_left;
              [apply (cidx_uses_kinds_subst_sum_cidx D true i1 (lift_cidx 0 1 val) 1 0 ltac:(lia) (cidx_uses_kinds_lift_shift D val 0 Hval) S2)
              |apply (cidx_uses_kinds_subst_sum_cidx D false i2 (lift_cidx 0 1 val) 1 0 ltac:(lia) (cidx_uses_kinds_lift_shift D val 0 Hval) S3)]. }
          eapply cidx_uses_kinds_subst_cidx_ge; [lia | | exact Hbr | exact Hval].
          intros _.
          assert (Hc : forall (u v : cidx D),
            cidx_uses_kinds true false false false false 0 u = false ->
            cidx_uses_kinds true false false false true 1 u = false ->
            cidx_case_branch_nat is_left 1 u = true ->
            cidx_uses_kinds true false false false false 0 v = false ->
            cidx_uses_kinds true false false false false 0 (subst_sum_cidx is_left 1 v u) = false).
          { intros u v Hu0 Hu1 Hbu Hv.
            assert (Hlift0 : forall (w : cidx D) (rho : nat -> nat) c, (forall y, rho y <> c) ->
              cidx_uses_kinds true false false false false c (ren_cidx rho w) = false).
            { induction w; intros rho c Hrho; cbn; try reflexivity;
                try (rewrite (IHw1 _ _ Hrho), (IHw2 _ _ Hrho); reflexivity);
                try (apply (IHw _ _ Hrho));
                try (apply Nat.eqb_neq; apply Hrho).
              rewrite (proj2 (Nat.eqb_neq _ _) (Hrho s)); cbn.
              assert (HrhoS : forall y, ren_shift rho y <> S c) by (intros [| y']; cbn; [lia | pose proof (Hrho y'); lia]).
              rewrite (IHw1 _ _ HrhoS), (IHw2 _ _ HrhoS); reflexivity. }
            assert (Hu : forall (u0 : cidx D) c0 (v0 : cidx D) k0,
              k0 < c0 ->
              cidx_uses_kinds true false false false false k0 u0 = false ->
              cidx_uses_kinds true false false false true c0 u0 = false ->
              cidx_case_branch_nat is_left c0 u0 = true ->
              cidx_uses_kinds true false false false false k0 v0 = false ->
              cidx_uses_kinds true false false false false k0 (subst_sum_cidx is_left c0 v0 u0) = false).
            { induction u0; intros c0 v0 k0 Hkc H0u Hcu Hbu0 Hv0; cbn in *; try reflexivity.
              - apply orb_false_iff in H0u as [A1 A2]; apply orb_false_iff in Hcu as [C1 C2];
                apply andb_true_iff in Hbu0 as [D1 D2];
                rewrite (IHu0_1 _ v0 k0 Hkc A1 C1 D1 Hv0), (IHu0_2 _ v0 k0 Hkc A2 C2 D2 Hv0); reflexivity.
              - apply (IHu0 _ v0 k0 Hkc H0u Hcu Hbu0 Hv0).
              - destruct (Nat.ltb_spec b c0); cbn; [exact H0u | destruct (Nat.eqb_spec b c0) as [-> | Hne]; [discriminate | cbn; apply Nat.eqb_neq; lia]].
              - destruct (Nat.ltb_spec p c0); cbn; [exact H0u | destruct (Nat.eqb_spec p c0) as [-> | Hne]; [discriminate | cbn; apply Nat.eqb_neq; lia]].
              - destruct (Nat.ltb_spec p c0); cbn; [exact H0u | destruct (Nat.eqb_spec p c0) as [-> | Hne]; [discriminate | cbn; apply Nat.eqb_neq; lia]].
              - apply orb_false_iff in H0u as [A12 A3]; apply orb_false_iff in A12 as [A1 A2].
                apply orb_false_iff in Hcu as [C2 C3].
                apply andb_true_iff in Hbu0 as [D12 D3]; apply andb_true_iff in D12 as [D0u D2'].
                destruct (Nat.eqb_spec s c0) as [-> | Hne]; cbn in *.
                + cbn in D0u; apply negb_true_iff in D0u.
                  assert (Hlift_0 : cidx_uses_kinds true false false false false 0 (lift_cidx 0 1 v0) = false) by
                    (unfold lift_cidx; apply Hlift0; intro y; unfold ren_lift; destruct (Nat.ltb_spec y 0); lia).
                  eapply cidx_uses_kinds_subst_cidx_ge; [lia | | | exact Hv0].
                  * intros Hk0_0; subst k0.
                    destruct is_left;
                      [apply (IHu0_1 (S c0) (lift_cidx 0 1 v0) 0 ltac:(lia) D0u C2 D2' Hlift_0)
                      |apply (IHu0_2 (S c0) (lift_cidx 0 1 v0) 0 ltac:(lia) D0u C3 D3 Hlift_0)].
                  * destruct is_left;
                      [apply (IHu0_1 (S c0) (lift_cidx 0 1 v0) (S k0) ltac:(lia) A2 C2 D2' (cidx_uses_kinds_lift_shift D v0 k0 Hv0))
                      |apply (IHu0_2 (S c0) (lift_cidx 0 1 v0) (S k0) ltac:(lia) A3 C3 D3 (cidx_uses_kinds_lift_shift D v0 k0 Hv0))].
                + destruct (Nat.ltb_spec s c0); cbn;
                    rewrite (IHu0_1 (S c0) (lift_cidx 0 1 v0) (S k0) ltac:(lia) A2 C2 D2' (cidx_uses_kinds_lift_shift D v0 k0 Hv0)),
                            (IHu0_2 (S c0) (lift_cidx 0 1 v0) (S k0) ltac:(lia) A3 C3 D3 (cidx_uses_kinds_lift_shift D v0 k0 Hv0));
                    [rewrite A1 | rewrite (proj2 (Nat.eqb_neq _ k0)) by lia]; reflexivity. }
            apply Hu; [lia | exact Hu0 | exact Hu1 | exact Hbu | exact Hv]. }
          apply negb_true_iff in B0.
          assert (Hlift_val : cidx_uses_kinds true false false false false 0 (lift_cidx 0 1 val) = false).
          { clear. assert (Hrho : forall (w : cidx D) rho c, (forall y, rho y <> c) -> cidx_uses_kinds true false false false false c (ren_cidx rho w) = false).
            { induction w; intros rho c Hrho; cbn; try reflexivity; try (rewrite (IHw1 _ _ Hrho), (IHw2 _ _ Hrho); reflexivity); try (apply (IHw _ _ Hrho)); try (apply Nat.eqb_neq; apply Hrho).
              rewrite (proj2 (Nat.eqb_neq _ _) (Hrho s)); cbn.
              assert (HrhoS : forall y, ren_shift rho y <> S c) by (intros [| y']; cbn; [lia | pose proof (Hrho y'); lia]).
              rewrite (IHw1 _ _ HrhoS), (IHw2 _ _ HrhoS); reflexivity. }
            unfold lift_cidx; apply Hrho; intro y; unfold ren_lift; destruct (Nat.ltb_spec y 0); lia. }
          destruct is_left; [apply Hc; [exact B0 | exact H2 | exact B2 | exact Hlift_val] | apply Hc; [exact B0 | exact H3 | exact B3 | exact Hlift_val]].
        * apply Nat.eqb_neq in S1. rewrite (proj2 (Nat.eqb_neq _ 0)) by lia; cbn.
          pose proof (cidx_uses_kinds_subst_sum_cidx D is_left i1 (lift_cidx 0 1 val) 1 0 ltac:(lia) (cidx_uses_kinds_lift_shift D val 0 Hval) S2) as Hs1.
          pose proof (cidx_uses_kinds_subst_sum_cidx D is_left i2 (lift_cidx 0 1 val) 1 0 ltac:(lia) (cidx_uses_kinds_lift_shift D val 0 Hval) S3) as Hs2.
          cbn [Nat.add] in Hs1, Hs2; rewrite Hs1, Hs2; reflexivity.
    - replace k with (c + (k - c)) in Hval |- * by lia.
      replace (S k) with (c + S (k - c)) in Hsk by lia.
      exact (cidx_uses_kinds_subst_sum_cidx D is_left i val c (k - c) ltac:(lia) Hval Hsk). }
  assert (Hgen : forall (T0 : cty D) (val : cidx D) c k,
    c <= k ->
    (c = k -> cty_uses_kinds true false false false false false true c T0 = false) ->
    (c = k -> cty_case_branch_nat is_left c T0 = true) ->
    cty_uses_kinds true false false false false false false (S k) T0 = false ->
    cidx_uses_kinds true false false false false k val = false ->
    cty_uses_kinds true false false false false false false k (subst_sum_cty is_left c val T0) = false).
  { induction T0 using cty_ind_nested; intros val c k Hck Hceq Hbr0 Hsk Hval; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hck Hceq Hbr0 Hsk Hval));
      try (apply orb_false_iff in Hsk as [H1 H2];
           rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj1 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H1 Hval),
                   (IHT0_2 _ _ _ Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj2 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H2 Hval); reflexivity);
      try solve_elim_var x c k Hceq Hsk;
      try solve_elim_var b c k Hceq Hsk.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj1 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H1 Hval),
              (Hci len val c k Hck (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj2 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H2 Hval).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj1 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H1 Hval),
              (IHT0_2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia))))
                 (fun Heq => proj2 (proj1 (andb_true_iff _ _) (Hbr0 ltac:(lia)))) H2
                 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity.
    - apply orb_false_iff in Hsk as [H1 H2].
      rewrite (IHT0_1 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj1 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H1 Hval),
              (IHT0_2 (lift_cidx 0 1 val) (S c) (S k) ltac:(lia)
                 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq ltac:(lia))))
                 (fun Heq => proj2 (proj1 (andb_true_iff _ _) (Hbr0 ltac:(lia)))) H2
                 (cidx_uses_kinds_lift_shift D val k Hval)).
      reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hsk as [H1 H2'].
      rewrite (H2 _ _ _ Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj1 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H1 Hval),
              (IHf H3 (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj2 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H2'). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hsk as [H1 H2].
      rewrite (Hci idx val c k Hck (fun Heq => proj1 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj1 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H1 Hval),
              (IH (fun Heq => proj2 (proj1 (orb_false_iff _ _) (Hceq Heq))) (fun Heq => proj2 (proj1 (andb_true_iff _ _) (Hbr0 Heq))) H2). reflexivity. }
  intros val k Hval H0 Hbr Hsk. exact (Hgen T val 0 k ltac:(lia) (fun Heq => H0 (eq_sym Heq)) (fun Heq => Hbr (eq_sym Heq)) Hsk Hval).
Qed.

Lemma spec_box_body_uses_kinds_nat : forall (D : JoinDomain) q c (T : cty D) k,
  c < k ->
  cty_uses_kinds true false false false false false false k T = false ->
  cty_uses_kinds true false false false false false false k (spec_box_body_cty q c T) = false.
Proof.
  intros D q c T.
  assert (Hci : forall (i : cidx D) c0 k0, c0 < k0 ->
    cidx_uses_kinds true false false false false k0 i = false ->
    cidx_uses_kinds true false false false false k0 (spec_box_body_cidx q c0 i) = false).
  { induction i; intros c0 k0 Hck Hi; cbn in *; try reflexivity; try assumption;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ _ Hck H1), (IHi2 _ _ Hck H2); reflexivity);
      try (apply (IHi _ _ Hck Hi)).
    - destruct (Nat.eqb_spec b c0); cbn; [reflexivity | exact Hi].
    - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
      rewrite H1, (IHi1 (S c0) (S k0) ltac:(lia) H2), (IHi2 (S c0) (S k0) ltac:(lia) H3). reflexivity. }
  revert c. induction T using cty_ind_nested; intros c k Hck HT; cbn in *; try reflexivity; try assumption;
    try (apply (IHT _ _ Hck HT));
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 _ _ Hck H1), (IHT2 _ _ Hck H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT _ _ Hck H1), (Hci len c k Hck H2). reflexivity.
  - destruct (Nat.eqb_spec b c); subst; cbn; [apply Nat.eqb_neq; lia | exact HT].
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ Hck H1), (IHT2 (S c) (S k) ltac:(lia) H2). reflexivity.
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT1 _ _ Hck H1), (IHT2 (S c) (S k) ltac:(lia) H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 Hr]. rewrite (H2 _ _ Hck H1), (IHf H3 Hr). reflexivity.
  - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [H1 Hr]. rewrite (Hci idx c k Hck H1), (IH Hr). reflexivity.
Qed.

Lemma spec_box_body_uses_kinds_0 : forall (D : JoinDomain) q (T : cty D),
  cty_uses_kinds true false false true false false false 0 T = false ->
  cty_uses_kinds true false false false false false false 0 (spec_box_body_cty q 0 T) = false.
Proof.
  intros D q T.
  assert (Hci : forall (i : cidx D) c,
    cidx_uses_kinds true true false false false c i = false ->
    cidx_uses_kinds true false false false false c (spec_box_body_cidx q c i) = false).
  { induction i; intro c; cbn; intro Hi; try reflexivity; try assumption;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 _ H1), (IHi2 _ H2); reflexivity);
      try (apply IHi; exact Hi).
    - destruct (Nat.eqb_spec b c) as [-> | Hne]; cbn; [reflexivity | apply Nat.eqb_neq; exact Hne].
    - apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
      rewrite H1, (IHi1 (S c) H2), (IHi2 (S c) H3). reflexivity. }
  assert (Hgen : forall (T0 : cty D) c,
    cty_uses_kinds true false false true false false false c T0 = false ->
    cty_uses_kinds true false false false false false false c (spec_box_body_cty q c T0) = false).
  { induction T0 using cty_ind_nested; intro c; cbn; intro HT; try reflexivity; try assumption;
      try (apply IHT0; exact HT);
      try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT0_1 _ H1), (IHT0_2 _ H2); reflexivity).
    - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT0 _ H1), (Hci len c H2). reflexivity.
    - destruct (Nat.eqb_spec b c) as [-> | Hne]; cbn; [discriminate | apply Nat.eqb_neq; exact Hne].
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in HT as [H1 Hr]. rewrite (H2 _ H1), (IHf H3 Hr). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT as [H1 Hr]. rewrite (Hci idx c H1), (IH Hr). reflexivity. }
  exact (Hgen T 0).
Qed.

Lemma cty_uses_kinds_subst_var_0_no0 : forall (D : JoinDomain) (T : cty D) y k,
  cty_uses_kinds true false false false false false false 0 T = false ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  cty_uses_kinds true false false false false false false k (subst_var_in_cty 0 y T) = false.
Proof.
  intros D T y k H0 Hsk. unfold subst_var_in_cty. cbn [Nat.iter].
  assert (Hren : forall (T0 : cty D) (rho : nat -> nat) c k0,
    (forall z, z <> c -> z <> S k0 -> rho z <> k0) ->
    cty_uses_kinds true false false false false false false c T0 = false ->
    cty_uses_kinds true false false false false false false (S k0) T0 = false ->
    cty_uses_kinds true false false false false false false k0 (ren_cty rho T0) = false).
  { assert (Hci : forall (i : cidx D) (rho : nat -> nat) c k0,
      (forall z, z <> c -> z <> S k0 -> rho z <> k0) ->
      cidx_uses_kinds true false false false false c i = false ->
      cidx_uses_kinds true false false false false (S k0) i = false ->
      cidx_uses_kinds true false false false false k0 (ren_cidx rho i) = false).
    { induction i; intros rho c k0 Hne Hi0 Hisk; cbn in *; try reflexivity;
        try (apply orb_false_iff in Hi0 as [A1 A2]; apply orb_false_iff in Hisk as [B1 B2];
             rewrite (IHi1 _ _ _ Hne A1 B1), (IHi2 _ _ _ Hne A2 B2); reflexivity);
        try (apply (IHi _ _ _ Hne Hi0 Hisk));
        try (apply Nat.eqb_neq in Hi0; apply Nat.eqb_neq in Hisk; apply Nat.eqb_neq; apply Hne; assumption).
      apply orb_false_iff in Hi0 as [A12 A3]; apply orb_false_iff in A12 as [A1 A2].
      apply orb_false_iff in Hisk as [B12 B3]; apply orb_false_iff in B12 as [B1 B2].
      apply Nat.eqb_neq in A1; apply Nat.eqb_neq in B1.
      rewrite (proj2 (Nat.eqb_neq _ _) (Hne s A1 B1)); cbn.
      assert (HneS : forall z, z <> S c -> z <> S (S k0) -> ren_shift rho z <> S k0) by
        (intros [| z'] Hz1 Hz2; cbn; [lia | pose proof (Hne z' ltac:(lia) ltac:(lia)); lia]).
      rewrite (IHi1 _ _ _ HneS A2 B2), (IHi2 _ _ _ HneS A3 B3). reflexivity. }
    induction T0 using cty_ind_nested; intros rho c k0 Hne HT0 HTsk; cbn in *; try reflexivity;
      try (apply (IHT0 _ _ _ Hne HT0 HTsk));
      try (apply orb_false_iff in HT0 as [A1 A2]; apply orb_false_iff in HTsk as [B1 B2];
           rewrite (IHT0_1 _ _ _ Hne A1 B1), (IHT0_2 _ _ _ Hne A2 B2); reflexivity);
      try (apply Nat.eqb_neq in HT0; apply Nat.eqb_neq in HTsk; apply Nat.eqb_neq; apply Hne; assumption).
    - apply orb_false_iff in HT0 as [A1 A2]; apply orb_false_iff in HTsk as [B1 B2].
      rewrite (IHT0 _ _ _ Hne A1 B1), (Hci len _ _ _ Hne A2 B2). reflexivity.
    - apply orb_false_iff in HT0 as [A1 A2]; apply orb_false_iff in HTsk as [B1 B2].
      assert (HneS : forall z, z <> S c -> z <> S (S k0) -> ren_shift rho z <> S k0) by
        (intros [| z'] Hz1 Hz2; cbn; [lia | pose proof (Hne z' ltac:(lia) ltac:(lia)); lia]).
      rewrite (IHT0_1 _ _ _ Hne A1 B1), (IHT0_2 _ _ _ HneS A2 B2). reflexivity.
    - apply orb_false_iff in HT0 as [A1 A2]; apply orb_false_iff in HTsk as [B1 B2].
      assert (HneS : forall z, z <> S c -> z <> S (S k0) -> ren_shift rho z <> S k0) by
        (intros [| z'] Hz1 Hz2; cbn; [lia | pose proof (Hne z' ltac:(lia) ltac:(lia)); lia]).
      rewrite (IHT0_1 _ _ _ Hne A1 B1), (IHT0_2 _ _ _ HneS A2 B2). reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
      apply orb_false_iff in HT0 as [A1 Ar]; apply orb_false_iff in HTsk as [B1 Br].
      rewrite (Hhd _ _ _ Hne A1 B1), (IHf Htl Ar Br). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [A1 Ar]; apply orb_false_iff in HTsk as [B1 Br].
      rewrite (Hci idx _ _ _ Hne A1 B1), (IH Ar Br). reflexivity. }
  apply (Hren T _ 0 k); [intros [| z'] Hz0 Hzsk; cbn; [lia | lia] | exact H0 | exact Hsk].
Qed.

Lemma core_derives_nat_safe : forall (D : JoinDomain) (b : cbinding D) env_b,
  cannotation b = CNat ->
  forall env t j, CoreDerives env t j ->
    forall env_a, env = env_a ++ b :: env_b ->
    cty_uses_kinds true false false false false false false (length env_a) (cresult_type j) = false.
Proof.
  intros D b env_b Hb env t j H.
  induction H using CoreDerives_ind_mut with
    (P := fun env t j _ => forall env_a, env = env_a ++ b :: env_b ->
      cty_uses_kinds true false false false false false false (length env_a) (cresult_type j) = false)
    (P0 := fun env fs u v _ => True);
    try (intros env_a Henv; subst env; cbn [cresult_type]); try reflexivity; try exact I.
  - (* CoreVar *)
    lazymatch goal with
    | Hl : clookup _ x = Some e, Htd : CTypeDemand _ (cannotation e) row |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | ->] | Hgt];
        [ rewrite skipn_app in Htd;
          replace (S x - length env_a) with 0 in Htd by lia; cbn [skipn] in Htd;
          pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd (skipn (S x) env_a) eq_refl) as He;
          rewrite length_skipn in He;
          replace (length env_a) with (S x + (length env_a - S x)) by lia;
          apply cty_uses_kinds_ren_plus; exact He
        | unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia;
          inversion Hl; subst e; rewrite Hb; cbn; reflexivity
        | apply cty_uses_kinds_ren_gt; lia ]
    end.
  - (* CoreLam *)
    lazymatch goal with
    | Ha : CTypeDemand _ dom a |- _ =>
        pose proof (IHCoreDerives ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) eq_refl) as Hcod;
        cbn [length cresult_type] in Hcod;
        cbn; rewrite (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Ha env_a eq_refl), Hcod; reflexivity
    end.
  - (* CoreApp *)
    lazymatch goal with
    | Ha_dom : CTypeDemand _ dom a_dom, Hb_cod : CTypeDemand _ cod b0,
      Hdm_eq : cty_alpha_eq kind dom,
      Happ : app_result_ty dom cod arg = Some res_ty |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hb_cod ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) eq_refl) as Hcod_s;
        cbn [length] in Hcod_s;
        unfold app_result_ty in Happ;
        destruct dom;
        try (destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst res_ty;
             apply cty_uses_kinds_unshift_0; assumption);
        [ destruct arg; cbn in Happ;
          try (destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst res_ty;
               apply cty_uses_kinds_unshift_0; assumption);
          [ inversion Happ; subst res_ty;
            apply cty_uses_kinds_subst_cidx_0;
            [ cbn; reflexivity
            | intros Hk0; subst; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ]
          | inversion Happ; subst res_ty;
            inversion H0; subst;
            apply cty_uses_kinds_subst_cidx_0;
            [ lazymatch goal with Hc : CIdxDemand _ _ _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hc env_a eq_refl) end
            | intro Hk0; subst; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ] ]
        | destruct arg; cbn in Happ;
          try (destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst res_ty;
               apply cty_uses_kinds_unshift_0; assumption);
          [ inversion Happ; subst res_ty;
            apply cty_uses_kinds_subst_tvar_0;
            [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
              [ exfalso; inversion H0; subst;
                lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
                  inversion Hlk; subst ee; unfold cty_alpha_eq in Hdm_eq; rewrite erase_hints_ren, Hb in Hdm_eq; cbn in Hdm_eq; discriminate
                end
              | cbn; apply Nat.eqb_neq; exact Hne ]
            | intros _; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ]
          | inversion Happ; subst res_ty;
            apply cty_uses_kinds_subst_tvar_0;
            [ inversion H0; subst;
              lazymatch goal with
              | _ : CoreDerives _ (CTypeVal ?T0) _, Htd : CTypeDemand _ ?T0 _ |- _ =>
                  exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd env_a eq_refl)
              end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
            | exact Hcod_s ] ] ]
    end.
  - (* CLet *)
    lazymatch goal with
    | Hnf : cty_uses_var 0 bod_ty = false |- _ =>
        apply cty_uses_kinds_unshift_0; [exact Hnf | exact (IHCoreDerives2 (_ :: env_a) eq_refl)]
    end.
  - (* CPair *)
    lazymatch goal with
    | Ha : CTypeDemand _ fst_ty a, Hb_snd : CTypeDemand _ snd_ty b0 |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hb_snd ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) eq_refl) as Hsnd;
        cbn [length] in Hsnd;
        cbn; rewrite (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Ha env_a eq_refl), Hsnd;
        reflexivity
    end.
  - (* CLetPair *)
    lazymatch goal with
    | Hres : ?res_ty = spec_pair_subj_cty ?pr ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres;
        pose proof Hmot as Hmot_saved;
        destruct pr; unfold spec_pair_subj_cty
    end;
    try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
    [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
      [ exfalso;
        lazymatch goal with Hdv : CoreDerives _ (CVar _) {| cresult_type := CSigma _ _ _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
          inversion Hdv; subst;
          lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSigma _ _ _ _ |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
            inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
          end
        end
      | apply cty_uses_kinds_subst_var_0; [exact Hne | exact Hm_s] ]
    | destruct (term_as_cidx pr1) as [c1_idx |] eqn:E1; [destruct (term_as_cidx pr2) as [c2_idx |] eqn:E2 |];
      try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
      lazymatch goal with Hpr : CoreDerives _ (CPair _ _ _ _ _ _) _ |- _ => inversion Hpr; subst end;
      assert (Hc1 : cidx_uses_kinds true false false false false (length env_a) c1_idx = false) by
        (destruct pr1; cbn in E1; try discriminate; inversion E1; subst;
         [ cbn; reflexivity
         | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
             inversion Hdv; subst;
             lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end
           end ]);
      assert (Hc2 : cidx_uses_kinds true false false false false (length env_a) c2_idx = false) by
        (destruct pr2; cbn in E2; try discriminate; inversion E2; subst;
         [ cbn; reflexivity
         | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
             inversion Hdv; subst;
             lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end
           end ]);
      apply cty_uses_kinds_subst_pair_0;
      [ exact Hc1 | exact Hc2
      | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSigma; [apply cty_alpha_eq_refl | reflexivity | reflexivity]]
      | exact Hm_s ] ].
  - (* CorePromote *)
    cbn; exact (IHCoreDerives env_a eq_refl).
  - (* CoreLetBox *)
    lazymatch goal with
    | Hres : ?res_ty = spec_box_subj_cty ?box_term ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; pose proof Hmot as Hmot_saved; destruct box_term; unfold spec_box_subj_cty
    end;
    try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
    [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
      [ exfalso;
        lazymatch goal with Hdv : CoreDerives _ (CVar _) {| cresult_type := CBox _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
          inversion Hdv; subst;
          lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CBox _ _ |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
            inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
          end
        end
      | apply cty_uses_kinds_subst_var_0; [exact Hne | exact Hm_s] ]
    | destruct box_term;
      try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
      [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
        [ apply cty_uses_kinds_subst_var_0_no0;
          [ apply spec_box_body_uses_kinds_0;
            eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity |];
            lazymatch goal with Hdp : CoreDerives _ (CPromote _ (CVar _)) {| cresult_type := CBox _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
              inversion Hdp; subst;
              lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                inversion Hdv; subst;
                lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
                  inversion Hlk; subst ee;
                  rewrite Hb; unfold flags_allow; cbn; reflexivity
                end
              end
            end
          | apply spec_box_body_uses_kinds_nat; [lia | exact Hm_s] ]
        | apply cty_uses_kinds_subst_var_0; [exact Hne | apply spec_box_body_uses_kinds_nat; [lia | exact Hm_s]] ]
      | lazymatch goal with Hdp : CoreDerives _ (CPromote _ (CNatVal _)) _ |- _ =>
          inversion Hdp; subst;
          lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
            inversion Hdv; subst;
            apply cty_uses_kinds_subst_box_nat_0;
            [ lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | unfold flags_allow; cbn; reflexivity]
            | exact Hm_s ]
          end
        end
      | lazymatch goal with Hdp : CoreDerives _ (CPromote _ (CTypeVal _)) _ |- _ =>
          inversion Hdp; subst;
          lazymatch goal with Hdv : CoreDerives _ (CTypeVal ?tt) _ |- _ =>
            inversion Hdv; subst;
            apply cty_uses_kinds_subst_box_ty_0;
            [ lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) ?tt _ |- _ => exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd env_a eq_refl) end
            | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | unfold flags_allow; cbn; reflexivity]
            | exact Hm_s ]
          end
        end ] ].
  - (* CoreInl *)
    lazymatch goal with
    | Hrhs : CTypeDemand _ rhs_ty b0 |- _ =>
        pose proof (IHCoreDerives env_a eq_refl) as HA; cbn [cresult_type] in HA;
        cbn; rewrite HA, (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hrhs env_a eq_refl); reflexivity
    end.
  - (* CoreInr *)
    lazymatch goal with
    | Hlhs : CTypeDemand _ ?lhs_ty ?a0 |- _ =>
        pose proof (IHCoreDerives env_a eq_refl) as HB; cbn [cresult_type] in HB;
        cbn; rewrite (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hlhs env_a eq_refl), HB; reflexivity
    end.
  - (* CoreMatchSum *)
    lazymatch goal with
    | Hres : ?res_ty = spec_sum_subj_cty ?scrut ?mot,
      Hsc_t : CoreDerives _ ?scrut {| cresult_type := CSum ?A ?B; ccomp_demand := _; ctype_demand_row := _ |},
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; pose proof Hmot as Hmot_saved; destruct scrut; unfold spec_sum_subj_cty
    end;
    try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
    [ destruct (Nat.eq_dec x0 (length env_a)) as [-> | Hne];
      [ exfalso;
        lazymatch goal with Hdv : CoreDerives _ (CVar _) {| cresult_type := CSum _ _; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
          inversion Hdv; subst;
          lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSum _ _ |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
            inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
          end
        end
      | apply cty_uses_kinds_subst_var_0; [exact Hne | exact Hm_s] ]
    | destruct (term_as_cidx scrut) as [c_idx |] eqn:Ev;
      try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
      lazymatch goal with Hsc : CoreDerives _ (CInl _ _) _ |- _ => inversion Hsc; subst end;
      assert (Hc : cidx_uses_kinds true false false false false (length env_a) c_idx = false) by
        (destruct scrut; cbn in Ev; try discriminate; inversion Ev; subst;
         [ cbn; reflexivity
         | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
             inversion Hdv; subst;
             lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end
           end ]);
      apply cty_uses_kinds_subst_sum_0;
      [ exact Hc
      | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSum; [apply cty_alpha_eq_refl | reflexivity]]
      | intros _;
        lazymatch goal with
        | _ : CoreDerives _ (CInl _ _) {| cresult_type := CSum ?AA ?BB; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
            destruct AA eqn:EA;
            [ lazymatch type of Hmot_saved with CTypeDemand (?hd' :: _) _ _ =>
                refine (proj2 (cdemand_case_branch_nat D hd' (env_a ++ b :: env_b) true CNat BB _ _) _ _ _ Hmot_saved [] eq_refl);
                [unfold cty_alpha_eq; reflexivity | reflexivity]
              end
            | apply cty_uses_var_case_branch_nat; assumption .. ]
        end
      | exact Hm_s ]
    | destruct (term_as_cidx scrut) as [c_idx |] eqn:Ev;
      try (apply cty_uses_kinds_unshift_0; [assumption | exact Hm_s]);
      lazymatch goal with Hsc : CoreDerives _ (CInr _ _) _ |- _ => inversion Hsc; subst end;
      assert (Hc : cidx_uses_kinds true false false false false (length env_a) c_idx = false) by
        (destruct scrut; cbn in Ev; try discriminate; inversion Ev; subst;
         [ cbn; reflexivity
         | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
             inversion Hdv; subst;
             lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end
           end ]);
      apply cty_uses_kinds_subst_sum_0;
      [ exact Hc
      | intros _; eapply ctype_demand_uses_kinds; [exact Hmot_saved | reflexivity | eapply flags_allow_CSum; [apply cty_alpha_eq_refl | reflexivity]]
      | intros _;
        lazymatch goal with
        | _ : CoreDerives _ (CInr _ _) {| cresult_type := CSum ?AA ?BB; ccomp_demand := _; ctype_demand_row := _ |} |- _ =>
            destruct BB eqn:EB;
            [ lazymatch type of Hmot_saved with CTypeDemand (?hd' :: _) _ _ =>
                refine (proj2 (cdemand_case_branch_nat D hd' (env_a ++ b :: env_b) false AA CNat _ _) _ _ _ Hmot_saved [] eq_refl);
                [unfold cty_alpha_eq; reflexivity | reflexivity]
              end
            | apply cty_uses_var_case_branch_nat; assumption .. ]
        end
      | exact Hm_s ] ].
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
                 cty_uses_kinds true false false false false false false (length env_a) ft || go_fs rest
             end) (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fs0) = false);
        [ intros env0 fs0 u0 v0 H0; induction H0; intro H0env; subst; cbn;
          [ reflexivity
          | lazymatch goal with Htd : CTypeDemand _ _ _ |- _ =>
              rewrite (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd env_a eq_refl), (IHCRecordElemDerives eq_refl); reflexivity
            end ]
        | exact (Hgo _ _ _ _ Hrec eq_refl) ]
    end.
  - (* CoreMatchRecord *)
    lazymatch goal with
    | Hmot : CTypeDemand _ ?mot _ |- cty_uses_kinds _ _ _ _ _ _ _ _ ?mot = false =>
        exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot env_a eq_refl)
    end.
  - (* CoreSubgrade *)
    lazymatch goal with
    | Hvt : CTypeDemand _ ?target _ |- cty_uses_kinds _ _ _ _ _ _ _ _ ?target = false =>
        exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hvt env_a eq_refl)
    end.
  - (* CoreFix *)
    lazymatch goal with
    | Hres : ?res_ty = spec_fix_subj_cty ?scrut ?mot,
      Hmot : CTypeDemand (?hd :: _) ?mot ?v_mot,
      Hdep : match term_as_cidx ?scrut with Some _ => True | None => cty_uses_var 0 ?mot = false end |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot (hd :: env_a) eq_refl) as Hm_s;
        cbn [length] in Hm_s;
        rewrite Hres; unfold spec_fix_subj_cty;
        destruct (term_as_cidx scrut) as [c_idx |] eqn:Es;
        [ assert (Hc : cidx_uses_kinds true false false false false (length env_a) c_idx = false) by
            (destruct scrut; cbn in Es; try discriminate; inversion Es; subst;
             [ cbn; reflexivity
             | lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end
               end ]);
          apply cty_uses_kinds_subst_cidx_0;
          [ exact Hc
          | intros _; eapply ctype_demand_uses_kinds; [exact Hmot | reflexivity | unfold flags_allow; cbn; reflexivity]
          | exact Hm_s ]
        | apply cty_uses_kinds_unshift_0; [exact Hdep | exact Hm_s] ]
    end.
Qed.
Definition spec_box_body_uses_kinds := spec_box_body_uses_kinds_nat.

Lemma cdemand_box_nat_safe : forall (D : JoinDomain) (q : grade D) (env : cenv D) e0 T d,
  cannotation e0 = CBox q CNat ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds false false false true false false false 0 T = false.
Proof.
  intros D q env e0 T d He0 HT_orig.
  assert (Hidx : forall env1 i d0, CIdxDemand env1 i d0 ->
    forall env_p, env1 = env_p ++ [e0] ++ env ->
      cidx_uses_kinds false true false false false (length env_p) i = false).
  { intros env1 i d0 H. induction H; intros env_p Henv; try rewrite Henv in *; cbn; try reflexivity;
      try (rewrite (IHCIdxDemand1 _ eq_refl), (IHCIdxDemand2 _ eq_refl); reflexivity);
      try (apply (IHCIdxDemand _ eq_refl)).
    - destruct (Nat.eq_dec x (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec p (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec p (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec s (length env_p)) as [-> | Hne].
      + unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
        inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0, erase_hints_ren in H0; cbn in H0; discriminate.
      + apply Nat.eqb_neq in Hne. rewrite Hne.
        pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_p ++ [e0] ++ env)) |} :: env_p) eq_refl) as Hl1.
        pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_p ++ [e0] ++ env)) |} :: env_p) eq_refl) as Hr1.
        cbn [length] in Hl1, Hr1. rewrite Hl1, Hr1. reflexivity. }
  assert (Hgen : forall env1 T1 d1, CTypeDemand env1 T1 d1 ->
    forall env_p, env1 = env_p ++ [e0] ++ env ->
      cty_uses_kinds false false false true false false false (length env_p) T1 = false).
  { intros env1 T1 d1 HT.
    induction HT using CTypeDemand_ind_mut with
      (P := fun env1 T1 d1 _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        cty_uses_kinds false false false true false false false (length env_p) T1 = false)
      (P0 := fun env1 fs df _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        Forall (fun '(_, _, ft) => cty_uses_kinds false false false true false false false (length env_p) ft = false) fs)
      (P1 := fun env1 ls dl _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        Forall (fun i => cidx_uses_kinds false true false false false (length env_p) i = false) ls);
      intros env_p Henv; try rewrite Henv in *; cbn; try reflexivity;
      try (apply IHHT; reflexivity);
      try (rewrite (IHHT1 _ eq_refl), (IHHT2 _ eq_refl); reflexivity);
      try apply Forall_nil.
    - rewrite (IHHT _ eq_refl), (Hidx _ _ _ c _ eq_refl). reflexivity.
    - destruct (Nat.eq_dec x (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      lazymatch goal with
      | Hlk : clookup _ _ = Some _, Ha : cty_alpha_eq _ _ |- _ =>
          unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
          inversion Hlk; subst; unfold cty_alpha_eq in Ha; rewrite He0 in Ha; try rewrite erase_hints_ren in Ha; cbn in Ha; discriminate
      end.
    - destruct (Nat.eq_dec b (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      lazymatch goal with
      | Hlk : clookup _ _ = Some _, Ha : cty_alpha_eq _ _ |- _ =>
          unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
          inversion Hlk; subst; unfold cty_alpha_eq in Ha; rewrite He0 in Ha; try rewrite erase_hints_ren in Ha; cbn in Ha; discriminate
      end.
    - rewrite (IHHT1 _ eq_refl).
      exact (IHHT2 (_ :: env_p) eq_refl).
    - rewrite (IHHT1 _ eq_refl).
      exact (IHHT2 (_ :: env_p) eq_refl).
    - pose proof (IHHT _ eq_refl) as Hf. clear - Hf. induction fields as [| [[? ?] ?] ? IH]; cbn; inversion Hf; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
    - pose proof (IHHT _ eq_refl) as Hl. clear - Hl. induction indices as [| ? ? IH]; cbn; inversion Hl; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
    - apply Forall_cons; [exact (IHHT _ eq_refl) | exact (IHHT0 _ eq_refl)].
    - apply Forall_cons; [exact (Hidx _ _ _ c _ eq_refl) | exact (IHHT _ eq_refl)]. }
  exact (Hgen (e0 :: env) T d HT_orig [] eq_refl).
Qed.

Lemma cdemand_not_nat_idx0_safe : forall (D : JoinDomain) (env : cenv D) e0 T d,
  erase_hints (cannotation e0) <> CNat ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds false true true true true true true 0 T = false.
Proof.
  intros D env e0 T d Hnn HT_orig.
  assert (Hidx : forall env1 i d0, CIdxDemand env1 i d0 ->
    forall env_p, env1 = env_p ++ [e0] ++ env ->
      cidx_uses_kinds false true true true true (length env_p) i = false).
  { intros env1 i d0 H. induction H; intros env_p Henv; try rewrite Henv in *; cbn; try reflexivity;
      try (rewrite (IHCIdxDemand1 _ eq_refl), (IHCIdxDemand2 _ eq_refl); reflexivity);
      try (apply (IHCIdxDemand _ eq_refl)).
    - destruct (Nat.eq_dec x (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0. cbn in H0. contradiction.
    - pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length (env_p ++ [e0] ++ env)) |} :: env_p) eq_refl) as Hl1.
      pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length (env_p ++ [e0] ++ env)) |} :: env_p) eq_refl) as Hr1.
      cbn [length] in Hl1, Hr1. rewrite Hl1, Hr1. reflexivity. }
  assert (Hgen : forall env1 T1 d1, CTypeDemand env1 T1 d1 ->
    forall env_p, env1 = env_p ++ [e0] ++ env ->
      cty_uses_kinds false true true true true true true (length env_p) T1 = false).
  { intros env1 T1 d1 HT.
    induction HT using CTypeDemand_ind_mut with
      (P := fun env1 T1 d1 _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        cty_uses_kinds false true true true true true true (length env_p) T1 = false)
      (P0 := fun env1 fs df _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        Forall (fun '(_, _, ft) => cty_uses_kinds false true true true true true true (length env_p) ft = false) fs)
      (P1 := fun env1 ls dl _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        Forall (fun i => cidx_uses_kinds false true true true true (length env_p) i = false) ls);
      intros env_p Henv; try rewrite Henv in *; cbn; try reflexivity;
      try (apply IHHT; reflexivity);
      try (rewrite (IHHT1 _ eq_refl), (IHHT2 _ eq_refl); reflexivity);
      try apply Forall_nil.
    - rewrite (IHHT _ eq_refl), (Hidx _ _ _ c _ eq_refl). reflexivity.
    - rewrite (IHHT1 _ eq_refl). exact (IHHT2 (_ :: env_p) eq_refl).
    - rewrite (IHHT1 _ eq_refl). exact (IHHT2 (_ :: env_p) eq_refl).
    - pose proof (IHHT _ eq_refl) as Hf. clear - Hf. induction fields as [| [[? ?] ?] ? IH]; cbn; inversion Hf; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
    - pose proof (IHHT _ eq_refl) as Hl. clear - Hl. induction indices as [| ? ? IH]; cbn; inversion Hl; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
    - apply Forall_cons; [exact (IHHT _ eq_refl) | exact (IHHT0 _ eq_refl)].
    - apply Forall_cons; [exact (Hidx _ _ _ c _ eq_refl) | exact (IHHT _ eq_refl)]. }
  exact (Hgen (e0 :: env) T d HT_orig [] eq_refl).
Qed.

Lemma cdemand_sum_nat_safe : forall (D : JoinDomain) (A B : cty D) (env : cenv D) e0 T d,
  cannotation e0 = CSum A B ->
  (A = CNat \/ B = CNat) ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds false false false false false false true 0 T = false.
Proof.
  intros D A B env e0 T d He0 _ HT_orig.
  assert (Hidx : forall env1 i d0, CIdxDemand env1 i d0 ->
    forall env_p, env1 = env_p ++ [e0] ++ env ->
      cidx_uses_kinds false false false false true (length env_p) i = false).
  { intros env1 i d0 H. induction H; intros env_p Henv; try rewrite Henv in *; cbn; try reflexivity;
      try (rewrite (IHCIdxDemand1 _ eq_refl), (IHCIdxDemand2 _ eq_refl); reflexivity);
      try (apply (IHCIdxDemand _ eq_refl)).
    - destruct (Nat.eq_dec x (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec b (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec p (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - destruct (Nat.eq_dec p (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      unfold clookup in H. rewrite nth_error_app2, Nat.sub_diag in H by lia.
      inversion H; subst e. unfold cty_alpha_eq in H0; rewrite He0 in H0; cbn in H0; discriminate.
    - pose proof (IHCIdxDemand1 ({| cbinder := 0; cannotation := A0; ctype_uses := vec_zero (length (env_p ++ [e0] ++ env)) |} :: env_p) eq_refl) as Hl1.
      pose proof (IHCIdxDemand2 ({| cbinder := 0; cannotation := B0; ctype_uses := vec_zero (length (env_p ++ [e0] ++ env)) |} :: env_p) eq_refl) as Hr1.
      cbn [length] in Hl1, Hr1. rewrite Hl1, Hr1. reflexivity. }
  assert (Hgen : forall env1 T1 d1, CTypeDemand env1 T1 d1 ->
    forall env_p, env1 = env_p ++ [e0] ++ env ->
      cty_uses_kinds false false false false false false true (length env_p) T1 = false).
  { intros env1 T1 d1 HT.
    induction HT using CTypeDemand_ind_mut with
      (P := fun env1 T1 d1 _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        cty_uses_kinds false false false false false false true (length env_p) T1 = false)
      (P0 := fun env1 fs df _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        Forall (fun '(_, _, ft) => cty_uses_kinds false false false false false false true (length env_p) ft = false) fs)
      (P1 := fun env1 ls dl _ => forall env_p, env1 = env_p ++ [e0] ++ env ->
        Forall (fun i => cidx_uses_kinds false false false false true (length env_p) i = false) ls);
      intros env_p Henv; try rewrite Henv in *; cbn; try reflexivity;
      try (apply IHHT; reflexivity);
      try (rewrite (IHHT1 _ eq_refl), (IHHT2 _ eq_refl); reflexivity);
      try apply Forall_nil.
    - rewrite (IHHT _ eq_refl), (Hidx _ _ _ c _ eq_refl). reflexivity.
    - destruct (Nat.eq_dec x (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      lazymatch goal with
      | Hlk : clookup _ _ = Some _, Ha : cty_alpha_eq _ _ |- _ =>
          unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
          inversion Hlk; subst; unfold cty_alpha_eq in Ha; rewrite He0 in Ha; try rewrite erase_hints_ren in Ha; cbn in Ha; discriminate
      end.
    - destruct (Nat.eq_dec b (length env_p)) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
      lazymatch goal with
      | Hlk : clookup _ _ = Some _, Ha : cty_alpha_eq _ _ |- _ =>
          unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
          inversion Hlk; subst; unfold cty_alpha_eq in Ha; rewrite He0 in Ha; try rewrite erase_hints_ren in Ha; cbn in Ha; discriminate
      end.
    - rewrite (IHHT1 _ eq_refl).
      exact (IHHT2 (_ :: env_p) eq_refl).
    - rewrite (IHHT1 _ eq_refl).
      exact (IHHT2 (_ :: env_p) eq_refl).
    - pose proof (IHHT _ eq_refl) as Hf. clear - Hf. induction fields as [| [[? ?] ?] ? IH]; cbn; inversion Hf; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
    - pose proof (IHHT _ eq_refl) as Hl. clear - Hl. induction indices as [| ? ? IH]; cbn; inversion Hl; subst; [reflexivity | rewrite H1, (IH H2); reflexivity].
    - apply Forall_cons; [exact (IHHT _ eq_refl) | exact (IHHT0 _ eq_refl)].
    - apply Forall_cons; [exact (Hidx _ _ _ c _ eq_refl) | exact (IHHT _ eq_refl)]. }
  exact (Hgen (e0 :: env) T d HT_orig [] eq_refl).
Qed.


Lemma vec_subst_skipn_prefix : forall (D : JoinDomain) p k z (v : list (grade D)),
  p <= k ->
  vec_subst (k - p) z (skipn p v) = skipn p (vec_subst k z v).
Proof.
  intros D p. induction p as [| p IH]; intros k z [| a v] Hpk; cbn.
  - rewrite Nat.sub_0_r. destruct k; reflexivity.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct k; cbn; [lia | destruct (k - p); reflexivity].
  - destruct k as [| k']; [lia |]. cbn. apply IH; lia.
Qed.

Lemma vec_subst_firstn_prefix : forall (D : JoinDomain) p k z (v : list (grade D)),
  p <= k ->
  firstn p (vec_subst k z v) = firstn p v.
Proof.
  intros D p. induction p as [| p IH]; intros k z v Hpk; [reflexivity |].
  destruct k as [| k'], v as [| a v]; cbn; try lia; try reflexivity.
  f_equal; apply IH; lia.
Qed.

Lemma branch_rel_vec_allows : forall (D : JoinDomain) (u v : list (grade D)),
  branch_rel u v -> vec_allows u v.
Proof.
  intros D u v H. unfold branch_rel in H. destruct (grade_join D); [exact H | subst; apply vec_allows_refl].
Qed.

Lemma branch_rel_allows_trans : forall (D : JoinDomain) (u v w : list (grade D)),
  branch_rel u v -> vec_allows v w -> vec_allows u w.
Proof.
  intros D u v w H1 H2. eapply vec_allows_trans; [apply branch_rel_vec_allows; exact H1 | exact H2].
Qed.

Lemma CTypeDemand_CNat_inv : forall (D : JoinDomain) (env : cenv D) d,
  CTypeDemand env CNat d -> d = vec_zero (length env).
Proof.
  intros D env d H. inversion H; reflexivity.
Qed.

Lemma vec_allows_zero_branch_rel : forall (D : JoinDomain) n (u : list (grade D)),
  (grade_join D = None -> forall (g : grade D), allows zero g -> g = zero) ->
  vec_allows (vec_zero n) u ->
  branch_rel (vec_zero n) u.
Proof.
  intros D n u Hz H. unfold branch_rel. destruct (grade_join D) eqn:Hj; [exact H |].
  pose proof (Hz eq_refl) as Hz0. clear Hz Hj.
  induction n as [| n IH] in u, H |- *; destruct u; inversion H; subst; cbn; [reflexivity |].
  f_equal; [symmetry; apply Hz0; assumption | apply IH; assumption].
Qed.

Lemma cty_alpha_eq_CPi_inv : forall (D : JoinDomain) (T : cty D) x s r dom cod,
  cty_alpha_eq T (CPi x s r dom cod) ->
  exists x0 dom0 cod0, T = CPi x0 s r dom0 cod0 /\ cty_alpha_eq dom0 dom /\ cty_alpha_eq cod0 cod.
Proof.
  intros D T x s r dom cod H. unfold cty_alpha_eq in H.
  destruct T; cbn in H; try discriminate.
  inversion H; subst. eexists _, _, _; split; [reflexivity | split; assumption].
Qed.

Lemma cty_alpha_eq_CSigma_inv : forall (D : JoinDomain) (T : cty D) x r A B,
  cty_alpha_eq T (CSigma x r A B) ->
  exists x0 A0 B0, T = CSigma x0 r A0 B0 /\ cty_alpha_eq A0 A /\ cty_alpha_eq B0 B.
Proof.
  intros D T x r A B H. unfold cty_alpha_eq in H.
  destruct T; cbn in H; try discriminate.
  inversion H; subst. eexists _, _, _; split; [reflexivity | split; assumption].
Qed.

Lemma cty_alpha_eq_CBox_inv : forall (D : JoinDomain) (T : cty D) q A,
  cty_alpha_eq T (CBox q A) ->
  exists A0, T = CBox q A0 /\ cty_alpha_eq A0 A.
Proof.
  intros D T q A H. unfold cty_alpha_eq in H.
  destruct T; cbn in H; try discriminate.
  inversion H; subst. exists T. split; [reflexivity | assumption].
Qed.

Lemma cty_alpha_eq_CSum_inv : forall (D : JoinDomain) (T : cty D) A B,
  cty_alpha_eq T (CSum A B) ->
  exists A0 B0, T = CSum A0 B0 /\ cty_alpha_eq A0 A /\ cty_alpha_eq B0 B.
Proof.
  intros D T A B H. unfold cty_alpha_eq in H.
  destruct T; cbn in H; try discriminate.
  inversion H; subst. exists T1, T2. split; [reflexivity | split; assumption].
Qed.

Lemma cty_alpha_eq_CRecord_inv : forall (D : JoinDomain) (T : cty D) id fs,
  cty_alpha_eq T (CRecord id fs) ->
  exists fs0, T = CRecord id fs0 /\
    Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2) fs0 fs.
Proof.
  intros D T id fs H. unfold cty_alpha_eq in H.
  destruct T; cbn in H; try discriminate.
  inversion H; subst. exists fields. split; [reflexivity |].
  clear H. revert fields H2. induction fs as [| [[fn fg] ft] rest IH]; intros [| [[fn0 fg0] ft0] rest0] H2; cbn in *; try discriminate.
  - apply Forall2_nil.
  - inversion H2; subst. apply Forall2_cons; [split; [reflexivity | split; [reflexivity | assumption]] | apply IH; assumption].
Qed.

Lemma cty_alpha_eq_CNat_inv : forall (D : JoinDomain) (T : cty D),
  cty_alpha_eq T CNat -> T = CNat.
Proof.
  intros D T H. unfold cty_alpha_eq in H. destruct T; cbn in H; try discriminate; reflexivity.
Qed.

Lemma cty_alpha_eq_CUniv_inv : forall (D : JoinDomain) (T : cty D) lvl,
  cty_alpha_eq T (CUniv lvl) -> T = CUniv lvl.
Proof.
  intros D T lvl H. unfold cty_alpha_eq in H. destruct T; cbn in H; try discriminate; inversion H; reflexivity.
Qed.

Lemma cty_alpha_eq_CBool_inv : forall (D : JoinDomain) (T : cty D),
  cty_alpha_eq T CBool -> T = CBool.
Proof.
  intros D T H. unfold cty_alpha_eq in H. destruct T; cbn in H; try discriminate; reflexivity.
Qed.

Lemma subst_cidx_in_cty_unshift_0 : forall (D : JoinDomain) (T : cty D) val k,
  cty_uses_var 0 T = false ->
  cty_uses_kinds true false false false false false false (S k) T = false ->
  subst_cidx_in_cty k val (unshift_cty 0 T) =
  unshift_cty 0 (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) T).
Proof.
  intros D T val k Hnf HT.
  unfold unshift_cty.
  change (ren_cty (Nat.iter 0 ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) T) with (ren_cty (r_var 0 0) T).
  rewrite (ren_cty_r_var_no_use D T 0 0 (S k) Hnf).
  change (ren_cty (r_var 0 (S k)) T) with (subst_var_in_cty 0 (S k) T).
  rewrite (subst_cidx_ren_var_comm D T val (S k) k ltac:(lia) HT).
  destruct (Nat.ltb_spec (S k) k); [lia |].
  replace (S k - 1) with k by lia.
  unfold subst_var_in_cty.
  change (Nat.iter 0 ren_shift (fun i => match i with 0 => k | S i' => i' end)) with (r_var 0 k).
  change (Nat.iter 0 ren_shift (fun i => match i with 0 => 0 | S i' => i' end)) with (r_var 0 0).
  apply ren_cty_r_var_no_use.
  apply cty_uses_var_subst_cidx_0; [lia | exact HT | apply lift_cidx_uses_var_0 | exact Hnf].
Qed.

Lemma cty_uses_kinds_lift_inv : forall (D : JoinDomain) (T : cty D) k,
  cty_uses_kinds true false false false false false false (S k) (lift_cty 0 1 T) = false ->
  cty_uses_kinds true false false false false false false k T = false.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) c k,
    cty_uses_kinds true false false false false false false (S (c + k)) (lift_cty c 1 T0) = false ->
    cty_uses_kinds true false false false false false false (c + k) T0 = false).
  { assert (Hci : forall (i : cidx D) c0 k0,
      cidx_uses_kinds true false false false false (S (c0 + k0)) (lift_cidx c0 1 i) = false ->
      cidx_uses_kinds true false false false false (c0 + k0) i = false).
    { induction i; intros c0 k0 Hi; cbn in *; try reflexivity;
        try solve [apply orb_false_iff in Hi as [Ha Hb]; rewrite (IHi1 c0 k0 Ha), (IHi2 c0 k0 Hb); reflexivity];
        try solve [apply (IHi c0 k0 Hi)];
        try solve [unfold ren_lift in Hi; destruct (b <? c0) eqn:Eb; [apply Nat.ltb_lt in Eb | apply Nat.ltb_ge in Eb]; apply Nat.eqb_neq in Hi; apply Nat.eqb_neq; lia];
        try solve [unfold ren_lift in Hi; destruct (p <? c0) eqn:Ep; [apply Nat.ltb_lt in Ep | apply Nat.ltb_ge in Ep]; apply Nat.eqb_neq in Hi; apply Nat.eqb_neq; lia].
      apply orb_false_iff in Hi as [H12 H3]; apply orb_false_iff in H12 as [Ha Hb].
      unfold ren_lift in Ha. assert (Hs : (s =? c0 + k0) = false) by (destruct (s <? c0) eqn:Es; [apply Nat.ltb_lt in Es | apply Nat.ltb_ge in Es]; apply Nat.eqb_neq in Ha; apply Nat.eqb_neq; lia).
      assert (Hs1 : ren_cidx (ren_shift (ren_lift c0 1)) i1 = lift_cidx (S c0) 1 i1)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn [ren_shift];
            [destruct (0 <? S c0) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; lia
            | destruct (y <? c0) eqn:E1, (S y <? S c0) eqn:E2; [apply Nat.ltb_lt in E1, E2 | apply Nat.ltb_lt in E1; apply Nat.ltb_ge in E2 | apply Nat.ltb_ge in E1; apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E1, E2]; lia]).
      assert (Hs2 : ren_cidx (ren_shift (ren_lift c0 1)) i2 = lift_cidx (S c0) 1 i2)
        by (unfold lift_cidx; apply ren_cidx_ext; intros [| y]; unfold ren_lift; cbn [ren_shift];
            [destruct (0 <? S c0) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; lia
            | destruct (y <? c0) eqn:E1, (S y <? S c0) eqn:E2; [apply Nat.ltb_lt in E1, E2 | apply Nat.ltb_lt in E1; apply Nat.ltb_ge in E2 | apply Nat.ltb_ge in E1; apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E1, E2]; lia]).
      rewrite Hs1 in Hb; rewrite Hs2 in H3. replace (S (S (c0 + k0))) with (S (S c0 + k0)) in Hb, H3 by lia.
      replace (S (c0 + k0)) with (S c0 + k0) by lia.
      rewrite Hs, (IHi1 (S c0) k0 Hb), (IHi2 (S c0) k0 H3); reflexivity. }
    induction T0 using cty_ind_nested; intros c k Hu; cbn in *; try reflexivity;
      try solve [apply (IHT0 c k Hu)];
      try solve [apply orb_false_iff in Hu as [H1 H2]; rewrite (IHT0_1 c k H1), (IHT0_2 c k H2); reflexivity].
    - apply orb_false_iff in Hu as [H1 H2].
      change (ren_cidx (ren_lift c 1) len) with (lift_cidx c 1 len) in H2.
      rewrite (IHT0 c k H1), (Hci _ _ _ H2). reflexivity.
    - unfold ren_lift in Hu. destruct (x <? c) eqn:Ex; [apply Nat.ltb_lt in Ex | apply Nat.ltb_ge in Ex]; apply Nat.eqb_neq in Hu; apply Nat.eqb_neq; lia.
    - unfold ren_lift in Hu. destruct (b <? c) eqn:Eb; [apply Nat.ltb_lt in Eb | apply Nat.ltb_ge in Eb]; apply Nat.eqb_neq in Hu; apply Nat.eqb_neq; lia.
    - apply orb_false_iff in Hu as [H1 H2].
      assert (Hs : ren_cty (ren_shift (ren_lift c 1)) T0_2 = lift_cty (S c) 1 T0_2)
        by (unfold lift_cty; apply ren_cty_ext; intros [| y]; unfold ren_lift; cbn [ren_shift];
            [destruct (0 <? S c) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; lia
            | destruct (y <? c) eqn:E1, (S y <? S c) eqn:E2; [apply Nat.ltb_lt in E1, E2 | apply Nat.ltb_lt in E1; apply Nat.ltb_ge in E2 | apply Nat.ltb_ge in E1; apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E1, E2]; lia]).
      rewrite Hs in H2. replace (S (S (c + k))) with (S (S c + k)) in H2 by lia.
      replace (S (c + k)) with (S c + k) by lia.
      rewrite (IHT0_1 c k H1), (IHT0_2 (S c) k H2). reflexivity.
    - apply orb_false_iff in Hu as [H1 H2].
      assert (Hs : ren_cty (ren_shift (ren_lift c 1)) T0_2 = lift_cty (S c) 1 T0_2)
        by (unfold lift_cty; apply ren_cty_ext; intros [| y]; unfold ren_lift; cbn [ren_shift];
            [destruct (0 <? S c) eqn:E; [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; lia
            | destruct (y <? c) eqn:E1, (S y <? S c) eqn:E2; [apply Nat.ltb_lt in E1, E2 | apply Nat.ltb_lt in E1; apply Nat.ltb_ge in E2 | apply Nat.ltb_ge in E1; apply Nat.ltb_lt in E2 | apply Nat.ltb_ge in E1, E2]; lia]).
      rewrite Hs in H2. replace (S (S (c + k))) with (S (S c + k)) in H2 by lia.
      replace (S (c + k)) with (S c + k) by lia.
      rewrite (IHT0_1 c k H1), (IHT0_2 (S c) k H2). reflexivity.
    - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
      inversion H; subst; cbn in H2. apply orb_false_iff in Hu as [H1 Hr]. rewrite (H2 c k H1), (IHf H3 Hr). reflexivity.
    - induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Hu as [H1 Hr].
      change (ren_cidx (ren_lift c 1) idx) with (lift_cidx c 1 idx) in H1.
      rewrite (Hci _ _ _ H1), (IH Hr). reflexivity. }
  intros k H. exact (Hgen T 0 k H).
Qed.

Lemma subst_cidx_in_cty_lift_n_comm : forall (D : JoinDomain) n k (T : cty D) val,
  cty_uses_kinds true false false false false false false k T = false ->
  subst_cidx_in_cty (n + k) (lift_cidx 0 n val) (lift_cty 0 n T) =
  lift_cty 0 n (subst_cidx_in_cty k val T).
Proof.
  intros D n. induction n as [| n IH]; intros k T val Hk; cbn.
  - rewrite lift_cidx_0_0, !lift_cty_0_0; reflexivity.
  - rewrite <- lift_cty_add with (a := 1) (b := n).
    rewrite <- lift_cidx_add with (a := 1) (b := n).
    assert (Hn : cty_uses_kinds true false false false false false false (n + k) (lift_cty 0 n T) = false).
    { replace (lift_cty 0 n T) with (ren_cty (plus n) T)
        by (unfold lift_cty; apply ren_cty_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:E; nat_bool_hyps; lia).
      apply cty_uses_kinds_ren_plus; exact Hk. }
    replace (S n + k) with (S (n + k)) by lia.
    rewrite (subst_cidx_in_cty_lift_1_comm_gen D (lift_cty 0 n T) (lift_cidx 0 n val) 0 (n + k) ltac:(lia) Hn).
    rewrite (IH k T val Hk), lift_cty_add. reflexivity.
Qed.

Lemma cty_uses_kinds_lift_n_false : forall (D : JoinDomain) (T : cty D) n k,
  cty_uses_kinds true false false false false false false k T = false ->
  cty_uses_kinds true false false false false false false (n + k) (lift_cty 0 n T) = false.
Proof.
  intros D T n k H.
  replace (lift_cty 0 n T) with (ren_cty (plus n) T)
    by (unfold lift_cty; apply ren_cty_ext; intro y; unfold ren_lift; destruct (y <? 0) eqn:E; nat_bool_hyps; lia).
  apply cty_uses_kinds_ren_plus; exact H.
Qed.

Lemma branch_rel_firstn : forall (D : JoinDomain) n (u v : list (grade D)),
  branch_rel u v -> branch_rel (firstn n u) (firstn n v).
Proof.
  intros D n. induction n as [| n IH]; intros [| a u] [| b v] H; cbn in *; try apply branch_rel_refl;
    unfold branch_rel in *; destruct (grade_join D) eqn:Hj; try discriminate; try congruence;
    try solve [inversion H].
  inversion H as [| ? ? ? ? Ha Hrest]; subst; constructor; [assumption | apply (IH u v); exact Hrest].
Qed.

Lemma branch_rel_skipn : forall (D : JoinDomain) n (u v : list (grade D)),
  branch_rel u v -> branch_rel (skipn n u) (skipn n v).
Proof.
  intros D n. induction n as [| n IH]; intros [| a u] [| b v] H; cbn in *; try exact H;
    try apply branch_rel_refl; unfold branch_rel in *; destruct (grade_join D) eqn:Hj;
    try discriminate; try congruence; try solve [inversion H].
  inversion H as [| ? ? ? ? Ha Hrest]; subst; apply (IH u v); exact Hrest.
Qed.

Lemma vec_is_zero_iff : forall (D : JoinDomain) (u : list (grade D)),
  vec_is_zero u = true <-> u = vec_zero (length u).
Proof.
  intros D u. induction u as [| a u [IH1 IH2]]; cbn; [split; reflexivity |].
  split; intro H.
  - apply andb_true_iff in H as [Ha Hu]. destruct (grade_eqb_spec D a zero); [| discriminate].
    subst a; f_equal; apply IH1; exact Hu.
  - inversion H as [[H1 H2]]. destruct (grade_eqb_spec D zero zero); [| contradiction].
    apply andb_true_iff; split; [reflexivity | rewrite <- H2; apply IH2; exact H2].
Qed.

Lemma branch_rel_vec_is_zero : forall (D : JoinDomain),
  ErasureDomain D ->
  forall n (u : list (grade D)),
  branch_rel u (vec_zero n) ->
  vec_is_zero u = true.
Proof.
  intros D ED n u H. unfold branch_rel in H. destruct (grade_join D).
  - pose proof (vec_allows_length D u (vec_zero n) H) as Hlen.
    unfold vec_zero in Hlen; rewrite repeat_length in Hlen; subst n.
    rewrite (vec_allows_zero_eq D ED u H). apply vec_is_zero_iff; unfold vec_zero; rewrite repeat_length; reflexivity.
  - subst u. apply vec_is_zero_iff; unfold vec_zero; rewrite repeat_length; reflexivity.
Qed.

Lemma cenv_demand_rel_trans : forall (D : JoinDomain) (env1 env2 env3 : cenv D),
  cenv_demand_rel env1 env2 ->
  cenv_demand_rel env2 env3 ->
  cenv_demand_rel env1 env3.
Proof.
  intros D env1 env2 env3 [Hl12 H12] [Hl23 H23].
  pose proof (cenv_demand_rel_alpha D env1 env2 (conj Hl12 H12)) as Ha12.
  split; [lia |].
  intros x e3 Hl3.
  destruct (H23 x e3 Hl3) as [e2 [Hl2 [Hb2 [Ha2 [Hbr2 Hfn2]]]]].
  destruct (H12 x e2 Hl2) as [e1 [Hl1 [Hb1 [Ha1 [Hbr1 Hfn1]]]]].
  exists e1; split; [exact Hl1 |].
  split; [congruence | split; [eapply cty_alpha_eq_trans; eassumption | split; [eapply branch_rel_trans; eassumption |]]].
  intros row Hrow1 Hva3.
  assert (Hrow2 : CTypeDemand (skipn (S x) env2) (cannotation e2) row) by
    (eapply CTypeDemand_alpha; [exact Ha1 | apply cenv_alpha_eq_skipn; exact Ha12 | exact Hrow1]).
  apply (Hfn1 row Hrow1 (Hfn2 row Hrow2 Hva3)).
Qed.

Lemma CRecordExtendEnv_nat_safe : forall (D : JoinDomain) (b : cbinding D) env_b,
  cannotation b = CNat ->
  forall env1 bs fields body_env,
  CRecordExtendEnv env1 bs fields body_env ->
  forall env_a, env1 = env_a ++ b :: env_b ->
  Forall (fun '(_, _, ft) => cty_uses_kinds true false false false false false false (length env_a) ft = false) fields.
Proof.
  intros D b env_b Hb env1 bs fields body_env Hext.
  induction Hext; intros env_a Henv; subst env.
  - constructor.
  - constructor.
    + exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ H env_a eq_refl).
    + pose proof (IHHext ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a) eq_refl) as Hrest.
      clear - Hrest. induction rest as [| [[n0 g0] t0] rs IH]; inversion Hrest; subst; constructor.
      * apply cty_uses_kinds_lift_inv; exact H1.
      * apply IH; exact H2.
Qed.

Lemma record_extend_subst_cidx : forall (D : JoinDomain) (idx : cidx D) z env_b (b : cbinding D),
  cannotation b = CNat ->
  CIdxDemand env_b idx z ->
  forall env1 bs fields body_env env_a fields',
  env1 = env_a ++ b :: env_b ->
  cenv_nat_safe env_a (length env_a) ->
  CRecordExtendEnv env1 bs fields body_env ->
  Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) =>
    n1 = n2 /\ g1 = g2 /\
    cty_alpha_eq t1 (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) t2)) fields' fields ->
  exists ext_a body_env',
    body_env = ext_a ++ b :: env_b /\
    length ext_a = length fields + length env_a /\
    cenv_nat_safe ext_a (length ext_a) /\
    CRecordExtendEnv (subst_cidx_cenv idx z env_a ++ env_b) bs fields' body_env' /\
    cenv_demand_rel body_env' (subst_cidx_cenv idx z ext_a ++ env_b).
Proof.
  intros D idx z env_b b Hb Hidx env1 bs fields body_env env_a fields' Henv Hsafe Hext Hfs.
  pose proof (CRecordExtendEnv_nat_safe D b env_b Hb _ _ _ _ Hext env_a Henv) as Hnat_fs.
  revert env_a fields' Henv Hsafe Hfs Hnat_fs.
  induction Hext; intros env_a fields' Henv Hsafe Hfs Hnat_fs; subst env.
  - inversion Hfs; subst.
    exists env_a, (subst_cidx_cenv idx z env_a ++ env_b).
    split; [reflexivity | split; [reflexivity | split; [exact Hsafe | split; [constructor | apply cenv_demand_rel_refl]]]].
  - inversion Hfs as [| [[fn1 fg1] ft1] [[fn2 fg2] ft2] fs1' fs2' [Hn [Hg Hft]] Hrest]; subst.
    inversion Hnat_fs as [| ? ? Hft_safe Hrest_safe]; subst.
    destruct (subst_ctype_demand D idx z env_a b env_b ft row Hb Hsafe Hidx H) as [row' [Hrow' Hbr]].
    assert (Hrow1 : CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) ft1 row') by
      (eapply CTypeDemand_alpha_ty; [exact Hrow' | apply cty_alpha_eq_sym; exact Hft]).
    assert (Hsafe1 : cenv_nat_safe ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a) (S (length env_a))) by
      (apply cenv_nat_safe_cons; [exact Hft_safe | exact Hsafe]).
    assert (Hfs1 : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) =>
      n1 = n2 /\ g1 = g2 /\
      cty_alpha_eq t1 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) t2))
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
    { clear - Hrest Hrest_safe.
      induction Hrest; inversion Hrest_safe; subst; constructor; [| apply IHHrest; exact H3].
      destruct x as [[n1 g1] t1], y as [[n2 g2] t2], H as [-> [-> Ht]].
      split; [reflexivity | split; [reflexivity |]].
      cbn [length] in *.
      eapply cty_alpha_eq_trans; [apply (ren_cty_alpha_eq D (ren_lift 0 1)); exact Ht |].
      replace (lift_cidx 0 (S (length env_a)) idx) with (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) by (rewrite lift_cidx_add; reflexivity).
      change (ren_cty (ren_lift 0 1) (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) t2))
        with (lift_cty 0 1 (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) t2)).
      rewrite <- (subst_cidx_in_cty_lift_1_comm_gen D t2 (lift_cidx 0 (length env_a) idx) 0 (length env_a) ltac:(lia) H2).
      apply cty_alpha_eq_refl. }
    assert (Hnat_rest : Forall (fun '(_, _, ft0) =>
      cty_uses_kinds true false false false false false false (S (length env_a)) ft0 = false)
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
    { clear - Hrest_safe. induction rest as [| [[n0 g0] t0] rs IH]; inversion Hrest_safe; subst; constructor; [| apply IH; exact H2].
      replace (S (length env_a)) with (1 + length env_a) by lia. apply cty_uses_kinds_lift_n_false; exact H1. }
    destruct (IHHext ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a)
                (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1') eq_refl Hsafe1 Hfs1 Hnat_rest)
      as [ext_a [body_env_0 [Hbody [Hlen_ext [Hsafe_ext [Hext0 Hrel0]]]]]].
    assert (Hfs_id : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\ cty_alpha_eq t1 t2)
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')
      (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) fs1')).
    { clear. induction fs1' as [| [[n0 g0] t0] rs IH]; constructor; [split; [reflexivity | split; [reflexivity | apply cty_alpha_eq_refl]] | exact IH]. }
    assert (Hrel_head : cenv_demand_rel
      ({| cbinder := b0; cannotation := ft1; ctype_uses := row' |} :: subst_cidx_cenv idx z env_a ++ env_b)
      (subst_cidx_cenv idx z ({| cbinder := b0; cannotation := ft; ctype_uses := row |} :: env_a) ++ env_b)).
    { cbn [subst_cidx_cenv app]. apply cenv_demand_rel_cons;
        [apply cenv_demand_rel_refl | exact Hft | exact Hrow1 | exact Hbr]. }
    destruct (record_extend_demand_rel D _ bs _ body_env_0 _ _ Hext0 Hrel_head Hfs_id) as [body_env' [Hext_rest Hrel_rest]].
    exists ext_a, body_env'.
    split; [exact Hbody | split; [rewrite length_map in Hlen_ext; cbn [length] in *; lia | split; [exact Hsafe_ext | split]]].
    + eapply CRecordExtCons; [exact Hrow1 | exact Hext_rest].
    + eapply cenv_demand_rel_trans; [exact Hrel_rest | exact Hrel0].
Qed.

Lemma app_result_ty_subst_cidx : forall (D : JoinDomain) k (val : cidx D) dom cod arg res_ty dom0 cod0,
  cty_uses_kinds true false false false false false false k dom = false ->
  cty_uses_kinds true false false false false false false (S k) cod = false ->
  (match dom with CUniv _ => cty_uses_kinds false true false false false false false 0 cod = false | _ => True end) ->
  (match arg with CNatVal i => cidx_uses_kinds true false false false false k i = false | _ => True end) ->
  (match dom with CUniv _ => match arg with CTypeVal t => cty_uses_kinds true false false false false false false k t = false | _ => True end | _ => True end) ->
  (match dom with CUniv _ => match arg with CVar y => y <> k | _ => True end | _ => True end) ->
  cty_alpha_eq dom0 (subst_cidx_in_cty k val dom) ->
  cty_alpha_eq cod0 (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) cod) ->
  app_result_ty dom cod arg = Some res_ty ->
  exists res',
    app_result_ty dom0 cod0 (subst_cidx_in_cterm k val arg) = Some res' /\
    cty_alpha_eq res' (subst_cidx_in_cty k val res_ty).
Proof.
  intros D k val dom cod arg res_ty dom0 cod0 Hdom_safe Hcod_safe Hcod_tvar Harg_safe Ht_safe Hnvar Hdom0 Hcod0 Happ.
  assert (Hnone : match dom with CNat => term_as_cidx arg = None | CUniv _ => match arg with CTypeVal _ => False | CVar _ => False | _ => True end | _ => True end ->
    cty_uses_var 0 cod = false ->
    unshift_cty 0 cod = res_ty ->
    cty_uses_var 0 cod0 = false /\
    cty_alpha_eq (unshift_cty 0 cod0) (subst_cidx_in_cty k val res_ty)).
  { intros _ Hnf <-.
    assert (Hnv : cty_uses_var 0 (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) cod) = false).
    { apply cty_uses_var_subst_cidx_0; [lia | exact Hcod_safe | apply lift_cidx_uses_var_0 | exact Hnf]. }
    split.
    - rewrite (cty_uses_var_alpha_eq D 0 cod0 _ Hcod0). exact Hnv.
    - eapply cty_alpha_eq_trans; [apply cty_alpha_eq_unshift; exact Hcod0 |].
      rewrite (subst_cidx_in_cty_unshift_0 D cod val k Hnf Hcod_safe). apply cty_alpha_eq_refl. }
  destruct dom; unfold app_result_ty in Happ |- *; cbn [subst_cidx_in_cty] in Hdom0;
    [
    | destruct dom0; unfold cty_alpha_eq in Hdom0; cbn in Hdom0; try discriminate;
      destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
      destruct (Hnone I eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0]
    | destruct dom0; unfold cty_alpha_eq in Hdom0; cbn in Hdom0; try discriminate;
      destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
      destruct (Hnone I eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0]
    |
    | destruct dom0; unfold cty_alpha_eq in Hdom0; cbn in Hdom0; try discriminate;
      destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
      destruct (Hnone I eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0] .. ].
  - apply cty_alpha_eq_CNat_inv in Hdom0; subst dom0.
    destruct arg; cbn [term_as_cidx subst_cidx_in_cterm] in *;
      [ | | destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
              destruct (Hnone eq_refl eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0] .. ].
    + destruct (lt_eq_lt_dec x k) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); cbn [term_as_cidx];
        inversion Happ; subst;
        (eexists; split; [reflexivity |
          eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hcod0 |];
          rewrite (subst_cidx_in_cty_subst_cidx D cod (CIdxVar _) val 0 k ltac:(lia) ltac:(cbn; reflexivity) Hcod_safe);
          cbn [subst_cidx]; repeat (rw_nat_bool; cbv iota); apply cty_alpha_eq_refl]).
    + inversion Happ; subst. eexists; split; [reflexivity |].
      eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hcod0 |].
      rewrite (subst_cidx_in_cty_subst_cidx D cod i val 0 k ltac:(lia) Harg_safe Hcod_safe);
        apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_CUniv_inv in Hdom0; subst dom0.
    destruct arg; cbn [term_as_cidx subst_cidx_in_cterm] in *;
      [ | destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
          destruct (Hnone I eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0]
      | destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
        destruct (Hnone I eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0]
      |
      | destruct (cty_uses_var 0 cod) eqn:Enf; [discriminate |]; inversion Happ; subst;
        destruct (Hnone I eq_refl eq_refl) as [Enf0 Ha0]; rewrite Enf0; eexists; split; [reflexivity | exact Ha0] .. ].
    + destruct (Nat.eq_dec x k) as [-> | Hne]; [exfalso; exact (Hnvar eq_refl) |].
      destruct (lt_eq_lt_dec x k) as [[Hlt | ->] | Hgt]; [| exfalso; exact (Hne eq_refl) |]; repeat (rw_nat_bool; cbv iota); cbn [term_as_cidx];
        inversion Happ; subst;
        (eexists; split; [reflexivity |
          eapply cty_alpha_eq_trans; [apply cty_alpha_eq_subst_tvar; [apply cty_alpha_eq_refl | exact Hcod0] |];
          pose proof (subst_cidx_tvar_in_cty D cod (CTVar x) val k ltac:(cbn; rw_nat_bool; reflexivity) Hcod_safe Hcod_tvar) as Hcm;
          cbn [Nat.add subst_cidx_in_cty] in Hcm;
          try (rewrite (proj2 (Nat.ltb_lt x k) ltac:(lia)) in Hcm);
          try (rewrite (proj2 (Nat.ltb_ge x k) ltac:(lia)) in Hcm);
          try (rewrite (proj2 (Nat.eqb_neq x k) ltac:(lia)) in Hcm);
          cbv iota in Hcm; rewrite Hcm; apply cty_alpha_eq_refl]).
    + inversion Happ; subst. eexists; split; [reflexivity |].
      eapply cty_alpha_eq_trans; [apply cty_alpha_eq_subst_tvar; [apply cty_alpha_eq_refl | exact Hcod0] |].
      pose proof (subst_cidx_tvar_in_cty D cod T val k Ht_safe Hcod_safe Hcod_tvar) as Hcm;
      rewrite Hcm; apply cty_alpha_eq_refl.
Qed.

Lemma term_as_cidx_subst_none : forall (D : JoinDomain) k (val : cidx D) t,
  term_as_cidx t = None ->
  term_as_cidx (subst_cidx_in_cterm k val t) = None.
Proof.
  intros D k val t H. destruct t; cbn in *; try discriminate; reflexivity.
Qed.

Lemma term_as_cidx_subst_some : forall (D : JoinDomain) (b : cbinding D) env_a env_b t j (i val : cidx D),
  cannotation b = CNat ->
  CoreDerives (env_a ++ b :: env_b) t j ->
  term_as_cidx t = Some i ->
  cidx_uses_kinds true false false false false (length env_a) i = false /\
  term_as_cidx (subst_cidx_in_cterm (length env_a) val t) =
    Some (subst_cidx (length env_a) val i).
Proof.
  intros D b env_a env_b t j i val Hb Hd Ht.
  destruct t; cbn in Ht; try discriminate; inversion Ht; subst i.
  - cbn [cidx_uses_kinds subst_cidx_in_cterm subst_cidx]. split; [reflexivity |]. destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); cbn; reflexivity.
  - inversion Hd; subst.
    lazymatch goal with Hc : CIdxDemand _ _ _ |- _ => split; [exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hc env_a eq_refl) | cbn; reflexivity] end.
Qed.

Lemma skipn_vec_zero_app : forall (D : JoinDomain) n (l : list (grade D)),
  skipn n (vec_zero n ++ l) = l.
Proof.
  intros D n l. unfold vec_zero.
  rewrite skipn_app, repeat_length, Nat.sub_diag, skipn_all2 by (rewrite repeat_length; lia).
  reflexivity.
Qed.

Lemma branch_rel_app : forall (D : JoinDomain) (u1 u2 v1 v2 : list (grade D)),
  branch_rel u1 v1 -> branch_rel u2 v2 -> branch_rel (u1 ++ u2) (v1 ++ v2).
Proof.
  intros D u1 u2 v1 v2 H1 H2. unfold branch_rel in *.
  destruct (grade_join D); [apply Forall2_app; assumption | subst; reflexivity].
Qed.

Lemma lift_cidx_1_S : forall (D : JoinDomain) k (i : cidx D),
  lift_cidx 0 (S k) i = lift_cidx 0 1 (lift_cidx 0 k i).
Proof.
  intros D k i. symmetry. apply (lift_cidx_add D 1 k i).
Qed.

Lemma lift_cidx_2_SS : forall (D : JoinDomain) k (i : cidx D),
  lift_cidx 0 (S (S k)) i = lift_cidx 0 2 (lift_cidx 0 k i).
Proof.
  intros D k i. symmetry. apply (lift_cidx_add D 2 k i).
Qed.

Ltac rw_nat_bool_in H :=
  repeat match type of H with
  | context [?a <? ?b] =>
      first [ rewrite (proj2 (Nat.ltb_lt a b) ltac:(nat_bool_hyps; lia)) in H
            | rewrite (proj2 (Nat.ltb_ge a b) ltac:(nat_bool_hyps; lia)) in H ]
  | context [?a =? ?b] =>
      first [ rewrite (proj2 (Nat.eqb_eq a b) ltac:(nat_bool_hyps; lia)) in H
            | rewrite (proj2 (Nat.eqb_neq a b) ltac:(nat_bool_hyps; lia)) in H ]
  end; cbv iota in H.

Lemma app_type_arg_demand_length : forall (D : JoinDomain) (dom : cty D) (arg : cterm D) (u v : list (grade D)) n,
  length u = n -> length v = n -> length (app_type_arg_demand dom arg u v) = n.
Proof.
  intros D dom arg u v n Hu Hv. unfold app_type_arg_demand.
  destruct dom; try exact Hu. destruct arg; try exact Hu; exact Hv.
Qed.

Lemma branch_rel_app_type_arg_demand : forall (D : JoinDomain) k (val : cidx D) (z : list (grade D))
  (dom dom0 : cty D) (arg : cterm D) (u v u' v' : list (grade D)),
  cty_alpha_eq dom0 (subst_cidx_in_cty k val dom) ->
  branch_rel u' (vec_subst k z u) ->
  branch_rel v' (vec_subst k z v) ->
  branch_rel (app_type_arg_demand dom0 (subst_cidx_in_cterm k val arg) u' v')
             (vec_subst k z (app_type_arg_demand dom arg u v)).
Proof.
  intros D k val z dom dom0 arg u v u' v' Hdom Hu Hv.
  unfold app_type_arg_demand, cty_alpha_eq in *.
  destruct dom; cbn in Hdom; destruct dom0; cbn in Hdom; try discriminate; try exact Hu.
  destruct arg; cbn; try exact Hu;
    [destruct (lt_eq_lt_dec x k) as [[? | ?] | ?]; repeat (rw_nat_bool; cbv iota); exact Hu | exact Hv].
Qed.

Theorem core_value_substitution : forall (D : JoinDomain),
  ErasureDomain D ->
  (grade_join D = None -> forall g, @allows D zero g -> g = zero) ->
  forall (idx : cidx D) z env_a (b : cbinding D) env_b t j,
  cannotation b = CNat ->
  cenv_nat_safe env_a (length env_a) ->
  CIdxDemand env_b idx z ->
  CoreDerives (env_a ++ b :: env_b) t j ->
  exists j',
    CoreDerives (subst_cidx_cenv idx z env_a ++ env_b)
      (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) t) j' /\
    cty_alpha_eq (cresult_type j')
      (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) (cresult_type j)) /\
    branch_rel (ccomp_demand j') (vec_subst (length env_a) z (ccomp_demand j)) /\
    branch_rel (ctype_demand_row j') (vec_subst (length env_a) z (ctype_demand_row j)).
Proof.
  intros D ED Hz_join idx z env_a b env_b t j Hb Hsafe Hidx H.
  assert (Hz_len : length z = length env_b) by (eapply cidx_demand_length; exact Hidx).
  remember (env_a ++ b :: env_b) as env1 eqn:Henv1.
  revert env_a Henv1 Hsafe.
  induction H using CoreDerives_ind_mut with
    (P := fun env1 t j _ => forall env_a, env1 = env_a ++ b :: env_b ->
      cenv_nat_safe env_a (length env_a) ->
      exists j',
        CoreDerives (subst_cidx_cenv idx z env_a ++ env_b)
          (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) t) j' /\
        cty_alpha_eq (cresult_type j')
          (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) (cresult_type j)) /\
        branch_rel (ccomp_demand j') (vec_subst (length env_a) z (ccomp_demand j)) /\
        branch_rel (ctype_demand_row j') (vec_subst (length env_a) z (ctype_demand_row j)))
    (P0 := fun env1 fs u v _ => forall env_a, env1 = env_a ++ b :: env_b ->
      cenv_nat_safe env_a (length env_a) ->
      exists u' v',
        CRecordElemDerives (subst_cidx_cenv idx z env_a ++ env_b)
          (map (fun '(fn, fg, ft, fv) =>
             (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft,
                      subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) fv)) fs)
          u' v' /\
        branch_rel u' (vec_subst (length env_a) z u) /\
        branch_rel v' (vec_subst (length env_a) z v));
    intros env_a Henv1 Hsafe; subst env; cbn [subst_cidx_in_cterm].
  - (* CoreVar *)
    lazymatch goal with
    | Hl : clookup _ x = Some e, Htd : CTypeDemand _ (cannotation e) row, Hva : vec_allows row (ctype_uses e) |- _ =>
        destruct (lt_eq_lt_dec x (length env_a)) as [[Hlt | Heq_x] | Hgt]; repeat (rw_nat_bool; cbv iota);
        [ destruct (subst_cidx_lookup_lt D idx z env_a b env_b x e Hlt Hsafe Hl) as [e' [Hl' [Hren [Hvec [Hsk1 Hsk2]]]]];
          destruct (subst_cidx_lookup_lt_ann_raw D idx z env_a b env_b x e Hlt Hl) as [e_raw [Hl_raw [Hann_raw [Hvec_raw [Hsk1_raw Hsk2_raw]]]]];
          assert (He'_eq : e' = e_raw) by (rewrite Hl' in Hl_raw; inversion Hl_raw; reflexivity); subst e_raw;
          rewrite Hsk2 in Htd;
          assert (Hsafe_sk : cenv_nat_safe (skipn (S x) env_a) (length (skipn (S x) env_a))) by (apply cenv_nat_safe_skipn; exact Hsafe);
          destruct (subst_ctype_demand D idx z (skipn (S x) env_a) b env_b (cannotation e) row Hb Hsafe_sk Hidx Htd) as [row' [Hrow' Hbr_row]];
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
          | cbn [ccomp_demand]; rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_lt;
            [apply branch_rel_refl | exact Hz_len | exact Hlt]
          | cbn [ctype_demand_row]; rewrite Hvec; apply branch_rel_refl ]
        | subst x;
          assert (Heqb : e = b) by (unfold clookup in Hl; rewrite nth_error_app2, Nat.sub_diag in Hl by lia; inversion Hl; reflexivity);
          subst e;
          rewrite skipn_app, Nat.sub_succ_l in Htd by lia;
          rewrite Nat.sub_diag, skipn_all2 in Htd by lia; cbn [app skipn] in Htd;
          rewrite Hb in Htd; apply CTypeDemand_CNat_inv in Htd; subst row;
          destruct (weaken_cidx_demand_app_left D env_b idx z Hidx (subst_cidx_cenv idx z env_a)) as [z' [Hz' Hbr_z]];
          rewrite subst_cidx_cenv_length in Hz', Hbr_z;
          eexists; split; [| split; [| split]];
          [ apply CoreNatVal; exact Hz'
          | cbn [cresult_type]; rewrite Hb; cbn; apply cty_alpha_eq_refl
          | cbn [ccomp_demand]; rewrite length_app; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_eq, vec_scale_one by exact Hz_len;
            exact Hbr_z
          | cbn [ctype_demand_row];
            rewrite length_app, subst_cidx_cenv_length;
            assert (Hlen_ub : length z = length (ctype_uses b)) by
              (rewrite <- (vec_allows_length D _ _ Hva), vec_zero_length; exact Hz_len);
            rewrite (vec_subst_zero_prefix D (length env_a) z (ctype_uses b) Hlen_ub);
            replace (vec_zero (D := D) (length env_a + length env_b))
              with (vec_zero (D := D) (length env_a) ++ vec_zero (D := D) (length env_b))
              by (unfold vec_zero; rewrite repeat_app; reflexivity);
            apply branch_rel_app; [apply branch_rel_refl | apply vec_allows_zero_branch_rel; assumption] ]
        | destruct (subst_cidx_lookup_gt_ann D idx z env_a b env_b x e Hgt Hl) as [e' [Hl' [Hann' [Hren Hsk]]]];
          assert (Hx_len : x < length (env_a ++ b :: env_b)) by (eapply clookup_lt_length; exact Hl);
          rewrite length_app in Hx_len; cbn [length] in Hx_len;
          assert (Hlen_e : length (vec_zero (S x) ++ ctype_uses e) = S (length env_a + length env_b)) by
            (rewrite length_app, vec_zero_length;
             rewrite <- (vec_allows_length D row (ctype_uses e) Hva);
             rewrite (ctype_demand_length D _ _ _ Htd), length_skipn, length_app; cbn [length]; lia);
          destruct (subst_cidx_lookup_gt D idx z env_a b env_b x e Hgt Hz_len Hlen_e Hl) as [e_gt [Hl0 [Hren0 [Hvec0 Hsk0]]]];
          assert (He_gt : e' = e_gt) by (rewrite Hl' in Hl0; inversion Hl0; reflexivity); subst e_gt;
          rewrite <- Hsk0 in Htd;
          assert (Huses' : ctype_uses e' = ctype_uses e) by
            (assert (Hvs : vec_subst (length env_a) z (vec_zero (S x) ++ ctype_uses e) =
                           vec_zero (S (x - 1)) ++ ctype_uses e) by
               (replace (vec_zero (D := D) (S x) ++ ctype_uses e)
                  with (vec_zero (D := D) (S (length env_a)) ++ (vec_zero (D := D) (x - length env_a) ++ ctype_uses e))
                  by (rewrite app_assoc; unfold vec_zero; rewrite <- repeat_app; f_equal; f_equal; lia);
                rewrite vec_subst_zero_prefix by (rewrite length_app, vec_zero_length; rewrite length_app, vec_zero_length in Hlen_e; lia);
                rewrite app_assoc; unfold vec_zero; rewrite <- repeat_app; f_equal; f_equal; lia);
             rewrite Hvs in Hvec0;
             pose proof (f_equal (skipn (S (x - 1))) Hvec0) as Hsk_u;
             rewrite !skipn_vec_zero_app in Hsk_u; exact Hsk_u);
          rewrite <- Hann' in Htd; rewrite <- Huses' in Hva;
          eexists; split; [| split; [| split]];
          [ eapply CoreVar; [exact Hl' | exact Htd | exact Hva]
          | cbn [cresult_type]; rewrite Hren0; apply cty_alpha_eq_refl
          | cbn [ccomp_demand]; rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_single_gt;
            [apply branch_rel_refl | exact Hz_len | exact Hgt | lia]
          | cbn [ctype_demand_row]; rewrite Hvec0; apply branch_rel_refl ] ]
    end.
  - (* CoreNatVal *)
    lazymatch goal with
    | Hd : CIdxDemand _ i d |- _ =>
        destruct (subst_cidx_demand D idx z env_a b env_b i d Hb Hsafe Hidx Hd) as [d' [Hd' Hbrd]];
        eexists; split; [| split; [| split]];
        [ apply CoreNatVal; exact Hd'
        | cbn [cresult_type subst_cidx_in_cty]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; exact Hbrd
        | cbn [ctype_demand_row]; rewrite !length_app, subst_cidx_cenv_length; cbn [length];
          rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len; apply branch_rel_refl ]
    end.
  - (* CoreBoolVal *)
    eexists; split; [| split; [| split]];
    [ apply CoreBoolVal
    | cbn [cresult_type subst_cidx_in_cty]; apply cty_alpha_eq_refl
    | cbn [ccomp_demand]; rewrite !length_app, subst_cidx_cenv_length; cbn [length];
      rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len; apply branch_rel_refl
    | cbn [ctype_demand_row]; rewrite !length_app, subst_cidx_cenv_length; cbn [length];
      rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len; apply branch_rel_refl ].
  - (* CoreTypeVal *)
    lazymatch goal with
    | Hd : CTypeDemand _ T v, Hlv : CUniverseLevel _ T lvl |- _ =>
        destruct (subst_ctype_demand D idx z env_a b env_b T v Hb Hsafe Hidx Hd) as [v' [Hv' Hbrv]];
        pose proof (subst_cuniverse_level D idx z env_a b env_b T lvl Hb Hlv) as Hlv';
        eexists; split; [| split; [| split]];
        [ eapply CoreTypeVal; [exact Hv' | exact Hlv']
        | cbn [cresult_type subst_cidx_in_cty]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; rewrite !length_app, subst_cidx_cenv_length; cbn [length];
          rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len; apply branch_rel_refl
        | cbn [ctype_demand_row]; exact Hbrv ]
    end.
  - (* CoreLam *)
    lazymatch goal with
    | Ha : CTypeDemand _ dom a, Hs : allows (nth_grade u 0) s, Hr : allows (nth_grade v 0) r |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Ha env_a eq_refl) as Hdom_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b dom a Hb Hsafe Hidx Ha) as [a' [Ha' Hbra]];
        assert (Hsafe1 : cenv_nat_safe ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (IHCoreDerives ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env_a) eq_refl Hsafe1)
          as [[cod1 u1 v1] [Hb1 [Hcod [Hu Hv]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hcod, Hu, Hv;
        cbn [subst_cidx_cenv length app] in Hb1, Hcod, Hu, Hv;
        rewrite (lift_cidx_1_S D (length env_a) idx) in Hb1, Hcod;
        assert (Hrel1 : cenv_demand_rel
          ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) dom; ctype_uses := a' |}
           :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) dom;
              ctype_uses := vec_subst (length env_a) z a |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | apply cty_alpha_eq_refl | exact Ha' | exact Hbra]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hb1 _ Hrel1) as [[cod2 u2 v2] [Hb2 [Hcod2 [Hu2 Hv2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hcod2, Hu2, Hv2;
        lazymatch goal with
        | Hbd : CoreDerives (_ :: env_a ++ b :: env_b) _ _ |- _ =>
            pose proof (core_derives_lengths D _ _ _ Hbd) as [Hlen_u Hlen_v]
        end;
        cbn [ccomp_demand ctype_demand_row length] in Hlen_u, Hlen_v; rewrite length_app in Hlen_u, Hlen_v; cbn [ccomp_demand ctype_demand_row length] in Hlen_u, Hlen_v;
        assert (Hu_tr : branch_rel u2 (vec_subst (S (length env_a)) z u)) by (eapply branch_rel_trans; eassumption);
        assert (Hv_tr : branch_rel v2 (vec_subst (S (length env_a)) z v)) by (eapply branch_rel_trans; eassumption);
        assert (Hs2 : allows (nth_grade u2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hs]);
        assert (Hr2 : allows (nth_grade v2 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hv_tr) | rewrite vec_subst_nth_lt by lia; exact Hr]);
        eexists; split; [| split; [| split]];
        [ eapply CoreLam; [exact Ha' | exact Hb2 | exact Hs2 | exact Hr2]
        | cbn [cresult_type subst_cidx_in_cty];
          assert (Hcod_eq : cty_alpha_eq cod2 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) cod)) by
            (eapply cty_alpha_eq_trans; eassumption);
          unfold cty_alpha_eq in *; cbn; rewrite Hcod_eq; reflexivity
        | cbn [ccomp_demand]; rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu_tr
        | cbn [ctype_demand_row];
          pose proof (ctype_demand_length D _ _ _ Ha) as Hlen_a;
          rewrite length_app in Hlen_a; cbn [ccomp_demand ctype_demand_row length] in Hlen_a;
          rewrite (vec_subst_add D (length env_a) z a (tl v) (length env_b)) by (try exact Hz_len; destruct v; cbn in *; lia);
          apply branch_rel_add; [exact Hbra | rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hv_tr] ]
    end.
  - (* CoreApp *)
    lazymatch goal with
    | Hdm_eq : cty_alpha_eq kind dom,
      Ha_dom : CTypeDemand _ dom a_dom,
      Hb_cod : CTypeDemand _ cod b0,
      Hbr_allow : allows (nth_grade b0 0) r,
      Huniv : forall lvl arg_ty, dom = CUniv lvl -> _,
      Happ : app_result_ty dom cod arg = Some res_ty,
      Hz_ty : z_type = app_type_arg_demand dom arg u_arg v_arg |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[rt_fn w' v_fn'] [Hfn' [Hrt_fn [Hw' Hv_fn']]]];
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[rt_arg u_arg' v_arg'] [Harg' [Hrt_arg [Hu_arg' Hv_arg']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in *;
        destruct (cty_alpha_eq_CPi_inv D rt_fn x s r
                    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) dom)
                    (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) cod) Hrt_fn)
          as [x0 [dom0 [cod0 [-> [Hdom0 Hcod0]]]]];
        rewrite lift_cidx_add in Hcod0;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Ha_dom env_a eq_refl) as Hdom_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hb_cod ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) eq_refl) as Hcod_safe;
        cbn [length] in Hcod_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b dom a_dom Hb Hsafe Hidx Ha_dom) as [a_dom' [Ha_dom' Hbra]];
        assert (Ha_dom0 : CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) dom0 a_dom') by
          (eapply CTypeDemand_alpha_ty; [exact Ha_dom' | apply cty_alpha_eq_sym; exact Hdom0]);
        assert (Hsafe_x : cenv_nat_safe ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (subst_ctype_demand D idx z ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env_a) b env_b cod b0 Hb Hsafe_x Hidx Hb_cod)
          as [b_cod' [Hb_cod' Hbrb]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hb_cod', Hbrb;
        rewrite (lift_cidx_1_S D (length env_a) idx) in Hb_cod';
        rewrite <- (lift_cidx_add D 1 (length env_a) idx) in Hcod0;
        assert (Hb_cod0 : CTypeDemand ({| cbinder := x0; cannotation := dom0; ctype_uses := a_dom' |} :: subst_cidx_cenv idx z env_a ++ env_b) cod0 b_cod') by
          (eapply CTypeDemand_alpha_ty;
           [ eapply CTypeDemand_alpha_env; [| exact Hb_cod'];
             constructor; [cbn; apply cty_alpha_eq_sym; exact Hdom0 | apply cenv_alpha_eq_refl]
           | apply cty_alpha_eq_sym; exact Hcod0 ]);
        assert (Hdm_eq0 : cty_alpha_eq rt_arg dom0) by
          (eapply cty_alpha_eq_trans; [exact Hrt_arg | eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hdm_eq | apply cty_alpha_eq_sym; exact Hdom0]]);
        pose proof (ctype_demand_length D _ _ _ Hb_cod) as Hlen_b;
        cbn [ccomp_demand ctype_demand_row length] in Hlen_b; rewrite length_app in Hlen_b; cbn [ccomp_demand ctype_demand_row length] in Hlen_b;
        assert (Hbr_allow0 : allows (nth_grade b_cod' 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | rewrite vec_subst_nth_lt by lia; exact Hbr_allow]);
        assert (Harg_safe : match arg with CNatVal i => cidx_uses_kinds true false false false false (length env_a) i = false | _ => True end) by
          (destruct arg; try exact I; inversion H0; subst;
           lazymatch goal with Hc : CIdxDemand _ _ _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hc env_a eq_refl) end);
        assert (Hnvar : match dom, arg with CUniv _, CVar y => y <> length env_a | _, _ => True end) by
          (destruct dom, arg; try exact I;
           lazymatch goal with |- ?y <> length env_a =>
             destruct (Nat.eq_dec y (length env_a)) as [-> |]; try assumption;
             inversion H0; subst;
             lazymatch goal with Hlk : clookup _ (length env_a) = Some ?ee |- _ =>
               assert (Heqb : ee = b) by (unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; reflexivity);
               subst ee; unfold cty_alpha_eq in Hdm_eq; rewrite erase_hints_ren, Hb in Hdm_eq; cbn in Hdm_eq; discriminate
             end
           end);
        assert (Hcod_tvar : match dom with CUniv _ => cty_uses_kinds false true false false false false false 0 cod = false | _ => True end) by
          (destruct dom; try exact I; eapply ctype_demand_uses_kinds; [exact Hb_cod | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]);
        assert (Ht_safe : match dom, arg with CUniv _, CTypeVal t => cty_uses_kinds true false false false false false false (length env_a) t = false | _, _ => True end) by
          (destruct dom, arg; try exact I; inversion H0; subst;
           lazymatch goal with |- cty_uses_kinds _ _ _ _ _ _ _ _ ?tt = false =>
             lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) tt _ |- _ =>
               exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd env_a eq_refl)
             end
           end);
        destruct (app_result_ty_subst_cidx D (length env_a) (lift_cidx 0 (length env_a) idx) dom cod arg res_ty dom0 cod0
                    Hdom_safe Hcod_safe Hcod_tvar Harg_safe Ht_safe Hnvar
                    Hdom0 Hcod0 Happ) as [res' [Hres' Hres_eq]];
        assert (Huniv0 : forall lvl arg_ty, dom0 = CUniv lvl ->
                  (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) arg = CTypeVal arg_ty \/
                   (exists y, subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) arg = CVar y /\ arg_ty = CTVar y)) ->
                  CUniverseLevel (subst_cidx_cenv idx z env_a ++ env_b) arg_ty lvl) by
          (intros lvl arg_ty Hdom0_u [Hctv | [y [Hcv ->]]];
           [ assert (Hdom_u : dom = CUniv lvl) by
               (subst dom0; unfold cty_alpha_eq in Hdom0; destruct dom; cbn in Hdom0; try discriminate; inversion Hdom0; reflexivity);
             destruct arg; cbn in Hctv; try discriminate;
             [ lazymatch type of Hctv with (if ?x0 =? _ then _ else _) = _ =>
                 destruct (Nat.eqb_spec x0 (length env_a)); [discriminate | destruct (Nat.ltb_spec x0 (length env_a)); discriminate]
               end
             | inversion Hctv; subst arg_ty;
               eapply subst_cuniverse_level; [exact Hb | apply Huniv with (lvl := lvl); [exact Hdom_u | left; reflexivity]] ]
           | assert (Hdom_u : dom = CUniv lvl) by
               (subst dom0; unfold cty_alpha_eq in Hdom0; destruct dom; cbn in Hdom0; try discriminate; inversion Hdom0; reflexivity);
             destruct arg; cbn in Hcv; try discriminate;
             lazymatch type of Hcv with (if ?y0 =? _ then _ else _) = _ =>
               destruct (lt_eq_lt_dec y0 (length env_a)) as [[Hlt | Heq_y] | Hgt];
               [ rewrite (proj2 (Nat.eqb_neq y0 (length env_a)) ltac:(lia)), (proj2 (Nat.ltb_lt y0 (length env_a)) Hlt) in Hcv;
                 inversion Hcv; subst y;
                 pose proof (subst_cuniverse_level D idx z env_a b env_b (CTVar y0) lvl Hb
                               (Huniv lvl (CTVar y0) Hdom_u (or_intror (ex_intro _ y0 (conj eq_refl eq_refl))))) as Hlv_s;
                 cbn [subst_cidx_in_cty] in Hlv_s;
                 rewrite (proj2 (Nat.ltb_lt y0 (length env_a)) Hlt) in Hlv_s; exact Hlv_s
               | subst y0; rewrite Nat.eqb_refl in Hcv; discriminate
               | rewrite (proj2 (Nat.eqb_neq y0 (length env_a)) ltac:(lia)), (proj2 (Nat.ltb_ge y0 (length env_a)) ltac:(lia)) in Hcv;
                 inversion Hcv; subst y;
                 pose proof (subst_cuniverse_level D idx z env_a b env_b (CTVar y0) lvl Hb
                               (Huniv lvl (CTVar y0) Hdom_u (or_intror (ex_intro _ y0 (conj eq_refl eq_refl))))) as Hlv_s;
                 cbn [subst_cidx_in_cty] in Hlv_s;
                 rewrite (proj2 (Nat.ltb_ge y0 (length env_a)) ltac:(lia)), (proj2 (Nat.eqb_neq y0 (length env_a)) ltac:(lia)) in Hlv_s;
                 exact Hlv_s ]
             end ]);
        eexists; split; [| split; [| split]];
        [ eapply CoreApp; [exact Hfn' | exact Harg' | exact Hdm_eq0 | exact Ha_dom0 | exact Hb_cod0 | exact Hbr_allow0
                          | exact Huniv0 | exact Hres' | reflexivity]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
          pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ua _];
          rewrite length_app in Hlen_w, Hlen_ua; cbn [ccomp_demand ctype_demand_row length] in Hlen_w, Hlen_ua;
          rewrite (vec_subst_add D (length env_a) z w (vec_scale s u_arg) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [exact Hw' | apply branch_rel_scale; exact Hu_arg']
        | cbn [ctype_demand_row];
          pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ua Hlen_va];
          rewrite length_app in Hlen_ua, Hlen_va; cbn [ccomp_demand ctype_demand_row length] in Hlen_ua, Hlen_va;
          assert (Hbr_z : branch_rel (app_type_arg_demand dom0 (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) arg) u_arg' v_arg')
                            (vec_subst (length env_a) z (app_type_arg_demand dom arg u_arg v_arg))) by
            (eapply branch_rel_app_type_arg_demand; [exact Hdom0 | exact Hu_arg' | exact Hv_arg']);
          rewrite Hz_ty;
          rewrite (vec_subst_add D (length env_a) z (tl b0) (vec_scale r (app_type_arg_demand dom arg u_arg v_arg)) (length env_b));
          [ rewrite vec_subst_scale; apply branch_rel_add; [rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbrb | apply branch_rel_scale; exact Hbr_z]
          | exact Hz_len
          | destruct b0; cbn in *; lia
          | rewrite vec_scale_length; eapply app_type_arg_demand_length; [lia | lia] ] ]
    end.
  - (* CLet *)
    lazymatch goal with
    | Hann : CTypeDemand _ ann a_ann, Hrhs_eq : cty_alpha_eq rhs_ty ann,
      Hs : allows (nth_grade u_bod 0) s, Hr : allows (nth_grade v_bod 0) r,
      Hnf : cty_uses_var 0 bod_ty = false |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hann env_a eq_refl) as Hann_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b ann a_ann Hb Hsafe Hidx Hann) as [a_ann' [Ha_ann' Hbra]];
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[rhs_ty' u_rhs' v_rhs'] [Hrhs' [Hrt_rhs [Hu_rhs' Hv_rhs']]]];
        assert (Hsafe1 : cenv_nat_safe ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (IHCoreDerives2 ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env_a) eq_refl Hsafe1)
          as [[bod_ty1 u_bod1 v_bod1] [Hbod1 [Hrt_bod1 [Hu_bod1 Hv_bod1]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hrt_rhs, Hu_rhs', Hv_rhs', Hrt_bod1, Hu_bod1, Hv_bod1, Hbod1;
        rewrite (lift_cidx_1_S D (length env_a) idx) in Hbod1, Hrt_bod1;
        assert (Hrel1 : cenv_demand_rel
          ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ann; ctype_uses := a_ann' |}
           :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ann;
              ctype_uses := vec_subst (length env_a) z a_ann |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | apply cty_alpha_eq_refl | exact Ha_ann' | exact Hbra]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hbod1 _ Hrel1) as [[bod_ty2 u_bod2 v_bod2] [Hbod2 [Hrt_bod2 [Hu_bod2 Hv_bod2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hrt_bod2, Hu_bod2, Hv_bod2;
        assert (Hbod_eq : cty_alpha_eq bod_ty2 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) bod_ty)) by
          (eapply cty_alpha_eq_trans; [exact Hrt_bod2 | exact Hrt_bod1]);
        assert (Hcod_safe : cty_uses_kinds true false false false false false false (S (length env_a)) bod_ty = false) by
          (exact (core_derives_nat_safe D b env_b Hb _ _ _ H0 ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env_a) eq_refl));
        assert (Hnf2 : cty_uses_var 0 bod_ty2 = false) by
          (rewrite (cty_uses_var_alpha_eq D 0 bod_ty2 _ Hbod_eq);
           apply cty_uses_var_subst_cidx_0; [lia | exact Hcod_safe | apply lift_cidx_uses_var_0 | exact Hnf]);
        assert (Hu_tr : branch_rel u_bod2 (vec_subst (S (length env_a)) z u_bod)) by (eapply branch_rel_trans; [exact Hu_bod2 | exact Hu_bod1]);
        assert (Hv_tr : branch_rel v_bod2 (vec_subst (S (length env_a)) z v_bod)) by (eapply branch_rel_trans; [exact Hv_bod2 | exact Hv_bod1]);
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_u Hlen_v];
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_ur Hlen_vr];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_u, Hlen_v, Hlen_ur, Hlen_vr;
        rewrite length_app in Hlen_u, Hlen_v, Hlen_ur, Hlen_vr; cbn [length] in Hlen_u, Hlen_v, Hlen_ur, Hlen_vr;
        assert (Hs2 : allows (nth_grade u_bod2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hs]);
        assert (Hr2 : allows (nth_grade v_bod2 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hv_tr) | rewrite vec_subst_nth_lt by lia; exact Hr]);
        eexists; split; [| split; [| split]];
        [ eapply CoreLet;
          [ exact Ha_ann' | exact Hrhs'
          | eapply cty_alpha_eq_trans; [exact Hrt_rhs | apply subst_cidx_alpha_eq; exact Hrhs_eq]
          | exact Hbod2 | exact Hs2 | exact Hr2 | exact Hnf2 ]
        | cbn [cresult_type];
          eapply cty_alpha_eq_trans; [apply cty_alpha_eq_unshift; exact Hbod_eq |];
          rewrite (subst_cidx_in_cty_unshift_0 D bod_ty (lift_cidx 0 (length env_a) idx) (length env_a) Hnf Hcod_safe);
          apply cty_alpha_eq_refl
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) z (tl u_bod) (vec_scale s u_rhs) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct u_bod; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu_tr | apply branch_rel_scale; exact Hu_rhs']
        | cbn [ctype_demand_row];
          assert (Hbr_z : branch_rel (app_type_arg_demand (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ann)
                                        (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) rhs) u_rhs' v_rhs')
                            (vec_subst (length env_a) z (app_type_arg_demand ann rhs u_rhs v_rhs))) by
            (eapply branch_rel_app_type_arg_demand; [apply cty_alpha_eq_refl | exact Hu_rhs' | exact Hv_rhs']);
          rewrite (vec_subst_add D (length env_a) z (tl v_bod) (vec_scale r (app_type_arg_demand ann rhs u_rhs v_rhs)) (length env_b));
          [ rewrite vec_subst_scale; apply branch_rel_add; [rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hv_tr | apply branch_rel_scale; exact Hbr_z]
          | exact Hz_len
          | destruct v_bod; cbn in *; lia
          | rewrite vec_scale_length; eapply app_type_arg_demand_length; [lia | lia] ] ]
    end.
  - (* CPair *)
    lazymatch goal with
    | Ha : CTypeDemand _ fst_ty a, Hb_snd : CTypeDemand _ snd_ty b0,
      Hr : allows (nth_grade b0 0) r,
      Hf_eq : cty_alpha_eq fst_act fst_ty,
      Happ : app_result_ty fst_ty snd_ty fst_val = Some exp_snd,
      Hs_eq : cty_alpha_eq snd_act exp_snd |- _ =>
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Ha env_a eq_refl) as Hfst_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hb_snd ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) eq_refl) as Hsnd_safe;
        cbn [length] in Hsnd_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b fst_ty a Hb Hsafe Hidx Ha) as [a' [Ha' Hbra]];
        assert (Hsafe1 : cenv_nat_safe ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (subst_ctype_demand D idx z ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env_a) b env_b snd_ty b0 Hb Hsafe1 Hidx Hb_snd)
          as [b' [Hb' Hbrb]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hb', Hbrb;
        rewrite (lift_cidx_1_S D (length env_a) idx) in Hb';
        assert (Hb0' : CTypeDemand ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) fst_ty; ctype_uses := a' |}
                                     :: subst_cidx_cenv idx z env_a ++ env_b)
                                   (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) snd_ty) b') by
          (eapply CTypeDemand_alpha_env;
           [| exact Hb']; constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]);
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[fst_act' u_l' v_l'] [Hl' [Hft' [Hu_l' Hv_l']]]];
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[snd_act' u_r' v_r'] [Hr' [Hsd' [Hu_r' Hv_r']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hft', Hu_l', Hv_l', Hsd', Hu_r', Hv_r';
        assert (Hnvar : match fst_ty, fst_val with CUniv _, CVar y => y <> length env_a | _, _ => True end) by
          (destruct fst_ty, fst_val; try exact I;
           lazymatch goal with |- ?y <> _ => destruct (Nat.eq_dec y (length env_a)) as [-> |]; try assumption end;
           inversion H; subst;
           lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
             assert (Heqb : ee = b) by (unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; reflexivity);
             subst ee; unfold cty_alpha_eq in Hf_eq; rewrite erase_hints_ren, Hb in Hf_eq; cbn in Hf_eq; discriminate
           end);
        assert (Hsnd_tvar : match fst_ty with CUniv _ => cty_uses_kinds false true false false false false false 0 snd_ty = false | _ => True end) by
          (destruct fst_ty; try exact I; eapply ctype_demand_uses_kinds; [exact Hb_snd | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]);
        assert (Hfv_nat : match fst_val with CNatVal i => cidx_uses_kinds true false false false false (length env_a) i = false | _ => True end) by
          (destruct fst_val; try exact I; inversion H; subst;
           lazymatch goal with Hcd : CIdxDemand _ _ _ |- _ => exact (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) end);
        assert (Hfv_t : match fst_ty, fst_val with CUniv _, CTypeVal t => cty_uses_kinds true false false false false false false (length env_a) t = false | _, _ => True end) by
          (destruct fst_ty, fst_val; try exact I; inversion H; subst;
           lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) _ _ |- _ => exact (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd env_a eq_refl) end);
        destruct (app_result_ty_subst_cidx D (length env_a) (lift_cidx 0 (length env_a) idx) fst_ty snd_ty fst_val exp_snd
                    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) fst_ty)
                    (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) snd_ty)
                    Hfst_safe Hsnd_safe Hsnd_tvar Hfv_nat Hfv_t Hnvar (cty_alpha_eq_refl _ _) ltac:(rewrite lift_cidx_add; apply cty_alpha_eq_refl) Happ)
          as [exp_snd' [Happ' Hexp_eq]];
        pose proof (ctype_demand_length D _ _ _ Ha) as Hlen_a;
        pose proof (ctype_demand_length D _ _ _ Hb_snd) as Hlen_b;
        cbn [length] in Hlen_a, Hlen_b; rewrite length_app in Hlen_a, Hlen_b; cbn [length] in Hlen_a, Hlen_b;
        assert (Hr'0 : allows (nth_grade b' 0) r) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbrb) | rewrite vec_subst_nth_lt by lia; exact Hr]);
        eexists; split; [| split; [| split]];
        [ eapply CorePair;
          [ exact Ha' | exact Hb0' | exact Hr'0 | exact Hl'
          | eapply cty_alpha_eq_trans; [exact Hft' | apply subst_cidx_alpha_eq; exact Hf_eq]
          | exact Hr' | exact Happ'
          | eapply cty_alpha_eq_trans; [exact Hsd' | eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hs_eq | apply cty_alpha_eq_sym; exact Hexp_eq]] ]
        | cbn [cresult_type subst_cidx_in_cty]; rewrite lift_cidx_add; apply cty_alpha_eq_refl
        | cbn [ccomp_demand];
          pose proof (core_derives_lengths D _ _ _ H) as [Hlen_l _];
          pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_r _];
          rewrite length_app in Hlen_l, Hlen_r; cbn [ccomp_demand ctype_demand_row length] in Hlen_l, Hlen_r;
          rewrite (vec_subst_add D (length env_a) z u_l u_r (length env_b)) by lia;
          apply branch_rel_add; assumption
        | cbn [ctype_demand_row];
          rewrite (vec_subst_add D (length env_a) z a (tl b0) (length env_b)) by (destruct b0; cbn in *; lia);
          apply branch_rel_add; [exact Hbra | rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbrb] ]
    end.
  - (* CLetPair *)
    lazymatch goal with
    | HA : CTypeDemand _ A a, HB : CTypeDemand _ B b0,
      Hmot : CTypeDemand _ mot v_mot, Hkap : allows (nth_grade v_mot 0) kappa,
      Hexp : exp_mot = spec_pair_body_cty 0 mot, Hmot_eq : cty_alpha_eq act_mot exp_mot,
      Hs1 : allows (nth_grade u_b 1) s, Hs0 : allows (nth_grade u_b 0) s,
      Hdep : match pr with CPair _ _ _ _ _ _ => _ | CVar _ => _ | _ => _ end,
      Hres : res_ty = spec_pair_subj_cty pr mot |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[prt' w' v_p'] [Hpr' [Hprt [Hw' Hv_p']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in Hprt, Hw', Hv_p';
        destruct (cty_alpha_eq_CSigma_inv D prt' z0 r
                    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A)
                    (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) B) Hprt)
          as [z1 [A0 [B0 [-> [HA0 HB0]]]]];
        rewrite <- (lift_cidx_1_S D (length env_a) idx) in HB0;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ HA env_a eq_refl) as HA_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ HB ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl) as HB_safe;
        cbn [length] in HB_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot ({| cbinder := 0; cannotation := CSigma z0 r A B; ctype_uses := vec_add a (tl b0) |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b A a Hb Hsafe Hidx HA) as [a' [Ha' Hbra]];
        assert (HA0' : CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) A0 a') by
          (eapply CTypeDemand_alpha_ty; [exact Ha' | apply cty_alpha_eq_sym; exact HA0]);
        assert (Hsafe_A : cenv_nat_safe ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (subst_ctype_demand D idx z ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) b env_b B b0 Hb Hsafe_A Hidx HB)
          as [b' [Hb' Hbrb]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hb', Hbrb;
        assert (HB0' : CTypeDemand ({| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b) B0 b') by
          (eapply CTypeDemand_alpha; cycle 2;
           [ exact Hb' | apply cty_alpha_eq_sym; exact HB0
           | constructor; [cbn; apply cty_alpha_eq_sym; exact HA0 | apply cenv_alpha_eq_refl] ]);
        assert (Hsafe_sig : cenv_nat_safe ({| cbinder := 0; cannotation := CSigma z0 r A B; ctype_uses := vec_add a (tl b0) |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; [cbn; rewrite HA_safe, HB_safe; reflexivity | exact Hsafe]);
        destruct (subst_ctype_demand D idx z ({| cbinder := 0; cannotation := CSigma z0 r A B; ctype_uses := vec_add a (tl b0) |} :: env_a) b env_b mot v_mot Hb Hsafe_sig Hidx Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := 0; cannotation := CSigma z1 r A0 B0; ctype_uses := vec_add a' (tl b') |} :: subst_cidx_cenv idx z env_a ++ env_b)
                                      (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) v_mot') by
          (eapply CTypeDemand_alpha_env;
           [| exact Hv_mot'];
           constructor; [cbn; unfold cty_alpha_eq in *; cbn; rewrite <- (lift_cidx_1_S D (length env_a) idx); rewrite HA0, HB0; reflexivity | apply cenv_alpha_eq_refl]);
        assert (Hsafe_B : cenv_nat_safe ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (S (length env_a)))) by
          (apply cenv_nat_safe_cons; [exact HB_safe | exact Hsafe_A]);
        destruct (IHCoreDerives2 ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl Hsafe_B)
          as [[act_mot1 u_b1 v_b1] [Hb1 [Hact1 [Hu_b1 Hv_b1]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hb1, Hact1, Hu_b1, Hv_b1;
        rewrite (lift_cidx_2_SS D (length env_a) idx) in Hb1, Hact1;
        assert (Hrel_B : cenv_demand_rel
          ({| cbinder := y; cannotation := B0; ctype_uses := b' |} :: {| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := y; cannotation := subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) B;
              ctype_uses := vec_subst (S (length env_a)) z b0 |}
           :: {| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A;
                 ctype_uses := vec_subst (length env_a) z a |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons;
           [ apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HA0 | exact HA0' | exact Hbra]
           | exact HB0
           | exact HB0'
           | exact Hbrb ]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hb1 _ Hrel_B) as [[act_mot2 u_b2 v_b2] [Hb2 [Hact2 [Hu_b2 Hv_b2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hact2, Hu_b2, Hv_b2;
        assert (Hu_tr : branch_rel u_b2 (vec_subst (S (S (length env_a))) z u_b)) by (eapply branch_rel_trans; [exact Hu_b2 | exact Hu_b1]);
        assert (Hact_tr : cty_alpha_eq act_mot2 (subst_cidx_in_cty (S (S (length env_a))) (lift_cidx 0 2 (lift_cidx 0 (length env_a) idx)) act_mot)) by
          (eapply cty_alpha_eq_trans; [exact Hact2 | exact Hact1]);
        assert (Hspec_body : subst_cidx_in_cty (S (S (length env_a))) (lift_cidx 0 2 (lift_cidx 0 (length env_a) idx)) (spec_pair_body_cty 0 mot) =
                             spec_pair_body_cty 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot)) by
          (rewrite <- (lift_cidx_2_SS D (length env_a) idx), (lift_cidx_1_S D (S (length env_a)) idx);
           apply subst_cidx_spec_pair_body; [lia | rewrite (lift_cidx_1_S D (length env_a) idx); apply cidx_uses_kinds_lift_c | exact Hmot_safe]);
        assert (Hmot_eq2 : cty_alpha_eq act_mot2 (spec_pair_body_cty 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))) by
          (eapply cty_alpha_eq_trans; [exact Hact_tr |]; rewrite <- Hspec_body, <- Hexp; apply subst_cidx_alpha_eq; exact Hmot_eq);
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ub _];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_vm, Hlen_w, Hlen_ub;
        rewrite length_app in Hlen_vm, Hlen_w, Hlen_ub; cbn [length] in Hlen_vm, Hlen_w, Hlen_ub;
        assert (Hkap2 : allows (nth_grade v_mot' 0) kappa) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; exact Hkap]);
        assert (Hs1_2 : allows (nth_grade u_b2 1) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 1 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hs1]);
        assert (Hs0_2 : allows (nth_grade u_b2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu_tr) | rewrite vec_subst_nth_lt by lia; exact Hs0]);
        assert (Hmot_nf_fn : cty_uses_var 0 mot = false ->
                  cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false) by
          (intro Hnf; apply cty_uses_var_subst_cidx_0; [lia | exact Hmot_safe | rewrite (lift_cidx_1_S D (length env_a) idx); apply lift_cidx_uses_var_0 | exact Hnf]);
        assert (Hdep2 : match subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) pr with
                        | CPair _ _ _ _ fv sv => match term_as_cidx fv, term_as_cidx sv with Some _, Some _ => True | _, _ => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false end
                        | CVar _ => True
                        | _ => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false
                        end) by
          (destruct pr; cbn [subst_cidx_in_cterm]; try (apply Hmot_nf_fn; exact Hdep);
           [ lazymatch goal with |- match (if ?nv =? _ then _ else _) with _ => _ end =>
               destruct (Nat.eq_dec nv (length env_a)) as [-> | Hne];
               [ exfalso; inversion H; subst;
                 lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSigma _ _ _ _ |- _ =>
                   unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
                   inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
                 end
               | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)); exact I ]
             end
           | destruct (term_as_cidx pr1) eqn:E1; [destruct (term_as_cidx pr2) eqn:E2;
               [ destruct pr1, pr2; cbn in E1, E2 |- *; try discriminate;
                 repeat (destruct (_ =? _) || destruct (_ <? _)); cbn; exact I
               | rewrite (term_as_cidx_subst_none _ _ _ _ E2); destruct (term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) pr1)); apply Hmot_nf_fn; exact Hdep ]
               | rewrite (term_as_cidx_subst_none _ _ _ _ E1); destruct (term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) pr2)); apply Hmot_nf_fn; exact Hdep ] ]);
        assert (Hres_eq : cty_alpha_eq (spec_pair_subj_cty (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) pr)
                                         (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))
                            (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) res_ty)) by
          (rewrite Hres; destruct pr; unfold spec_pair_subj_cty; cbn [subst_cidx_in_cterm];
            try (rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl);
           [ lazymatch goal with |- context [if ?nv =? _ then _ else _] =>
               destruct (Nat.eq_dec nv (length env_a)) as [-> | Hne];
               [ exfalso; inversion H; subst;
                 lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSigma _ _ _ _ |- _ =>
                   unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia;
                   inversion Hlk; subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
                 end
               | rewrite (proj2 (Nat.eqb_neq _ _) Hne);
                 destruct (Nat.ltb_spec nv (length env_a)) as [Hlt | Hge];
                 idtac;
                 idtac;
                 pose proof (subst_cidx_ren_var_comm D mot (lift_cidx 0 (length env_a) idx) nv (length env_a) Hne Hmot_safe) as Hrv;
                 rw_nat_bool_in Hrv; rewrite <- (lift_cidx_1_S D (length env_a) idx) in Hrv; rewrite Hrv; apply cty_alpha_eq_refl ]
             end
           | destruct (term_as_cidx pr1) eqn:E1; [destruct (term_as_cidx pr2) eqn:E2 |];
             [ inversion H; subst;
               lazymatch goal with
               | H_e1 : term_as_cidx ?p1 = Some ?cc1, H_e2 : term_as_cidx ?p2 = Some ?cc2,
                 Hdv1 : CoreDerives _ ?p1 _, Hdv2 : CoreDerives _ ?p2 _ |- _ =>
                   destruct (term_as_cidx_subst_some D b env_a env_b p1 _ cc1 (lift_cidx 0 (length env_a) idx) Hb Hdv1 H_e1) as [Hc1' ->];
                   destruct (term_as_cidx_subst_some D b env_a env_b p2 _ cc2 (lift_cidx 0 (length env_a) idx) Hb Hdv2 H_e2) as [Hc2' ->];
                   pose proof (subst_cidx_subst_pair_comm_gen D mot cc1 cc2 (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                                 ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) Hc1' Hc2' ltac:(cbn; exact Hmot_safe)) as Hcm;
                   cbn [Nat.add subst_cidx_in_cty] in Hcm; rewrite ?lift_cidx_0_0, ?lift_cty_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl
               end
             | rewrite (term_as_cidx_subst_none _ _ _ _ E2); destruct (term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) pr1));
               rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl
             | rewrite (term_as_cidx_subst_none _ _ _ _ E1); destruct (term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) pr2));
               rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl ] ]);
        eexists; rewrite <- (lift_cidx_1_S D (length env_a) idx); split; [| split; [| split]];
        [ eapply CoreLetPair;
          [ exact Hpr' | exact HA0' | exact HB0' | exact Hv_mot0 | exact Hkap2 | exact Hb2
          | reflexivity | exact Hmot_eq2 | exact Hs1_2 | exact Hs0_2 | exact Hdep2 | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) z (tl (tl u_b)) (vec_scale s w) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct u_b as [| ? [| ? ?]]; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite !vec_subst_tl by (destruct u_b; cbn in *; lia); apply branch_rel_tl, branch_rel_tl; exact Hu_tr
          | apply branch_rel_scale; exact Hw' ]
        | cbn [ctype_demand_row];
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale kappa w) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot | apply branch_rel_scale; exact Hw' ] ]
    end.
  - (* CorePromote *)
    destruct (IHCoreDerives env_a eq_refl Hsafe) as [[A' u' v'] [Hpv' [HA' [Hu' Hv']]]].
    cbn [cresult_type ccomp_demand ctype_demand_row] in HA', Hu', Hv'.
    eexists; split; [| split; [| split]];
    [ apply CorePromote; exact Hpv'
    | cbn [cresult_type subst_cidx_in_cty]; unfold cty_alpha_eq in *; cbn; rewrite HA'; reflexivity
    | cbn [ccomp_demand]; rewrite vec_subst_scale; apply branch_rel_scale; exact Hu'
    | cbn [ctype_demand_row]; exact Hv' ].
  - (* CoreLetBox *)
    lazymatch goal with
    | HA : CTypeDemand _ A a, Hmot : CTypeDemand _ mot v_mot, Hkap : allows (nth_grade v_mot 0) kappa,
      Hexp : exp_mot = spec_box_body_cty q 0 mot, Hmot_eq : cty_alpha_eq act_mot exp_mot,
      Hwq : allows (nth_grade w 0) q, Hbw : allows (nth_grade bw 0) (mul q kappa),
      Hdep : context [cty_uses_var 0 mot = false],
      Hres : res_ty = spec_box_subj_cty box_term mot,
      Hzty : ?z_ty = _ |- context [vec_scale _ ?z_ty] =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[bt' zb' vz'] [Hbx' [Hbt [Hzb' Hvz']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in Hbt, Hzb', Hvz';
        destruct (cty_alpha_eq_CBox_inv D bt' q (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A) Hbt)
          as [A0 [-> HA0]];
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ HA env_a eq_refl) as HA_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b A a Hb Hsafe Hidx HA) as [a' [Ha' Hbra]];
        assert (HA0' : CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) A0 a') by
          (eapply CTypeDemand_alpha_ty; [exact Ha' | apply cty_alpha_eq_sym; exact HA0]);
        assert (Hsafe_box : cenv_nat_safe ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; [cbn; exact HA_safe | exact Hsafe]);
        destruct (subst_ctype_demand D idx z ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env_a) b env_b mot v_mot Hb Hsafe_box Hidx Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := 0; cannotation := CBox q A0; ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b)
                                      (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) v_mot') by
          (eapply CTypeDemand_alpha_env;
           [| exact Hv_mot' ];
           constructor; [cbn; unfold cty_alpha_eq in *; cbn; rewrite HA0; reflexivity | apply cenv_alpha_eq_refl]);
        assert (Hsafe_A : cenv_nat_safe ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (IHCoreDerives2 ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl Hsafe_A)
          as [[act_mot1 w1 bw1] [Hb1 [Hact1 [Hw1 Hbw1]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hb1, Hact1, Hw1, Hbw1;
        rewrite (lift_cidx_1_S D (length env_a) idx) in Hb1, Hact1;
        assert (Hrel_A : cenv_demand_rel
          ({| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A;
              ctype_uses := vec_subst (length env_a) z a |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HA0 | exact HA0' | exact Hbra]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hb1 _ Hrel_A) as [[act_mot2 w2 bw2] [Hb2 [Hact2 [Hw2 Hbw2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hact2, Hw2, Hbw2;
        assert (Hw_tr : branch_rel w2 (vec_subst (S (length env_a)) z w)) by (eapply branch_rel_trans; [exact Hw2 | exact Hw1]);
        assert (Hbw_tr : branch_rel bw2 (vec_subst (S (length env_a)) z bw)) by (eapply branch_rel_trans; [exact Hbw2 | exact Hbw1]);
        assert (Hact_tr : cty_alpha_eq act_mot2 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) act_mot)) by
          (eapply cty_alpha_eq_trans; [exact Hact2 | exact Hact1]);
        assert (Hspec_body : subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) (spec_box_body_cty q 0 mot) =
                             spec_box_body_cty q 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot)) by
          (rewrite (lift_cidx_1_S D (length env_a) idx);
           apply subst_cidx_spec_box_body; [lia | exact Hmot_safe]);
        assert (Hmot_eq2 : cty_alpha_eq act_mot2 (spec_box_body_cty q 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))) by
          (eapply cty_alpha_eq_trans; [exact Hact_tr |]; rewrite <- Hspec_body, <- Hexp; apply subst_cidx_alpha_eq; exact Hmot_eq);
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
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbw_tr) | rewrite vec_subst_nth_lt by lia; exact Hbw]);
        assert (Hmot_nf_fn : cty_uses_var 0 mot = false ->
                  cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false) by
          (intro Hnf; apply cty_uses_var_subst_cidx_0; [lia | exact Hmot_safe | rewrite (lift_cidx_1_S D (length env_a) idx); apply lift_cidx_uses_var_0 | exact Hnf]);
        assert (Hbx_not_var : forall yb, box_term = CVar yb -> yb <> length env_a) by
          (intros yb -> ->; inversion H; subst;
           lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CBox _ _ |- _ =>
             assert (Heqb : ee = b) by (unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; reflexivity);
             subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
           end);
        assert (Hdep2 : match subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) box_term with
                        | CPromote _ (CNatVal _) | CPromote _ (CTypeVal _) | CPromote _ (CVar _) | CVar _ => True
                        | _ => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false
                        end) by
          (destruct box_term; cbn [subst_cidx_in_cterm]; try (apply Hmot_nf_fn; exact Hdep);
           [ lazymatch goal with |- match (if ?nv =? _ then _ else _) with _ => _ end =>
               destruct (Nat.eq_dec nv (length env_a)) as [Heqn | Hne];
               [ exfalso; exact (Hbx_not_var nv eq_refl Heqn)
               | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)); exact I ]
             end
           | destruct box_term; cbn [subst_cidx_in_cterm]; try (apply Hmot_nf_fn; exact Hdep); try exact I;
             repeat (destruct (_ =? _) || destruct (_ <? _)); exact I ]);
        assert (Hres_eq : cty_alpha_eq (spec_box_subj_cty (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) box_term)
                                         (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))
                            (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) res_ty)) by
          (rewrite Hres; destruct box_term; unfold spec_box_subj_cty; cbn [subst_cidx_in_cterm];
            try (rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl);
           [ lazymatch goal with |- context [if ?nv =? _ then _ else _] =>
               destruct (Nat.eq_dec nv (length env_a)) as [Heqn | Hne]; [exfalso; exact (Hbx_not_var nv eq_refl Heqn) |];
               rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)) as [Hlt | Hge];
               idtac;
               idtac;
               pose proof (subst_cidx_ren_var_comm D mot (lift_cidx 0 (length env_a) idx) nv (length env_a) Hne Hmot_safe) as Hrv;
               rw_nat_bool_in Hrv; rewrite <- (lift_cidx_1_S D (length env_a) idx) in Hrv; rewrite Hrv; apply cty_alpha_eq_refl
             end
           | destruct box_term; cbn [subst_cidx_in_cterm];
             try (rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl);
             [ inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ (CVar ?nv) _ |- _ =>
                 inversion Hdv; subst;
                 destruct (Nat.eq_dec nv (length env_a)) as [-> | Hne];
                 [ rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn [subst_cidx_in_cterm];
                   assert (Hm0 : cty_uses_kinds false false false true false false false 0 mot = false) by
                     (lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst;
                        rewrite Hb in Hmot; cbn [cannotation ren_cty] in Hmot;
                        eapply cdemand_box_nat_safe; cycle 1; [exact Hmot | cbn; reflexivity]
                      end);
                   pose proof (subst_cidx_box_var_to_nat_gen D mot q (lift_cidx 0 (length env_a) idx) 0 (length env_a) Hm0 Hmot_safe) as Hbvn;
                   cbn in Hbvn; rewrite lift_cidx_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hbvn;
                   replace (r_var 0 (length env_a)) with (Nat.iter 0 ren_shift (fun i => match i with 0 => length env_a | S i' => i' end)) in Hbvn by reflexivity;
                   unfold subst_var_in_cty; rewrite Hbvn; apply cty_alpha_eq_refl
                 | rewrite (proj2 (Nat.eqb_neq _ _) Hne);
                   destruct (Nat.ltb_spec nv (length env_a)) as [Hlt | Hge];
                   idtac;
                   idtac;
                   pose proof (spec_box_body_uses_kinds D q 0 mot (S (length env_a)) ltac:(lia) Hmot_safe) as Hsb_safe;
                   pose proof (subst_cidx_ren_var_comm D (spec_box_body_cty q 0 mot) (lift_cidx 0 (length env_a) idx) nv (length env_a) Hne Hsb_safe) as Hrv;
                   rw_nat_bool_in Hrv; rewrite Hrv, <- (lift_cidx_1_S D (length env_a) idx) in *; rewrite Hspec_body; apply cty_alpha_eq_refl ]
               end
             | inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ =>
                   pose proof (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) as Hi_safe;
                   pose proof (subst_cidx_subst_box_nat_comm_gen D mot q ii (lift_cidx 0 (length env_a) idx) 0 (length env_a) ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) Hi_safe ltac:(cbn; exact Hmot_safe)) as Hcm;
                   cbn [Nat.add subst_cidx_in_cty] in Hcm; rewrite ?lift_cidx_0_0, ?lift_cty_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl
                 end
               end
             | inversion H; subst;
               lazymatch goal with Hdv : CoreDerives _ (CTypeVal ?tt) _ |- _ =>
                 inversion Hdv; subst;
                 lazymatch goal with Htd : CTypeDemand (env_a ++ b :: env_b) ?tt _ |- _ =>
                   pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Htd env_a eq_refl) as HT_safe;
                   pose proof (subst_cidx_subst_box_ty_comm_gen D mot tt q (lift_cidx 0 (length env_a) idx) 0 (length env_a) ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) HT_safe ltac:(cbn; exact Hmot_safe)) as Hcm;
                   cbn [Nat.add subst_cidx_in_cty] in Hcm; rewrite ?lift_cidx_0_0, ?lift_cty_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl
                 end
               end ] ]);
        eexists; rewrite <- (lift_cidx_1_S D (length env_a) idx); split; [| split; [| split]];
        [ rewrite <- (lift_cidx_1_S D (length env_a) idx) in Hb2; eapply CoreLetBox;
          [ exact Hbx' | exact HA0' | exact Hv_mot0 | exact Hkap2 | exact Hb2
          | reflexivity | exact Hmot_eq2 | exact Hwq2 | exact Hbw2_a | exact Hdep2 | reflexivity | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          rewrite (vec_subst_add D (length env_a) z (tl w) z_b (length env_b)) by (destruct w; cbn in *; lia);
          apply branch_rel_add; [rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hw_tr | exact Hzb']
        | cbn [ctype_demand_row];
          assert (Hzty' : branch_rel
            (match subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) box_term with
             | CPromote q' (CTypeVal _) => vec_scale q' vz' | _ => zb' end)
            (vec_subst (length env_a) z z_ty)) by
            (rewrite Hzty; destruct box_term; cbn [subst_cidx_in_cterm]; try exact Hzb';
             [ repeat (destruct (_ =? _) || destruct (_ <? _)); exact Hzb'
             | destruct box_term; cbn [subst_cidx_in_cterm]; try exact Hzb';
               [ repeat (destruct (_ =? _) || destruct (_ <? _)); exact Hzb'
               | rewrite vec_subst_scale; apply branch_rel_scale; exact Hvz' ] ]);
          assert (Hlen_zty : length z_ty = length env_a + S (length env_b)) by
            (rewrite Hzty; destruct box_term; try exact Hlen_zb;
             lazymatch goal with |- length (match ?inn with _ => _ end) = _ =>
               destruct inn; try exact Hlen_zb; rewrite vec_scale_length; exact Hlen_vz
             end);
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale kappa z_ty) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot | apply branch_rel_scale; exact Hzty' ] ]
    end.
  - (* CoreInl *)
    lazymatch goal with
    | Hrhs : CTypeDemand _ rhs_ty b0 |- _ =>
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[A' u' a'] [Hv' [HA' [Hu' Ha']]]];
        destruct (subst_ctype_demand D idx z env_a b env_b rhs_ty b0 Hb Hsafe Hidx Hrhs) as [b' [Hb' Hbrb]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in HA', Hu', Ha';
        eexists; split; [| split; [| split]];
        [ eapply CoreInl; [exact Hv' | exact Hb']
        | cbn [cresult_type subst_cidx_in_cty]; unfold cty_alpha_eq in *; cbn; rewrite HA'; reflexivity
        | cbn [ccomp_demand]; exact Hu'
        | cbn [ctype_demand_row];
          pose proof (core_derives_lengths D _ _ _ H) as [_ Hlen_a];
          pose proof (ctype_demand_length D _ _ _ Hrhs) as Hlen_b;
          rewrite length_app in Hlen_a, Hlen_b; cbn [ccomp_demand ctype_demand_row length] in Hlen_a, Hlen_b;
          rewrite (vec_subst_add D (length env_a) z a b0 (length env_b)) by lia;
          apply branch_rel_add; assumption ]
    end.
  - (* CoreInr *)
    lazymatch goal with
    | Hlhs : CTypeDemand _ lhs_ty ?a_r |- context [vec_add ?a_r ?b_r] =>
        destruct (subst_ctype_demand D idx z env_a b env_b lhs_ty a_r Hb Hsafe Hidx Hlhs) as [a' [Ha' Hbra]];
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[B' u' b'] [Hv' [HB' [Hu' Hb']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in HB', Hu', Hb';
        eexists; split; [| split; [| split]];
        [ eapply CoreInr; [exact Ha' | exact Hv']
        | cbn [cresult_type subst_cidx_in_cty]; unfold cty_alpha_eq in *; cbn; rewrite HB'; reflexivity
        | cbn [ccomp_demand]; exact Hu'
        | cbn [ctype_demand_row];
          pose proof (ctype_demand_length D _ _ _ Hlhs) as Hlen_a;
          pose proof (core_derives_lengths D _ _ _ H) as [_ Hlen_b];
          cbn [ccomp_demand ctype_demand_row length] in Hlen_a, Hlen_b;
          rewrite length_app in Hlen_a, Hlen_b; cbn [length] in Hlen_a, Hlen_b;
          rewrite (vec_subst_add D (length env_a) z a_r b_r (length env_b)) by lia;
          apply branch_rel_add; assumption ]
    end.
  - (* CoreMatchSum *)
    lazymatch goal with
    | Hsne : s <> zero, HA : CTypeDemand _ A a, HB : CTypeDemand _ B b0,
      Hmot : CTypeDemand _ mot v_mot, Hkap : allows (nth_grade v_mot 0) kappa,
      Ht1 : cty_alpha_eq t1 (spec_sum_branch_cty true 0 mot),
      Ht2 : cty_alpha_eq t2 (spec_sum_branch_cty false 0 mot),
      Hs1 : allows (nth_grade u1 0) s, Hs2 : allows (nth_grade u2 0) s,
      Hbv : BranchVec (tl u1) (tl u2) u_br,
      Hdep : context [cty_uses_var 0 mot = false],
      Hres : res_ty = spec_sum_subj_cty scrut mot |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[srt' w' vs'] [Hscr' [Hsrt [Hw' Hvs']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in Hsrt, Hw', Hvs';
        destruct (cty_alpha_eq_CSum_inv D srt'
                    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A)
                    (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) B) Hsrt)
          as [A0 [B0 [-> [HA0 HB0]]]];
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ HA env_a eq_refl) as HA_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ HB env_a eq_refl) as HB_safe;
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b0 |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b A a Hb Hsafe Hidx HA) as [a' [Ha' Hbra]];
        destruct (subst_ctype_demand D idx z env_a b env_b B b0 Hb Hsafe Hidx HB) as [b' [Hb' Hbrb]];
        assert (HA0' : CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) A0 a') by
          (eapply CTypeDemand_alpha_ty; [exact Ha' | apply cty_alpha_eq_sym; exact HA0]);
        assert (HB0' : CTypeDemand (subst_cidx_cenv idx z env_a ++ env_b) B0 b') by
          (eapply CTypeDemand_alpha_ty; [exact Hb' | apply cty_alpha_eq_sym; exact HB0]);
        assert (Hsafe_sum : cenv_nat_safe ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b0 |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; [cbn; rewrite HA_safe, HB_safe; reflexivity | exact Hsafe]);
        destruct (subst_ctype_demand D idx z ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b0 |} :: env_a) b env_b mot v_mot Hb Hsafe_sum Hidx Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := 0; cannotation := CSum A0 B0; ctype_uses := vec_add a' b' |} :: subst_cidx_cenv idx z env_a ++ env_b)
                                      (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) v_mot') by
          (eapply CTypeDemand_alpha_env;
           [| exact Hv_mot' ];
           constructor; [cbn; unfold cty_alpha_eq in *; cbn; rewrite HA0, HB0; reflexivity | apply cenv_alpha_eq_refl]);
        assert (Hsafe_A : cenv_nat_safe ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        assert (Hsafe_B : cenv_nat_safe ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; assumption);
        destruct (IHCoreDerives2 ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env_a) eq_refl Hsafe_A)
          as [[tl1 u1_1 b1_1] [Hlb1 [Htl1 [Hu1_1 Hb1_1]]]];
        destruct (IHCoreDerives3 ({| cbinder := y; cannotation := B; ctype_uses := b0 |} :: env_a) eq_refl Hsafe_B)
          as [[tr1 u2_1 b2_1] [Hrb1 [Htr1 [Hu2_1 Hb2_1]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_cenv length cbinder cannotation ctype_uses app] in Hlb1, Htl1, Hu1_1, Hb1_1, Hrb1, Htr1, Hu2_1, Hb2_1;
        rewrite (lift_cidx_1_S D (length env_a) idx) in Hlb1, Htl1, Hrb1, Htr1;
        assert (Hrel_A : cenv_demand_rel
          ({| cbinder := x; cannotation := A0; ctype_uses := a' |} :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := x; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) A;
              ctype_uses := vec_subst (length env_a) z a |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HA0 | exact HA0' | exact Hbra]);
        assert (Hrel_B : cenv_demand_rel
          ({| cbinder := y; cannotation := B0; ctype_uses := b' |} :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := y; cannotation := subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) B;
              ctype_uses := vec_subst (length env_a) z b0 |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons; [apply cenv_demand_rel_refl | exact HB0 | exact HB0' | exact Hbrb]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hlb1 _ Hrel_A) as [[tl2 u1_2 b1_2] [Hlb2 [Htl2 [Hu1_2 Hb1_2]]]];
        destruct (core_derives_cenv_rel D ED _ _ _ Hrb1 _ Hrel_B) as [[tr2 u2_2 b2_2] [Hrb2 [Htr2 [Hu2_2 Hb2_2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htl2, Hu1_2, Hb1_2, Htr2, Hu2_2, Hb2_2;
        assert (Hu1_tr : branch_rel u1_2 (vec_subst (S (length env_a)) z u1)) by (eapply branch_rel_trans; [exact Hu1_2 | exact Hu1_1]);
        assert (Hu2_tr : branch_rel u2_2 (vec_subst (S (length env_a)) z u2)) by (eapply branch_rel_trans; [exact Hu2_2 | exact Hu2_1]);
        assert (Htl_tr : cty_alpha_eq tl2 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) t1)) by
          (eapply cty_alpha_eq_trans; [exact Htl2 | exact Htl1]);
        assert (Htr_tr : cty_alpha_eq tr2 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) t2)) by
          (eapply cty_alpha_eq_trans; [exact Htr2 | exact Htr1]);
        assert (Hspec_l : subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) (spec_sum_branch_cty true 0 mot) =
                          spec_sum_branch_cty true 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot)) by
          (rewrite (lift_cidx_1_S D (length env_a) idx);
           apply subst_cidx_spec_sum_branch; [lia | exact Hmot_safe]);
        assert (Hspec_r : subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 1 (lift_cidx 0 (length env_a) idx)) (spec_sum_branch_cty false 0 mot) =
                          spec_sum_branch_cty false 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot)) by
          (rewrite (lift_cidx_1_S D (length env_a) idx);
           apply subst_cidx_spec_sum_branch; [lia | exact Hmot_safe]);
        assert (Ht1_2 : cty_alpha_eq tl2 (spec_sum_branch_cty true 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htl_tr | rewrite <- Hspec_l; apply subst_cidx_alpha_eq; exact Ht1]);
        assert (Ht2_2 : cty_alpha_eq tr2 (spec_sum_branch_cty false 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htr_tr | rewrite <- Hspec_r; apply subst_cidx_alpha_eq; exact Ht2]);
        pose proof (ctype_demand_length D _ _ _ Hmot) as Hlen_vm;
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_u1 _];
        pose proof (core_derives_lengths D _ _ _ H1) as [Hlen_u2 _];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_vm, Hlen_w, Hlen_u1, Hlen_u2;
        rewrite length_app in Hlen_vm, Hlen_w, Hlen_u1, Hlen_u2; cbn [length] in Hlen_vm, Hlen_w, Hlen_u1, Hlen_u2;
        assert (Hkap2 : allows (nth_grade v_mot' 0) kappa) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; exact Hkap]);
        assert (Hs1_2 : allows (nth_grade u1_2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu1_tr) | rewrite vec_subst_nth_lt by lia; exact Hs1]);
        assert (Hs2_2 : allows (nth_grade u2_2 0) s) by
          (eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hu2_tr) | rewrite vec_subst_nth_lt by lia; exact Hs2]);
        assert (Hbr_tl1 : branch_rel (tl u1_2) (vec_subst (length env_a) z (tl u1))) by
          (rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu1_tr);
        assert (Hbr_tl2 : branch_rel (tl u2_2) (vec_subst (length env_a) z (tl u2))) by
          (rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hu2_tr);
        destruct (BranchVec_subst D (length env_a) z (tl u1) (tl u2) u_br (tl u1_2) (tl u2_2) (length env_b)
                    Hz_len ltac:(destruct u1; cbn in *; lia) ltac:(destruct u2; cbn in *; lia) Hbv Hbr_tl1 Hbr_tl2)
          as [ubr' [Hubr' Hbr_u]];
        assert (Hmot_nf_fn : cty_uses_var 0 mot = false ->
                  cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false) by
          (intro Hnf; apply cty_uses_var_subst_cidx_0; [lia | exact Hmot_safe | rewrite (lift_cidx_1_S D (length env_a) idx); apply lift_cidx_uses_var_0 | exact Hnf]);
        assert (Hscr_not_var : forall ys, scrut = CVar ys -> ys <> length env_a) by
          (intros ys -> ->; inversion H; subst;
           lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CSum _ _ |- _ =>
             assert (Heqb : ee = b) by (unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; reflexivity);
             subst ee; rewrite Hb in Heq; cbn in Heq; discriminate
           end);
        assert (Hdep2 : match subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) scrut with
                        | CInl _ v => match term_as_cidx v, A0 with Some _, CNat => True | _, _ => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false end
                        | CInr _ v => match term_as_cidx v, B0 with Some _, CNat => True | _, _ => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false end
                        | CVar _ => True
                        | _ => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false
                        end) by
          (destruct scrut; cbn [subst_cidx_in_cterm]; try (apply Hmot_nf_fn; exact Hdep);
           [ lazymatch goal with |- match (if ?nv =? _ then _ else _) with _ => _ end =>
               destruct (Nat.eq_dec nv (length env_a)) as [Heqn | Hne]; [exfalso; exact (Hscr_not_var nv eq_refl Heqn) | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)); exact I]
             end
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct A eqn:EA;
               [ destruct scrut; cbn in Ev |- *; try discriminate; destruct A0; unfold cty_alpha_eq in HA0; cbn in HA0; try discriminate; try exact I; repeat (destruct (_ =? _) || destruct (_ <? _)); exact I
               | destruct (term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) scrut)); destruct A0; try exact I; apply Hmot_nf_fn; exact Hdep .. ]
             | rewrite (term_as_cidx_subst_none _ _ _ _ Ev); destruct A0; apply Hmot_nf_fn; exact Hdep ]
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct B eqn:EB;
               [ destruct scrut; cbn in Ev |- *; try discriminate; destruct B0; unfold cty_alpha_eq in HB0; cbn in HB0; try discriminate; try exact I; repeat (destruct (_ =? _) || destruct (_ <? _)); exact I
               | destruct (term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) scrut)); destruct B0; try exact I; apply Hmot_nf_fn; exact Hdep .. ]
             | rewrite (term_as_cidx_subst_none _ _ _ _ Ev); destruct B0; apply Hmot_nf_fn; exact Hdep ] ]);
        assert (Hres_eq : cty_alpha_eq (spec_sum_subj_cty (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) scrut)
                                         (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))
                            (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) res_ty)) by
          (rewrite Hres; destruct scrut; unfold spec_sum_subj_cty; cbn [subst_cidx_in_cterm];
            try (rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl);
           [ lazymatch goal with |- context [if ?nv =? _ then _ else _] =>
               destruct (Nat.eq_dec nv (length env_a)) as [Heqn | Hne]; [exfalso; exact (Hscr_not_var nv eq_refl Heqn) |];
               rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)) as [Hlt | Hge];
               idtac;
               idtac;
               pose proof (subst_cidx_ren_var_comm D mot (lift_cidx 0 (length env_a) idx) nv (length env_a) Hne Hmot_safe) as Hrv;
               rw_nat_bool_in Hrv; rewrite <- (lift_cidx_1_S D (length env_a) idx) in Hrv; rewrite Hrv; apply cty_alpha_eq_refl
             end
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct scrut; cbn [term_as_cidx subst_cidx_in_cterm] in *; try discriminate; injection Ev as <-;
               [ lazymatch goal with |- context [if ?nv =? _ then _ else _] =>
                   destruct (Nat.eq_dec nv (length env_a)) as [-> | Hne];
                   [ rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn [term_as_cidx];
                     assert (Hm0 : cty_uses_kinds false false false false false false true 0 mot = false) by
                       (inversion H; subst;
                        lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                          inversion Hdv; subst;
                          lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst;
                            rewrite Hb in Hmot; cbn [cannotation ren_cty] in Hmot;
                            eapply cdemand_sum_nat_safe; cycle 2; [exact Hmot | cbn; reflexivity | left; reflexivity]
                          end
                        end);
                     pose proof (subst_cidx_sum_var_to_nat_gen D mot true (lift_cidx 0 (length env_a) idx) 0 (length env_a) Hm0 Hmot_safe) as Hsvn;
                     cbn [Nat.add] in Hsvn; rewrite lift_cidx_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hsvn;
                     rewrite Hsvn; apply cty_alpha_eq_refl
                   | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)) as [Hlt | Hge];
                     cbn [term_as_cidx];
                     pose proof (subst_cidx_subst_sum_comm_gen D mot true (CIdxVar nv) (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                                   ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) ltac:(cbn; reflexivity) ltac:(cbn; exact Hmot_safe)) as Hcm;
                     cbn [Nat.add subst_cidx_in_cty subst_cidx] in Hcm; rw_nat_bool_in Hcm;
                     rewrite ?lift_cidx_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl ]
                 end
               | inversion H; subst;
                 lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                   inversion Hdv; subst;
                   lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ =>
                     pose proof (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) as Hi_safe;
                     pose proof (subst_cidx_subst_sum_comm_gen D mot true ii (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                                   ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) Hi_safe ltac:(cbn; exact Hmot_safe)) as Hcm;
                     cbn [Nat.add subst_cidx_in_cty] in Hcm; rewrite ?lift_cidx_0_0, ?lift_cty_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl
                   end
                 end ]
             | rewrite (term_as_cidx_subst_none _ _ _ _ Ev);
               rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl ]
           | destruct (term_as_cidx scrut) eqn:Ev;
             [ destruct scrut; cbn [term_as_cidx subst_cidx_in_cterm] in *; try discriminate; injection Ev as <-;
               [ lazymatch goal with |- context [if ?nv =? _ then _ else _] =>
                   destruct (Nat.eq_dec nv (length env_a)) as [-> | Hne];
                   [ rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn [term_as_cidx];
                     assert (Hm0 : cty_uses_kinds false false false false false false true 0 mot = false) by
                       (inversion H; subst;
                        lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
                          inversion Hdv; subst;
                          lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
                            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst;
                            rewrite Hb in Hmot; cbn [cannotation ren_cty] in Hmot;
                            eapply cdemand_sum_nat_safe; cycle 2; [exact Hmot | cbn; reflexivity | right; reflexivity]
                          end
                        end);
                     pose proof (subst_cidx_sum_var_to_nat_gen D mot false (lift_cidx 0 (length env_a) idx) 0 (length env_a) Hm0 Hmot_safe) as Hsvn;
                     cbn [Nat.add] in Hsvn; rewrite lift_cidx_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hsvn;
                     rewrite Hsvn; apply cty_alpha_eq_refl
                   | rewrite (proj2 (Nat.eqb_neq _ _) Hne); destruct (Nat.ltb_spec nv (length env_a)) as [Hlt | Hge];
                     cbn [term_as_cidx];
                     pose proof (subst_cidx_subst_sum_comm_gen D mot false (CIdxVar nv) (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                                   ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) ltac:(cbn; reflexivity) ltac:(cbn; exact Hmot_safe)) as Hcm;
                     cbn [Nat.add subst_cidx_in_cty subst_cidx] in Hcm; rw_nat_bool_in Hcm;
                     rewrite ?lift_cidx_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl ]
                 end
               | inversion H; subst;
                 lazymatch goal with Hdv : CoreDerives _ (CNatVal ?ii) _ |- _ =>
                   inversion Hdv; subst;
                   lazymatch goal with Hcd : CIdxDemand _ ?ii _ |- _ =>
                     pose proof (proj1 (cdemand_nat_safe D b env_b Hb) _ _ _ Hcd env_a eq_refl) as Hi_safe;
                     pose proof (subst_cidx_subst_sum_comm_gen D mot false ii (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                                   ltac:(right; eapply cdemand_not_nat_idx0_safe; cycle 1; [exact Hmot | cbn; discriminate]) Hi_safe ltac:(cbn; exact Hmot_safe)) as Hcm;
                     cbn [Nat.add subst_cidx_in_cty] in Hcm; rewrite ?lift_cidx_0_0, ?lift_cty_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl
                   end
                 end ]
             | rewrite (term_as_cidx_subst_none _ _ _ _ Ev);
               rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl ] ]);
        eexists; rewrite <- (lift_cidx_1_S D (length env_a) idx); split; [| split; [| split]];
        [ rewrite <- (lift_cidx_1_S D (length env_a) idx) in Hlb2, Hrb2; eapply CoreMatchSum;
          [ exact Hsne | exact Hscr' | exact HA0' | exact HB0' | exact Hv_mot0 | exact Hkap2
          | exact Hlb2 | exact Hrb2 | exact Ht1_2 | exact Ht2_2 | exact Hs1_2 | exact Hs2_2
          | exact Hubr' | exact Hdep2 | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          pose proof (BranchVec_length D (tl u1) (tl u2) u_br ltac:(destruct u1, u2; cbn in *; lia) Hbv) as Hlen_ubr;
          cbn [length] in Hlen_ubr;
          rewrite (vec_subst_add D (length env_a) z (vec_scale s w) u_br (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct u1; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [apply branch_rel_scale; exact Hw' | exact Hbr_u]
        | cbn [ctype_demand_row];
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale kappa w) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot | apply branch_rel_scale; exact Hw' ] ]
    end.
  - (* CoreIf *)
    lazymatch goal with
    | Heq : cty_alpha_eq t1 t2, Hbu : BranchVec u1 u2 u_br, Hbv : BranchVec v1 v2 v_br |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[tc' uc' vc'] [Hc' [Htc [Huc' Hvc']]]];
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[t1' u1' v1'] [Hth' [Ht1 [Hu1' Hv1']]]];
        destruct (IHCoreDerives3 env_a eq_refl Hsafe) as [[t2' u2' v2'] [Hel' [Ht2 [Hu2' Hv2']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in Htc, Huc', Hvc', Ht1, Hu1', Hv1', Ht2, Hu2', Hv2';
        apply cty_alpha_eq_CBool_inv in Htc; subst tc';
        pose proof (core_derives_lengths D _ _ _ H) as [Hlen_uc _];
        pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_u1 Hlen_v1];
        pose proof (core_derives_lengths D _ _ _ H1) as [Hlen_u2 Hlen_v2];
        cbn [ccomp_demand ctype_demand_row length] in Hlen_uc, Hlen_u1, Hlen_v1, Hlen_u2, Hlen_v2;
        rewrite length_app in Hlen_uc, Hlen_u1, Hlen_v1, Hlen_u2, Hlen_v2; cbn [length] in Hlen_uc, Hlen_u1, Hlen_v1, Hlen_u2, Hlen_v2;
        destruct (BranchVec_subst D (length env_a) z u1 u2 u_br u1' u2' (length env_b) Hz_len ltac:(lia) ltac:(lia) Hbu Hu1' Hu2') as [ubr' [Hubr' Hbr_u]];
        destruct (BranchVec_subst D (length env_a) z v1 v2 v_br v1' v2' (length env_b) Hz_len ltac:(lia) ltac:(lia) Hbv Hv1' Hv2') as [vbr' [Hvbr' Hbr_v]];
        eexists; split; [| split; [| split]];
        [ eapply CoreIf;
          [ exact Hc' | exact Hth' | exact Hel'
          | eapply cty_alpha_eq_trans; [exact Ht1 | eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Heq | apply cty_alpha_eq_sym; exact Ht2]]
          | exact Hubr' | exact Hvbr' ]
        | cbn [cresult_type]; exact Ht1
        | cbn [ccomp_demand];
          pose proof (BranchVec_length D u1 u2 u_br ltac:(lia) Hbu) as Hlen_ubr;
          rewrite (vec_subst_add D (length env_a) z u_c u_br (length env_b)) by lia;
          apply branch_rel_add; [exact Huc' | exact Hbr_u]
        | cbn [ctype_demand_row]; exact Hbr_v ]
    end.
  - (* CoreRecordMk *)
    destruct (IHCoreDerives env_a eq_refl Hsafe) as [u' [v' [Helems [Hu' Hv']]]].
    eexists; split; [| split; [| split]];
    [ apply CoreRecordMk; exact Helems
    | cbn [cresult_type subst_cidx_in_cty];
      replace (map (fun '(fn, fg, ft, _) => (fn, fg, ft))
                (map (fun '(fn, fg, ft, fv) =>
                   (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft,
                            subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) fv)) fields))
        with (map (fun '(fn, fg, ft) => (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft))
                (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields))
        by (rewrite !map_map; apply map_ext; intros [[[fn fg] ft] fv]; reflexivity);
      apply cty_alpha_eq_refl
    | cbn [ccomp_demand]; exact Hu'
    | cbn [ctype_demand_row]; exact Hv' ].
  - (* CoreMatchRecord *)
    lazymatch goal with
    | Hsne : s <> zero, Hmot : CTypeDemand _ mot v_mot,
      Hlen_eq : length bs = length fields,
      Hext : CRecordExtendEnv _ bs fields body_env,
      Htb_eq : cty_alpha_eq t_b (lift_cty 0 (length fields) mot),
      Hfa_rec : CRecordFieldAllows s fields (firstn (length fields) u_b) |- _ =>
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[tr' w' vs'] [Hscr' [Htr [Hw' Hvs']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in Htr, Hw', Hvs';
        destruct (cty_alpha_eq_CRecord_inv D tr' id
                    (map (fun '(fn, fg, ft) => (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft)) fields) Htr)
          as [fields' [-> Hfs_sub]];
        assert (Hfs_a : Forall2 (fun '(n1, g1, t1) '(n2, g2, t2) => n1 = n2 /\ g1 = g2 /\
                  cty_alpha_eq t1 (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) t2)) fields' fields) by
          (clear - Hfs_sub; revert fields Hfs_sub; induction fields' as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
           cbn in Hfs; inversion Hfs; subst; [apply Forall2_nil | apply Forall2_cons; [assumption | apply IH; assumption]]);
        assert (Hlen_fs : length bs = length fields') by (rewrite Hlen_eq; symmetry; apply (Forall2_length Hfs_a));
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot env_a eq_refl) as Hmot_safe;
        destruct (subst_ctype_demand D idx z env_a b env_b mot v_mot Hb Hsafe Hidx Hmot) as [v_mot' [Hv_mot' Hbr_mot]];
        destruct (record_extend_subst_cidx D idx z env_b b Hb Hidx _ bs fields body_env env_a fields' eq_refl Hsafe Hext Hfs_a)
          as [ext_a [body_env' [Hbody [Hlen_ext [Hsafe_ext [Hext' Hrel_ext]]]]]];
        destruct (IHCoreDerives2 ext_a Hbody Hsafe_ext) as [[tb1 ub1 vb1] [Hbod1 [Htb1 [Hub1 Hvb1]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htb1, Hub1, Hvb1;
        destruct (core_derives_cenv_rel D ED _ _ _ Hbod1 _ Hrel_ext) as [[tb2 ub2 vb2] [Hbod2 [Htb2 [Hub2 Hvb2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htb2, Hub2, Hvb2;
        assert (Hub_tr : branch_rel ub2 (vec_subst (length ext_a) z u_b)) by (eapply branch_rel_trans; [exact Hub2 | exact Hub1]);
        assert (Htb_tr : cty_alpha_eq tb2 (subst_cidx_in_cty (length ext_a) (lift_cidx 0 (length ext_a) idx) t_b)) by
          (eapply cty_alpha_eq_trans; [exact Htb2 | exact Htb1]);
        rewrite Hlen_ext in Htb_tr, Hub_tr;
        assert (Htb2_eq : cty_alpha_eq tb2 (lift_cty 0 (length fields') (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) mot))) by
          (rewrite (Forall2_length Hfs_a);
           eapply cty_alpha_eq_trans; [exact Htb_tr |];
           eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Htb_eq |];
           rewrite <- (lift_cidx_add D (length fields) (length env_a) idx), (subst_cidx_in_cty_lift_n_comm D (length fields) (length env_a) mot (lift_cidx 0 (length env_a) idx) Hmot_safe);
           apply cty_alpha_eq_refl);
        assert (Hfa2 : Forall2 (@allows D) (firstn (length fields) ub2) (firstn (length fields) u_b)) by
          (pose proof (branch_rel_firstn D (length fields) _ _ Hub_tr) as Hfr;
           rewrite vec_subst_firstn_prefix in Hfr by lia;
           apply branch_rel_allows; exact Hfr);
        assert (Hfa_map : CRecordFieldAllows s
                            (map (fun '(fn, fg, ft) => (fn, fg, subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) ft)) fields)
                            (firstn (length fields) u_b)) by
          (clear - Hfa_rec; induction Hfa_rec; cbn; [apply CRecordAllowsNil | apply CRecordAllowsCons; assumption]);
        assert (Hallows2 : CRecordFieldAllows s fields' (firstn (length fields') ub2)) by
          (rewrite (Forall2_length Hfs_a); eapply record_allows_mono; [exact Hfa_map | exact Hfa2 | exact Hfs_sub]);
        eexists; split; [| split; [| split]];
        [ rewrite Hlen_ext, <- Hlen_eq, <- lift_cidx_add in Hbod2;
          eapply CoreMatchRecord; [exact Hsne | exact Hscr' | exact Hv_mot' | exact Hlen_fs | exact Hext' | exact Hbod2 | exact Htb2_eq | exact Hallows2]
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; rewrite (Forall2_length Hfs_a);
          pose proof (core_derives_lengths D _ _ _ H) as [Hlen_w _];
          pose proof (core_derives_lengths D _ _ _ H0) as [Hlen_ub _];
          cbn [ccomp_demand ctype_demand_row length] in Hlen_ub, Hlen_w;
          rewrite Hbody, length_app, Hlen_ext in Hlen_ub; cbn [length] in Hlen_ub;
          rewrite length_app in Hlen_w; cbn [length] in Hlen_w;
          rewrite (vec_subst_add D (length env_a) z (vec_scale s w) (skipn (length fields) u_b) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; try rewrite length_skipn; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ apply branch_rel_scale; exact Hw'
          | replace (vec_subst (length env_a) z (skipn (length fields) u_b))
              with (skipn (length fields) (vec_subst (length fields + length env_a) z u_b))
              by (rewrite <- (vec_subst_skipn_prefix D (length fields) (length fields + length env_a) z u_b ltac:(lia)); f_equal; lia);
            apply branch_rel_skipn; exact Hub_tr ]
        | cbn [ctype_demand_row]; exact Hbr_mot ]
    end.
  - (* CoreSubgrade *)
    lazymatch goal with
    | Hsub : Subty _ actual target, Hvt : CTypeDemand _ target vt |- _ =>
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[act' u' v'] [Hb' [Hact' [Hu' Hv']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Hact', Hu', Hv';
        pose proof (subst_subty D idx z env_a b env_b actual target Hb Hsub) as Hsub';
        assert (Hsub0 : Subty (subst_cidx_cenv idx z env_a ++ env_b) act'
                          (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) target)) by
          (eapply Subty_alpha; [exact Hsub' | apply cenv_alpha_eq_refl | apply cty_alpha_eq_sym; exact Hact' | apply cty_alpha_eq_refl]);
        destruct (subst_ctype_demand D idx z env_a b env_b target vt Hb Hsafe Hidx Hvt) as [vt' [Hvt' Hbr_vt]];
        eexists; split; [| split; [| split]];
        [ eapply CoreSubgrade; [exact Hb' | exact Hsub0 | exact Hvt']
        | cbn [cresult_type]; apply cty_alpha_eq_refl
        | cbn [ccomp_demand]; exact Hu'
        | cbn [ctype_demand_row]; exact Hbr_vt ]
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
        destruct (IHCoreDerives1 env_a eq_refl Hsafe) as [[st' us' vs'] [Hscr' [Hst [Hus' Hvs']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_in_cty] in Hst, Hus', Hvs';
        apply cty_alpha_eq_CNat_inv in Hst; subst st';
        pose proof (proj2 (cdemand_nat_safe D b env_b Hb) _ _ _ Hmot ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl) as Hmot_safe;
        cbn [length] in Hmot_safe;
        assert (Hsafe_xn : cenv_nat_safe ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) (S (length env_a))) by
          (apply cenv_nat_safe_cons; [reflexivity | exact Hsafe]);
        destruct (subst_ctype_demand D idx z ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) b env_b mot v_mot Hb Hsafe_xn Hidx Hmot)
          as [v_mot' [Hv_mot' Hbr_mot]];
        cbn [subst_cidx_cenv length cbinder cannotation ctype_uses app subst_cidx_in_cty] in Hv_mot', Hbr_mot;
        assert (Hv_mot0 : CTypeDemand ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (subst_cidx_cenv idx z env_a ++ env_b)) |} :: subst_cidx_cenv idx z env_a ++ env_b)
                                      (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) v_mot') by
          (eapply CTypeDemand_alpha_env; [| exact Hv_mot']; constructor; [cbn; apply cty_alpha_eq_refl | apply cenv_alpha_eq_refl]);
        destruct (IHCoreDerives2 env_a eq_refl Hsafe) as [[tb' ub' vb'] [Hbas' [Htb' [Hub' Hvb']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htb', Hub', Hvb';
        assert (Hbeq' : cty_alpha_eq tb' (subst_cidx_in_cty 0 (CIdxLit 0) (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htb' |];
           eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hbeq |];
           pose proof (subst_cidx_in_cty_subst_cidx D mot (CIdxLit 0) (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                         ltac:(lia) ltac:(cbn; reflexivity) Hmot_safe) as Hcm;
           cbn [subst_cidx] in Hcm; rewrite <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl);
        assert (Hsafe_xr : cenv_nat_safe ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
                                          {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a)
                                         (S (S (length env_a)))) by
          (apply cenv_nat_safe_cons; [exact Hmot_safe | exact Hsafe_xn]);
        destruct (IHCoreDerives3 ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
                                  {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (env_a ++ b :: env_b)) |} :: env_a) eq_refl Hsafe_xr)
          as [[tst1 ust1 vst1] [Hstp1 [Htst1 [Hust1 Hvst1]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row subst_cidx_cenv length cbinder cannotation ctype_uses app subst_cidx_in_cty] in Hstp1, Htst1, Hust1, Hvst1;
        rewrite (lift_cidx_2_SS D (length env_a) idx) in Hstp1, Htst1;
        assert (Hrel_xr : cenv_demand_rel
          ({| cbinder := xr; cannotation := subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot; ctype_uses := v_mot' |}
           :: {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length (subst_cidx_cenv idx z env_a ++ env_b)) |}
           :: subst_cidx_cenv idx z env_a ++ env_b)
          ({| cbinder := xr; cannotation := subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot;
              ctype_uses := vec_subst (S (length env_a)) z v_mot |}
           :: {| cbinder := xn; cannotation := CNat;
                 ctype_uses := vec_subst (length env_a) z (vec_zero (length (env_a ++ b :: env_b))) |}
           :: subst_cidx_cenv idx z env_a ++ env_b)) by
          (apply cenv_demand_rel_cons;
           [ apply cenv_demand_rel_cons;
             [ apply cenv_demand_rel_refl
             | apply cty_alpha_eq_refl
             | apply CTypeNat
             | rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len; apply branch_rel_refl ]
           | apply cty_alpha_eq_refl
           | exact Hv_mot0
           | exact Hbr_mot ]);
        destruct (core_derives_cenv_rel D ED _ _ _ Hstp1 _ Hrel_xr) as [[tst2 ust2 vst2] [Hstp2 [Htst2 [Hust2 Hvst2]]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htst2, Hust2, Hvst2;
        assert (Hust_tr : branch_rel ust2 (vec_subst (S (S (length env_a))) z u_st)) by (eapply branch_rel_trans; [exact Hust2 | exact Hust1]);
        assert (Htst_tr : cty_alpha_eq tst2 (subst_cidx_in_cty (S (S (length env_a))) (lift_cidx 0 2 (lift_cidx 0 (length env_a) idx)) t_st)) by
          (eapply cty_alpha_eq_trans; [exact Htst2 | exact Htst1]);
        assert (Hsteq' : cty_alpha_eq tst2 (spec_fix_step_cty (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))) by
          (eapply cty_alpha_eq_trans; [exact Htst_tr |];
           eapply cty_alpha_eq_trans; [apply subst_cidx_alpha_eq; exact Hsteq |];
           rewrite (subst_cidx_spec_fix_step D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx); apply cty_alpha_eq_refl);
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
        assert (Hust_tl_br : branch_rel (tl (tl ust2)) (vec_subst (length env_a) z (tl (tl u_st)))) by
          (rewrite !vec_subst_tl by (destruct u_st; cbn in *; lia); apply branch_rel_tl, branch_rel_tl; exact Hust_tr);
        assert (Hrecok' : fix_recurrence_ok s_rec (tl (tl ust2))) by
          (unfold fix_recurrence_ok in Hrecok |- *;
           destruct (vec_is_zero (tl (tl u_st))) eqn:Ez;
           [ apply vec_is_zero_iff in Ez;
             replace (length (tl (tl u_st))) with (S (length env_a + length env_b)) in Ez by (destruct u_st as [| ? [| ? ?]]; cbn in *; lia);
             rewrite Ez, vec_subst_zero in Hust_tl_br by exact Hz_len;
             rewrite (branch_rel_vec_is_zero D ED _ _ Hust_tl_br); exact I
           | destruct (vec_is_zero (tl (tl ust2))); [exact I | exact Hrecok] ]);
        assert (Hdep2 : match term_as_cidx (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) scrut) with
                        | Some _ => True
                        | None => cty_uses_var 0 (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot) = false
                        end) by
          (destruct (term_as_cidx scrut) as [ci |] eqn:Es;
           [ destruct (term_as_cidx_subst_some D b env_a env_b scrut _ ci (lift_cidx 0 (length env_a) idx) Hb H Es) as [_ ->]; exact I
           | rewrite (term_as_cidx_subst_none _ _ _ _ Es);
             apply cty_uses_var_subst_cidx_0; [lia | exact Hmot_safe | rewrite (lift_cidx_1_S D (length env_a) idx); apply lift_cidx_uses_var_0 | exact Hdep] ]);
        assert (Hres_eq : cty_alpha_eq (spec_fix_subj_cty (subst_cidx_in_cterm (length env_a) (lift_cidx 0 (length env_a) idx) scrut)
                                         (subst_cidx_in_cty (S (length env_a)) (lift_cidx 0 (S (length env_a)) idx) mot))
                            (subst_cidx_in_cty (length env_a) (lift_cidx 0 (length env_a) idx) res_ty)) by
          (rewrite Hres; unfold spec_fix_subj_cty;
           destruct (term_as_cidx scrut) as [ci |] eqn:Es;
           [ destruct (term_as_cidx_subst_some D b env_a env_b scrut _ ci (lift_cidx 0 (length env_a) idx) Hb H Es) as [Hc_safe ->];
             pose proof (subst_cidx_in_cty_subst_cidx D mot ci (lift_cidx 0 (length env_a) idx) 0 (length env_a)
                           ltac:(lia) Hc_safe Hmot_safe) as Hcm;
             cbn [Nat.add] in Hcm; rewrite ?lift_cidx_0_0, <- (lift_cidx_1_S D (length env_a) idx) in Hcm; rewrite Hcm; apply cty_alpha_eq_refl
           | rewrite (term_as_cidx_subst_none _ _ _ _ Es);
             rewrite (subst_cidx_in_cty_unshift_0 D mot (lift_cidx 0 (length env_a) idx) (length env_a) Hdep Hmot_safe), <- (lift_cidx_1_S D (length env_a) idx);
             apply cty_alpha_eq_refl ]);
        eexists; rewrite <- (lift_cidx_1_S D (length env_a) idx); split; [| split; [| split]];
        [ eapply CoreFix;
          [ exact Hscr' | exact Hv_mot0 | exact Hbas' | exact Hbeq' | exact Hstp2 | exact Hsteq'
          | exact Hrec0' | exact Hrec1' | exact Hrecok' | exact Hdep2 | reflexivity ]
        | cbn [cresult_type]; exact Hres_eq
        | cbn [ccomp_demand];
          assert (Hlen_tlu : length (tl (tl u_st)) = S (length env_a + length env_b)) by (destruct u_st as [| ? [| ? ?]]; cbn in *; lia);
          rewrite (vec_subst_add D (length env_a) z u_s (vec_add u_b (vec_scale s_rec (tl (tl u_st)))) (length env_b))
            by (try exact Hz_len; try (rewrite vec_add_length by (rewrite vec_scale_length; lia)); lia);
          rewrite (vec_subst_add D (length env_a) z u_b (vec_scale s_rec (tl (tl u_st))) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; lia);
          rewrite vec_subst_scale; apply branch_rel_add; [exact Hus' | apply branch_rel_add; [exact Hub' | apply branch_rel_scale; exact Hust_tl_br]]
        | cbn [ctype_demand_row];
          rewrite (vec_subst_add D (length env_a) z (tl v_mot) (vec_scale (nth_grade v_mot 0) u_s) (length env_b))
            by (try exact Hz_len; try rewrite vec_scale_length; destruct v_mot; cbn in *; lia);
          rewrite vec_subst_scale; apply branch_rel_add;
          [ rewrite vec_subst_tl by lia; apply branch_rel_tl; exact Hbr_mot
          | apply branch_rel_scale_grade;
            [ eapply allows_trans; [exact (branch_rel_nth D _ _ 0 Hbr_mot) | rewrite vec_subst_nth_lt by lia; apply allows_refl]
            | intro Hnone; pose proof (branch_rel_nth D _ _ 0 Hbr_mot) as Hn0;
              unfold branch_rel in Hbr_mot; rewrite Hnone in Hbr_mot; rewrite Hbr_mot, vec_subst_nth_lt by lia; reflexivity
            | exact Hus' ] ] ]
    end.
  - (* CRecordElemNil *)
    eexists _, _; split; [constructor |];
    rewrite !length_app, subst_cidx_cenv_length; cbn [length]; rewrite Nat.add_succ_r, vec_subst_zero by exact Hz_len;
    split; apply branch_rel_refl.
  - (* CRecordElemCons *)
    lazymatch goal with
    | Htv : cty_alpha_eq t_v ft, Hdt : CTypeDemand _ ft dt, Hrec : CRecordElemDerives _ _ _ _ |- _ =>
        destruct (IHCoreDerives env_a eq_refl Hsafe) as [[tv' uv' vv'] [Hv' [Htv' [Huv' Hvv']]]];
        cbn [cresult_type ccomp_demand ctype_demand_row] in Htv', Huv', Hvv';
        destruct (subst_ctype_demand D idx z env_a b env_b ft dt Hb Hsafe Hidx Hdt) as [dt' [Hdt' Hbr_dt]];
        destruct (IHCoreDerives0 env_a eq_refl Hsafe) as [ur' [vr' [Hrest' [Hur' Hvr']]]];
        eexists _, _; split;
        [ eapply CRecordElemCons;
          [ exact Hv'
          | eapply cty_alpha_eq_trans; [exact Htv' | apply subst_cidx_alpha_eq; exact Htv]
          | exact Hdt'
          | exact Hrest' ]
        | split;
          [ pose proof (core_derives_lengths D _ _ _ H) as [Hlen_uv _];
            pose proof (record_elem_derives_lengths D _ _ _ _ Hrec) as [Hlen_ur _];
            cbn [ccomp_demand ctype_demand_row length] in Hlen_uv, Hlen_ur;
            rewrite length_app in Hlen_uv, Hlen_ur; cbn [length] in Hlen_uv, Hlen_ur;
            rewrite (vec_subst_add D (length env_a) z (vec_scale fg u_v) u_rest (length env_b))
              by (try exact Hz_len; try rewrite vec_scale_length; lia);
            rewrite vec_subst_scale; apply branch_rel_add; [apply branch_rel_scale; exact Huv' | exact Hur']
          | pose proof (ctype_demand_length D _ _ _ Hdt) as Hlen_dt;
            pose proof (record_elem_derives_lengths D _ _ _ _ Hrec) as [_ Hlen_vr];
            cbn [ccomp_demand ctype_demand_row length] in Hlen_dt, Hlen_vr;
            rewrite length_app in Hlen_dt, Hlen_vr; cbn [length] in Hlen_dt, Hlen_vr;
            rewrite (vec_subst_add D (length env_a) z dt v_rest (length env_b)) by lia;
            apply branch_rel_add; [exact Hbr_dt | exact Hvr'] ] ]
    end.
Qed.

(* ================================================================= *)
(* Part A1: Subtyping & Subgrading Admissibility                     *)
(* ================================================================= *)

Lemma Subty_any_env : forall (D : JoinDomain) (env1 env2 : cenv D) A B,
  Subty env1 A B ->
  Subty env2 A B.
Proof.
  intros D env1 env2 A B H.
  revert env2.
  induction H; intros env2.
  - apply SubRefl; exact H.
  - apply SubBox; [exact H | apply IHSubty].
  - eapply SubPi; [exact H | exact H0 | apply IHSubty1 | apply IHSubty2].
  - eapply SubSigma; [exact H | apply IHSubty1 | apply IHSubty2].
  - apply SubSum; [apply IHSubty1 | apply IHSubty2].
  - apply SubVec; [exact H | apply IHSubty].
Qed.

Lemma Subty_refl : forall (D : JoinDomain) (env : cenv D) A,
  Subty env A A.
Proof.
  intros D env A. apply SubRefl, cty_alpha_eq_refl.
Qed.

Lemma Subty_trans : forall (D : JoinDomain) (env : cenv D) A B C,
  Subty env A B ->
  Subty env B C ->
  Subty env A C.
Proof.
  intros D env A B C HAB HBC.
  revert env A C HAB HBC.
  induction B using cty_ind_nested; intros env A C HAB HBC;
    inversion HAB; subst;
    try (eapply Subty_alpha; [exact HBC | apply cenv_alpha_eq_refl | apply cty_alpha_eq_sym; eassumption | apply cty_alpha_eq_refl]);
    inversion HBC; subst;
    try (eapply Subty_alpha; [exact HAB | apply cenv_alpha_eq_refl | apply cty_alpha_eq_refl | eassumption]).
  - lazymatch goal with
    | Hc1 : cidx_eqb _ len = true, Hc2 : cidx_eqb len _ = true |- _ =>
        apply cidx_eqb_sound in Hc1; subst; apply SubVec; [exact Hc2 | eapply IHB; eassumption]
    end.
  - eapply SubPi.
    + eapply allows_trans; eassumption.
    + eapply allows_trans; eassumption.
    + eapply IHB1; eassumption.
    + lazymatch goal with
      | Hc1 : Subty (_ :: env) _ B2, Hc2 : Subty (_ :: env) B2 _ |- _ =>
          eapply IHB2; [eapply Subty_any_env; exact Hc1 | exact Hc2]
      end.
  - eapply SubSigma.
    + eapply allows_trans; eassumption.
    + eapply IHB1; eassumption.
    + lazymatch goal with
      | Hc1 : Subty (_ :: env) _ B2, Hc2 : Subty (_ :: env) B2 _ |- _ =>
          eapply IHB2; [exact Hc1 | eapply Subty_any_env; exact Hc2]
      end.
  - apply SubBox; [eapply allows_trans; eassumption | eapply IHB; eassumption].
  - apply SubSum; [eapply IHB1; eassumption | eapply IHB2; eassumption].
Qed.

Theorem core_subgrade_admissible : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (env env' : cenv D) t j target vt,
    cenv_demand_rel env' env ->
    CoreDerives env t j ->
    Subty env (cresult_type j) target ->
    CTypeDemand env' target vt ->
    exists j',
      CoreDerives env' (CSubgrade target t) j' /\
      cty_alpha_eq (cresult_type j') target /\
      branch_rel (ccomp_demand j') (ccomp_demand j) /\
      branch_rel (ctype_demand_row j') vt.
Proof.
  intros D ED env env' t j target vt Hrel Hder Hsub Hvt.
  destruct (core_derives_cenv_rel D ED env t j Hder env' Hrel) as [j1 [Hder1 [Hres1 [Hu1 Hv1]]]].
  pose proof (cenv_demand_rel_alpha D env' env Hrel) as Halpha.
  assert (Hsub1 : Subty env' (cresult_type j1) target) by
    (eapply Subty_alpha; [exact Hsub | apply cenv_alpha_eq_sym; exact Halpha | apply cty_alpha_eq_sym; exact Hres1 | apply cty_alpha_eq_refl]).
  destruct j1 as [act1 u1 v1].
  eexists. split; [| split; [| split]].
  - eapply CoreSubgrade; [exact Hder1 | exact Hsub1 | exact Hvt].
  - cbn [cresult_type]. apply cty_alpha_eq_refl.
  - cbn [ccomp_demand]. exact Hu1.
  - cbn [ctype_demand_row]. apply branch_rel_refl.
Qed.

(* ================================================================= *)
(* Part A2: Grade Substitution (JoinDomainMap Transport)             *)
(* ================================================================= *)

Fixpoint map_cidx {A B : JoinDomain} (m : JoinDomainMap A B) (i : cidx A) : cidx B :=
  match i with
  | CIdxVar x => CIdxVar x
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (map_cidx m l) (map_cidx m r)
  | CIdxProm q i' => CIdxProm (translate m q) (map_cidx m i')
  | CIdxUnbox b => CIdxUnbox b
  | CIdxFst p => CIdxFst p
  | CIdxSnd p => CIdxSnd p
  | CIdxCase s l r => CIdxCase s (map_cidx m l) (map_cidx m r)
  end.

Fixpoint map_cty {A B : JoinDomain} (m : JoinDomainMap A B) (T : cty A) : cty B :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (map_cty m elem) (map_cidx m len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar x
  | CTProm q inner => CTProm (translate m q) (map_cty m inner)
  | CTUnbox b => CTUnbox b
  | CPi x s r dom cod => CPi x (translate m s) (translate m r) (map_cty m dom) (map_cty m cod)
  | CSigma x r f s => CSigma x (translate m r) (map_cty m f) (map_cty m s)
  | CBox q inner => CBox (translate m q) (map_cty m inner)
  | CSum l r => CSum (map_cty m l) (map_cty m r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft)) fields)
  | CInd id indices => CInd id (map (map_cidx m) indices)
  end.

Fixpoint map_cterm {A B : JoinDomain} (m : JoinDomainMap A B) (t : cterm A) : cterm B :=
  match t with
  | CVar x => CVar x
  | CNatVal i => CNatVal (map_cidx m i)
  | CBoolVal b => CBoolVal b
  | CTypeVal T => CTypeVal (map_cty m T)
  | CLam x s r dom body => CLam x (translate m s) (translate m r) (map_cty m dom) (map_cterm m body)
  | CApp fn arg => CApp (map_cterm m fn) (map_cterm m arg)
  | CLet x s r ann rhs body => CLet x (translate m s) (translate m r) (map_cty m ann) (map_cterm m rhs) (map_cterm m body)
  | CPair x r ft st fv sv => CPair x (translate m r) (map_cty m ft) (map_cty m st) (map_cterm m fv) (map_cterm m sv)
  | CLetPair x y s kappa mot pr body =>
      CLetPair x y (translate m s) (translate m kappa) (map_cty m mot) (map_cterm m pr) (map_cterm m body)
  | CPromote q v => CPromote (translate m q) (map_cterm m v)
  | CLetBox x kappa mot bx body =>
      CLetBox x (translate m kappa) (map_cty m mot) (map_cterm m bx) (map_cterm m body)
  | CInl rt v => CInl (map_cty m rt) (map_cterm m v)
  | CInr lt v => CInr (map_cty m lt) (map_cterm m v)
  | CMatchSum x y s kappa mot scrut lb rb =>
      CMatchSum x y (translate m s) (translate m kappa) (map_cty m mot) (map_cterm m scrut) (map_cterm m lb) (map_cterm m rb)
  | CIf c th el => CIf (map_cterm m c) (map_cterm m th) (map_cterm m el)
  | CRecordMk id fields =>
      CRecordMk id (map (fun '(fn, fg, ft, fv) => (fn, translate m fg, map_cty m ft, map_cterm m fv)) fields)
  | CMatchRecord id s mot scrut bs body =>
      CMatchRecord id (translate m s) (map_cty m mot) (map_cterm m scrut) bs (map_cterm m body)
  | CSubgrade target body => CSubgrade (map_cty m target) (map_cterm m body)
  | CFix xn xr sr mot scrut base step =>
      CFix xn xr (translate m sr) (map_cty m mot) (map_cterm m scrut) (map_cterm m base) (map_cterm m step)
  end.

Definition map_cbinding {A B : JoinDomain} (m : JoinDomainMap A B) (e : cbinding A) : cbinding B :=
  {| cbinder := cbinder e;
     cannotation := map_cty m (cannotation e);
     ctype_uses := map (translate m) (ctype_uses e) |}.

Definition map_cenv {A B : JoinDomain} (m : JoinDomainMap A B) (env : cenv A) : cenv B :=
  map (map_cbinding m) env.

Definition map_cjudgment {A B : JoinDomain} (m : JoinDomainMap A B) (j : cjudgment A) : cjudgment B :=
  {| cresult_type := map_cty m (cresult_type j);
     ccomp_demand := map (translate m) (ccomp_demand j);
     ctype_demand_row := map (translate m) (ctype_demand_row j) |}.

Lemma map_vec_zero : forall (A B : JoinDomain) (m : JoinDomainMap A B) n,
  map (translate m) (vec_zero n) = vec_zero n.
Proof.
  intros A B m n. unfold vec_zero. induction n as [| n IH]; cbn; [reflexivity |].
  rewrite translate_zero, IH. reflexivity.
Qed.

Lemma map_vec_single : forall (A B : JoinDomain) (m : JoinDomainMap A B) n x q,
  map (translate m) (vec_single n x q) = vec_single n x (translate m q).
Proof.
  intros A B m n. induction n as [| n IH]; intros [| x'] q; cbn [map vec_single]; try reflexivity.
  - rewrite map_vec_zero. reflexivity.
  - rewrite translate_zero, IH. reflexivity.
Qed.

Lemma map_vec_add : forall (A B : JoinDomain) (m : JoinDomainMap A B) u v,
  map (translate m) (vec_add u v) = vec_add (map (translate m) u) (map (translate m) v).
Proof.
  intros A B m u. induction u as [| a u IH]; intros [| b v]; cbn; try reflexivity.
  rewrite translate_add, IH. reflexivity.
Qed.

Lemma map_vec_scale : forall (A B : JoinDomain) (m : JoinDomainMap A B) q u,
  map (translate m) (vec_scale q u) = vec_scale (translate m q) (map (translate m) u).
Proof.
  intros A B m q u. unfold vec_scale. rewrite !map_map. apply map_ext.
  intro x. apply translate_mul.
Qed.

Lemma map_vec_allows : forall (A B : JoinDomain) (m : JoinDomainMap A B) u v,
  vec_allows u v ->
  vec_allows (map (translate m) u) (map (translate m) v).
Proof.
  intros A B m u v H. induction H; cbn; constructor; [apply translate_allows; assumption | assumption].
Qed.

Lemma map_nth_grade : forall (A B : JoinDomain) (m : JoinDomainMap A B) u k,
  translate m (nth_grade u k) = nth_grade (map (translate m) u) k.
Proof.
  intros A B m u. induction u as [| a u IH]; intros [| k]; cbn; try apply translate_zero; try reflexivity.
  apply IH.
Qed.

Lemma map_tl : forall (X Y : Type) (f : X -> Y) (u : list X),
  map f (tl u) = tl (map f u).
Proof.
  intros X Y f [| a u]; reflexivity.
Qed.

Lemma map_skipn : forall (X Y : Type) (f : X -> Y) n (u : list X),
  map f (skipn n u) = skipn n (map f u).
Proof.
  intros X Y f n. induction n as [| n IH]; intros [| a u]; cbn; try reflexivity. apply IH.
Qed.

Lemma map_firstn : forall (X Y : Type) (f : X -> Y) n (u : list X),
  map f (firstn n u) = firstn n (map f u).
Proof.
  intros X Y f n. induction n as [| n IH]; intros [| a u]; cbn; try reflexivity.
  cbn. f_equal. apply IH.
Qed.

Lemma map_clookup : forall (A B : JoinDomain) (m : JoinDomainMap A B) env x e,
  clookup env x = Some e ->
  clookup (map_cenv m env) x = Some (map_cbinding m e).
Proof.
  intros A B m env x e H. unfold clookup, map_cenv in *.
  rewrite nth_error_map, H. reflexivity.
Qed.

Lemma map_cenv_length : forall (A B : JoinDomain) (m : JoinDomainMap A B) env,
  length (map_cenv m env) = length env.
Proof.
  intros A B m env. unfold map_cenv. apply length_map.
Qed.

Lemma map_erase_hints : forall (A B : JoinDomain) (m : JoinDomainMap A B) T,
  erase_hints (map_cty m T) = map_cty m (erase_hints T).
Proof.
  intros A B m T. induction T using cty_ind_nested; cbn; try reflexivity;
    try (f_equal; assumption); try (f_equal; [assumption | assumption]).
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
Qed.

Lemma map_cty_alpha_eq : forall (A B : JoinDomain) (m : JoinDomainMap A B) T1 T2,
  cty_alpha_eq T1 T2 ->
  cty_alpha_eq (map_cty m T1) (map_cty m T2).
Proof.
  intros A B m T1 T2 H. unfold cty_alpha_eq in *.
  rewrite !map_erase_hints, H. reflexivity.
Qed.

Lemma map_cty_alpha_eq_r : forall (A B : JoinDomain) (m : JoinDomainMap A B) T1 T2 T2',
  cty_alpha_eq T1 T2 ->
  T2' = map_cty m T2 ->
  cty_alpha_eq (map_cty m T1) T2'.
Proof.
  intros A B m T1 T2 T2' H ->. apply map_cty_alpha_eq; exact H.
Qed.

Lemma map_ren_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) r i,
  ren_cidx r (map_cidx m i) = map_cidx m (ren_cidx r i).
Proof.
  intros A B m r i. revert r. induction i; intro r; cbn;
    try reflexivity; try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
Qed.

Lemma map_ren_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) r T,
  ren_cty r (map_cty m T) = map_cty m (ren_cty r T).
Proof.
  intros A B m r T. revert r. induction T using cty_ind_nested; intro rn; cbn;
    try reflexivity; try (rewrite IHT; reflexivity); try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT, map_ren_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_ren_cidx | exact IH].
Qed.

Lemma map_lift_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) c d i,
  lift_cidx c d (map_cidx m i) = map_cidx m (lift_cidx c d i).
Proof.
  intros A B m c d i. apply map_ren_cidx.
Qed.

Lemma map_lift_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) c d T,
  lift_cty c d (map_cty m T) = map_cty m (lift_cty c d T).
Proof.
  intros A B m c d T. apply map_ren_cty.
Qed.

Lemma map_unshift_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) k i,
  unshift_cidx k (map_cidx m i) = map_cidx m (unshift_cidx k i).
Proof.
  intros A B m k i. apply map_ren_cidx.
Qed.

Lemma map_unshift_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k T,
  unshift_cty k (map_cty m T) = map_cty m (unshift_cty k T).
Proof.
  intros A B m k T. apply map_ren_cty.
Qed.

Lemma map_subst_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) k val i,
  subst_cidx k (map_cidx m val) (map_cidx m i) = map_cidx m (subst_cidx k val i).
Proof.
  intros A B m k val i. revert k val. induction i; intros k val; cbn;
    try reflexivity; try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
  - destruct (x =? k); [reflexivity | destruct (x <? k); reflexivity].
  - rewrite map_lift_cidx, IHi1, IHi2. reflexivity.
Qed.

Lemma map_subst_cidx_in_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k val T,
  subst_cidx_in_cty k (map_cidx m val) (map_cty m T) = map_cty m (subst_cidx_in_cty k val T).
Proof.
  intros A B m k val T. revert k val.
  induction T using cty_ind_nested; intros k val; cbn; try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity);
    try (rewrite IHT1, map_lift_cidx, IHT2; reflexivity).
  - rewrite IHT, map_subst_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_subst_cidx | exact IH].
Qed.

Lemma map_subst_tvar_in_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) k i,
  subst_tvar_in_cidx k (map_cidx m i) = map_cidx m (subst_tvar_in_cidx k i).
Proof.
  intros A B m k i. revert k. induction i; intro k; cbn;
    repeat (destruct (_ <? _) || destruct (_ =? _)); cbn;
    try reflexivity; try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
Qed.

Lemma map_subst_tvar_in_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k U T,
  subst_tvar_in_cty k (map_cty m U) (map_cty m T) = map_cty m (subst_tvar_in_cty k U T).
Proof.
  intros A B m k U T. revert k U.
  induction T using cty_ind_nested; intros k U; cbn; try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity);
    try (rewrite IHT1, map_lift_cty, IHT2; reflexivity).
  - rewrite IHT, map_subst_tvar_in_cidx. reflexivity.
  - repeat (destruct (_ <? _) || destruct (_ =? _)); reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_subst_tvar_in_cidx | exact IH].
Qed.

Lemma map_subst_pair_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) k fi si i,
  subst_pair_cidx k (map_cidx m fi) (map_cidx m si) (map_cidx m i) = map_cidx m (subst_pair_cidx k fi si i).
Proof.
  intros A B m k fi si i. revert k fi si. induction i; intros k fi si; cbn;
    repeat (destruct (_ <? _) || destruct (_ =? _)); cbn;
    try reflexivity; try (rewrite ?map_lift_cidx, IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
Qed.

Lemma map_subst_pair_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k fi si T,
  subst_pair_cty k (map_cidx m fi) (map_cidx m si) (map_cty m T) = map_cty m (subst_pair_cty k fi si T).
Proof.
  intros A B m k fi si T. revert k fi si.
  induction T using cty_ind_nested; intros k fi si; cbn; try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity);
    try (rewrite IHT1, !map_lift_cidx, IHT2; reflexivity).
  - rewrite IHT, map_subst_pair_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_subst_pair_cidx | exact IH].
Qed.

Lemma map_subst_box_nat_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) k q bi i,
  subst_box_nat_cidx k (translate m q) (map_cidx m bi) (map_cidx m i) = map_cidx m (subst_box_nat_cidx k q bi i).
Proof.
  intros A B m k q bi i. revert k q bi. induction i; intros k q0 bi; cbn;
    repeat (destruct (_ <? _) || destruct (_ =? _)); cbn;
    try reflexivity; try (rewrite ?map_lift_cidx, IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
Qed.

Lemma map_subst_box_nat_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k q bi T,
  subst_box_nat_cty k (translate m q) (map_cidx m bi) (map_cty m T) = map_cty m (subst_box_nat_cty k q bi T).
Proof.
  intros A B m k q bi T. revert k q bi.
  induction T using cty_ind_nested; intros k q0 bi; cbn;
    repeat (destruct (_ <? _) || destruct (_ =? _)); try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity);
    try (rewrite IHT1, map_lift_cidx, IHT2; reflexivity).
  - rewrite IHT, map_subst_box_nat_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_subst_box_nat_cidx | exact IH].
Qed.

Lemma map_subst_box_ty_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k q U T,
  subst_box_ty_cty k (translate m q) (map_cty m U) (map_cty m T) = map_cty m (subst_box_ty_cty k q U T).
Proof.
  intros A B m k q U T. revert k q U.
  induction T using cty_ind_nested; intros k q0 U; cbn;
    repeat (destruct (_ <? _) || destruct (_ =? _)); try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity);
    try (rewrite IHT1, map_lift_cty, IHT2; reflexivity).
  - rewrite IHT, map_subst_tvar_in_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_subst_tvar_in_cidx | exact IH].
Qed.

Lemma map_subst_sum_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) il k vi i,
  subst_sum_cidx il k (map_cidx m vi) (map_cidx m i) = map_cidx m (subst_sum_cidx il k vi i).
Proof.
  intros A B m il k vi i. revert il k vi. induction i; intros il k vi; cbn;
    repeat (destruct (_ <? _) || destruct (_ =? _)); cbn;
    try reflexivity; try (rewrite ?map_lift_cidx, IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity);
    try (rewrite map_lift_cidx; destruct il; cbv iota; [rewrite IHi1 | rewrite IHi2]; rewrite map_subst_cidx; reflexivity).
Qed.

Lemma map_subst_sum_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) il k vi T,
  subst_sum_cty il k (map_cidx m vi) (map_cty m T) = map_cty m (subst_sum_cty il k vi T).
Proof.
  intros A B m il k vi T. revert il k vi.
  induction T using cty_ind_nested; intros il k vi; cbn; try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity);
    try (rewrite IHT1, map_lift_cidx, IHT2; reflexivity).
  - rewrite IHT, map_subst_sum_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_subst_sum_cidx | exact IH].
Qed.

Lemma map_spec_pair_body_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) k i,
  spec_pair_body_cidx k (map_cidx m i) = map_cidx m (spec_pair_body_cidx k i).
Proof.
  intros A B m k i. revert k. induction i; intro k; cbn;
    repeat (destruct (_ =? _) || destruct (_ <? _)); cbn;
    try reflexivity; try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
Qed.

Lemma map_spec_pair_body_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) k T,
  spec_pair_body_cty k (map_cty m T) = map_cty m (spec_pair_body_cty k T).
Proof.
  intros A B m k T. revert k. induction T using cty_ind_nested; intro k; cbn;
    try reflexivity; try (rewrite IHT; reflexivity); try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT, map_spec_pair_body_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_spec_pair_body_cidx | exact IH].
Qed.

Lemma map_spec_box_body_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) q k i,
  spec_box_body_cidx (translate m q) k (map_cidx m i) = map_cidx m (spec_box_body_cidx q k i).
Proof.
  intros A B m q k i. revert k. induction i; intro k; cbn;
    repeat (destruct (_ =? _)); cbn;
    try reflexivity; try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
Qed.

Lemma map_spec_box_body_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) q k T,
  spec_box_body_cty (translate m q) k (map_cty m T) = map_cty m (spec_box_body_cty q k T).
Proof.
  intros A B m q k T. revert k. induction T using cty_ind_nested; intro k; cbn;
    repeat (destruct (_ =? _)); cbn;
    try reflexivity; try (rewrite IHT; reflexivity); try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT, map_spec_box_body_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_spec_box_body_cidx | exact IH].
Qed.

Lemma map_spec_sum_branch_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) il k i,
  spec_sum_branch_cidx il k (map_cidx m i) = map_cidx m (spec_sum_branch_cidx il k i).
Proof.
  intros A B m il k i. revert k. induction i; intro k; cbn;
    repeat (destruct (_ =? _) || destruct (_ <? _)); cbn;
    try reflexivity; try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity).
  - destruct il; change (@CIdxVar B 0) with (map_cidx m (@CIdxVar A 0));
      rewrite map_subst_sum_cidx, map_ren_cidx; reflexivity.
Qed.

Lemma map_spec_sum_branch_cty : forall (A B : JoinDomain) (m : JoinDomainMap A B) il k T,
  spec_sum_branch_cty il k (map_cty m T) = map_cty m (spec_sum_branch_cty il k T).
Proof.
  intros A B m il k T. revert k. induction T using cty_ind_nested; intro k; cbn;
    try reflexivity; try (rewrite IHT; reflexivity); try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT, map_spec_sum_branch_cidx. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. f_equal; [f_equal; apply H2 | apply IH; exact H3].
  - f_equal. induction indices as [| idx rest IH]; cbn; [reflexivity |].
    f_equal; [apply map_spec_sum_branch_cidx | exact IH].
Qed.

Lemma map_term_as_cidx : forall (A B : JoinDomain) (m : JoinDomainMap A B) t,
  term_as_cidx (map_cterm m t) = option_map (map_cidx m) (term_as_cidx t).
Proof.
  intros A B m t. destruct t; reflexivity.
Qed.

Lemma map_cty_uses_var : forall (A B : JoinDomain) (m : JoinDomainMap A B) k T,
  cty_uses_var k (map_cty m T) = cty_uses_var k T.
Proof.
  intros A B m k T.
  assert (Hi : forall i k0, cidx_uses_var k0 (map_cidx m i) = cidx_uses_var k0 i).
  { induction i; intro k0; cbn; try reflexivity;
      try (rewrite IHi1, IHi2; reflexivity); try (rewrite IHi; reflexivity). }
  revert k. induction T using cty_ind_nested; intro k; cbn; try reflexivity;
    try (apply IHT); try (rewrite IHT1, IHT2; reflexivity).
  - rewrite IHT, Hi. reflexivity.
  - induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. rewrite H2, (IH H3). reflexivity.
  - induction indices as [| idx rest IH]; cbn; [reflexivity |].
    rewrite Hi, IH. reflexivity.
Qed.

Lemma map_branch_vec : forall (A B : JoinDomain) (m : JoinDomainMap A B),
  (forall j2, grade_join B = Some j2 -> forall x, j2 x x = x) ->
  forall u1 u2 u,
  BranchVec u1 u2 u ->
  BranchVec (map (translate m) u1) (map (translate m) u2) (map (translate m) u).
Proof.
  intros A B m Hidem u1 u2 u Hbr. unfold BranchVec in *.
  destruct (grade_join A) as [j1 |] eqn:Hj1.
  - destruct (jmap_join_compat A B m j1 Hj1) as [j2 [Hj2 Hcomm]].
    rewrite Hj2. subst u. clear Hj1 Hj2.
    revert u2. induction u1 as [| a u1 IH]; intros [| b u2]; cbn; [reflexivity | reflexivity | reflexivity |].
    rewrite Hcomm, IH. reflexivity.
  - destruct Hbr as [-> ->].
    destruct (grade_join B) as [j2 |] eqn:Hj2; [| split; reflexivity].
    induction u2 as [| a u2 IH]; cbn; [reflexivity | rewrite (Hidem j2 eq_refl), <- IH; reflexivity].
Qed.

Lemma map_cidx_demand : forall (A B : JoinDomain) (m : JoinDomainMap A B),
  (forall j2, grade_join B = Some j2 -> forall x, j2 x x = x) ->
  forall env i d,
  CIdxDemand env i d ->
  CIdxDemand (map_cenv m env) (map_cidx m i) (map (translate m) d).
Proof.
  intros A B m Hidem env i d H. induction H; cbn.
  - rewrite map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CIdxDemandVar; [apply map_clookup; exact H | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact H0 | reflexivity]].
  - rewrite map_vec_zero, <- (map_cenv_length A B m env). apply CIdxDemandLit.
  - rewrite map_vec_add. apply CIdxDemandAdd; assumption.
  - rewrite map_vec_scale. apply CIdxDemandProm; assumption.
  - rewrite map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CIdxDemandUnbox; [apply map_clookup; exact H | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact H0 | reflexivity]].
  - rewrite map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CIdxDemandFst; [apply map_clookup; exact H | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact H0 | reflexivity]].
  - rewrite map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CIdxDemandSnd; [apply map_clookup; exact H | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact H0 | reflexivity]].
  - rewrite map_vec_add, map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CIdxDemandCase;
      [ apply map_clookup; exact H
      | cbn [cannotation map_cbinding]; rewrite map_ren_cty; eapply map_cty_alpha_eq_r; [exact H0 | reflexivity]
      | unfold map_cenv in IHCIdxDemand1; cbn [map] in IHCIdxDemand1; unfold map_cbinding in IHCIdxDemand1; cbn [cbinder cannotation ctype_uses] in IHCIdxDemand1;
        rewrite map_vec_zero, <- (map_cenv_length A B m env) in IHCIdxDemand1; exact IHCIdxDemand1
      | unfold map_cenv in IHCIdxDemand2; cbn [map] in IHCIdxDemand2; unfold map_cbinding in IHCIdxDemand2; cbn [cbinder cannotation ctype_uses] in IHCIdxDemand2;
        rewrite map_vec_zero, <- (map_cenv_length A B m env) in IHCIdxDemand2; exact IHCIdxDemand2
      | rewrite <- !map_tl; apply map_branch_vec; [exact Hidem | exact H3] ].
Qed.

Lemma map_ctype_demand : forall (A B : JoinDomain) (m : JoinDomainMap A B),
  (forall j2, grade_join B = Some j2 -> forall x, j2 x x = x) ->
  forall env T d,
  CTypeDemand env T d ->
  CTypeDemand (map_cenv m env) (map_cty m T) (map (translate m) d).
Proof.
  intros A B m Hidem env T d H.
  induction H using CTypeDemand_ind_mut with
    (P := fun env T d _ => CTypeDemand (map_cenv m env) (map_cty m T) (map (translate m) d))
    (P0 := fun env fs df _ => CRecordFieldDemand (map_cenv m env)
      (map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft)) fs) (map (translate m) df))
    (P1 := fun env ls dl _ => CIdxListDemand (map_cenv m env) (map (map_cidx m) ls) (map (translate m) dl));
    cbn; try (rewrite map_vec_zero, <- (map_cenv_length A B m env); constructor).
  - rewrite map_vec_add. apply CTypeVec; [exact IHCTypeDemand | apply map_cidx_demand; [exact Hidem | exact c]].
  - rewrite map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CTypeTVar; [apply map_clookup; exact e0 | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact c | reflexivity]].
  - rewrite map_vec_scale. apply CTypeTProm; exact IHCTypeDemand.
  - rewrite map_vec_single, translate_one, <- (map_cenv_length A B m env).
    eapply CTypeTUnbox; [apply map_clookup; exact e0 | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact c | reflexivity]].
  - rewrite map_vec_add, map_tl. eapply CTypePi; [exact IHCTypeDemand1 | exact IHCTypeDemand2 |].
    rewrite <- map_nth_grade. apply translate_allows; exact a0.
  - rewrite map_vec_add, map_tl. eapply CTypeSigma; [exact IHCTypeDemand1 | exact IHCTypeDemand2 |].
    rewrite <- map_nth_grade. apply translate_allows; exact a0.
  - apply CTypeBox; exact IHCTypeDemand.
  - rewrite map_vec_add. apply CTypeSum; assumption.
  - apply CTypeRecord; exact IHCTypeDemand.
  - apply CTypeInd; exact IHCTypeDemand.
  - rewrite map_vec_add. apply CRecordFieldCons; assumption.
  - rewrite map_vec_add. apply CIdxListCons; [apply map_cidx_demand; [exact Hidem | exact c] | exact IHCTypeDemand].
Qed.

Lemma map_cuniverse_level : forall (A B : JoinDomain) (m : JoinDomainMap A B) env T lvl,
  CUniverseLevel env T lvl ->
  CUniverseLevel (map_cenv m env) (map_cty m T) lvl.
Proof.
  intros A B m env T lvl H.
  induction H using CUniverseLevel_ind_mut with
    (P := fun env T lvl _ => CUniverseLevel (map_cenv m env) (map_cty m T) lvl)
    (P0 := fun env fs lvl _ => CRecordFieldLevel (map_cenv m env)
      (map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft)) fs) lvl);
    cbn; try constructor; try assumption.
  - eapply CLevelTVar; [apply map_clookup; exact e0 | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact c | reflexivity]].
  - eapply CLevelTUnbox; [apply map_clookup; exact e0 | cbn [cannotation map_cbinding]; eapply map_cty_alpha_eq_r; [exact c | reflexivity]].
Qed.

Lemma map_cidx_eqb : forall (A B : JoinDomain) (m : JoinDomainMap A B) i1 i2,
  cidx_eqb i1 i2 = true ->
  cidx_eqb (map_cidx m i1) (map_cidx m i2) = true.
Proof.
  intros A B m i1 i2 H. apply cidx_eqb_sound in H. subst i2. apply cidx_eqb_refl.
Qed.

Lemma map_subty : forall (A B : JoinDomain) (m : JoinDomainMap A B) env T1 T2,
  Subty env T1 T2 ->
  Subty (map_cenv m env) (map_cty m T1) (map_cty m T2).
Proof.
  intros A B m env T1 T2 H. induction H; cbn.
  - apply SubRefl, map_cty_alpha_eq; exact H.
  - apply SubBox; [apply translate_allows; exact H | exact IHSubty].
  - eapply SubPi; [apply translate_allows; exact H | apply translate_allows; exact H0 | exact IHSubty1 |].
    eapply Subty_any_env; exact IHSubty2.
  - eapply SubSigma; [apply translate_allows; exact H | exact IHSubty1 |].
    eapply Subty_any_env; exact IHSubty2.
  - apply SubSum; assumption.
  - apply SubVec; [apply map_cidx_eqb; exact H | exact IHSubty].
Qed.

Lemma map_crecord_extend : forall (A B : JoinDomain) (m : JoinDomainMap A B),
  (forall j2, grade_join B = Some j2 -> forall x, j2 x x = x) ->
  forall env bs fs body_env,
  CRecordExtendEnv env bs fs body_env ->
  CRecordExtendEnv (map_cenv m env) bs
    (map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft)) fs)
    (map_cenv m body_env).
Proof.
  intros A B m Hidem env bs fs body_env H. induction H; cbn.
  - apply CRecordExtNil.
  - apply CRecordExtCons with (row := map (translate m) row).
    + apply map_ctype_demand; [exact Hidem | exact H].
    + cbn [map_cenv map] in IHCRecordExtendEnv.
      replace (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0))
                   (map (fun '(fn0, fg0, ft0) => (fn0, translate m fg0, map_cty m ft0)) rest))
         with (map (fun '(fn0, fg0, ft0) => (fn0, translate m fg0, map_cty m ft0))
                   (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest))
        by (rewrite !map_map; apply map_ext; intros [[n0 g0] t0]; rewrite map_lift_cty; reflexivity).
      exact IHCRecordExtendEnv.
Qed.

Lemma map_crecord_field_allows : forall (A B : JoinDomain) (m : JoinDomainMap A B) s fs us,
  CRecordFieldAllows s fs us ->
  CRecordFieldAllows (translate m s)
    (map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft)) fs)
    (map (translate m) us).
Proof.
  intros A B m s fs us H. induction H; cbn;
    [apply CRecordAllowsNil | apply CRecordAllowsCons; [rewrite <- translate_mul; apply translate_allows; exact H | assumption]].
Qed.

Theorem core_grade_substitution : forall (A B : JoinDomain) (m : JoinDomainMap A B),
  (forall g, translate m g = zero -> g = zero) ->
  (forall j2, grade_join B = Some j2 -> forall x, j2 x x = x) ->
  forall env t j,
    CoreDerives env t j ->
    CoreDerives (map_cenv m env) (map_cterm m t) (map_cjudgment m j).
Proof.
  intros A B m Hzero_ref Hidem env t j H.
  induction H using CoreDerives_ind_mut with
    (P := fun env t j _ => CoreDerives (map_cenv m env) (map_cterm m t) (map_cjudgment m j))
    (P0 := fun env fs u v _ => CRecordElemDerives (map_cenv m env)
      (map (fun '(fn, fg, ft, fv) => (fn, translate m fg, map_cty m ft, map_cterm m fv)) fs)
      (map (translate m) u) (map (translate m) v));
    unfold map_cjudgment in *; cbn [map_cterm cresult_type ccomp_demand ctype_demand_row] in *.
  - rewrite <- map_ren_cty, map_app, map_vec_single, map_vec_zero, translate_one, <- (map_cenv_length A B m env).
    change (map_cty m (cannotation e)) with (cannotation (map_cbinding m e));
    change (map (translate m) (ctype_uses e)) with (ctype_uses (map_cbinding m e)).
    eapply CoreVar; [apply map_clookup; exact e0 | |].
    + unfold map_cenv in *. rewrite <- map_skipn. apply (map_ctype_demand _ _ _ Hidem); exact c.
    + apply map_vec_allows; exact v.
  - rewrite map_vec_zero, <- (map_cenv_length A B m env).
    apply CoreNatVal; apply map_cidx_demand; [exact Hidem | exact c].
  - rewrite !map_vec_zero, <- (map_cenv_length A B m env). apply CoreBoolVal.
  - rewrite map_vec_zero, <- (map_cenv_length A B m env).
    apply CoreTypeVal; [apply (map_ctype_demand _ _ _ Hidem); exact c | apply map_cuniverse_level; exact c0].
  - rewrite map_vec_add, !map_tl.
    eapply CoreLam; [apply (map_ctype_demand _ _ _ Hidem); exact c | exact IHCoreDerives | |];
      rewrite <- map_nth_grade; apply translate_allows; assumption.
  - lazymatch goal with
    | Hkd : cty_alpha_eq _ dom,
      Hdm : CTypeDemand env dom _,
      Hcd : CTypeDemand (_ :: env) cod _,
      Huniv : forall _ _, dom = CUniv _ -> _,
      Hres : app_result_ty dom cod arg = Some res_ty |- _ =>
      assert (Hres_eq : app_result_ty (map_cty m dom) (map_cty m cod) (map_cterm m arg) = Some (map_cty m res_ty));
      [ unfold app_result_ty in Hres |- *; rewrite map_term_as_cidx;
        destruct dom; cbn in Hres |- *;
        try (rewrite map_cty_uses_var; destruct (cty_uses_var 0 cod); inversion Hres; rewrite map_unshift_cty; reflexivity);
        [ destruct (term_as_cidx arg) eqn:Ea; cbn in Hres |- *;
            [ inversion Hres; rewrite map_subst_cidx_in_cty; reflexivity
            | rewrite map_cty_uses_var; destruct (cty_uses_var 0 cod); inversion Hres; rewrite map_unshift_cty; reflexivity ]
        | destruct arg; cbn [map_cterm];
            try (rewrite map_cty_uses_var; destruct (cty_uses_var 0 cod); inversion Hres; rewrite map_unshift_cty; reflexivity);
            [ lazymatch goal with
              | |- Some (subst_tvar_in_cty 0 (CTVar ?v) _) = _ =>
                inversion Hres; subst;
                change (@CTVar B v) with (map_cty m (@CTVar A v));
                rewrite map_subst_tvar_in_cty; reflexivity
              end
            | inversion Hres; subst; rewrite map_subst_tvar_in_cty; reflexivity ] ]
      | assert (Hz_eq : map (translate m) z_type = app_type_arg_demand (map_cty m dom) (map_cterm m arg) (map (translate m) u_arg) (map (translate m) v_arg));
        [ subst z_type; unfold app_type_arg_demand; destruct dom; cbn; try reflexivity;
          destruct arg; reflexivity
        | rewrite !map_vec_add, !map_vec_scale, map_tl, Hz_eq;
          eapply CoreApp;
            [ exact IHCoreDerives1
            | exact IHCoreDerives2
            | apply map_cty_alpha_eq; exact Hkd
            | apply (map_ctype_demand _ _ _ Hidem); exact Hdm
            | apply (map_ctype_demand A B m Hidem) in Hcd;
              unfold map_cenv in Hcd; cbn [map] in Hcd;
              unfold map_cbinding in Hcd; cbn [cbinder cannotation ctype_uses] in Hcd;
              exact Hcd
            | rewrite <- map_nth_grade; apply translate_allows; assumption
            | intros lvl0 arg_ty Hdom [Htv | [y0 [Harg Hty]]];
              [ destruct dom; inversion Hdom; subst lvl0;
                destruct arg; inversion Htv; subst arg_ty;
                apply map_cuniverse_level; exact (Huniv _ _ eq_refl (or_introl eq_refl))
              | destruct dom; inversion Hdom; subst lvl0;
                destruct arg; inversion Harg; subst;
                lazymatch goal with
                | |- CUniverseLevel _ (CTVar ?v) _ =>
                  change (@CTVar B v) with (map_cty m (@CTVar A v));
                  apply map_cuniverse_level; exact (Huniv _ _ eq_refl (or_intror (ex_intro _ v (conj eq_refl eq_refl))))
                end ]
            | exact Hres_eq
            | reflexivity ] ] ]
    end.
  - lazymatch goal with
    | Hdm : CTypeDemand env _ _,
      Hceq : cty_alpha_eq _ _,
      Huse : cty_uses_var 0 bod_ty = false |- _ =>
      assert (Hz_eq : map (translate m) (app_type_arg_demand ann rhs u_rhs v_rhs) =
        app_type_arg_demand (map_cty m ann) (map_cterm m rhs) (map (translate m) u_rhs) (map (translate m) v_rhs))
        by (unfold app_type_arg_demand; destruct ann; cbn; try reflexivity; destruct rhs; reflexivity);
      rewrite !map_vec_add, !map_vec_scale, !map_tl, <- map_unshift_cty, Hz_eq;
      eapply CoreLet;
        [ apply (map_ctype_demand A B m Hidem); exact Hdm
        | exact IHCoreDerives1
        | apply map_cty_alpha_eq; exact Hceq
        | exact IHCoreDerives2
        | rewrite <- map_nth_grade; apply translate_allows; assumption
        | rewrite <- map_nth_grade; apply translate_allows; assumption
        | rewrite map_cty_uses_var; exact Huse ]
    end.
  - lazymatch goal with
    | Hdm1 : CTypeDemand env fst_ty _,
      Hdm2 : CTypeDemand (_ :: env) snd_ty _,
      Hceq1 : cty_alpha_eq _ fst_ty,
      Hceq2 : cty_alpha_eq _ exp_snd,
      Hres : app_result_ty fst_ty snd_ty fst_val = Some exp_snd |- _ =>
      assert (Hres_eq : app_result_ty (map_cty m fst_ty) (map_cty m snd_ty) (map_cterm m fst_val) = Some (map_cty m exp_snd));
      [ unfold app_result_ty in Hres |- *; rewrite map_term_as_cidx;
        destruct fst_ty; cbn in Hres |- *;
        try (rewrite map_cty_uses_var; destruct (cty_uses_var 0 snd_ty); inversion Hres; subst; rewrite map_unshift_cty; reflexivity);
        [ destruct (term_as_cidx fst_val); cbn in Hres |- *;
            [ inversion Hres; subst; rewrite map_subst_cidx_in_cty; reflexivity
            | rewrite map_cty_uses_var; destruct (cty_uses_var 0 snd_ty); inversion Hres; subst; rewrite map_unshift_cty; reflexivity ]
        | destruct fst_val; cbn [map_cterm];
            try (rewrite map_cty_uses_var; destruct (cty_uses_var 0 snd_ty); inversion Hres; subst; rewrite map_unshift_cty; reflexivity);
            [ lazymatch goal with
              | |- Some (subst_tvar_in_cty 0 (CTVar ?v) _) = _ =>
                inversion Hres; subst;
                change (@CTVar B v) with (map_cty m (@CTVar A v));
                rewrite map_subst_tvar_in_cty; reflexivity
              end
            | inversion Hres; subst; rewrite map_subst_tvar_in_cty; reflexivity ] ]
      | rewrite !map_vec_add, map_tl;
        eapply CorePair;
          [ apply (map_ctype_demand A B m Hidem); exact Hdm1
          | apply (map_ctype_demand A B m Hidem) in Hdm2;
            unfold map_cenv in Hdm2; cbn [map] in Hdm2;
            unfold map_cbinding in Hdm2; cbn [cbinder cannotation ctype_uses] in Hdm2;
            rewrite ?map_vec_zero in Hdm2; try rewrite <- (map_cenv_length A B m env) in Hdm2; exact Hdm2
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | exact IHCoreDerives1
          | apply map_cty_alpha_eq; exact Hceq1
          | exact IHCoreDerives2
          | exact Hres_eq
          | apply map_cty_alpha_eq; exact Hceq2 ] ]
    end.
  - lazymatch goal with
    | Hdm1 : CTypeDemand env _ _,
      Hdm2 : CTypeDemand (_ :: env) _ _,
      Hdm_mot : CTypeDemand (_ :: env) mot _,
      Hceq : cty_alpha_eq _ _ |- _ =>
      assert (Hspec_b : map_cty m (spec_pair_body_cty 0 mot) = spec_pair_body_cty 0 (map_cty m mot)) by
        (symmetry; apply map_spec_pair_body_cty);
      assert (Hspec_s : map_cty m (spec_pair_subj_cty pr mot) = spec_pair_subj_cty (map_cterm m pr) (map_cty m mot));
      [ unfold spec_pair_subj_cty; destruct pr; try (rewrite map_unshift_cty; reflexivity);
        [ cbn; unfold subst_var_in_cty; rewrite map_ren_cty; reflexivity
        | cbn; rewrite !map_term_as_cidx;
          destruct (term_as_cidx pr1); [destruct (term_as_cidx pr2); [cbn; rewrite map_subst_pair_cty; reflexivity | rewrite map_unshift_cty; reflexivity] | rewrite map_unshift_cty; reflexivity] ]
      | rewrite !map_vec_add, !map_vec_scale, !map_tl;
        eapply CoreLetPair;
          [ exact IHCoreDerives1
          | apply (map_ctype_demand _ _ _ Hidem); exact Hdm1
          | apply (map_ctype_demand A B m Hidem) in Hdm2;
            unfold map_cenv in Hdm2; cbn [map] in Hdm2;
            unfold map_cbinding in Hdm2; cbn [cbinder cannotation ctype_uses] in Hdm2;
            rewrite ?map_vec_zero in Hdm2; try rewrite <- (map_cenv_length A B m env) in Hdm2; exact Hdm2
          | apply (map_ctype_demand A B m Hidem) in Hdm_mot;
            unfold map_cenv in Hdm_mot; cbn [map] in Hdm_mot;
            unfold map_cbinding in Hdm_mot; cbn [cbinder cannotation ctype_uses] in Hdm_mot;
            rewrite map_vec_add, map_tl in Hdm_mot; exact Hdm_mot
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | exact IHCoreDerives2
          | reflexivity
          | subst exp_mot; rewrite <- Hspec_b; apply map_cty_alpha_eq; exact Hceq
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | destruct pr; cbn in *; try (rewrite map_cty_uses_var; assumption); try exact I;
            rewrite !map_term_as_cidx;
            destruct (term_as_cidx pr1); [destruct (term_as_cidx pr2); [exact I | rewrite map_cty_uses_var; assumption] | rewrite map_cty_uses_var; assumption]
          | subst res_ty; exact Hspec_s ] ]
    end.
  - rewrite map_vec_scale. apply CorePromote; exact IHCoreDerives.
  - lazymatch goal with
    | Hdm1 : CTypeDemand env _ _,
      Hdm_mot : CTypeDemand (_ :: env) mot _,
      Hceq : cty_alpha_eq _ _ |- _ =>
      assert (Hspec_b : map_cty m (spec_box_body_cty q 0 mot) = spec_box_body_cty (translate m q) 0 (map_cty m mot)) by
        (symmetry; apply map_spec_box_body_cty);
      assert (Hspec_s : map_cty m (spec_box_subj_cty box_term mot) = spec_box_subj_cty (map_cterm m box_term) (map_cty m mot));
      [ unfold spec_box_subj_cty; destruct box_term; try (rewrite map_unshift_cty; reflexivity);
        [ cbn; unfold subst_var_in_cty; rewrite map_ren_cty; reflexivity
        | destruct box_term; try (rewrite map_unshift_cty; reflexivity); cbn;
          [ unfold subst_var_in_cty; rewrite map_spec_box_body_cty, map_ren_cty; reflexivity
          | rewrite map_subst_box_nat_cty; reflexivity
          | rewrite map_subst_box_ty_cty; reflexivity ] ]
      | assert (Hzty : map (translate m) z_ty =
          match map_cterm m box_term with CPromote q' (CTypeVal _) => vec_scale q' (map (translate m) vz) | _ => map (translate m) z_b end);
        [ subst z_ty; destruct box_term; try reflexivity; destruct box_term; try reflexivity;
          cbn; rewrite map_vec_scale; reflexivity
        | rewrite !map_vec_add, map_vec_scale, !map_tl, Hzty;
          eapply CoreLetBox;
            [ exact IHCoreDerives1
            | apply (map_ctype_demand _ _ _ Hidem); exact Hdm1
            | apply (map_ctype_demand A B m Hidem) in Hdm_mot;
              unfold map_cenv in Hdm_mot; cbn [map] in Hdm_mot;
              unfold map_cbinding in Hdm_mot; cbn [cbinder cannotation ctype_uses] in Hdm_mot;
              rewrite ?map_vec_zero in Hdm_mot; try rewrite <- (map_cenv_length A B m env) in Hdm_mot; exact Hdm_mot
            | rewrite <- map_nth_grade; apply translate_allows; assumption
            | exact IHCoreDerives2
            | reflexivity
            | subst exp_mot; rewrite <- Hspec_b; apply map_cty_alpha_eq; exact Hceq
            | first
                [ rewrite <- map_nth_grade; apply translate_allows; assumption
                | rewrite <- map_nth_grade, <- translate_mul; apply translate_allows; assumption ]
            | first
                [ rewrite <- map_nth_grade; apply translate_allows; assumption
                | rewrite <- map_nth_grade, <- translate_mul; apply translate_allows; assumption ]
            | destruct box_term; cbn in *; try (rewrite map_cty_uses_var; assumption); try exact I;
              destruct box_term; cbn in *; try (rewrite map_cty_uses_var; assumption); exact I
            | subst res_ty; exact Hspec_s
            | reflexivity ] ] ]
    end.
  - rewrite map_vec_add. apply CoreInl; [exact IHCoreDerives | apply (map_ctype_demand _ _ _ Hidem); assumption].
  - rewrite map_vec_add. apply CoreInr; [apply (map_ctype_demand _ _ _ Hidem); assumption | exact IHCoreDerives].
  - lazymatch goal with
    | Hnz : _ <> zero,
      Hdm_l : CTypeDemand env A0 _,
      Hdm_r : CTypeDemand env B0 _,
      Hdm_mot : CTypeDemand (_ :: env) mot _ |- _ =>
      assert (Hspec_l : map_cty m (spec_sum_branch_cty true 0 mot) = spec_sum_branch_cty true 0 (map_cty m mot)) by
        (symmetry; apply map_spec_sum_branch_cty);
      assert (Hspec_r : map_cty m (spec_sum_branch_cty false 0 mot) = spec_sum_branch_cty false 0 (map_cty m mot)) by
        (symmetry; apply map_spec_sum_branch_cty);
      assert (Hspec_s : map_cty m (spec_sum_subj_cty scrut mot) = spec_sum_subj_cty (map_cterm m scrut) (map_cty m mot));
      [ unfold spec_sum_subj_cty; destruct scrut; try (rewrite map_unshift_cty; reflexivity);
        [ cbn; unfold subst_var_in_cty; rewrite map_ren_cty; reflexivity
        | cbn; rewrite map_term_as_cidx; destruct (term_as_cidx scrut); [cbn; rewrite map_subst_sum_cty; reflexivity | rewrite map_unshift_cty; reflexivity]
        | cbn; rewrite map_term_as_cidx; destruct (term_as_cidx scrut); [cbn; rewrite map_subst_sum_cty; reflexivity | rewrite map_unshift_cty; reflexivity] ]
      | rewrite !map_vec_add, !map_vec_scale, map_tl;
        eapply CoreMatchSum;
          [ intro Hsz; apply Hnz, Hzero_ref; exact Hsz
          | exact IHCoreDerives1
          | apply (map_ctype_demand A B m Hidem); exact Hdm_l
          | apply (map_ctype_demand A B m Hidem); exact Hdm_r
          | apply (map_ctype_demand A B m Hidem) in Hdm_mot;
            unfold map_cenv in Hdm_mot; cbn [map] in Hdm_mot;
            unfold map_cbinding in Hdm_mot; cbn [cbinder cannotation ctype_uses] in Hdm_mot;
            rewrite map_vec_add in Hdm_mot; exact Hdm_mot
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | exact IHCoreDerives2
          | exact IHCoreDerives3
          | rewrite <- Hspec_l; apply map_cty_alpha_eq; assumption
          | rewrite <- Hspec_r; apply map_cty_alpha_eq; assumption
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | rewrite <- !map_tl; apply map_branch_vec; [exact Hidem | assumption]
          | destruct scrut; cbn in *; try (rewrite map_cty_uses_var; assumption); try exact I;
            rewrite map_term_as_cidx; destruct (term_as_cidx scrut); cbn;
            [ destruct A0; cbn in *; try exact I; rewrite map_cty_uses_var; assumption
            | destruct A0; cbn in *; rewrite map_cty_uses_var; assumption
            | destruct B0; cbn in *; try exact I; rewrite map_cty_uses_var; assumption
            | destruct B0; cbn in *; rewrite map_cty_uses_var; assumption ]
          | subst res_ty; exact Hspec_s ] ]
    end.
  - rewrite map_vec_add. eapply CoreIf;
      [ exact IHCoreDerives1
      | exact IHCoreDerives2
      | exact IHCoreDerives3
      | apply map_cty_alpha_eq; assumption
      | apply map_branch_vec; [exact Hidem | assumption]
      | apply map_branch_vec; [exact Hidem | assumption] ].
  - cbn [map_cty].
    replace (map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft))
                 (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields))
       with (map (fun '(fn, fg, ft, _) => (fn, fg, ft))
                 (map (fun '(fn, fg, ft, fv) => (fn, translate m fg, map_cty m ft, map_cterm m fv)) fields))
      by (rewrite !map_map; apply map_ext; intros [[[fn fg] ft] fv]; reflexivity).
    apply CoreRecordMk; exact IHCoreDerives.
  - lazymatch goal with
    | Hnz : _ <> zero,
      Hext : CRecordExtendEnv env bs fields _ |- _ =>
      rewrite !map_vec_add, map_vec_scale, map_skipn, <- (length_map (fun '(fn, fg, ft) => (fn, translate m fg, map_cty m ft)) fields);
      eapply CoreMatchRecord;
        [ intro Hsz; apply Hnz, Hzero_ref; exact Hsz
        | exact IHCoreDerives1
        | apply (map_ctype_demand A B m Hidem); eassumption
        | rewrite length_map; assumption
        | apply (map_crecord_extend _ _ _ Hidem); exact Hext
        | exact IHCoreDerives2
        | rewrite length_map, map_lift_cty; apply map_cty_alpha_eq; assumption
        | rewrite length_map, <- map_firstn; apply map_crecord_field_allows; assumption ]
    end.
  - eapply CoreSubgrade; [exact IHCoreDerives | apply map_subty; eassumption | apply (map_ctype_demand A B m Hidem); eassumption].
  - lazymatch goal with
    | Hdm_mot : CTypeDemand (_ :: env) mot _,
      Hfix : fix_recurrence_ok _ _ |- _ =>
      assert (Hspec_st : map_cty m (spec_fix_step_cty mot) = spec_fix_step_cty (map_cty m mot)) by
        (unfold spec_fix_step_cty;
         change (@CIdxAdd B (@CIdxVar B 1) (@CIdxLit B 1)) with (map_cidx m (@CIdxAdd A (@CIdxVar A 1) (@CIdxLit A 1)));
         rewrite map_ren_cty, map_subst_cidx_in_cty; reflexivity);
      assert (Hspec_s : map_cty m (spec_fix_subj_cty scrut mot) = spec_fix_subj_cty (map_cterm m scrut) (map_cty m mot));
      [ unfold spec_fix_subj_cty; rewrite map_term_as_cidx;
        destruct (term_as_cidx scrut); cbn; [rewrite map_subst_cidx_in_cty; reflexivity | rewrite map_unshift_cty; reflexivity]
      | rewrite !map_vec_add, !map_vec_scale, !map_tl, map_nth_grade;
        eapply CoreFix;
          [ exact IHCoreDerives1
          | apply (map_ctype_demand A B m Hidem) in Hdm_mot;
            unfold map_cenv in Hdm_mot; cbn [map] in Hdm_mot;
            unfold map_cbinding in Hdm_mot; cbn [cbinder cannotation ctype_uses] in Hdm_mot;
            rewrite ?map_vec_zero in Hdm_mot; try rewrite <- (map_cenv_length A B m env) in Hdm_mot; exact Hdm_mot
          | exact IHCoreDerives2
          | change (@CIdxLit B 0) with (map_cidx m (@CIdxLit A 0));
            rewrite map_subst_cidx_in_cty;
            apply map_cty_alpha_eq; assumption
          | unfold map_cenv in IHCoreDerives3; cbn [map] in IHCoreDerives3;
            unfold map_cbinding in IHCoreDerives3; cbn [cbinder cannotation ctype_uses] in IHCoreDerives3;
            rewrite ?map_vec_zero in IHCoreDerives3; try rewrite <- (map_cenv_length A B m env) in IHCoreDerives3; exact IHCoreDerives3
          | rewrite <- Hspec_st; apply map_cty_alpha_eq; assumption
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | rewrite <- map_nth_grade; apply translate_allows; assumption
          | unfold fix_recurrence_ok in Hfix |- *; rewrite <- !map_tl;
            destruct (vec_is_zero (map (translate m) (tl (tl u_st)))) eqn:Em; [exact I |];
            destruct (vec_is_zero (tl (tl u_st))) eqn:Ez;
            [ apply vec_is_zero_iff in Ez; rewrite Ez, map_vec_zero in Em;
              exfalso; pose proof (proj2 (vec_is_zero_iff B (@vec_zero B (length (tl (tl u_st))))) ltac:(unfold vec_zero; f_equal; symmetry; apply repeat_length)) as Hzz; congruence
            | destruct Hfix as [Hf1 [Hf2 Hf3]]; split; [| split];
              [ rewrite <- (translate_one A B m); apply translate_allows; exact Hf1
              | rewrite <- (translate_add A B m); apply translate_allows; exact Hf2
              | rewrite <- (translate_mul A B m); apply translate_allows; exact Hf3 ] ]
          | rewrite map_term_as_cidx; destruct (term_as_cidx scrut); cbn; [exact I | rewrite map_cty_uses_var; assumption]
          | subst res_ty; exact Hspec_s ] ]
    end.
  - rewrite !map_vec_zero, <- (map_cenv_length A B m env). apply CRecordElemNil.
  - rewrite !map_vec_add, map_vec_scale.
    eapply CRecordElemCons;
      [ exact IHCoreDerives
      | apply map_cty_alpha_eq; assumption
      | apply (map_ctype_demand A B m Hidem); eassumption
      | exact IHCoreDerives0 ].
Qed.

(* ================================================================= *)
(* Part A3: Zero-Type-Use Irrelevance                                *)
(* ================================================================= *)

Fixpoint cidx_nonzero_uses_var {D : JoinDomain} (k : nat) (i : cidx D) : bool :=
  match i with
  | CIdxVar x => Nat.eqb x k
  | CIdxLit _ => false
  | CIdxAdd l r => cidx_nonzero_uses_var k l || cidx_nonzero_uses_var k r
  | CIdxProm q i' => if grade_eqb q zero then false else cidx_nonzero_uses_var k i'
  | CIdxUnbox b => Nat.eqb b k
  | CIdxFst p => Nat.eqb p k
  | CIdxSnd p => Nat.eqb p k
  | CIdxCase s l r =>
      Nat.eqb s k || cidx_nonzero_uses_var (S k) l || cidx_nonzero_uses_var (S k) r
  end.

Fixpoint cty_nonzero_uses_var {D : JoinDomain} (k : nat) (T : cty D) : bool :=
  match T with
  | CNat | CBool | CUniv _ => false
  | CVec elem len => cty_nonzero_uses_var k elem || cidx_nonzero_uses_var k len
  | CTVar x => Nat.eqb x k
  | CTProm q inner => if grade_eqb q zero then false else cty_nonzero_uses_var k inner
  | CTUnbox b => Nat.eqb b k
  | CPi _ _ _ dom cod => cty_nonzero_uses_var k dom || cty_nonzero_uses_var (S k) cod
  | CSigma _ _ f s => cty_nonzero_uses_var k f || cty_nonzero_uses_var (S k) s
  | CBox _ inner => cty_nonzero_uses_var k inner
  | CSum l r => cty_nonzero_uses_var k l || cty_nonzero_uses_var k r
  | CRecord _ fields => existsb (fun '(_, _, ft) => cty_nonzero_uses_var k ft) fields
  | CInd _ indices => existsb (cidx_nonzero_uses_var k) indices
  end.

Fixpoint no_zero_prom_cidx {D : JoinDomain} (i : cidx D) : Prop :=
  match i with
  | CIdxVar _ | CIdxLit _ | CIdxUnbox _ | CIdxFst _ | CIdxSnd _ => True
  | CIdxAdd l r => no_zero_prom_cidx l /\ no_zero_prom_cidx r
  | CIdxProm q i' => q <> zero /\ no_zero_prom_cidx i'
  | CIdxCase _ l r => no_zero_prom_cidx l /\ no_zero_prom_cidx r
  end.

Fixpoint no_zero_prom_cty {D : JoinDomain} (T : cty D) : Prop :=
  match T with
  | CNat | CBool | CUniv _ | CTVar _ | CTUnbox _ => True
  | CVec elem len => no_zero_prom_cty elem /\ no_zero_prom_cidx len
  | CTProm q inner => q <> zero /\ no_zero_prom_cty inner
  | CPi _ _ _ dom cod | CSigma _ _ dom cod => no_zero_prom_cty dom /\ no_zero_prom_cty cod
  | CBox _ inner => no_zero_prom_cty inner
  | CSum l r => no_zero_prom_cty l /\ no_zero_prom_cty r
  | CRecord _ fields =>
      (fix fields_nz (fs : list (nat * grade D * cty D)) : Prop :=
         match fs with
         | [] => True
         | (_, _, ft) :: rest => no_zero_prom_cty ft /\ fields_nz rest
         end) fields
  | CInd _ indices => Forall no_zero_prom_cidx indices
  end.

Lemma cidx_nonzero_uses_var_no_zero : forall (D : JoinDomain) k (i : cidx D),
  no_zero_prom_cidx i ->
  cidx_nonzero_uses_var k i = cidx_uses_var k i.
Proof.
  intros D k i. revert k. induction i; intros k Hnz; cbn in *; try reflexivity.
  - destruct Hnz as [H1 H2]. rewrite (IHi1 k H1), (IHi2 k H2). reflexivity.
  - destruct Hnz as [Hq Hi]. destruct (grade_eqb_spec D q zero); [contradiction | apply IHi; exact Hi].
  - destruct Hnz as [H1 H2]. rewrite (IHi1 (S k) H1), (IHi2 (S k) H2). reflexivity.
Qed.

Lemma cty_nonzero_uses_var_no_zero : forall (D : JoinDomain) k (T : cty D),
  no_zero_prom_cty T ->
  cty_nonzero_uses_var k T = cty_uses_var k T.
Proof.
  intros D k T. revert k. induction T using cty_ind_nested; intros k Hnz; cbn in *; try reflexivity;
    try (apply IHT; exact Hnz);
    try (destruct Hnz as [H1 H2]; rewrite (IHT1 k H1), (IHT2 k H2); reflexivity);
    try (destruct Hnz as [H1 H2]; rewrite (IHT1 k H1), (IHT2 (S k) H2); reflexivity).
  - destruct Hnz as [H1 H2]. rewrite (IHT k H1), (cidx_nonzero_uses_var_no_zero D k len H2). reflexivity.
  - destruct Hnz as [Hq Hi]. destruct (grade_eqb_spec D q zero); [contradiction | apply IHT; exact Hi].
  - induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
    inversion H; subst. cbn in H2. destruct Hnz as [H4 H5]. rewrite (H2 k H4), (IH H3 H5). reflexivity.
  - induction indices as [| idx rest IH]; cbn; [reflexivity |].
    inversion Hnz; subst. rewrite (cidx_nonzero_uses_var_no_zero D k idx H1), (IH H2). reflexivity.
Qed.

Lemma nth_grade_vec_single_eq : forall (D : JoinDomain) n x (q : grade D),
  x < n -> nth_grade (vec_single n x q) x = q.
Proof.
  intros D n. induction n as [| n IH]; intros [| x] q Hlt; cbn; try lia; [reflexivity |].
  apply IH; lia.
Qed.

Lemma nth_grade_vec_add : forall (D : JoinDomain) (u v : list (grade D)) k,
  length u = length v ->
  nth_grade (vec_add u v) k = add (nth_grade u k) (nth_grade v k).
Proof.
  intros D u. induction u as [| a u IH]; intros [| b v] [| k] Hlen; unfold nth_grade, nth_default in *; cbn in *; try lia;
    try (rewrite add_zero; reflexivity); try reflexivity.
  apply IH; lia.
Qed.

Lemma nth_grade_vec_scale : forall (D : JoinDomain) (q : grade D) (u : list (grade D)) k,
  nth_grade (vec_scale q u) k = mul q (nth_grade u k).
Proof.
  intros D q u. induction u as [| a u IH]; intros [| k]; unfold nth_grade, nth_default in *; cbn in *;
    try (rewrite mul_zero_r; reflexivity); try reflexivity.
  apply IH.
Qed.

Lemma BranchVec_nth_zero : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (u1 u2 u : list (grade D)) k,
    length u1 = length u2 ->
    BranchVec u1 u2 u ->
    nth_grade u k = zero ->
    nth_grade u1 k = zero /\ nth_grade u2 k = zero.
Proof.
  intros D ED u1 u2 u k Hlen Hbr Hz. unfold BranchVec in Hbr.
  destruct (grade_join D) as [j |] eqn:Hj.
  - subst u.
    pose proof (vec_allows_join_left D j u1 u2 Hj Hlen) as Hl.
    pose proof (vec_allows_join_right D j u1 u2 Hj Hlen) as Hr.
    split; apply (erasure_allows_zero_eq D ED); rewrite <- Hz;
      [eapply vec_allows_nth; exact Hl | eapply vec_allows_nth; exact Hr].
  - destruct Hbr as [-> ->]. split; exact Hz.
Qed.

Lemma core_zero_idx_use : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (env : cenv D) (i : cidx D) (d : list (grade D)) k,
    CIdxDemand env i d ->
    k < length env ->
    nth_grade d k = zero ->
    cidx_nonzero_uses_var k i = false.
Proof.
  intros D ED env i d k H. revert k.
  induction H; intros k Hlt Hz; cbn in *; try reflexivity.
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    exfalso. rewrite nth_grade_vec_single_eq in Hz by exact Hlt.
    apply (erasure_one_nonzero D ED). rewrite Hz. apply allows_refl.
  - rewrite nth_grade_vec_add in Hz by (erewrite !cidx_demand_length by eassumption; reflexivity).
    apply (erasure_add_zero D ED) in Hz as [Hz1 Hz2].
    rewrite (IHCIdxDemand1 k Hlt Hz1), (IHCIdxDemand2 k Hlt Hz2). reflexivity.
  - destruct (grade_eqb_spec D q zero) as [-> | Hnz]; [reflexivity |].
    rewrite nth_grade_vec_scale in Hz.
    apply (erasure_mul_zero D ED) in Hz as [Hq | Hd]; [contradiction |].
    apply IHCIdxDemand; [exact Hlt | exact Hd].
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    exfalso. rewrite nth_grade_vec_single_eq in Hz by exact Hlt.
    apply (erasure_one_nonzero D ED). rewrite Hz. apply allows_refl.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    exfalso. rewrite nth_grade_vec_single_eq in Hz by exact Hlt.
    apply (erasure_one_nonzero D ED). rewrite Hz. apply allows_refl.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    exfalso. rewrite nth_grade_vec_single_eq in Hz by exact Hlt.
    apply (erasure_one_nonzero D ED). rewrite Hz. apply allows_refl.
  - pose proof (cidx_demand_length D _ _ _ H1) as Hlen1.
    pose proof (cidx_demand_length D _ _ _ H2) as Hlen2.
    cbn [length] in Hlen1, Hlen2.
    pose proof (BranchVec_length D (tl dl) (tl dr) d_br ltac:(rewrite !length_tl, Hlen1, Hlen2; reflexivity) H3) as Hlen_br.
    rewrite nth_grade_vec_add in Hz by (rewrite vec_single_length, Hlen_br, length_tl, Hlen1; lia).
    apply (erasure_add_zero D ED) in Hz as [Hzs Hzb].
    destruct (BranchVec_nth_zero D ED (tl dl) (tl dr) d_br k ltac:(rewrite !length_tl, Hlen1, Hlen2; reflexivity) H3 Hzb) as [Hzl Hzr].
    destruct (Nat.eq_dec s k) as [-> | Hne].
    + exfalso. rewrite nth_grade_vec_single_eq in Hzs by exact Hlt.
      apply (erasure_one_nonzero D ED). rewrite Hzs. apply allows_refl.
    + apply Nat.eqb_neq in Hne. rewrite Hne.
      assert (Htl1 : nth_grade dl (S k) = zero) by (destruct dl; cbn in *; [reflexivity | exact Hzl]).
      assert (Htl2 : nth_grade dr (S k) = zero) by (destruct dr; cbn in *; [reflexivity | exact Hzr]).
      rewrite (IHCIdxDemand1 (S k) ltac:(cbn; lia) Htl1), (IHCIdxDemand2 (S k) ltac:(cbn; lia) Htl2).
      reflexivity.
Qed.

Lemma crecord_field_demand_length : forall (D : JoinDomain) (env : cenv D) fs df,
  CRecordFieldDemand env fs df -> length df = length env.
Proof.
  intros D env fs df H. induction H; [apply vec_zero_length | rewrite vec_add_length; [eapply ctype_demand_length; eassumption |]].
  erewrite ctype_demand_length by eassumption. symmetry; exact IHCRecordFieldDemand.
Qed.

Lemma core_zero_type_use : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (env : cenv D) (T : cty D) (d : list (grade D)) k,
    CTypeDemand env T d ->
    k < length env ->
    nth_grade d k = zero ->
    cty_nonzero_uses_var k T = false.
Proof.
  intros D ED env T d k H. revert k.
  induction H using CTypeDemand_ind_mut with
    (P := fun env T d _ => forall k, k < length env -> nth_grade d k = zero -> cty_nonzero_uses_var k T = false)
    (P0 := fun env fs df _ => forall k, k < length env -> nth_grade df k = zero ->
      existsb (fun '(_, _, ft) => cty_nonzero_uses_var k ft) fs = false)
    (P1 := fun env ls dl _ => forall k, k < length env -> nth_grade dl k = zero ->
      existsb (cidx_nonzero_uses_var k) ls = false);
    intros k Hlt Hz; cbn in *; try reflexivity.
  - rewrite nth_grade_vec_add in Hz by (erewrite ctype_demand_length, cidx_demand_length by eassumption; reflexivity).
    apply (erasure_add_zero D ED) in Hz as [Hze Hzd].
    lazymatch goal with
    | Hlen : CIdxDemand env len _ |- _ =>
      rewrite (IHCTypeDemand k Hlt Hze), (core_zero_idx_use D ED _ _ _ k Hlen Hlt Hzd); reflexivity
    end.
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    exfalso. rewrite nth_grade_vec_single_eq in Hz by exact Hlt.
    apply (erasure_one_nonzero D ED). rewrite Hz. apply allows_refl.
  - destruct (grade_eqb_spec D q zero) as [-> | Hnz]; [reflexivity |].
    rewrite nth_grade_vec_scale in Hz.
    apply (erasure_mul_zero D ED) in Hz as [Hq | Hd]; [contradiction |].
    apply IHCTypeDemand; [exact Hlt | exact Hd].
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [| apply Nat.eqb_neq; exact Hne].
    exfalso. rewrite nth_grade_vec_single_eq in Hz by exact Hlt.
    apply (erasure_one_nonzero D ED). rewrite Hz. apply allows_refl.
  - pose proof (ctype_demand_length D _ _ _ H) as Hlena.
    pose proof (ctype_demand_length D _ _ _ H0) as Hlenb. cbn [length] in Hlenb.
    rewrite nth_grade_vec_add in Hz by (rewrite length_tl, Hlena, Hlenb; lia).
    apply (erasure_add_zero D ED) in Hz as [Hza Hzb].
    assert (Htl : nth_grade b (S k) = zero) by (destruct b; cbn in *; [reflexivity | exact Hzb]).
    rewrite (IHCTypeDemand1 k Hlt Hza), (IHCTypeDemand2 (S k) ltac:(cbn; lia) Htl). reflexivity.
  - pose proof (ctype_demand_length D _ _ _ H) as Hlena.
    pose proof (ctype_demand_length D _ _ _ H0) as Hlenb. cbn [length] in Hlenb.
    rewrite nth_grade_vec_add in Hz by (rewrite length_tl, Hlena, Hlenb; lia).
    apply (erasure_add_zero D ED) in Hz as [Hza Hzb].
    assert (Htl : nth_grade b (S k) = zero) by (destruct b; cbn in *; [reflexivity | exact Hzb]).
    rewrite (IHCTypeDemand1 k Hlt Hza), (IHCTypeDemand2 (S k) ltac:(cbn; lia) Htl). reflexivity.
  - apply IHCTypeDemand; [exact Hlt | exact Hz].
  - rewrite nth_grade_vec_add in Hz by (erewrite !ctype_demand_length by eassumption; reflexivity).
    apply (erasure_add_zero D ED) in Hz as [Hzl Hzr].
    rewrite (IHCTypeDemand1 k Hlt Hzl), (IHCTypeDemand2 k Hlt Hzr). reflexivity.
  - apply IHCTypeDemand; [exact Hlt | exact Hz].
  - apply IHCTypeDemand; [exact Hlt | exact Hz].
  - rewrite nth_grade_vec_add in Hz by (erewrite ctype_demand_length, crecord_field_demand_length by eassumption; reflexivity).
    apply (erasure_add_zero D ED) in Hz as [Hzt Hzr].
    lazymatch goal with
    | Hft : forall _, _ -> _ -> cty_nonzero_uses_var _ _ = false,
      Hfs : forall _, _ -> _ -> existsb _ _ = false |- _ =>
      rewrite (Hft k Hlt Hzt), (Hfs k Hlt Hzr); reflexivity
    end.
  - rewrite nth_grade_vec_add in Hz by (erewrite cidx_demand_length, cidx_list_demand_length by eassumption; reflexivity).
    apply (erasure_add_zero D ED) in Hz as [Hzi Hzr].
    lazymatch goal with
    | Hci : CIdxDemand env _ _,
      Hls : forall _, _ -> _ -> existsb _ _ = false |- _ =>
      rewrite (core_zero_idx_use D ED _ _ _ k Hci Hlt Hzi), (Hls k Hlt Hzr); reflexivity
    end.
Qed.

Theorem core_zero_type_use_irrelevance : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (env : cenv D) (T : cty D) (d : list (grade D)) k,
    CTypeDemand env T d ->
    k < length env ->
    allows (nth_grade d k) zero ->
    no_zero_prom_cty T ->
    cty_uses_var k T = false /\
    (forall val1 val2, subst_cidx_in_cty k val1 T = subst_cidx_in_cty k val2 T) /\
    (forall U1 U2, subst_tvar_in_cty k U1 T = subst_tvar_in_cty k U2 T).
Proof.
  intros D ED env T d k HT Hlt Hall Hnz.
  apply (erasure_allows_zero_eq D ED) in Hall.
  pose proof (core_zero_type_use D ED env T d k HT Hlt Hall) as Hnu.
  rewrite (cty_nonzero_uses_var_no_zero D k T Hnz) in Hnu.
  split; [exact Hnu |].
  assert (Hci_eq : forall (i : cidx D) k0 v1 v2,
    cidx_uses_var k0 i = false -> subst_cidx k0 v1 i = subst_cidx k0 v2 i).
  { induction i; intros k0 v1 v2 Hi; cbn in *; try reflexivity;
      try (apply orb_false_iff in Hi as [H1 H2]; rewrite (IHi1 k0 v1 v2 H1), (IHi2 k0 v1 v2 H2); reflexivity);
      try (f_equal; apply IHi; exact Hi).
    - rewrite Hi. reflexivity.
    - apply orb_false_iff in Hi as [H12 H3]. apply orb_false_iff in H12 as [H1 H2].
      rewrite (IHi1 (S k0) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H2),
              (IHi2 (S k0) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H3). reflexivity. }
  assert (Hcty_cidx : forall (U : cty D) k0 v1 v2,
    cty_uses_var k0 U = false -> subst_cidx_in_cty k0 v1 U = subst_cidx_in_cty k0 v2 U).
  { induction U using cty_ind_nested; intros k0 v1 v2 HU; cbn in *; try reflexivity;
      try (f_equal; apply IHU; exact HU);
      try (apply orb_false_iff in HU as [H1 H2]; rewrite (IHU1 k0 v1 v2 H1), (IHU2 k0 v1 v2 H2); reflexivity);
      try (apply orb_false_iff in HU as [H1 H2]; rewrite (IHU1 k0 v1 v2 H1), (IHU2 (S k0) (lift_cidx 0 1 v1) (lift_cidx 0 1 v2) H2); reflexivity).
    - apply orb_false_iff in HU as [H1 H2]. rewrite (IHU k0 v1 v2 H1), (Hci_eq len k0 v1 v2 H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H; subst. cbn in H2. apply orb_false_iff in HU as [Hu1 Hu2].
      rewrite (H2 k0 v1 v2 Hu1), (IH H3 Hu2). reflexivity.
    - f_equal. induction indices as [| idx rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HU as [Hu1 Hu2]. rewrite (Hci_eq idx k0 v1 v2 Hu1), (IH Hu2). reflexivity. }
  assert (Hcty_tvar : forall (U : cty D) k0 V1 V2,
    cty_uses_var k0 U = false -> subst_tvar_in_cty k0 V1 U = subst_tvar_in_cty k0 V2 U).
  { induction U using cty_ind_nested; intros k0 V1 V2 HU; cbn in *; try reflexivity;
      try (f_equal; apply IHU; exact HU);
      try (apply orb_false_iff in HU as [H1 H2]; rewrite (IHU1 k0 V1 V2 H1), (IHU2 k0 V1 V2 H2); reflexivity);
      try (apply orb_false_iff in HU as [H1 H2]; rewrite (IHU1 k0 V1 V2 H1), (IHU2 (S k0) (lift_cty 0 1 V1) (lift_cty 0 1 V2) H2); reflexivity).
    - apply orb_false_iff in HU as [H1 H2]. rewrite (IHU k0 V1 V2 H1). reflexivity.
    - rewrite HU; reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H; subst. cbn in H2. apply orb_false_iff in HU as [Hu1 Hu2].
      rewrite (H2 k0 V1 V2 Hu1), (IH H3 Hu2). reflexivity. }
  split; [intros v1 v2; apply Hcty_cidx; exact Hnu | intros V1 V2; apply Hcty_tvar; exact Hnu].
Qed.

End GradedCoreMetatheory.
