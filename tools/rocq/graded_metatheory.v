(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Require Import graded_pure graded_domains.
Import ListNotations.

Module GradedMetatheory.
Import GradedPure.

(* ================================================================= *)
(* Part 1: Structural & Substitution Metatheory over GradedPure      *)
(* ================================================================= *)

Theorem derives_allows_mono :
  forall (allows1 allows2 : nat -> nat -> Prop),
    (forall a b, allows1 a b -> allows2 a b) ->
    forall env t res,
      DerivesWith allows1 env t res ->
      DerivesWith allows2 env t res.
Proof.
  intros allows1 allows2 mono env t res deriv.
  induction deriv; econstructor; eauto.
Qed.

Corollary exact_to_bounded_derives : forall env t res,
  Derives env t res ->
  DerivesWith (@GradedDomains.allows GradedDomains.NatBound) env t res.
Proof.
  intros env t res deriv.
  eapply derives_allows_mono; [| exact deriv].
  intros a b ->. apply Nat.le_refl.
Qed.

(* Context equivalence: judgments depend on env only through lookup *)

Lemma context_equiv_fresh : forall env1 env2 x,
  (forall y, lookup env1 y = lookup env2 y) ->
  fresh env1 x = fresh env2 x.
Proof.
  intros env1 env2 x eq_lkp. unfold fresh. now rewrite eq_lkp.
Qed.

Lemma context_equiv_index : forall env1 env2 i d,
  (forall y, lookup env1 y = lookup env2 y) ->
  IndexDemand env1 i d ->
  IndexDemand env2 i d.
Proof.
  intros env1 env2 i d eq_lkp H.
  induction H; econstructor; eauto.
  now rewrite <- eq_lkp.
Qed.

Lemma context_equiv_cons : forall env1 env2 e,
  (forall y, lookup env1 y = lookup env2 y) ->
  forall y, lookup (e :: env1) y = lookup (e :: env2) y.
Proof.
  intros env1 env2 e eq_lkp y. cbn.
  destruct (Nat.eqb y (binder e)); [reflexivity | apply eq_lkp].
Qed.

Lemma context_equiv_type : forall env1 env2 kind d,
  (forall y, lookup env1 y = lookup env2 y) ->
  TypeDemand env1 kind d ->
  TypeDemand env2 kind d.
Proof.
  intros env1 env2 kind d eq_lkp H.
  revert env2 eq_lkp.
  induction H; intros env2 eq_lkp; econstructor; eauto using context_equiv_index, context_equiv_cons.
  - now rewrite <- (context_equiv_fresh _ _ _ eq_lkp).
  - now rewrite <- eq_lkp.
Qed.

Lemma context_equiv_universe : forall env1 env2 kind lvl,
  (forall y, lookup env1 y = lookup env2 y) ->
  UniverseLevel env1 kind lvl ->
  UniverseLevel env2 kind lvl.
Proof.
  intros env1 env2 kind lvl eq_lkp H.
  revert env2 eq_lkp.
  induction H; intros env2 eq_lkp; econstructor; eauto using context_equiv_cons.
  now rewrite <- eq_lkp.
Qed.

Theorem context_equiv_derives : forall allows env1 env2 t res,
  (forall y, lookup env1 y = lookup env2 y) ->
  DerivesWith allows env1 t res ->
  DerivesWith allows env2 t res.
Proof.
  intros allows env1 env2 t res eq_lkp H.
  revert env2 eq_lkp.
  induction H; intros env2 eq_lkp;
    econstructor;
    eauto using context_equiv_index, context_equiv_type, context_equiv_universe, context_equiv_cons.
  - now rewrite <- eq_lkp.
  - now rewrite <- (context_equiv_fresh _ _ _ eq_lkp).
  - now rewrite <- (context_equiv_fresh _ _ _ eq_lkp).
  - now rewrite <- (context_equiv_fresh _ _ _ eq_lkp).
  - now rewrite <- (context_equiv_fresh _ _ _ eq_lkp).
  - now rewrite <- (context_equiv_fresh _ _ _ eq_lkp).
Qed.

Lemma lookup_exchange : forall prefix b1 b2 suffix y,
  binder b1 <> binder b2 ->
  lookup (prefix ++ b1 :: b2 :: suffix) y =
  lookup (prefix ++ b2 :: b1 :: suffix) y.
Proof.
  intros prefix b1 b2 suffix y neq.
  induction prefix as [| p rest IH]; cbn.
  - destruct (Nat.eqb y (binder b1)) eqn:e1; destruct (Nat.eqb y (binder b2)) eqn:e2; try reflexivity.
    apply Nat.eqb_eq in e1. apply Nat.eqb_eq in e2. congruence.
  - destruct (Nat.eqb y (binder p)); [reflexivity | exact IH].
Qed.

Theorem exchange_derives : forall allows prefix b1 b2 suffix t res,
  binder b1 <> binder b2 ->
  DerivesWith allows (prefix ++ b1 :: b2 :: suffix) t res ->
  DerivesWith allows (prefix ++ b2 :: b1 :: suffix) t res.
Proof.
  intros allows prefix b1 b2 suffix t res neq deriv.
  eapply context_equiv_derives; [| exact deriv].
  intro y. now apply lookup_exchange.
Qed.

(* Weakening *)

Fixpoint ty_binders (k : ty) : list nat :=
  match k with
  | Pi x _ dom cod => x :: ty_binders dom ++ ty_binders cod
  | _ => []
  end.

Fixpoint term_binders (t : term) : list nat :=
  match t with
  | Var _ | NatValue _ => []
  | Lambda x _ dom body => x :: ty_binders dom ++ term_binders body
  | ApplyNat c _ => term_binders c
  | ApplyValue c a => term_binders c ++ term_binders a
  | LetNat x _ _ body => x :: term_binders body
  | ApplyType c a => term_binders c ++ ty_binders a
  end.

Definition context_ty_binders (env : context) : list nat :=
  flat_map (fun e => ty_binders (annotation e)) env.

Lemma lookup_app_head : forall prefix suffix y,
  lookup (prefix ++ suffix) y =
  match lookup prefix y with
  | Some e => Some e
  | None => lookup suffix y
  end.
Proof.
  induction prefix as [| p rest IH]; intros suffix y; cbn.
  - reflexivity.
  - destruct (Nat.eqb y (binder p)); [reflexivity | apply IH].
Qed.

Lemma lookup_insert_some : forall prefix b suffix y e,
  fresh (prefix ++ suffix) (binder b) = true ->
  lookup (prefix ++ suffix) y = Some e ->
  lookup (prefix ++ b :: suffix) y = Some e.
Proof.
  intros prefix b suffix y e Hfresh Hlkp.
  rewrite !lookup_app_head in *.
  destruct (lookup prefix y) as [ep |] eqn:Hp; [exact Hlkp |].
  cbn. destruct (Nat.eqb y (binder b)) eqn:Eyb.
  - apply Nat.eqb_eq in Eyb. subst y.
    unfold fresh in Hfresh. rewrite lookup_app_head in Hfresh.
    destruct (lookup prefix (binder b)); [discriminate |].
    now rewrite Hlkp in Hfresh.
  - exact Hlkp.
Qed.

Lemma fresh_insert : forall prefix b suffix y,
  y <> binder b ->
  fresh (prefix ++ suffix) y = true ->
  fresh (prefix ++ b :: suffix) y = true.
Proof.
  intros prefix b suffix y Hneq Hfresh.
  unfold fresh in *. rewrite !lookup_app_head in *.
  destruct (lookup prefix y); [discriminate |].
  cbn. destruct (Nat.eqb y (binder b)) eqn:Eyb.
  - apply Nat.eqb_eq in Eyb. congruence.
  - exact Hfresh.
Qed.

Lemma fresh_cons_inv : forall e env x,
  fresh (e :: env) x = true ->
  x <> binder e /\ fresh env x = true.
Proof.
  intros e env x H. unfold fresh in H. cbn in H.
  destruct (Nat.eqb x (binder e)) eqn:E.
  - discriminate.
  - apply Nat.eqb_neq in E. split; assumption.
Qed.

Lemma fresh_cons_intro : forall e env x,
  x <> binder e ->
  fresh env x = true ->
  fresh (e :: env) x = true.
Proof.
  intros e env x Hneq Hfresh. unfold fresh. cbn.
  apply Nat.eqb_neq in Hneq. rewrite Hneq. exact Hfresh.
Qed.

Theorem weakening_index : forall prefix b suffix i d,
  fresh (prefix ++ suffix) (binder b) = true ->
  IndexDemand (prefix ++ suffix) i d ->
  IndexDemand (prefix ++ b :: suffix) i d.
Proof.
  intros prefix b suffix i d Hfresh Hd.
  induction Hd; econstructor; eauto using lookup_insert_some.
Qed.

Theorem weakening_type : forall prefix b suffix kind d,
  fresh (prefix ++ suffix) (binder b) = true ->
  ~ In (binder b) (ty_binders kind) ->
  TypeDemand (prefix ++ suffix) kind d ->
  TypeDemand (prefix ++ b :: suffix) kind d.
Proof.
  intros prefix b suffix kind d Hfresh Hnot Hd.
  remember (prefix ++ suffix) as env eqn:Eenv.
  revert prefix Hfresh Hnot Eenv.
  induction Hd; intros prefix Hfresh Hnot Eenv; subst; cbn in Hnot; econstructor;
    eauto using weakening_index, lookup_insert_some.
  - apply fresh_insert; [| exact H].
    intro Heq. apply Hnot. now left.
  - apply IHHd1; [exact Hfresh | | reflexivity].
    intro Hin. apply Hnot. right. apply in_or_app. now left.
  - change (TypeDemand (({| binder := x; annotation := domain; type_uses := a |} :: prefix) ++ b :: suffix) codomain b0).
    apply IHHd2; [| | reflexivity].
    + apply fresh_cons_intro; [| exact Hfresh].
      intro Heq. apply Hnot. now left.
    + intro Hin. apply Hnot. right. apply in_or_app. now right.
Qed.

Theorem weakening_universe : forall prefix b suffix kind lvl,
  fresh (prefix ++ suffix) (binder b) = true ->
  UniverseLevel (prefix ++ suffix) kind lvl ->
  UniverseLevel (prefix ++ b :: suffix) kind lvl.
Proof.
  intros prefix b suffix kind lvl Hfresh Hl.
  remember (prefix ++ suffix) as env eqn:Eenv.
  revert prefix Hfresh Eenv.
  induction Hl; intros prefix Hfresh Eenv; subst; econstructor; eauto using lookup_insert_some.
  change (UniverseLevel (({| binder := x; annotation := domain; type_uses := [] |} :: prefix) ++ b :: suffix) codomain j).
  destruct (Nat.eq_dec x (binder b)) as [Heq | Hneq].
  - eapply context_equiv_universe; [| exact Hl2].
    intro y. cbn [app].
    destruct (Nat.eqb y x) eqn:Eyx.
    + unfold lookup. cbn. rewrite Eyx. reflexivity.
    + unfold lookup; cbn. rewrite Eyx.
      fold (lookup (prefix ++ suffix) y). fold (lookup (prefix ++ b :: suffix) y).
      rewrite !lookup_app_head.
      destruct (lookup prefix y) as [ep |] eqn:Hp; [reflexivity |].
      unfold lookup at 2; cbn. fold (lookup suffix y).
      rewrite Heq in Eyx. rewrite Eyx. reflexivity.
  - apply IHHl2; [apply fresh_cons_intro; [cbn; congruence | exact Hfresh] | reflexivity].
Qed.

Lemma type_demand_ty_binders_fresh : forall env kind d y,
  TypeDemand env kind d ->
  In y (ty_binders kind) ->
  fresh env y = true.
Proof.
  intros env kind d y Hd.
  induction Hd; cbn; intro Hin; try contradiction.
  destruct Hin as [<- | Hin].
  - exact H.
  - apply in_app_or in Hin as [Hdom | Hcod]; [auto |].
    apply IHHd2 in Hcod. apply fresh_cons_inv in Hcod. tauto.
Qed.

Lemma ty_binders_subst_type_incl : forall x arg kind y,
  In y (ty_binders (substitute_type x arg kind)) ->
  In y (ty_binders kind).
Proof.
  intros x arg kind.
  induction kind; intros y Hin; cbn in *; try exact Hin.
  destruct Hin as [<- | Hin]; [now left | right].
  apply in_app_or in Hin as [Hdom | Hcod]; apply in_or_app.
  - left. auto.
  - right. destruct (Nat.eqb x x0); auto.
Qed.

Lemma ty_binders_subst_type_var_incl : forall x arg kind y,
  In y (ty_binders (substitute_type_variable x arg kind)) ->
  In y (ty_binders kind) \/ In y (ty_binders arg).
Proof.
  intros x arg kind.
  induction kind as [| len | x0 allow dom IHkind1 cod IHkind2 | lvl | n];
    intros y Hin; cbn in *; try (left; exact Hin).
  - destruct Hin as [<- | Hin]; [left; now left |].
    apply in_app_or in Hin as [Hdom | Hcod].
    + destruct (IHkind1 y Hdom); [left; right; apply in_or_app; now left | now right].
    + destruct (Nat.eqb x x0).
      * left; right; apply in_or_app; now right.
      * destruct (IHkind2 y Hcod); [left; right; apply in_or_app; now right | now right].
  - destruct (Nat.eqb x n); [now right | cbn in Hin; contradiction].
Qed.

Lemma derives_result_ty_binders_fresh : forall allows env t res y,
  DerivesWith allows env t res ->
  In y (ty_binders (result_type res)) ->
  fresh env y = true.
Proof.
  intros allows env t res y deriv Hin.
  apply derives_type_demand in deriv as [row [Htd _]].
  eapply type_demand_ty_binders_fresh; eassumption.
Qed.

Lemma not_in_context_ty_binders_lookup : forall env b y entry,
  ~ In b (context_ty_binders env) ->
  lookup env y = Some entry ->
  ~ In b (ty_binders (annotation entry)).
Proof.
  induction env as [| e rest IH]; intros b y entry Hnot Hlkp.
  - discriminate.
  - cbn in Hnot, Hlkp.
    destruct (Nat.eqb y (binder e)).
    + inversion Hlkp; subst. intro Hin. apply Hnot. apply in_or_app. now left.
    + apply IH with (y := y); [| exact Hlkp].
      intro Hin. apply Hnot. apply in_or_app. now right.
Qed.

Lemma ty_binders_derives_sub : forall allows env t res x,
  DerivesWith allows env t res ->
  In x (ty_binders (result_type res)) ->
  In x (term_binders t) \/ In x (context_ty_binders env).
Proof.
  intros allows env t res x Hderiv.
  induction Hderiv; cbn; intro Hin.
  - right.
    assert (Hmem : In entry env).
    { clear -H. induction env as [| e rest IH]; [discriminate |].
      cbn in H. destruct (Nat.eqb x0 (binder e)); [inversion H; subst; now left | right; auto]. }
    unfold context_ty_binders. rewrite in_flat_map. exists entry. split; assumption.
  - contradiction.
  - destruct Hin as [<- | Hin]; [left; now left |].
    apply in_app_or in Hin as [Hdom | Hcod].
    + left. right. apply in_or_app. now left.
    + destruct (IHHderiv Hcod) as [Htb | Hcb].
      * left. right. apply in_or_app. now right.
      * cbn in Hcb. apply in_app_or in Hcb as [Hdom | Hctx].
        -- left. right. apply in_or_app. now left.
        -- right. exact Hctx.
  - apply ty_binders_subst_type_incl in Hin.
    assert (Hin_pi : In x (ty_binders (Pi x0 allowance Natural codomain))) by (cbn; right; exact Hin).
    exact (IHHderiv Hin_pi).
  - assert (Hin_pi : In x (ty_binders (Pi x0 allowance domain codomain))) by (cbn; right; apply in_or_app; now right).
    destruct (IHHderiv1 Hin_pi) as [Htb | Hcb]; [left; apply in_or_app; now left | right; exact Hcb].
  - apply ty_binders_subst_type_incl in Hin.
    destruct (IHHderiv Hin) as [Htb | Hcb].
    + left. now right.
    + cbn in Hcb. right. exact Hcb.
  - apply ty_binders_subst_type_var_incl in Hin as [Hcod | Harg].
    + assert (Hin_pi : In x (ty_binders (Pi x0 allowance (Universe level) codomain))) by (cbn; right; exact Hcod).
      destruct (IHHderiv Hin_pi) as [Htb | Hcb]; [left; apply in_or_app; now left | right; exact Hcb].
    + left. apply in_or_app. now right.
Qed.

Theorem weakening_derives : forall allows prefix b suffix t res,
  fresh (prefix ++ suffix) (binder b) = true ->
  ~ In (binder b) (term_binders t) ->
  ~ In (binder b) (context_ty_binders (prefix ++ suffix)) ->
  DerivesWith allows (prefix ++ suffix) t res ->
  DerivesWith allows (prefix ++ b :: suffix) t res.
Proof.
  intros allows prefix b suffix t res Hfresh Hterm Hctx Hderiv.
  remember (prefix ++ suffix) as env eqn:Eenv.
  revert prefix Hfresh Hterm Hctx Eenv.
  induction Hderiv; intros prefix Hfresh Hterm Hctx Eenv; subst.
  - eapply GradeVar; [eauto using lookup_insert_some | | exact H1].
    eapply weakening_type; eauto.
    eapply not_in_context_ty_binders_lookup; eassumption.
  - constructor. now apply weakening_index.
  - cbn in Hterm.
    assert (Hx_neq : x <> binder b) by (intro; apply Hterm; now left).
    assert (Hb_dom : ~ In (binder b) (ty_binders domain))
      by (intro Hin; apply Hterm; right; apply in_or_app; now left).
    assert (Hb_body : ~ In (binder b) (term_binders body))
      by (intro Hin; apply Hterm; right; apply in_or_app; now right).
    eapply GradeLambda; eauto using fresh_insert, weakening_type.
    change (DerivesWith allows (({| binder := x; annotation := domain; type_uses := a |} :: prefix) ++ b :: suffix) body
              {| result_type := codomain; computation_demand := u; type_demand_row := v |}).
    apply IHHderiv; [now apply fresh_cons_intro | exact Hb_body | | reflexivity].
    cbn. intro Hin. apply in_app_or in Hin as [H1' | H2']; contradiction.
  - cbn in Hterm.
    assert (Hx_neq : x <> binder b).
    { intro Heq.
      assert (Hin : In (binder b) (ty_binders (result_type {| result_type := Pi x allowance Natural codomain; computation_demand := w; type_demand_row := v |})))
        by (cbn; now left).
      eapply ty_binders_derives_sub in Hin; [| exact Hderiv].
      destruct Hin; contradiction. }
    assert (Hb_cod : ~ In (binder b) (ty_binders codomain)).
    { intro Hin.
      assert (Hin' : In (binder b) (ty_binders (result_type {| result_type := Pi x allowance Natural codomain; computation_demand := w; type_demand_row := v |})))
        by (cbn; right; exact Hin).
      eapply ty_binders_derives_sub in Hin'; [| exact Hderiv].
      destruct Hin'; contradiction. }
    assert (Hb_spec : ~ In (binder b) (ty_binders (substitute_type x argument codomain)))
      by (intro Hin; apply Hb_cod; eapply ty_binders_subst_type_incl; eassumption).
    eapply GradeApplyNat; eauto using fresh_insert, weakening_index, weakening_type.
    change (TypeDemand (({| binder := x; annotation := Natural; type_uses := [] |} :: prefix) ++ b :: suffix) codomain b0).
    apply weakening_type; [now apply fresh_cons_intro | exact Hb_cod | exact H1].
  - cbn in Hterm.
    assert (Hx_neq : x <> binder b).
    { intro Heq.
      assert (Hin : In (binder b) (ty_binders (result_type {| result_type := Pi x allowance domain codomain; computation_demand := w; type_demand_row := v |})))
        by (cbn; now left).
      eapply ty_binders_derives_sub in Hin; [| exact Hderiv1].
      destruct Hin as [Hc | Hc]; [apply Hterm; apply in_or_app; now left | contradiction]. }
    assert (Hb_cod : ~ In (binder b) (ty_binders codomain)).
    { intro Hin.
      assert (Hin' : In (binder b) (ty_binders (result_type {| result_type := Pi x allowance domain codomain; computation_demand := w; type_demand_row := v |})))
        by (cbn; right; apply in_or_app; now right).
      eapply ty_binders_derives_sub in Hin'; [| exact Hderiv1].
      destruct Hin' as [Hc | Hc]; [apply Hterm; apply in_or_app; now left | contradiction]. }
    eapply GradeApplyValue; eauto using fresh_insert, weakening_type.
    + apply IHHderiv1; [exact Hfresh | | exact Hctx | reflexivity].
      intro Hin; apply Hterm; apply in_or_app; now left.
    + apply IHHderiv2; [exact Hfresh | | exact Hctx | reflexivity].
      intro Hin; apply Hterm; apply in_or_app; now right.
  - cbn in Hterm.
    assert (Hx_neq : x <> binder b) by (intro; apply Hterm; now left).
    assert (Hb_body : ~ In (binder b) (term_binders body)) by (intro; apply Hterm; now right).
    assert (Hb_kind : ~ In (binder b) (ty_binders kind)).
    { intro Hin.
      change (In (binder b) (ty_binders (result_type {| result_type := kind; computation_demand := u; type_demand_row := v |}))) in Hin.
      eapply ty_binders_derives_sub in Hin; [| exact Hderiv].
      destruct Hin as [Hc | Hc]; [contradiction |].
      cbn in Hc. contradiction. }
    assert (Hb_spec : ~ In (binder b) (ty_binders (substitute_type x initializer kind)))
      by (intro Hin; apply Hb_kind; eapply ty_binders_subst_type_incl; eassumption).
    eapply GradeLetNat; eauto using fresh_insert, weakening_index, weakening_type.
    change (DerivesWith allows (({| binder := x; annotation := Natural; type_uses := [] |} :: prefix) ++ b :: suffix) body
              {| result_type := kind; computation_demand := u; type_demand_row := v |}).
    apply IHHderiv; [now apply fresh_cons_intro | exact Hb_body | | reflexivity].
    cbn. exact Hctx.
  - cbn in Hterm.
    assert (Hb_c : ~ In (binder b) (term_binders callee)) by (intro; apply Hterm; apply in_or_app; now left).
    assert (Hb_a : ~ In (binder b) (ty_binders argument)) by (intro; apply Hterm; apply in_or_app; now right).
    assert (Hx_neq : x <> binder b).
    { intro Heq.
      assert (Hin : In (binder b) (ty_binders (result_type {| result_type := Pi x allowance (Universe level) codomain; computation_demand := w; type_demand_row := v |})))
        by (cbn; now left).
      eapply ty_binders_derives_sub in Hin; [| exact Hderiv].
      destruct Hin; contradiction. }
    assert (Hb_cod : ~ In (binder b) (ty_binders codomain)).
    { intro Hin.
      assert (Hin' : In (binder b) (ty_binders (result_type {| result_type := Pi x allowance (Universe level) codomain; computation_demand := w; type_demand_row := v |})))
        by (cbn; right; exact Hin).
      eapply ty_binders_derives_sub in Hin'; [| exact Hderiv].
      destruct Hin'; contradiction. }
    assert (Hb_spec : ~ In (binder b) (ty_binders (substitute_type_variable x argument codomain))).
    { intro Hin. apply ty_binders_subst_type_var_incl in Hin as [H1' | H2']; contradiction. }
    eapply GradeApplyType; eauto using fresh_insert, weakening_type, weakening_universe.
    change (TypeDemand (({| binder := x; annotation := Universe level; type_uses := [] |} :: prefix) ++ b :: suffix) codomain b0).
    apply weakening_type; [now apply fresh_cons_intro | exact Hb_cod | exact H2].
Qed.

(* Demand algebra lemmas *)

Lemma uses_scale : forall n d y,
  uses (scale n d) y = n * uses d y.
Proof.
  intros n d y. induction d as [| [k m] rest IH].
  - cbn. lia.
  - change ((if Nat.eqb y k then n * m else 0) + uses (scale n rest) y =
            n * ((if Nat.eqb y k then m else 0) + uses rest y)).
    rewrite IH. destruct (Nat.eqb y k); lia.
Qed.

Lemma uses_substitute_demand : forall x z d y,
  uses (substitute_demand x z d) y =
  (if Nat.eqb y x then 0 else uses d y) + uses d x * uses z y.
Proof.
  intros x z d y. unfold substitute_demand.
  now rewrite uses_append, uses_without, uses_scale.
Qed.

Lemma same_demand_refl : forall d, same_demand d d.
Proof. intros d x. reflexivity. Qed.

Lemma same_demand_sym : forall d1 d2, same_demand d1 d2 -> same_demand d2 d1.
Proof. intros d1 d2 H x. symmetry. apply H. Qed.

Lemma same_demand_trans : forall d1 d2 d3,
  same_demand d1 d2 -> same_demand d2 d3 -> same_demand d1 d3.
Proof. intros d1 d2 d3 H12 H23 x. now rewrite H12, H23. Qed.

Lemma same_demand_app_compat : forall a1 a2 b1 b2,
  same_demand a1 a2 -> same_demand b1 b2 -> same_demand (a1 ++ b1) (a2 ++ b2).
Proof.
  intros a1 a2 b1 b2 Ha Hb x. rewrite !uses_append. now rewrite Ha, Hb.
Qed.

Lemma same_demand_without_compat : forall x d1 d2,
  same_demand d1 d2 -> same_demand (without x d1) (without x d2).
Proof.
  intros x d1 d2 H y. rewrite !uses_without. destruct (Nat.eqb y x); [reflexivity | apply H].
Qed.

Lemma same_demand_scale_compat : forall n d1 d2,
  same_demand d1 d2 -> same_demand (scale n d1) (scale n d2).
Proof.
  intros n d1 d2 H y. rewrite !uses_scale. now rewrite H.
Qed.

Lemma same_demand_substitute_compat : forall x z1 z2 d1 d2,
  same_demand z1 z2 -> same_demand d1 d2 ->
  same_demand (substitute_demand x z1 d1) (substitute_demand x z2 d2).
Proof.
  intros x z1 z2 d1 d2 Hz Hd y. rewrite !uses_substitute_demand.
  now rewrite !Hd, Hz.
Qed.

Lemma substitute_demand_app : forall x z d1 d2,
  same_demand (substitute_demand x z (d1 ++ d2))
    (substitute_demand x z d1 ++ substitute_demand x z d2).
Proof.
  intros x z d1 d2 y. rewrite uses_append, !uses_substitute_demand, !uses_append.
  destruct (Nat.eqb y x); lia.
Qed.

Lemma substitute_demand_scale : forall x z n d,
  same_demand (substitute_demand x z (scale n d))
    (scale n (substitute_demand x z d)).
Proof.
  intros x z n d y. rewrite uses_scale, !uses_substitute_demand, !uses_scale.
  destruct (Nat.eqb y x); nia.
Qed.

Lemma substitute_demand_without : forall x y z d,
  x <> y -> uses z y = 0 ->
  same_demand (substitute_demand x z (without y d))
    (without y (substitute_demand x z d)).
Proof.
  intros x y z d Hneq Hzy k.
  assert (Hxy : Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hneq).
  rewrite uses_substitute_demand, !uses_without, uses_substitute_demand, Hxy.
  destruct (Nat.eqb k y) eqn:Eky; destruct (Nat.eqb k x) eqn:Ekx; cbn.
  - apply Nat.eqb_eq in Eky. apply Nat.eqb_eq in Ekx. congruence.
  - apply Nat.eqb_eq in Eky. subst k. rewrite Hzy. lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma substitute_demand_var_same : forall x z,
  uses z x = 0 ->
  same_demand (substitute_demand x z [(x, 1)]) z.
Proof.
  intros x z Hzx y. rewrite uses_substitute_demand. cbn.
  rewrite Nat.eqb_refl. destruct (Nat.eqb y x) eqn:Eyx.
  - apply Nat.eqb_eq in Eyx. subst y. rewrite Hzx. lia.
  - lia.
Qed.

Lemma substitute_demand_var_other : forall x y z,
  x <> y ->
  same_demand (substitute_demand x z [(y, 1)]) [(y, 1)].
Proof.
  intros x y z Hneq k. rewrite uses_substitute_demand. cbn.
  assert (Hxy : Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hneq).
  rewrite Hxy. destruct (Nat.eqb k x) eqn:Ekx; destruct (Nat.eqb k y) eqn:Eky; try lia.
  apply Nat.eqb_eq in Ekx. apply Nat.eqb_eq in Eky. congruence.
Qed.

Lemma zero_index_use_local : forall env i row,
  IndexDemand env i row -> forall x arg,
  uses row x = 0 -> substitute_index x arg i = i.
Proof.
  intros env i row Hd.
  induction Hd; intros x1 arg Hzero; cbn in *.
  - now destruct (Nat.eqb x1 x).
  - reflexivity.
  - rewrite uses_append in Hzero. apply Nat.eq_add_0 in Hzero as [Hl Hr].
    now rewrite IHHd1, IHHd2.
Qed.

Lemma zero_type_use_local : forall env kind row,
  TypeDemand env kind row -> forall x arg,
  uses row x = 0 -> substitute_type x arg kind = kind.
Proof.
  intros env kind row Hd.
  induction Hd; intros x1 arg Hzero; cbn.
  - reflexivity.
  - f_equal. eapply zero_index_use_local; eauto.
  - rewrite uses_append, uses_without in Hzero. apply Nat.eq_add_0 in Hzero as [Hdom Hcod].
    rewrite IHHd1 by exact Hdom.
    destruct (Nat.eqb x1 x); [reflexivity | now rewrite IHHd2].
  - reflexivity.
  - reflexivity.
Qed.

Lemma zero_type_var_use_local : forall env kind row,
  TypeDemand env kind row -> forall x arg,
  uses row x = 0 -> substitute_type_variable x arg kind = kind.
Proof.
  intros env kind row Hd.
  induction Hd; intros x1 arg Hzero; cbn in *.
  - reflexivity.
  - reflexivity.
  - rewrite uses_append, uses_without in Hzero. apply Nat.eq_add_0 in Hzero as [Hdom Hcod].
    rewrite IHHd1 by exact Hdom.
    destruct (Nat.eqb x1 x); [reflexivity | now rewrite IHHd2].
  - reflexivity.
  - destruct (Nat.eqb x1 x); [discriminate | reflexivity].
Qed.

Lemma zero_use_preserves_row_local : forall row arg x,
  uses row x = 0 -> same_demand (substitute_demand x arg row) row.
Proof.
  intros row arg x H0 y. rewrite uses_substitute_demand, H0, Nat.mul_0_l, Nat.add_0_r.
  destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst y; symmetry; exact H0 | reflexivity].
Qed.

(* Substitution metatheory *)

Fixpoint index_vars (i : index) : list nat :=
  match i with
  | IndexVar x => [x]
  | IndexLit _ => []
  | IndexAdd l r => index_vars l ++ index_vars r
  end.

Fixpoint ty_free_index_vars (bound : list nat) (k : ty) : list nat :=
  match k with
  | Natural | Universe _ | TypeVar _ => []
  | Vector len => filter (fun v => negb (existsb (Nat.eqb v) bound)) (index_vars len)
  | Pi x _ dom cod => ty_free_index_vars bound dom ++ ty_free_index_vars (x :: bound) cod
  end.

Lemma index_demand_uses_bound : forall env i d y,
  IndexDemand env i d ->
  (uses d y > 0 <-> In y (index_vars i)) /\
  (In y (index_vars i) -> exists entry, lookup env y = Some entry /\ annotation entry = Natural).
Proof.
  intros env i d y Hd. induction Hd; cbn.
  - split.
    + split; intro H1.
      * left. destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; congruence | lia].
      * destruct H1 as [<- | []]. rewrite Nat.eqb_refl. lia.
    + intros [<- | []]. exists entry. split; assumption.
  - split; [split; lia || contradiction | contradiction].
  - rewrite uses_append, in_app_iff. destruct IHHd1 as [I1 L1], IHHd2 as [I2 L2].
    split; [split; [intro Hgt; assert (uses p y > 0 \/ uses q y > 0) as [Hp | Hq] by lia;
      [left; apply I1; exact Hp | right; apply I2; exact Hq] |
      intros [Hp | Hq]; [apply I1 in Hp | apply I2 in Hq]; lia] |
      intros [H1 | H2]; auto].
Qed.

Lemma index_demand_absent_use : forall env i d y,
  IndexDemand env i d ->
  lookup env y = None ->
  uses d y = 0 /\ ~ In y (index_vars i).
Proof.
  intros env i d y Hd Hnone.
  destruct (index_demand_uses_bound env i d y Hd) as [[Hu1 _] Hl].
  assert (Hnot : ~ In y (index_vars i)).
  { intro Hin. destruct (Hl Hin) as [e [He _]]. congruence. }
  split; [| exact Hnot].
  destruct (uses d y) eqn:E; [reflexivity | exfalso; apply Hnot, Hu1; lia].
Qed.

Lemma type_demand_absent_use : forall env kind d y,
  TypeDemand env kind d ->
  lookup env y = None ->
  uses d y = 0.
Proof.
  intros env kind d y Hd. revert y.
  induction Hd; intros y Hnone; cbn.
  - reflexivity.
  - eapply index_demand_absent_use; eassumption.
  - rewrite uses_append, uses_without, IHHd1; [| exact Hnone].
    destruct (Nat.eqb y x) eqn:Eyx; [reflexivity |].
    apply IHHd2. cbn. rewrite Eyx. exact Hnone.
  - reflexivity.
  - destruct (Nat.eqb y x) eqn:Eyx; [| reflexivity].
    apply Nat.eqb_eq in Eyx. subst y. congruence.
Qed.

Lemma lookup_split_three : forall f inner x bx outer y,
  (forall e, binder (f e) = binder e) ->
  fresh inner x = true ->
  binder bx = x ->
  (y = x -> lookup (inner ++ bx :: outer) x = Some bx /\ lookup (map f inner ++ outer) x = lookup outer x) /\
  (y <> x ->
    (lookup inner y = None -> lookup (inner ++ bx :: outer) y = lookup outer y /\ lookup (map f inner ++ outer) y = lookup outer y) /\
    (forall e, lookup inner y = Some e -> lookup (inner ++ bx :: outer) y = Some e /\ lookup (map f inner ++ outer) y = Some (f e))).
Proof.
  intros f inner x bx outer y Hf Hfx Hbx.
  assert (Hmap_none : forall l z, lookup l z = None -> lookup (map f l) z = None).
  { intros l. induction l as [| p rest IH]; intros z Hz; [reflexivity |].
    unfold lookup in *; cbn in *; rewrite Hf.
    destruct (Nat.eqb z (binder p)); [discriminate | apply IH; exact Hz]. }
  assert (Hmap_some : forall l z e, lookup l z = Some e -> lookup (map f l) z = Some (f e)).
  { intros l. induction l as [| p rest IH]; intros z e Hz; [discriminate |].
    unfold lookup in *; cbn in *; rewrite Hf.
    destruct (Nat.eqb z (binder p)); [inversion Hz; reflexivity | apply IH; exact Hz]. }
  split.
  - intros ->. unfold fresh in Hfx.
    destruct (lookup inner x) eqn:Hlx; [discriminate |].
    rewrite !lookup_app_head, Hlx, (Hmap_none inner x Hlx). cbn.
    rewrite Hbx, Nat.eqb_refl. split; reflexivity.
  - intro Hneq. split.
    + intro Hnone. rewrite !lookup_app_head, Hnone, (Hmap_none inner y Hnone). cbn.
      rewrite Hbx. apply Nat.eqb_neq in Hneq. rewrite Hneq. split; reflexivity.
    + intros e Hsome. rewrite !lookup_app_head, Hsome, (Hmap_some inner y e Hsome). split; reflexivity.
Qed.

Lemma index_demand_weaken_app : forall inner outer arg z,
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  IndexDemand outer arg z ->
  IndexDemand (inner ++ outer) arg z.
Proof.
  intros inner outer arg z Hnoshad Hd.
  induction Hd; econstructor; eauto.
  rewrite lookup_app_head.
  assert (Hfr : fresh inner x = true).
  { apply Hnoshad. rewrite H. discriminate. }
  unfold fresh in Hfr. destruct (lookup inner x); [discriminate | exact H].
Qed.

Lemma index_demand_mono_lookup : forall env1 env2 i d,
  (forall y e, lookup env1 y = Some e -> lookup env2 y = Some e) ->
  IndexDemand env1 i d ->
  IndexDemand env2 i d.
Proof.
  intros env1 env2 i d Hmono Hd.
  induction Hd; econstructor; eauto.
Qed.

Lemma universe_level_mono_lookup : forall env1 env2 kind lvl,
  (forall y e, lookup env1 y = Some e -> lookup env2 y = Some e) ->
  UniverseLevel env1 kind lvl ->
  UniverseLevel env2 kind lvl.
Proof.
  intros env1 env2 kind lvl Hmono Hl.
  revert env2 Hmono.
  induction Hl; intros env2 Hmono; econstructor; eauto.
  apply IHHl2. intros y e Hy. cbn in *.
  destruct (Nat.eqb y x); [exact Hy | apply Hmono; exact Hy].
Qed.

Lemma lookup_weaken_mono : forall inner outer y e,
  (forall z, lookup outer z <> None -> fresh inner z = true) ->
  lookup outer y = Some e ->
  lookup (inner ++ outer) y = Some e.
Proof.
  intros inner outer y e Hnoshad Hlkp.
  rewrite lookup_app_head.
  assert (Hfr : fresh inner y = true) by (apply Hnoshad; rewrite Hlkp; discriminate).
  unfold fresh in Hfr. destruct (lookup inner y); [discriminate | exact Hlkp].
Qed.

Lemma type_demand_mono_lookup : forall env1 env2 kind d,
  (forall y e, lookup env1 y = Some e -> lookup env2 y = Some e) ->
  (forall y, In y (ty_binders kind) -> fresh env1 y = true -> fresh env2 y = true) ->
  TypeDemand env1 kind d ->
  TypeDemand env2 kind d.
Proof.
  intros env1 env2 kind d Hmono Hfr Hd.
  revert env2 Hmono Hfr.
  induction Hd; intros env2 Hmono Hfr; cbn in Hfr.
  - constructor.
  - constructor. eapply index_demand_mono_lookup; eassumption.
  - constructor.
    + apply Hfr; [now left | exact H].
    + apply IHHd1; [exact Hmono |].
      intros y Hy. apply Hfr. right. apply in_or_app. now left.
    + apply IHHd2.
      * intros y e Hy. cbn in *. destruct (Nat.eqb y x); [exact Hy | apply Hmono; exact Hy].
      * intros y Hy Hfy. apply fresh_cons_inv in Hfy as [Hneq Hfy].
        apply fresh_cons_intro; [exact Hneq |].
        apply Hfr; [right; apply in_or_app; now right | exact Hfy].
  - constructor.
  - eapply TypeVariable; [apply Hmono; exact H | exact H0].
Qed.

Lemma type_demand_weaken_app : forall inner outer arg z,
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  (forall y, In y (ty_binders arg) -> fresh inner y = true) ->
  TypeDemand outer arg z ->
  TypeDemand (inner ++ outer) arg z.
Proof.
  intros inner outer arg z Hnoshad Htb Hd.
  eapply type_demand_mono_lookup; [| | exact Hd].
  - intros y e Hy. apply lookup_weaken_mono; assumption.
  - intros y Hy Hfr. unfold fresh in *. rewrite lookup_app_head.
    assert (Hfi : fresh inner y = true) by (apply Htb; exact Hy).
    unfold fresh in Hfi. destruct (lookup inner y); [discriminate | exact Hfr].
Qed.

(* Helper: replacing type_uses of a binding in env with a same_demand preserves judgments *)
Lemma lookup_rel_cons : forall env1 env2 b1 b2,
  binder b1 = binder b2 ->
  annotation b1 = annotation b2 ->
  same_demand (type_uses b1) (type_uses b2) ->
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
             | None, None => True
             | _, _ => False
             end) ->
  (forall y, match lookup (b1 :: env1) y, lookup (b2 :: env2) y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
             | None, None => True
             | _, _ => False
             end).
Proof.
  intros env1 env2 b1 b2 Hb Ha Hs Hrel y. cbn.
  rewrite <- Hb. destruct (Nat.eqb y (binder b1)); [auto | apply Hrel].
Qed.

Lemma lookup_rel_refl : forall env y,
  match lookup env y, lookup env y with
  | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros env y. destruct (lookup env y); [repeat split; auto using same_demand_refl | exact I].
Qed.

Lemma index_demand_rel : forall env1 env2 i d,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
             | None, None => True
             | _, _ => False
             end) ->
  IndexDemand env1 i d ->
  IndexDemand env2 i d.
Proof.
  intros env1 env2 i d Hrel Hi.
  induction Hi.
  - specialize (Hrel x). rewrite H in Hrel.
    destruct (lookup env2 x) as [e2 |] eqn:E2; [| contradiction].
    destruct Hrel as [_ [Hann _]].
    eapply NaturalVariable; [exact E2 | rewrite <- Hann; exact H0].
  - constructor.
  - constructor; assumption.
Qed.

Lemma type_demand_rel : forall env1 env2 k d,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
             | None, None => True
             | _, _ => False
             end) ->
  TypeDemand env1 k d ->
  TypeDemand env2 k d.
Proof.
  intros env1 env2 k d Hrel Hk. revert env2 Hrel.
  induction Hk; intros env2 Hrel.
  - constructor.
  - constructor. eapply index_demand_rel; eassumption.
  - constructor.
    + specialize (Hrel x). unfold fresh in *.
      destruct (lookup env x), (lookup env2 x); try contradiction; assumption.
    + eauto.
    + eapply IHHk2. apply lookup_rel_cons; auto using same_demand_refl.
  - constructor.
  - specialize (Hrel x). rewrite H in Hrel.
    destruct (lookup env2 x) as [e2 |] eqn:E2; [| contradiction].
    destruct Hrel as [_ [Hann _]].
    eapply TypeVariable; [exact E2 | rewrite <- Hann; exact H0].
Qed.

Lemma universe_level_rel : forall env1 env2 k l,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
             | None, None => True
             | _, _ => False
             end) ->
  UniverseLevel env1 k l ->
  UniverseLevel env2 k l.
Proof.
  intros env1 env2 k l Hrel Hk. revert env2 Hrel.
  induction Hk; intros env2 Hrel.
  - constructor.
  - constructor.
  - constructor; [auto | apply IHHk2; apply lookup_rel_cons; auto using same_demand_refl].
  - constructor.
  - specialize (Hrel x). rewrite H in Hrel.
    destruct (lookup env2 x) as [e2 |] eqn:E2; [| contradiction].
    destruct Hrel as [_ [Hann _]].
    eapply LevelVariable; [exact E2 | rewrite <- Hann; exact H0].
Qed.

Lemma subst_index_demand : forall outer arg z inner x i d,
  IndexDemand outer arg z ->
  fresh outer x = true ->
  fresh inner x = true ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  IndexDemand (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) i d ->
  exists d',
    IndexDemand (map (rewrite_binding x arg z) inner ++ outer) (substitute_index x arg i) d' /\
    same_demand d' (substitute_demand x z d).
Proof.
  intros outer arg z inner x i d Harg Hfx_o Hfx_i Hnoshad Hd.
  remember (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) as env eqn:Eenv.
  induction Hd; subst; cbn [substitute_index].
  - destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    destruct (Nat.eqb x x0) eqn:Exx0.
    + apply Nat.eqb_eq in Exx0. subst x0.
      destruct (Heq eq_refl) as [Hlkp _]. rewrite H in Hlkp. inversion Hlkp; subst.
      exists z. split.
      * eapply index_demand_mono_lookup; [| exact Harg].
        intros y e Hy. apply lookup_weaken_mono; [| exact Hy].
        intros k Hk.
        assert (Hfk : fresh inner k = true) by (apply Hnoshad; exact Hk).
        unfold fresh in *. clear -Hfk. induction inner as [| p rest IH]; [reflexivity |].
        cbn in *. destruct (Nat.eqb k (binder p)); [discriminate | apply IH; exact Hfk].
      * apply same_demand_sym, substitute_demand_var_same.
        eapply index_demand_absent_use; [exact Harg |].
        unfold fresh in Hfx_o. now destruct (lookup outer x).
    + apply Nat.eqb_neq in Exx0.
      assert (Hx0neq : x0 <> x) by congruence.
      destruct (Hneq Hx0neq) as [Hnone Hsome].
      destruct (lookup inner x0) as [ei |] eqn:Hi.
      * destruct (Hsome ei eq_refl) as [H1 H2]. rewrite H in H1. inversion H1; subst.
        exists [(x0, 1)]. split.
        -- eapply NaturalVariable; [exact H2 |]. cbn. now rewrite H0.
        -- apply same_demand_sym, substitute_demand_var_other. congruence.
      * destruct (Hnone eq_refl) as [H1 H2]. rewrite H in H1.
        exists [(x0, 1)]. split.
        -- eapply NaturalVariable; [rewrite H2, <- H1; reflexivity | exact H0].
        -- apply same_demand_sym, substitute_demand_var_other. congruence.
  - exists []. split; [constructor |].
    intro y. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - destruct IHHd1 as [d1 [Hd1' Hs1]], IHHd2 as [d2 [Hd2' Hs2]].
    exists (d1 ++ d2). split; [constructor; assumption |].
    eapply same_demand_trans.
    + apply same_demand_app_compat; eassumption.
    + apply same_demand_sym, substitute_demand_app.
Qed.

Lemma subst_type_demand : forall outer arg z inner x kind d,
  IndexDemand outer arg z ->
  fresh outer x = true ->
  fresh inner x = true ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  TypeDemand (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) kind d ->
  exists d',
    TypeDemand (map (rewrite_binding x arg z) inner ++ outer) (substitute_type x arg kind) d' /\
    same_demand d' (substitute_demand x z d).
Proof.
  intros outer arg z inner x kind d Harg Hfx_o Hfx_i Hnoshad Hd.
  remember (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) as env eqn:Eenv.
  revert inner Hfx_i Hnoshad Eenv.
  induction Hd; intros inner Hfx_i Hnoshad Eenv; subst; cbn [substitute_type].
  - exists []. split; [constructor |].
    intro y. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - destruct (subst_index_demand outer arg z inner x length d Harg Hfx_o Hfx_i Hnoshad H)
      as [d' [Hd' Hs']].
    exists d'. split; [constructor; exact Hd' | exact Hs'].
  - destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1 _].
      rewrite H1 in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1 _]. rewrite H1 in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2]. rewrite H2, Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0)
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    destruct (IHHd1 inner Hfx_i Hnoshad eq_refl) as [a' [Ha' Hsa]].
    assert (Hfx_i' : fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    destruct (IHHd2 ({| binder := x0; annotation := domain; type_uses := a |} :: inner) Hfx_i' Hnoshad' eq_refl)
      as [b' [Hb' Hsb]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx.
    exists (a' ++ without x0 b'). split.
    + apply TypePi; [exact Hx0_fresh_after | exact Ha' |].
      eapply type_demand_rel; [| exact Hb'].
      apply lookup_rel_cons; [reflexivity | reflexivity | apply same_demand_sym; exact Hsa |].
      apply lookup_rel_refl.
    + eapply same_demand_trans.
      * apply same_demand_app_compat; [exact Hsa | apply same_demand_without_compat; exact Hsb].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_without; congruence || exact Hx0_notin_z].
        -- apply same_demand_sym, substitute_demand_app.
  - exists []. split; [constructor |].
    intro y. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      rewrite H in Hlkp. inversion Hlkp; subst. discriminate H0. }
    destruct (Hneq Hx0_neq) as [Hnone Hsome].
    exists [(x0, 1)]. split.
    + destruct (lookup inner x0) as [ei |] eqn:Hi.
      * destruct (Hsome ei eq_refl) as [H1 H2]. rewrite H in H1. inversion H1; subst.
        eapply TypeVariable; [exact H2 |]. cbn. now rewrite H0.
      * destruct (Hnone eq_refl) as [H1 H2]. rewrite H in H1.
        eapply TypeVariable; [rewrite H2, <- H1; reflexivity | exact H0].
    + apply same_demand_sym, substitute_demand_var_other. congruence.
Qed.

Lemma canonical_index_not_in : forall names x,
  ~ In x (map fst names) ->
  forall y, canonical_index names y = canonical_index names x -> y = x.
Proof.
  intros names x Hnotin y Heq. unfold canonical_index in Heq.
  destruct (find (fun b => Nat.eqb x (fst b)) names) eqn:F1.
  - exfalso. apply Hnotin. apply find_some in F1 as [Hin Hmatch].
    apply Nat.eqb_eq in Hmatch. rewrite Hmatch. apply in_map, Hin.
  - destruct (find (fun b => Nat.eqb y (fst b)) names) eqn:F2; lia.
Qed.

Lemma canonical_value_subst_comm : forall names x arg i,
  ~ In x (map fst names) ->
  (forall b, In b (map fst names) -> ~ In b (index_vars arg)) ->
  canonical_value names (substitute_index x arg i) =
  substitute_index (2 * x + 1) (canonical_value names arg) (canonical_value names i).
Proof.
  intros names x arg i Hxnotin Hbound.
  induction i as [y | n | l IHl r IHr]; cbn [substitute_index canonical_value].
  - destruct (Nat.eqb x y) eqn:Exy.
    + apply Nat.eqb_eq in Exy. subst y.
      unfold canonical_index.
      destruct (find (fun b => Nat.eqb x (fst b)) names) eqn:F.
      * exfalso. apply Hxnotin. apply find_some in F as [Hin Hm].
        apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
      * now rewrite Nat.eqb_refl.
    + cbn [substitute_index canonical_value]. unfold canonical_index.
      destruct (find (fun b => Nat.eqb y (fst b)) names) eqn:F.
      * destruct p as [k d]. cbn [snd].
        assert (Hneq : Nat.eqb (2 * x + 1) (2 * d) = false) by (apply Nat.eqb_neq; lia).
        now rewrite Hneq.
      * assert (Hneq : Nat.eqb (2 * x + 1) (2 * y + 1) = false).
        { apply Nat.eqb_neq. apply Nat.eqb_neq in Exy. lia. }
        now rewrite Hneq.
  - reflexivity.
  - now rewrite IHl, IHr.
Qed.

Lemma canonical_value_add_binder : forall names b d arg,
  ~ In b (index_vars arg) ->
  canonical_value ((b, d) :: names) arg = canonical_value names arg.
Proof.
  intros names b d arg Hnotin.
  induction arg as [y | n | l IHl r IHr]; cbn in *.
  - unfold canonical_index. cbn.
    destruct (Nat.eqb y b) eqn:Eyb.
    + apply Nat.eqb_eq in Eyb. exfalso. apply Hnotin. now left.
    + reflexivity.
  - reflexivity.
  - f_equal; [apply IHl | apply IHr]; intro; apply Hnotin; apply in_or_app; auto.
Qed.

Lemma canonical_type_subst_comm : forall names x arg kind,
  ~ In x (map fst names) ->
  (forall b, In b (map fst names) -> ~ In b (index_vars arg)) ->
  (forall b, In b (ty_binders kind) -> b <> x /\ ~ In b (index_vars arg)) ->
  canonical_type names (substitute_type x arg kind) =
  substitute_type (2 * x + 1) (canonical_value names arg) (canonical_type names kind).
Proof.
  intros names x arg kind. revert names.
  induction kind as [| len | y allow dom IHdom cod IHcod | lvl | v];
    intros names Hxnotin Hbound Hkind; cbn [substitute_type canonical_type ty_binders] in *.
  - reflexivity.
  - f_equal. apply canonical_value_subst_comm; assumption.
  - assert (Hy_neq : y <> x /\ ~ In y (index_vars arg)) by (apply Hkind; now left).
    assert (Hdom : forall b, In b (ty_binders dom) -> b <> x /\ ~ In b (index_vars arg))
      by (intros b Hb; apply Hkind; right; apply in_or_app; now left).
    assert (Hcod : forall b, In b (ty_binders cod) -> b <> x /\ ~ In b (index_vars arg))
      by (intros b Hb; apply Hkind; right; apply in_or_app; now right).
    assert (Hxy : Nat.eqb x y = false) by (apply Nat.eqb_neq; destruct Hy_neq; congruence).
    assert (H2xy : Nat.eqb (2 * x + 1) (2 * length names) = false) by (apply Nat.eqb_neq; lia).
    rewrite Hxy, H2xy, IHdom; try assumption.
    f_equal. rewrite IHcod; try assumption.
    + now rewrite canonical_value_add_binder by (destruct Hy_neq; exact H0).
    + cbn. intros [-> | Hin]; [destruct Hy_neq; congruence | auto].
    + cbn. intros b [<- | Hin]; [destruct Hy_neq; exact H0 | auto].
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint substitute_term (x : nat) (arg : index) (t : term) : term :=
  match t with
  | Var y => if Nat.eqb x y then NatValue arg else Var y
  | NatValue i => NatValue (substitute_index x arg i)
  | Lambda y allowance domain body =>
      Lambda y allowance (substitute_type x arg domain)
        (if Nat.eqb x y then body else substitute_term x arg body)
  | ApplyNat callee idx =>
      ApplyNat (substitute_term x arg callee) (substitute_index x arg idx)
  | ApplyValue callee argument =>
      ApplyValue (substitute_term x arg callee) (substitute_term x arg argument)
  | LetNat y allowance initializer body =>
      LetNat y allowance (substitute_index x arg initializer)
        (if Nat.eqb x y then body else substitute_term x arg body)
  | ApplyType callee ty_arg =>
      ApplyType (substitute_term x arg callee) (substitute_type x arg ty_arg)
  end.

Lemma substitute_type_comm : forall x1 a1 x2 a2 kind,
  x1 <> x2 ->
  ~ In x1 (index_vars a2) ->
  ~ In x2 (index_vars a1) ->
  substitute_type x1 a1 (substitute_type x2 a2 kind) =
  substitute_type x2 a2 (substitute_type x1 a1 kind).
Proof.
  intros x1 a1 x2 a2 kind Hneq H12 H21.
  assert (Hidx : forall i,
    substitute_index x1 a1 (substitute_index x2 a2 i) =
    substitute_index x2 a2 (substitute_index x1 a1 i)).
  { induction i as [y | n | l IHl r IHr]; cbn.
    - destruct (Nat.eqb x2 y) eqn:E2; destruct (Nat.eqb x1 y) eqn:E1; cbn.
      + apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. congruence.
      + rewrite ?E1, ?E2. clear E1 E2.
        assert (Hgen : forall a, ~ In x1 (index_vars a) -> substitute_index x1 a1 a = a).
        { clear -a1. induction a as [z | m | l2 IHl2 r2 IHr2]; intros Hnf; cbn in *.
          - destruct (Nat.eqb x1 z) eqn:Exz; [apply Nat.eqb_eq in Exz; exfalso; apply Hnf; now left | reflexivity].
          - reflexivity.
          - f_equal; [apply IHl2 | apply IHr2]; intro; apply Hnf; apply in_or_app; auto. }
        now apply Hgen.
      + rewrite ?E1, ?E2. clear E1 E2.
        assert (Hgen : forall a, ~ In x2 (index_vars a) -> a = substitute_index x2 a2 a).
        { clear -a2. induction a as [z | m | l1 IHl1 r1 IHr1]; intros Hnf; cbn in *.
          - destruct (Nat.eqb x2 z) eqn:Exz; [apply Nat.eqb_eq in Exz; exfalso; apply Hnf; now left | reflexivity].
          - reflexivity.
          - f_equal; [apply IHl1 | apply IHr1]; intro; apply Hnf; apply in_or_app; auto. }
        now apply Hgen.
      + rewrite ?E1, ?E2. reflexivity.
    - reflexivity.
    - now rewrite IHl, IHr. }
  induction kind; cbn; try reflexivity.
  - now rewrite Hidx.
  - rewrite IHkind1. f_equal.
    destruct (Nat.eqb x2 x) eqn:E2; destruct (Nat.eqb x1 x) eqn:E1; cbn; try reflexivity;
      now rewrite ?E1, ?E2, ?IHkind2.
Qed.

Lemma substitute_type_and_var_comm : forall x arg y ty_arg kind,
  x <> y ->
  ~ In x (ty_binders kind) ->
  substitute_type x arg (substitute_type_variable y ty_arg kind) =
  substitute_type_variable y (substitute_type x arg ty_arg) (substitute_type x arg kind).
Proof.
  intros x arg y ty_arg kind Hneq Hxnotin.
  induction kind as [| len | x0 allow dom IH1 cod IH2 | lvl | v]; cbn in *; try reflexivity.
  - assert (Hx0 : x0 <> x) by (intro E; apply Hxnotin; now left).
    assert (Ex0 : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    assert (Hd1 : ~ In x (ty_binders dom)) by (intro H; apply Hxnotin; right; apply in_or_app; now left).
    assert (Hd2 : ~ In x (ty_binders cod)) by (intro H; apply Hxnotin; right; apply in_or_app; now right).
    destruct (Nat.eqb y x0) eqn:Ey0; cbn; rewrite Ex0, (IH1 Hd1).
    + reflexivity.
    + rewrite (IH2 Hd2). reflexivity.
  - destruct (Nat.eqb y v); reflexivity.
Qed.

Definition context_wf (env : context) : Prop :=
  forall y e, lookup env y = Some e ->
    exists r, TypeDemand env (annotation e) r /\ same_demand (type_uses e) r.

Lemma lookup_wf_extends_step : forall env entry row,
  context_wf env ->
  fresh env (binder entry) = true ->
  TypeDemand env (annotation entry) row ->
  ~ In (binder entry) (ty_binders (annotation entry)) ->
  ~ In (binder entry) (context_ty_binders env) ->
  context_wf ({| binder := binder entry; annotation := annotation entry; type_uses := row |} :: env).
Proof.
  intros env entry row Hwf Hfr Htd Hnot1 Hnot2 y e Hlkp. cbn in Hlkp.
  destruct (Nat.eqb y (binder entry)) eqn:Ey.
  - inversion Hlkp; subst. cbn.
    exists row. split; [| apply same_demand_refl].
    eapply weakening_type with (prefix := []); cbn; eassumption.
  - destruct (Hwf y e Hlkp) as [r [Htd_e Hsd_e]].
    exists r. split; [| exact Hsd_e].
    eapply weakening_type with (prefix := []); cbn; eauto using not_in_context_ty_binders_lookup.
Qed.

Lemma derives_same_type_uses : forall allows env1 env2 t res,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2 /\ same_demand (type_uses e1) (type_uses e2)
             | None, None => True
             | _, _ => False
             end) ->
  DerivesWith allows env1 t res ->
  exists res', DerivesWith allows env2 t res' /\
    result_type res' = result_type res /\
    same_demand (computation_demand res') (computation_demand res) /\
    same_demand (type_demand_row res') (type_demand_row res).
Proof.
  intros allows env1 env2 t res Hrel Hderiv. revert env2 Hrel.
  induction Hderiv; intros env2 Hrel.
  - assert (Hrel_x := Hrel x). rewrite H in Hrel_x.
    destruct (lookup env2 x) as [e2 |] eqn:E2; [| contradiction].
    destruct Hrel_x as [_ [Hann Hsd]].
    eexists. split.
    + eapply GradeVar; [exact E2 | rewrite <- Hann; eapply type_demand_rel; eauto |].
      eapply same_demand_trans; [apply same_demand_sym; exact Hsd | exact H1].
    + cbn. split; [symmetry; exact Hann | split; [apply same_demand_refl | apply same_demand_sym; exact Hsd]].
  - eexists. split; [apply GradeNat; eapply index_demand_rel; eauto |].
    cbn; split; [reflexivity | split; apply same_demand_refl].
  - assert (Hfx : fresh env2 x = true).
    { specialize (Hrel x). unfold fresh in *. destruct (lookup env x), (lookup env2 x); try contradiction; assumption. }
    assert (Hdom : TypeDemand env2 domain a) by (eapply type_demand_rel; eauto).
    destruct (IHHderiv ({| binder := x; annotation := domain; type_uses := a |} :: env2)) as [[cod' u' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    { apply lookup_rel_cons; auto using same_demand_refl. }
    cbn in Hrt', Hcd', Htd'. subst cod'.
    eexists. split.
    + eapply GradeLambda; [exact Hfx | exact Hdom | exact Hd' |].
      now rewrite Hcd'.
    + cbn. split; [reflexivity | split].
      * apply same_demand_without_compat; exact Hcd'.
      * apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_without_compat; exact Htd'].
  - destruct (IHHderiv env2 Hrel) as [[rt' w' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    cbn in Hrt', Hcd', Htd'. rewrite Hrt' in Hd'.
    assert (Hfx : fresh env2 x = true).
    { specialize (Hrel x). unfold fresh in *. destruct (lookup env x), (lookup env2 x); try contradiction; assumption. }
    eexists. split.
    + eapply GradeApplyNat; eauto using index_demand_rel, type_demand_rel.
      eapply type_demand_rel; [| exact H1]. apply lookup_rel_cons; auto using same_demand_refl.
    + cbn. split; [reflexivity | split].
      * apply same_demand_app_compat; [exact Hcd' | apply same_demand_refl].
      * apply same_demand_refl.
  - destruct (IHHderiv1 env2 Hrel) as [[rt1 w' v'] [Hd1' [Hrt1' [Hcd1' Htd1']]]].
    destruct (IHHderiv2 env2 Hrel) as [[rt2 z' a'] [Hd2' [Hrt2' [Hcd2' Htd2']]]].
    cbn in *. rewrite Hrt1' in Hd1'. rewrite Hrt2' in Hd2'.
    assert (Hfx : fresh env2 x = true).
    { specialize (Hrel x). unfold fresh in *. destruct (lookup env x), (lookup env2 x); try contradiction; assumption. }
    eexists. split.
    + eapply GradeApplyValue; eauto using type_demand_rel.
    + cbn. split; [reflexivity | split].
      * apply same_demand_app_compat; [exact Hcd1' | apply same_demand_scale_compat; exact Hcd2'].
      * apply same_demand_refl.
  - assert (Hfx : fresh env2 x = true).
    { specialize (Hrel x). unfold fresh in *. destruct (lookup env x), (lookup env2 x); try contradiction; assumption. }
    destruct (IHHderiv ({| binder := x; annotation := Natural; type_uses := [] |} :: env2)) as [[kind' u' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    { apply lookup_rel_cons; auto using same_demand_refl. }
    cbn in *. subst kind'.
    eexists. split.
    + eapply GradeLetNat; eauto using index_demand_rel, type_demand_rel.
      * now rewrite Hcd'.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Htd'] | exact H3].
    + cbn. split; [reflexivity | split].
      * apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_without_compat; exact Hcd'].
      * apply same_demand_substitute_compat; [apply same_demand_refl | exact Htd'].
  - destruct (IHHderiv env2 Hrel) as [[rt' w' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    cbn in *. rewrite Hrt' in Hd'.
    assert (Hfx : fresh env2 x = true).
    { specialize (Hrel x). unfold fresh in *. destruct (lookup env x), (lookup env2 x); try contradiction; assumption. }
    eexists. split.
    + eapply GradeApplyType; eauto using type_demand_rel, universe_level_rel.
      eapply type_demand_rel; [| exact H2]. apply lookup_rel_cons; auto using same_demand_refl.
    + cbn. split; [reflexivity | split].
      * apply same_demand_app_compat; [exact Hcd' | apply same_demand_refl].
      * apply same_demand_refl.
Qed.

Lemma no_shad_map : forall f inner outer,
  (forall e, binder (f e) = binder e) ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  (forall y, lookup outer y <> None -> fresh (map f inner) y = true).
Proof.
  intros f inner outer Hf Hno y Hy.
  assert (Hfi : fresh inner y = true) by (apply Hno; exact Hy).
  unfold fresh in *. clear -Hf Hfi.
  induction inner as [| p rest IH]; [reflexivity |].
  cbn in *. rewrite Hf. destruct (Nat.eqb y (binder p)); [discriminate | apply IH; exact Hfi].
Qed.

Lemma substitute_index_distr : forall x arg x0 argument i,
  x <> x0 ->
  ~ In x0 (index_vars arg) ->
  substitute_index x arg (substitute_index x0 argument i) =
  substitute_index x0 (substitute_index x arg argument) (substitute_index x arg i).
Proof.
  intros x arg x0 argument i Hneq Hnotin.
  induction i as [y | n | l IHl r IHr]; cbn [substitute_index canonical_value].
  - destruct (Nat.eqb x0 y) eqn:E0; destruct (Nat.eqb x y) eqn:Ex; cbn.
    + apply Nat.eqb_eq in E0. apply Nat.eqb_eq in Ex. congruence.
    + rewrite ?E0, ?Ex. reflexivity.
    + rewrite ?E0, ?Ex. clear E0 Ex.
      assert (Hgen : forall a, ~ In x0 (index_vars a) ->
        a = substitute_index x0 (substitute_index x arg argument) a).
      { clear -x arg argument. induction a as [z | m | l2 IHl2 r2 IHr2]; intros Hnf; cbn in *.
        - destruct (Nat.eqb x0 z) eqn:Ex0z; [apply Nat.eqb_eq in Ex0z; exfalso; apply Hnf; now left | reflexivity].
        - reflexivity.
        - f_equal; [apply IHl2 | apply IHr2]; intro; apply Hnf; apply in_or_app; auto. }
      now apply Hgen.
    + rewrite ?E0, ?Ex. reflexivity.
  - reflexivity.
  - now rewrite IHl, IHr.
Qed.

Lemma substitute_type_distr : forall x arg x0 argument kind,
  x <> x0 ->
  ~ In x0 (index_vars arg) ->
  ~ In x (ty_binders kind) ->
  substitute_type x arg (substitute_type x0 argument kind) =
  substitute_type x0 (substitute_index x arg argument) (substitute_type x arg kind).
Proof.
  intros x arg x0 argument kind Hneq Hnotin Hxnb.
  induction kind as [| len | x1 allow dom IH1 cod IH2 | lvl | v]; cbn in *; try reflexivity.
  - f_equal. apply substitute_index_distr; assumption.
  - assert (Hx1 : x1 <> x) by (intro E; apply Hxnb; now left).
    assert (Ex : Nat.eqb x x1 = false) by (apply Nat.eqb_neq; congruence).
    assert (Hd1 : ~ In x (ty_binders dom)) by (intro H; apply Hxnb; right; apply in_or_app; now left).
    assert (Hd2 : ~ In x (ty_binders cod)) by (intro H; apply Hxnb; right; apply in_or_app; now right).
    rewrite (IH1 Hd1). f_equal.
    destruct (Nat.eqb x0 x1) eqn:E0; cbn; rewrite Ex.
    + reflexivity.
    + cbn. rewrite (IH2 Hd2). reflexivity.
Qed.

(* Also need same_demand for substitute_demand_distr:
   substitute_demand x z (substitute_demand x0 z0 b) == substitute_demand x0 (substitute_demand x z z0) (substitute_demand x z b)
   when x <> x0 and uses z x0 = 0! *)
Lemma substitute_demand_distr : forall x z x0 z0 b,
  x <> x0 ->
  uses z x0 = 0 ->
  same_demand (substitute_demand x z (substitute_demand x0 z0 b))
    (substitute_demand x0 (substitute_demand x z z0) (substitute_demand x z b)).
Proof.
  intros x z x0 z0 b Hneq H0 k.
  rewrite !uses_substitute_demand.
  destruct (Nat.eqb k x) eqn:Ekx; destruct (Nat.eqb k x0) eqn:Ekx0;
    destruct (Nat.eqb x0 x) eqn:Ex0x; destruct (Nat.eqb x x0) eqn:Exx0;
    try (apply Nat.eqb_eq in Ex0x; congruence);
    try (apply Nat.eqb_eq in Exx0; congruence);
    try (apply Nat.eqb_eq in Ekx; apply Nat.eqb_eq in Ekx0; congruence).
  - apply Nat.eqb_eq in Ekx. subst k. rewrite H0. lia.
  - apply Nat.eqb_eq in Ekx0. subst k. rewrite H0. lia.
  - lia.
Qed.

Lemma universe_level_univ_equiv : forall env1 env2 k l,
  (forall y e1 i, lookup env1 y = Some e1 -> annotation e1 = Universe i ->
    exists e2, lookup env2 y = Some e2 /\ annotation e2 = Universe i) ->
  UniverseLevel env1 k l ->
  UniverseLevel env2 k l.
Proof.
  intros env1 env2 k l Hrel Hl. revert env2 Hrel.
  induction Hl; intros env2 Hrel.
  - constructor.
  - constructor.
  - apply LevelPi; [auto |]. apply IHHl2.
    intros y e1 i0 Hy He1. cbn in *.
    destruct (Nat.eqb y x).
    + inversion Hy; subst. exists {| binder := x; annotation := domain; type_uses := [] |}. split; auto.
    + eapply Hrel; eassumption.
  - constructor.
  - destruct (Hrel x entry i H H0) as [e2 [E2 He2]].
    eapply LevelVariable; [exact E2 | exact He2].
Qed.

Lemma universe_level_subst_nat : forall outer arg z inner x k l,
  fresh inner x = true ->
  UniverseLevel (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) k l ->
  UniverseLevel (map (rewrite_binding x arg z) inner ++ outer) (substitute_type x arg k) l.
Proof.
  intros outer arg z inner x k l Hfx_i Hl.
  remember (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) as env eqn:Eenv.
  revert inner Hfx_i Eenv.
  induction Hl; intros inner Hfx_i Eenv; subst; cbn.
  - constructor.
  - constructor.
  - destruct (Nat.eqb x x0) eqn:Exx0.
    + apply LevelPi; [apply IHHl1; [exact Hfx_i | reflexivity] |].
      eapply universe_level_univ_equiv; [| exact Hl2].
      intros y e1 i0 Hy He1. unfold lookup at 1 in Hy. cbn [find binder] in Hy.
      destruct (Nat.eqb y x0) eqn:Eyx0.
      * inversion Hy; subst. cbn in He1.
        exists {| binder := x0; annotation := substitute_type x arg domain; type_uses := [] |}.
        unfold lookup. cbn [find binder]. rewrite Eyx0. split; [reflexivity | now rewrite He1].
      * fold (lookup (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) y) in Hy.
        unfold lookup at 1. cbn [find binder]. rewrite Eyx0.
        fold (lookup (map (rewrite_binding x arg z) inner ++ outer) y).
        destruct (lookup_split_three (rewrite_binding x arg z) inner x
          {| binder := x; annotation := Natural; type_uses := [] |} outer y
          (fun _ => eq_refl) Hfx_i eq_refl) as [_ Hneq].
        apply Nat.eqb_eq in Exx0. subst x0.
        assert (Hyx : y <> x) by (apply Nat.eqb_neq in Eyx0; exact Eyx0).
        destruct (Hneq Hyx) as [Hnone Hsome].
        destruct (lookup inner y) as [ei |] eqn:Hi.
        -- destruct (Hsome ei eq_refl) as [H1 H2]. rewrite H1 in Hy. inversion Hy; subst.
           exists (rewrite_binding x arg z e1). split; [exact H2 | cbn; now rewrite He1].
        -- destruct (Hnone eq_refl) as [H1 H2]. rewrite H1 in Hy.
           exists e1. split; [rewrite H2, Hy; reflexivity | exact He1].
    + apply LevelPi; [apply IHHl1; [exact Hfx_i | reflexivity] |].
      eapply universe_level_rel; [| apply (IHHl2 ({| binder := x0; annotation := domain; type_uses := [] |} :: inner));
        [apply fresh_cons_intro; [cbn; apply Nat.eqb_neq in Exx0; congruence | exact Hfx_i] | reflexivity]].
      apply lookup_rel_cons; [reflexivity | reflexivity | | apply lookup_rel_refl].
      intro y. cbn [type_uses rewrite_binding rewrite_binding_with].
      rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - constructor.
  - destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    destruct (Nat.eq_dec x0 x) as [-> | Hx0neq].
    + destruct (Heq eq_refl) as [Hlkp _]. rewrite H in Hlkp. inversion Hlkp; subst. discriminate H0.
    + destruct (Hneq Hx0neq) as [Hnone Hsome].
      destruct (lookup inner x0) as [ei |] eqn:Hi.
      * destruct (Hsome ei eq_refl) as [H1 H2]. rewrite H in H1. inversion H1; subst.
        eapply LevelVariable; [exact H2 |]. cbn. now rewrite H0.
      * destruct (Hnone eq_refl) as [H1 H2]. rewrite H in H1.
        eapply LevelVariable; [rewrite H2, <- H1; reflexivity | exact H0].
Qed.

Theorem value_substitution_derives : forall allows outer arg z inner x t res,
  context_wf outer ->
  IndexDemand outer arg z ->
  fresh outer x = true ->
  fresh inner x = true ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  DerivesWith allows (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) t res ->
  exists res',
    DerivesWith allows (map (rewrite_binding x arg z) inner ++ outer) (substitute_term x arg t) res' /\
    result_type res' = substitute_type x arg (result_type res) /\
    same_demand (computation_demand res') (substitute_demand x z (computation_demand res)) /\
    same_demand (type_demand_row res') (substitute_demand x z (type_demand_row res)).
Proof.
  intros allows outer arg z inner x t res Hwf Harg Hfx_o Hfx_i Hnoshad Hderiv.
  remember (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) as env eqn:Eenv.
  revert inner Hfx_i Hnoshad Eenv.
  induction Hderiv; intros inner Hfx_i Hnoshad Eenv; subst;
    cbn [substitute_term substitute_type substitute_index].
  - (* GradeVar *)
    destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    destruct (Nat.eqb x x0) eqn:Exx0.
    + apply Nat.eqb_eq in Exx0. subst x0.
      destruct (Heq eq_refl) as [Hlkp _]. rewrite H in Hlkp. inversion Hlkp; subst.
      assert (Harg' : IndexDemand (map (rewrite_binding x arg z) inner ++ outer) arg z).
      { eapply index_demand_mono_lookup; [| exact Harg].
        intros y e Hy. apply lookup_weaken_mono; [| exact Hy].
        apply no_shad_map; [intro; reflexivity | exact Hnoshad]. }
      eexists. split; [apply GradeNat; exact Harg' |].
      cbn [result_type computation_demand type_demand_row substitute_type].
      split; [reflexivity | split].
      * apply same_demand_sym, substitute_demand_var_same.
        eapply index_demand_absent_use; [exact Harg |].
        unfold fresh in Hfx_o. now destruct (lookup outer x).
      * intro y. rewrite uses_substitute_demand. cbn.
        destruct (Nat.eqb y x); reflexivity.
    + apply Nat.eqb_neq in Exx0.
      assert (Hx0neq : x0 <> x) by congruence.
      destruct (Hneq Hx0neq) as [Hnone Hsome].
      destruct (subst_type_demand outer arg z inner x (annotation entry) row Harg Hfx_o Hfx_i Hnoshad H0)
        as [row' [Hrow' Hsrow]].
      destruct (lookup inner x0) as [ei |] eqn:Hi.
      * destruct (Hsome ei eq_refl) as [H1' H2']. rewrite H in H1'. inversion H1'; subst.
        eexists. split.
        -- eapply GradeVar; [exact H2' | exact Hrow' |].
           cbn [type_uses rewrite_binding rewrite_binding_with].
           eapply same_demand_trans;
             [apply same_demand_substitute_compat; [apply same_demand_refl | exact H1] | apply same_demand_sym; exact Hsrow].
        -- cbn [result_type computation_demand type_demand_row type_uses rewrite_binding rewrite_binding_with].
           split; [reflexivity | split; [apply same_demand_sym, substitute_demand_var_other; congruence | apply same_demand_refl]].
      * destruct (Hnone eq_refl) as [H1' H2']. rewrite H in H1'.
        destruct (Hwf x0 entry (eq_sym H1')) as [ro [Htd_o Hsd_o]].
        assert (Hx_none_o : lookup outer x = None) by (unfold fresh in Hfx_o; now destruct (lookup outer x)).
        assert (Hux_ro : uses ro x = 0) by (eapply type_demand_absent_use; eassumption).
        assert (Hux_tu : uses (type_uses entry) x = 0) by (rewrite Hsd_o; exact Hux_ro).
        assert (Hsubst_ann : substitute_type x arg (annotation entry) = annotation entry)
          by (eapply zero_type_use_local; eassumption).
        assert (Hweak_row : TypeDemand (map (rewrite_binding x arg z) inner ++ outer) (annotation entry) ro).
        { apply type_demand_weaken_app.
          - apply no_shad_map; [intro; reflexivity | exact Hnoshad].
          - intros k Hk. apply (type_demand_ty_binders_fresh _ _ _ k H0) in Hk.
            unfold fresh in Hk. rewrite lookup_app_head in Hk.
            assert (Hki : fresh inner k = true) by (unfold fresh; destruct (lookup inner k); [discriminate | reflexivity]).
            unfold fresh in *. clear -Hki. induction inner as [| p rest IH]; [reflexivity |].
            cbn in *. destruct (Nat.eqb k (binder p)); [discriminate | apply IH; exact Hki].
          - exact Htd_o. }
        eexists. split.
        -- eapply GradeVar; [rewrite H2', <- H1'; reflexivity | exact Hweak_row | exact Hsd_o].
        -- cbn [result_type computation_demand type_demand_row]. split.
           ++ congruence.
           ++ split; [apply same_demand_sym, substitute_demand_var_other; congruence |].
              apply same_demand_sym, zero_use_preserves_row_local; exact Hux_tu.
  - (* GradeNat *)
    destruct (subst_index_demand outer arg z inner x i d Harg Hfx_o Hfx_i Hnoshad H)
      as [d' [Hd' Hs']].
    eexists. split; [apply GradeNat; exact Hd' |].
    cbn [result_type computation_demand type_demand_row substitute_type].
    split; [reflexivity | split; [exact Hs' |]].
    intro y. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - (* GradeLambda *)
    destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0)
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    destruct (subst_type_demand outer arg z inner x domain a Harg Hfx_o Hfx_i Hnoshad H0)
      as [a' [Ha' Hsa]].
    assert (Hfx_i' : fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    destruct (IHHderiv ({| binder := x0; annotation := domain; type_uses := a |} :: inner) Hfx_i' Hnoshad' eq_refl)
      as [res' [Hderiv' [Hrt' [Hcd' Htd']]]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx.
    destruct res' as [cod' u' v'].
    cbn [result_type computation_demand type_demand_row] in Hrt', Hcd', Htd'.
    destruct (derives_same_type_uses allows
      (rewrite_binding x arg z {| binder := x0; annotation := domain; type_uses := a |} :: map (rewrite_binding x arg z) inner ++ outer)
      ({| binder := x0; annotation := substitute_type x arg domain; type_uses := a' |} :: map (rewrite_binding x arg z) inner ++ outer)
      (substitute_term x arg body)
      {| result_type := cod'; computation_demand := u'; type_demand_row := v' |})
      as [res'' [Hderiv'' [Hrt'' [Hcd'' Htd'']]]].
    + apply lookup_rel_cons; [reflexivity | reflexivity | apply same_demand_sym; exact Hsa |].
      apply lookup_rel_refl.
    + exact Hderiv'.
    + destruct res'' as [cod'' u'' v''].
      cbn [result_type computation_demand type_demand_row] in Hrt'', Hcd'', Htd''.
      assert (Hu_x0 : uses u'' x0 = uses u x0).
      { rewrite Hcd'', Hcd', uses_substitute_demand, Hx0_notin_z, Nat.mul_0_r, Nat.add_0_r.
        assert (Hneq' : Nat.eqb x0 x = false) by (apply Nat.eqb_neq; exact Hx0_neq).
        now rewrite Hneq'. }
      eexists. split.
      * eapply GradeLambda; [exact Hx0_fresh_after | exact Ha' | exact Hderiv'' |].
        rewrite Hu_x0. exact H1.
      * cbn [result_type computation_demand type_demand_row substitute_type].
        split; [rewrite Hrt'', Hrt'; symmetry; now rewrite HEq_nx | split].
        -- eapply same_demand_trans; [apply same_demand_without_compat; eapply same_demand_trans; eassumption |].
           apply same_demand_sym, substitute_demand_without; [congruence | exact Hx0_notin_z].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [exact Hsa | apply same_demand_without_compat; eapply same_demand_trans; eassumption].
           ++ eapply same_demand_trans.
              ** apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_without; [congruence | exact Hx0_notin_z]].
              ** apply same_demand_sym, substitute_demand_app.
  - (* GradeApplyNat *)
    destruct (IHHderiv inner Hfx_i Hnoshad eq_refl) as [res_c' [Hdc' [Hrtc' [Hcdc' Htdc']]]].
    destruct res_c' as [rt_c' w' v'].
    cbn [result_type computation_demand type_demand_row] in Hrtc', Hcdc', Htdc'.
    rewrite Hrtc' in Hdc'. cbn [substitute_type] in Hdc'.
    destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0)
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    assert (Hx0_notin_arg : ~ In x0 (index_vars arg))
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    destruct (subst_index_demand outer arg z inner x argument z0 Harg Hfx_o Hfx_i Hnoshad H0)
      as [z0' [Hz0' Hsz0]].
    assert (Hfx_i' : fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    destruct (subst_type_demand outer arg z ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) x codomain b Harg Hfx_o Hfx_i' Hnoshad' H1)
      as [b' [Hb' Hsb]].
    destruct (subst_type_demand outer arg z inner x (substitute_type x0 argument codomain) output Harg Hfx_o Hfx_i Hnoshad H2)
      as [output' [Houtput' Hsout]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Hdc'.
    assert (Hb'' : TypeDemand ({| binder := x0; annotation := Natural; type_uses := [] |} :: map (rewrite_binding x arg z) inner ++ outer)
                     (substitute_type x arg codomain) b').
    { eapply type_demand_rel; [| exact Hb'].
      apply lookup_rel_cons; [reflexivity | cbn; reflexivity | | apply lookup_rel_refl].
      intro y. cbn [type_uses rewrite_binding rewrite_binding_with].
      rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x). }
    assert (Hx_not_cod : ~ In x (ty_binders codomain)).
    { intro Hin. apply (type_demand_ty_binders_fresh _ _ _ x H1) in Hin.
      apply fresh_cons_inv in Hin as [_ Hin].
      destruct (lookup_split_three (rewrite_binding x arg z) inner x
        {| binder := x; annotation := Natural; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq_x _].
      destruct (Heq_x eq_refl) as [Hlkp _]. unfold fresh in Hin. rewrite Hlkp in Hin. discriminate. }
    rewrite substitute_type_distr in Houtput' by (eauto; congruence).
    eexists. split.
    + eapply GradeApplyNat; [exact Hdc' | exact Hx0_fresh_after | exact Hz0' | exact Hb'' | exact Houtput' |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | exact Hsb] |].
      eapply same_demand_trans; [apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z] |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact H3] | apply same_demand_sym; exact Hsout].
    + cbn [result_type computation_demand type_demand_row].
      split; [symmetry; apply substitute_type_distr; eauto; congruence | split].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [exact Hcdc' | apply same_demand_scale_compat; exact Hsz0].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_scale].
           ++ apply same_demand_sym, substitute_demand_app.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | exact Hsb] |].
        apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z].
  - (* GradeApplyValue *)
    destruct (IHHderiv1 inner Hfx_i Hnoshad eq_refl) as [res_c' [Hdc' [Hrtc' [Hcdc' Htdc']]]].
    destruct (IHHderiv2 inner Hfx_i Hnoshad eq_refl) as [res_a' [Hda' [Hrta' [Hcda' Htda']]]].
    destruct res_c' as [rt_c' w' v']. destruct res_a' as [rt_a' z' a'].
    cbn [result_type computation_demand type_demand_row] in Hrtc', Hcdc', Htdc', Hrta', Hcda', Htda'.
    rewrite Hrtc' in Hdc'. rewrite Hrta' in Hda'. cbn [substitute_type] in Hdc'.
    destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H0. rewrite Hlkp in H0. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H0. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H0. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H0. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H0.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    destruct (subst_type_demand outer arg z inner x codomain b Harg Hfx_o Hfx_i Hnoshad H1)
      as [b' [Hb' Hsb]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Hdc'.
    assert (Hcanon : canonical_type [] (substitute_type x arg kind) = canonical_type [] (substitute_type x arg domain)).
    { destruct (derives_type_demand _ _ _ _ Hderiv1) as [row_pi [Htd_pi _]].
      destruct (derives_type_demand _ _ _ _ Hderiv2) as [row_k [Htd_k _]].
      inversion Htd_pi as [| | ? ? ? ? ? ? ? Htd_dom _ | |]; subst.
      assert (Hfx' : fresh (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) x = false).
      { destruct (lookup_split_three (rewrite_binding x arg z) inner x
          {| binder := x; annotation := Natural; type_uses := [] |} outer x
          (fun _ => eq_refl) Hfx_i eq_refl) as [Hqq _].
        destruct (Hqq eq_refl) as [Hqq1 _]. unfold fresh. now rewrite Hqq1. }
      assert (Harg_fresh : forall b_name, In b_name (ty_binders domain) -> ~ In b_name (index_vars arg)).
      { intros b_name Hbm Hin_arg.
        apply (type_demand_ty_binders_fresh _ _ _ b_name Htd_dom) in Hbm.
        destruct (index_demand_uses_bound _ _ _ b_name Harg) as [_ Hl].
        destruct (Hl Hin_arg) as [eb [Heb _]].
        assert (Hfr_o : fresh (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) b_name = false).
        { unfold fresh. rewrite lookup_app_head. destruct (lookup inner b_name); [reflexivity |].
          unfold lookup at 1. cbn [find binder]. fold (lookup outer b_name).
          destruct (Nat.eqb b_name x); [reflexivity | now rewrite Heb]. }
        rewrite Hfr_o in Hbm. discriminate. }
      assert (Harg_fresh_k : forall b_name, In b_name (ty_binders kind) -> ~ In b_name (index_vars arg)).
      { intros b_name Hbm Hin_arg.
        apply (type_demand_ty_binders_fresh _ _ _ b_name Htd_k) in Hbm.
        destruct (index_demand_uses_bound _ _ _ b_name Harg) as [_ Hl].
        destruct (Hl Hin_arg) as [eb [Heb _]].
        assert (Hfr_o : fresh (inner ++ {| binder := x; annotation := Natural; type_uses := [] |} :: outer) b_name = false).
        { unfold fresh. rewrite lookup_app_head. destruct (lookup inner b_name); [reflexivity |].
          unfold lookup at 1. cbn [find binder]. fold (lookup outer b_name).
          destruct (Nat.eqb b_name x); [reflexivity | now rewrite Heb]. }
        rewrite Hfr_o in Hbm. discriminate. }
      assert (Hnot_x_dom : forall b_name, In b_name (ty_binders domain) -> b_name <> x /\ ~ In b_name (index_vars arg)).
      { intros b_name Hbm. split; [| apply Harg_fresh; exact Hbm].
        apply (type_demand_ty_binders_fresh _ _ _ b_name Htd_dom) in Hbm.
        intro E. subst b_name. rewrite Hfx' in Hbm. discriminate. }
      assert (Hnot_x_k : forall b_name, In b_name (ty_binders kind) -> b_name <> x /\ ~ In b_name (index_vars arg)).
      { intros b_name Hbm. split; [| apply Harg_fresh_k; exact Hbm].
        apply (type_demand_ty_binders_fresh _ _ _ b_name Htd_k) in Hbm.
        intro E. subst b_name. rewrite Hfx' in Hbm. discriminate. }
      rewrite !canonical_type_subst_comm; try assumption; try (cbn; tauto).
      now rewrite H. }
    eexists. split.
    + eapply GradeApplyValue; [exact Hdc' | exact Hda' | exact Hcanon | exact Hx0_fresh_after | exact Hb'].
    + cbn [result_type computation_demand type_demand_row]. split; [reflexivity | split].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [exact Hcdc' | apply same_demand_scale_compat; exact Hcda'].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_scale].
           ++ apply same_demand_sym, substitute_demand_app.
      * exact Hsb.
  - (* GradeLetNat *)
    destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0)
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    assert (Hx0_notin_arg : ~ In x0 (index_vars arg))
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    destruct (subst_index_demand outer arg z inner x initializer z0 Harg Hfx_o Hfx_i Hnoshad H0)
      as [z0' [Hz0' Hsz0]].
    assert (Hfx_i' : fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    destruct (IHHderiv ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) Hfx_i' Hnoshad' eq_refl)
      as [[kind' u' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    cbn [result_type computation_demand type_demand_row] in Hrt', Hcd', Htd'. subst kind'.
    destruct (subst_type_demand outer arg z inner x (substitute_type x0 initializer kind) output Harg Hfx_o Hfx_i Hnoshad H2)
      as [output' [Houtput' Hsout]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx.
    destruct (derives_same_type_uses allows
      (rewrite_binding x arg z {| binder := x0; annotation := Natural; type_uses := [] |} :: map (rewrite_binding x arg z) inner ++ outer)
      ({| binder := x0; annotation := Natural; type_uses := [] |} :: map (rewrite_binding x arg z) inner ++ outer)
      (substitute_term x arg body)
      {| result_type := substitute_type x arg kind; computation_demand := u'; type_demand_row := v' |})
      as [[kind'' u'' v''] [Hd'' [Hrt'' [Hcd'' Htd'']]]].
    + apply lookup_rel_cons; [reflexivity | cbn; reflexivity | | apply lookup_rel_refl].
      intro y. cbn [type_uses rewrite_binding rewrite_binding_with].
      rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
    + exact Hd'.
    + cbn [result_type computation_demand type_demand_row] in Hrt'', Hcd'', Htd''. subst kind''.
      assert (Hx_not_kind : ~ In x (ty_binders kind)).
      { intro Hin. apply derives_type_demand in Hderiv as [rk [Htd_k _]].
        apply (type_demand_ty_binders_fresh _ _ _ x Htd_k) in Hin.
        apply fresh_cons_inv in Hin as [_ Hin].
        destruct (lookup_split_three (rewrite_binding x arg z) inner x
          {| binder := x; annotation := Natural; type_uses := [] |} outer x
          (fun _ => eq_refl) Hfx_i eq_refl) as [Heq_x _].
        destruct (Heq_x eq_refl) as [Hlkp _]. unfold fresh in Hin. rewrite Hlkp in Hin. discriminate. }
      rewrite substitute_type_distr in Houtput' by (eauto; congruence).
      assert (Hu_x0 : uses u'' x0 = uses u x0).
      { rewrite Hcd'', Hcd', uses_substitute_demand, Hx0_notin_z, Nat.mul_0_r, Nat.add_0_r.
        assert (Hneq' : Nat.eqb x0 x = false) by (apply Nat.eqb_neq; exact Hx0_neq).
        now rewrite Hneq'. }
      eexists. split.
      * eapply GradeLetNat; [exact Hx0_fresh_after | exact Hz0' | exact Hd'' | rewrite Hu_x0; exact H1 | exact Houtput' |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | eapply same_demand_trans; eassumption] |].
        eapply same_demand_trans; [apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact H3] | apply same_demand_sym; exact Hsout].
      * cbn [result_type computation_demand type_demand_row].
        split; [symmetry; apply substitute_type_distr; eauto; congruence | split].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [exact Hsz0 | apply same_demand_without_compat; eapply same_demand_trans; eassumption].
           ++ eapply same_demand_trans.
              ** apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_without; [congruence | exact Hx0_notin_z]].
              ** apply same_demand_sym, substitute_demand_app.
        -- eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | eapply same_demand_trans; eassumption] |].
           apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z].
  - (* GradeApplyType *)
    destruct (IHHderiv inner Hfx_i Hnoshad eq_refl) as [res_c' [Hdc' [Hrtc' [Hcdc' Htdc']]]].
    destruct res_c' as [rt_c' w' v'].
    cbn [result_type computation_demand type_demand_row] in Hrtc', Hcdc', Htdc'.
    rewrite Hrtc' in Hdc'. cbn [substitute_type] in Hdc'.
    destruct (lookup_split_three (rewrite_binding x arg z) inner x
      {| binder := x; annotation := Natural; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0)
      by (eapply index_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    destruct (subst_type_demand outer arg z inner x argument z0 Harg Hfx_o Hfx_i Hnoshad H0)
      as [z0' [Hz0' Hsz0]].
    assert (Hul' : UniverseLevel (map (rewrite_binding x arg z) inner ++ outer) (substitute_type x arg argument) level)
      by (apply universe_level_subst_nat; assumption).
    assert (Hfx_i' : fresh ({| binder := x0; annotation := Universe level; type_uses := [] |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := Universe level; type_uses := [] |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    destruct (subst_type_demand outer arg z ({| binder := x0; annotation := Universe level; type_uses := [] |} :: inner) x codomain b Harg Hfx_o Hfx_i' Hnoshad' H2)
      as [b' [Hb' Hsb]].
    destruct (subst_type_demand outer arg z inner x (substitute_type_variable x0 argument codomain) output Harg Hfx_o Hfx_i Hnoshad H3)
      as [output' [Houtput' Hsout]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Hdc'.
    assert (Hb'' : TypeDemand ({| binder := x0; annotation := Universe level; type_uses := [] |} :: map (rewrite_binding x arg z) inner ++ outer)
                     (substitute_type x arg codomain) b').
    { eapply type_demand_rel; [| exact Hb'].
      apply lookup_rel_cons; [reflexivity | cbn; reflexivity | | apply lookup_rel_refl].
      intro y. cbn [type_uses rewrite_binding rewrite_binding_with].
      rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x). }
    assert (Hx_not_cod : ~ In x (ty_binders codomain)).
    { intro Hin. apply (type_demand_ty_binders_fresh _ _ _ x H2) in Hin.
      apply fresh_cons_inv in Hin as [_ Hin].
      destruct (lookup_split_three (rewrite_binding x arg z) inner x
        {| binder := x; annotation := Natural; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq_x _].
      destruct (Heq_x eq_refl) as [Hlkp _]. unfold fresh in Hin. rewrite Hlkp in Hin. discriminate. }
    rewrite substitute_type_and_var_comm in Houtput' by (eauto; congruence).
    eexists. split.
    + eapply GradeApplyType; [exact Hdc' | exact Hx0_fresh_after | exact Hz0' | exact Hul' | exact Hb'' | exact Houtput' |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | exact Hsb] |].
      eapply same_demand_trans; [apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z] |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact H4] | apply same_demand_sym; exact Hsout].
    + cbn [result_type computation_demand type_demand_row].
      split; [symmetry; apply substitute_type_and_var_comm; eauto; congruence | split].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [exact Hcdc' | apply same_demand_scale_compat; exact Hsz0].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_scale].
           ++ apply same_demand_sym, substitute_demand_app.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | exact Hsb] |].
        apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z].
Qed.

(* Type substitution metatheory *)

Fixpoint ty_free_vars (bound : list nat) (k : ty) : list nat :=
  match k with
  | Natural | Vector _ | Universe _ => []
  | TypeVar x => if existsb (Nat.eqb x) bound then [] else [x]
  | Pi x _ dom cod => ty_free_vars bound dom ++ ty_free_vars (x :: bound) cod
  end.

Lemma index_demand_subst_tvar_env : forall outer arg z inner x lvl i d,
  fresh inner x = true ->
  IndexDemand (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer) i d ->
  IndexDemand (map (rewrite_type_binding x arg z) inner ++ outer) i d.
Proof.
  intros outer arg z inner x lvl i d Hfx_i Hd.
  induction Hd; [| constructor | constructor; assumption].
  destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
    {| binder := x; annotation := Universe lvl; type_uses := [] |} outer x0
    (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
  destruct (Nat.eq_dec x0 x) as [-> | Hx0neq].
  - destruct (Heq eq_refl) as [Hlkp _]. rewrite H in Hlkp. inversion Hlkp; subst. discriminate H0.
  - destruct (Hneq Hx0neq) as [Hnone Hsome].
    destruct (lookup inner x0) as [ei |] eqn:Hi.
    + destruct (Hsome ei eq_refl) as [H1' H2']. rewrite H in H1'. inversion H1'; subst.
      eapply NaturalVariable; [exact H2' | cbn; now rewrite H0].
    + destruct (Hnone eq_refl) as [H1' H2']. rewrite H in H1'.
      eapply NaturalVariable; [rewrite H2', <- H1'; reflexivity | exact H0].
Qed.

Lemma subst_type_var_demand : forall outer arg z inner x lvl kind d,
  TypeDemand outer arg z ->
  fresh outer x = true ->
  fresh inner x = true ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  (forall y, In y (ty_binders arg) -> fresh inner y = true /\ ~ In y (ty_binders kind)) ->
  TypeDemand (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer) kind d ->
  exists d',
    TypeDemand (map (rewrite_type_binding x arg z) inner ++ outer) (substitute_type_variable x arg kind) d' /\
    same_demand d' (substitute_demand x z d).
Proof.
  intros outer arg z inner x lvl kind d Harg Hfx_o Hfx_i Hnoshad Htb_arg Hd.
  remember (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer) as env eqn:Eenv.
  revert inner Hfx_i Hnoshad Htb_arg Eenv.
  induction Hd; intros inner Hfx_i Hnoshad Htb_arg Eenv; subst; cbn [substitute_type_variable].
  - exists []. split; [constructor |].
    intro y. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - assert (Hid : IndexDemand (map (rewrite_type_binding x arg z) inner ++ outer) length d)
      by (eapply index_demand_subst_tvar_env; eassumption).
    exists d. split; [constructor; exact Hid |].
    intro y. rewrite uses_substitute_demand.
    assert (Hux : uses d x = 0).
    { eapply index_demand_absent_use; [exact Hid |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe lvl; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq _].
      destruct (Heq eq_refl) as [_ H2]. rewrite H2.
      unfold fresh in Hfx_o. now destruct (lookup outer x). }
    rewrite Hux, Nat.mul_0_l, Nat.add_0_r.
    destruct (Nat.eqb y x) eqn:Eyx; [apply Nat.eqb_eq in Eyx; subst y; exact Hux | reflexivity].
  - destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe lvl; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_type_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0)
      by (eapply type_demand_absent_use; [exact Harg | exact Hx0_fresh_outer]).
    assert (Htb_dom : forall y, In y (ty_binders arg) -> fresh inner y = true /\ ~ In y (ty_binders domain)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi Hni]. split; [exact Hfi |].
      intro Hin. apply Hni. cbn. right. apply in_or_app. now left. }
    destruct (IHHd1 inner Hfx_i Hnoshad Htb_dom eq_refl) as [a' [Ha' Hsa]].
    assert (Hfx_i' : fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    assert (Htb_arg' : forall y, In y (ty_binders arg) ->
      fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) y = true /\
      ~ In y (ty_binders codomain)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi Hni]. split.
      - apply fresh_cons_intro; [| exact Hfi].
        intro E. cbn in E. subst y. apply Hni. cbn. now left.
      - intro Hin. apply Hni. cbn. right. apply in_or_app. now right. }
    destruct (IHHd2 ({| binder := x0; annotation := domain; type_uses := a |} :: inner) Hfx_i' Hnoshad' Htb_arg' eq_refl)
      as [b' [Hb' Hsb]].
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx.
    exists (a' ++ without x0 b'). split.
    + apply TypePi; [exact Hx0_fresh_after | exact Ha' |].
      eapply type_demand_rel; [| exact Hb'].
      apply lookup_rel_cons; [reflexivity | reflexivity | apply same_demand_sym; exact Hsa |].
      apply lookup_rel_refl.
    + eapply same_demand_trans.
      * apply same_demand_app_compat; [exact Hsa | apply same_demand_without_compat; exact Hsb].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_without; congruence || exact Hx0_notin_z].
        -- apply same_demand_sym, substitute_demand_app.
  - exists []. split; [constructor |].
    intro y. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb y x).
  - destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe lvl; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    destruct (Nat.eqb x x0) eqn:Exx0.
    + apply Nat.eqb_eq in Exx0. subst x0.
      exists z. split.
      * apply type_demand_weaken_app.
        -- apply no_shad_map; [intro; reflexivity | exact Hnoshad].
        -- intros y Hy. destruct (Htb_arg y Hy) as [Hfi _].
           unfold fresh in *. clear -Hfi. induction inner as [| p rest IH]; [reflexivity |].
           cbn in *. destruct (Nat.eqb y (binder p)); [discriminate | apply IH; exact Hfi].
        -- exact Harg.
      * apply same_demand_sym, substitute_demand_var_same.
        eapply type_demand_absent_use; [exact Harg |].
        unfold fresh in Hfx_o. now destruct (lookup outer x).
    + apply Nat.eqb_neq in Exx0.
      assert (Hx0neq : x0 <> x) by congruence.
      destruct (Hneq Hx0neq) as [Hnone Hsome].
      exists [(x0, 1)]. split.
      * destruct (lookup inner x0) as [ei |] eqn:Hi.
        -- destruct (Hsome ei eq_refl) as [H1' H2']. rewrite H in H1'. inversion H1'; subst.
           eapply TypeVariable; [exact H2' |]. cbn. now rewrite H0.
        -- destruct (Hnone eq_refl) as [H1' H2']. rewrite H in H1'.
           eapply TypeVariable; [rewrite H2', <- H1'; reflexivity | exact H0].
      * apply same_demand_sym, substitute_demand_var_other. congruence.
Qed.

Lemma index_demand_ann_equiv : forall env1 env2 i d,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2
             | None, None => True
             | _, _ => False
             end) ->
  IndexDemand env1 i d ->
  IndexDemand env2 i d.
Proof.
  intros env1 env2 i d Hrel Hi.
  induction Hi.
  - specialize (Hrel x). rewrite H in Hrel.
    destruct (lookup env2 x) as [e2 |] eqn:E2; [| contradiction].
    destruct Hrel as [_ Hann].
    eapply NaturalVariable; [exact E2 | rewrite <- Hann; exact H0].
  - constructor.
  - constructor; assumption.
Qed.

Lemma type_demand_ann_equiv : forall env1 env2 k d,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2
             | None, None => True
             | _, _ => False
             end) ->
  TypeDemand env1 k d ->
  TypeDemand env2 k d.
Proof.
  intros env1 env2 k d Hrel Hk. revert env2 Hrel.
  induction Hk; intros env2 Hrel.
  - constructor.
  - constructor. eapply index_demand_ann_equiv; eassumption.
  - constructor.
    + specialize (Hrel x). unfold fresh in *.
      destruct (lookup env x), (lookup env2 x); try contradiction; assumption.
    + eauto.
    + eapply IHHk2. intro y. unfold lookup. cbn [find binder].
      destruct (Nat.eqb y x) eqn:Eyx; [split; reflexivity |].
      fold (lookup env y). fold (lookup env2 y). exact (Hrel y).
  - constructor.
  - specialize (Hrel x). rewrite H in Hrel.
    destruct (lookup env2 x) as [e2 |] eqn:E2; [| contradiction].
    destruct Hrel as [_ Hann].
    eapply TypeVariable; [exact E2 | rewrite <- Hann; exact H0].
Qed.

Lemma subst_universe_level : forall outer arg z inner x lvl kind d k,
  UniverseLevel outer arg lvl ->
  fresh outer x = true ->
  fresh inner x = true ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  TypeDemand (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer) kind d ->
  UniverseLevel (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer) kind k ->
  UniverseLevel (map (rewrite_type_binding x arg z) inner ++ outer) (substitute_type_variable x arg kind) k.
Proof.
  intros outer arg z inner x lvl kind d k Harg Hfx_o Hfx_i Hnoshad Htd Hl.
  remember (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer) as env eqn:Eenv.
  revert inner d Hfx_i Hnoshad Htd Eenv.
  induction Hl; intros inner d Hfx_i Hnoshad Htd Eenv; subst; cbn [substitute_type_variable].
  - constructor.
  - constructor.
  - inversion Htd as [| | ? ? ? ? ? ? Hfr_x0 Htd_dom Htd_cod | |]; subst.
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0.
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe lvl; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq _].
      destruct (Heq eq_refl) as [Hlkp _]. unfold fresh in Hfr_x0. rewrite Hlkp in Hfr_x0. discriminate. }
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx.
    apply LevelPi; [eapply IHHl1; [exact Hfx_i | exact Hnoshad | exact Htd_dom | reflexivity] |].
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in Hfr_x0. rewrite lookup_app_head in Hfr_x0.
      destruct (lookup inner x0); [discriminate |].
      unfold lookup at 1 in Hfr_x0. cbn [find binder] in Hfr_x0.
      assert (Hx0x : Nat.eqb x0 x = false) by (apply Nat.eqb_neq; exact Hx0_neq).
      rewrite Hx0x in Hfr_x0. fold (lookup outer x0) in Hfr_x0.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    eapply universe_level_univ_equiv with
      (env1 := map (rewrite_type_binding x arg z) ({| binder := x0; annotation := domain; type_uses := [] |} :: inner) ++ outer).
    + intros y e1 i0 Hy He1. unfold lookup at 1 in Hy.
      rewrite map_cons, <- app_comm_cons in Hy.
      change (find (fun entry : binding => y =? binder entry)
        (rewrite_type_binding x arg z {| binder := x0; annotation := domain; type_uses := [] |} ::
         (map (rewrite_type_binding x arg z) inner ++ outer))) with
        (if y =? x0 then Some (rewrite_type_binding x arg z {| binder := x0; annotation := domain; type_uses := [] |})
         else lookup (map (rewrite_type_binding x arg z) inner ++ outer) y) in Hy.
      destruct (Nat.eqb y x0) eqn:Eyx0; try rewrite Eyx0 in Hy.
      * unfold rewrite_type_binding, rewrite_binding_with in Hy. cbn [annotation] in Hy.
        inversion Hy; subst. cbn [annotation] in He1.
        exists {| binder := x0; annotation := substitute_type_variable x arg domain; type_uses := [] |}.
        unfold lookup. cbn [find binder]. rewrite Eyx0. split; [reflexivity | exact He1].
      * unfold lookup at 1. cbn [find binder]. rewrite Eyx0.
        fold (lookup (map (rewrite_type_binding x arg z) inner ++ outer) y).
        exists e1. split; [exact Hy | exact He1].
    + eapply (IHHl2 ({| binder := x0; annotation := domain; type_uses := [] |} :: inner)).
      * apply fresh_cons_intro; [cbn; congruence | exact Hfx_i].
      * intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
        intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction.
      * eapply type_demand_ann_equiv; [| exact Htd_cod].
        intro y. unfold lookup. cbn [find binder].
        destruct (Nat.eqb y x0) eqn:Eyx; [split; reflexivity |].
        destruct (find (fun entry : binding => y =? binder entry)
          (inner ++ {| binder := x; annotation := Universe lvl; type_uses := [] |} :: outer));
          [split; reflexivity | exact I].
      * reflexivity.
  - constructor.
  - destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe lvl; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    destruct (Nat.eqb x x0) eqn:Exx0.
    + apply Nat.eqb_eq in Exx0. subst x0.
      destruct (Heq eq_refl) as [Hlkp _]. rewrite H in Hlkp. inversion Hlkp; subst.
      cbn in H0. inversion H0; subst.
      eapply universe_level_mono_lookup; [| exact Harg].
      intros y e Hy. apply lookup_weaken_mono; [| exact Hy].
      apply no_shad_map; [intro; reflexivity | exact Hnoshad].
    + apply Nat.eqb_neq in Exx0.
      assert (Hx0neq : x0 <> x) by congruence.
      destruct (Hneq Hx0neq) as [Hnone Hsome].
      destruct (lookup inner x0) as [ei |] eqn:Hi.
      * destruct (Hsome ei eq_refl) as [H1' H2']. rewrite H in H1'. inversion H1'; subst.
        eapply LevelVariable; [exact H2' |]. cbn. now rewrite H0.
      * destruct (Hnone eq_refl) as [H1' H2']. rewrite H in H1'.
        eapply LevelVariable; [rewrite H2', <- H1'; reflexivity | exact H0].
Qed.

Fixpoint term_var_free (x : nat) (t : term) : bool :=
  match t with
  | Var y => Nat.eqb x y
  | NatValue _ => false
  | Lambda y _ _ body => if Nat.eqb x y then false else term_var_free x body
  | ApplyNat c _ => term_var_free x c
  | ApplyValue c a => term_var_free x c || term_var_free x a
  | LetNat y _ _ body => if Nat.eqb x y then false else term_var_free x body
  | ApplyType c _ => term_var_free x c
  end.

Fixpoint substitute_type_var_in_term (x : nat) (arg : ty) (t : term) : term :=
  match t with
  | Var y => Var y
  | NatValue i => NatValue i
  | Lambda y allowance domain body =>
      Lambda y allowance (substitute_type_variable x arg domain)
        (if Nat.eqb x y then body else substitute_type_var_in_term x arg body)
  | ApplyNat callee idx =>
      ApplyNat (substitute_type_var_in_term x arg callee) idx
  | ApplyValue callee argument =>
      ApplyValue (substitute_type_var_in_term x arg callee) (substitute_type_var_in_term x arg argument)
  | LetNat y allowance initializer body =>
      LetNat y allowance initializer
        (if Nat.eqb x y then body else substitute_type_var_in_term x arg body)
  | ApplyType callee ty_arg =>
      ApplyType (substitute_type_var_in_term x arg callee) (substitute_type_variable x arg ty_arg)
  end.

Lemma index_demand_subst_absent : forall env i d x ty_arg,
  IndexDemand env i d ->
  lookup env x = None ->
  substitute_index x ty_arg i = i.
Proof.
  intros env i d x ty_arg Hi Hnone.
  induction Hi; cbn; try reflexivity.
  - destruct (Nat.eqb x x0) eqn:Ex; [apply Nat.eqb_eq in Ex; subst; rewrite H in Hnone; discriminate | reflexivity].
  - now rewrite IHHi1, IHHi2.
Qed.

Lemma type_demand_subst_nat_absent : forall env arg z x ty_arg,
  TypeDemand env arg z ->
  lookup env x = None ->
  substitute_type x ty_arg arg = arg.
Proof.
  intros env arg z x ty_arg Hd Hnone.
  induction Hd; cbn; try reflexivity.
  - f_equal. eapply index_demand_subst_absent; eassumption.
  - rewrite IHHd1 by exact Hnone.
    destruct (Nat.eqb x x0) eqn:Ex; [reflexivity |].
    f_equal. apply IHHd2. unfold lookup at 1. cbn [find binder].
    rewrite Ex. exact Hnone.
Qed.

Lemma substitute_type_and_var_comm2 : forall x arg y ty_arg kind,
  x <> y ->
  ~ In x (ty_binders kind) ->
  ~ In y (ty_binders kind) ->
  substitute_type y ty_arg arg = arg ->
  substitute_type_variable x arg (substitute_type y ty_arg kind) =
  substitute_type y ty_arg (substitute_type_variable x arg kind).
Proof.
  intros x arg y ty_arg kind Hneq Hx Hy Hfix.
  induction kind as [| len | x0 allow dom IH1 cod IH2 | lvl | v]; cbn in *; try reflexivity.
  - assert (Hx0 : x0 <> x) by (intro E; apply Hx; now left).
    assert (Hy0 : x0 <> y) by (intro E; apply Hy; now left).
    assert (Ex0 : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    assert (Ey0 : Nat.eqb y x0 = false) by (apply Nat.eqb_neq; congruence).
    assert (Hx1 : ~ In x (ty_binders dom)) by (intro H; apply Hx; right; apply in_or_app; now left).
    assert (Hx2 : ~ In x (ty_binders cod)) by (intro H; apply Hx; right; apply in_or_app; now right).
    assert (Hy1 : ~ In y (ty_binders dom)) by (intro H; apply Hy; right; apply in_or_app; now left).
    assert (Hy2 : ~ In y (ty_binders cod)) by (intro H; apply Hy; right; apply in_or_app; now right).
    rewrite Ex0, Ey0. cbn. rewrite (IH1 Hx1 Hy1), (IH2 Hx2 Hy2). reflexivity.
  - destruct (Nat.eqb x v); [symmetry; exact Hfix | reflexivity].
Qed.

Lemma subst_tvar_distr : forall x arg x0 ty_arg kind,
  x <> x0 ->
  ~ In x0 (ty_free_vars [] arg) ->
  ~ In x (ty_binders kind) ->
  ~ In x0 (ty_binders kind) ->
  substitute_type_variable x arg (substitute_type_variable x0 ty_arg kind) =
  substitute_type_variable x0 (substitute_type_variable x arg ty_arg) (substitute_type_variable x arg kind).
Proof.
  intros x arg x0 ty_arg kind Hneq Hnotin Hbx Hb0.
  induction kind; cbn in *; try reflexivity.
  - assert (Hx1 : x <> x1) by (intro E; apply Hbx; now left).
    assert (Hx01 : x0 <> x1) by (intro E; apply Hb0; now left).
    assert (Ex1 : Nat.eqb x x1 = false) by (apply Nat.eqb_neq; exact Hx1).
    assert (Ex01 : Nat.eqb x0 x1 = false) by (apply Nat.eqb_neq; exact Hx01).
    rewrite Ex1, Ex01. cbn.
    f_equal.
    + apply IHkind1; intro Hin; [apply Hbx | apply Hb0]; right; apply in_or_app; now left.
    + apply IHkind2; intro Hin; [apply Hbx | apply Hb0]; right; apply in_or_app; now right.
  - destruct (Nat.eqb x0 x1) eqn:E0; destruct (Nat.eqb x x1) eqn:Ex; cbn.
    + apply Nat.eqb_eq in E0. apply Nat.eqb_eq in Ex. congruence.
    + now rewrite E0.
    + rewrite Ex. clear E0 Ex.
      assert (Hgen : forall a bnd, ~ In x0 bnd -> ~ In x0 (ty_free_vars bnd a) ->
        substitute_type_variable x0 (substitute_type_variable x arg ty_arg) a = a).
      { intros a. induction a as [| ? | xb allow a1 IHa1 a2 IHa2 | ? | xv]; intros bnd Hbnd Hnf; cbn in *; try reflexivity.
        - assert (Hnf1 : ~ In x0 (ty_free_vars bnd a1)) by (intro; apply Hnf; apply in_or_app; now left).
          assert (Hnf2 : ~ In x0 (ty_free_vars (xb :: bnd) a2)) by (intro; apply Hnf; apply in_or_app; now right).
          rewrite (IHa1 bnd Hbnd Hnf1).
          destruct (Nat.eqb x0 xb) eqn:Ex1; [reflexivity |].
          f_equal. apply (IHa2 (xb :: bnd)); [intros [<- | ?]; [apply Nat.eqb_neq in Ex1; congruence | contradiction] | exact Hnf2].
        - destruct (Nat.eqb x0 xv) eqn:Ex1; [| reflexivity].
          apply Nat.eqb_eq in Ex1. subst xv.
          destruct (existsb (Nat.eqb x0) bnd) eqn:Eex.
          + apply existsb_exists in Eex as [z [Hz Heq]]. apply Nat.eqb_eq in Heq. subst z. contradiction.
          + exfalso. apply Hnf. now left. }
      symmetry. apply (Hgen arg [] (fun H => H) Hnotin).
    + now rewrite E0, Ex.
Qed.

Lemma type_demand_absent_tvar : forall env arg z x0,
  TypeDemand env arg z ->
  lookup env x0 = None ->
  ~ In x0 (ty_free_vars [] arg).
Proof.
  intros env arg z x0 Hd Hnone.
  assert (Hgen : forall bnd, In x0 bnd \/ lookup env x0 = None -> ~ In x0 (ty_free_vars bnd arg)).
  { clear -Hd. induction Hd; intros bnd Hor; cbn; try exact (fun H => H).
    - intro Hin. apply in_app_or in Hin as [H1 | H2].
      + eapply IHHd1; [exact Hor | exact H1].
      + eapply IHHd2; [| exact H2].
        destruct (Nat.eq_dec x0 x) as [<- | Hneq]; [left; now left |].
        destruct Hor as [Hb | Hn]; [left; now right | right; cbn; apply Nat.eqb_neq in Hneq; rewrite Hneq; exact Hn].
    - destruct (existsb (Nat.eqb x) bnd) eqn:Eex; [cbn; exact (fun H => H) |].
      cbn. intros [-> | []].
      destruct Hor as [Hb | Hn].
      + assert (E : existsb (Nat.eqb x0) bnd = true) by (apply existsb_exists; exists x0; rewrite Nat.eqb_refl; auto).
        congruence.
      + congruence. }
  apply (Hgen [] (or_intror Hnone)).
Qed.

Fixpoint ty_index_vars (k : ty) : list nat :=
  match k with
  | Natural | Universe _ | TypeVar _ => []
  | Vector len => index_vars len
  | Pi _ _ dom cod => ty_index_vars dom ++ ty_index_vars cod
  end.

Lemma type_demand_index_vars_lookup : forall env k d y,
  TypeDemand env k d ->
  In y (ty_index_vars k) ->
  In y (ty_binders k) \/ exists entry, lookup env y = Some entry.
Proof.
  intros env k d y Hd. induction Hd; cbn; try contradiction.
  - intro Hin. right.
    destruct (index_demand_uses_bound env length d y H) as [_ Hl].
    destruct (Hl Hin) as [entry [He _]]. exists entry. exact He.
  - intro Hin. apply in_app_or in Hin as [Hin | Hin].
    + destruct (IHHd1 Hin) as [Hb | [e He]]; [left; right; apply in_or_app; now left | now right; exists e].
    + destruct (IHHd2 Hin) as [Hb | [e He]]; [left; right; apply in_or_app; now right |].
      cbn in He. destruct (Nat.eqb y x) eqn:Eyx.
      * apply Nat.eqb_eq in Eyx. left; now left.
      * right. exists e. exact He.
Qed.

Lemma in_ty_free_vars_gen : forall bnd k v,
  In v (ty_free_vars bnd k) <-> (~ In v bnd /\ In v (ty_free_vars [] k)).
Proof.
  intros bnd k v. revert bnd. induction k; intros bnd; cbn; try tauto.
  - rewrite !in_app_iff, IHk1, (IHk2 (x :: bnd)), (IHk2 [x]).
    cbn. split.
    + intros [[Hb H1] | [Hnx H2]].
      * split; [exact Hb | left; exact H1].
      * split; [intro Hin; apply Hnx; now right | right; split; [intros [-> | []]; apply Hnx; now left | exact H2]].
    + intros [Hb [H1 | [Hnx H2]]]; [left; split; assumption |].
      right. split; [intros [<- | ?]; [apply Hnx; now left | contradiction] | exact H2].
  - destruct (existsb (Nat.eqb x) bnd) eqn:Eex; cbn.
    + apply existsb_exists in Eex as [z [Hz Heq]]. apply Nat.eqb_eq in Heq. subst z.
      split; [contradiction | intros [Hb [-> | []]]; contradiction].
    + split; [intros [<- | []]; split; [| now left] | intros [_ [<- | []]]; now left].
      intro Hin. assert (Et : existsb (Nat.eqb x) bnd = true) by (apply existsb_exists; exists x; rewrite Nat.eqb_refl; auto).
      congruence.
Qed.

Lemma in_ty_free_index_vars_gen : forall bnd k v,
  In v (ty_free_index_vars bnd k) <-> (~ In v bnd /\ In v (ty_free_index_vars [] k)).
Proof.
  intros bnd k v. revert bnd. induction k; intros bnd; cbn; try tauto.
  - rewrite !filter_In. cbn.
    destruct (existsb (Nat.eqb v) bnd) eqn:Eex; cbn.
    + apply existsb_exists in Eex as [z [Hz Heq]]. apply Nat.eqb_eq in Heq. subst z.
      split; [intros [_ [=]] | intros [? _]; contradiction].
    + split; [intros [Hin _]; split; [| split; auto] | intros [_ [Hin _]]; split; auto].
      intro Hin2. assert (Et : existsb (Nat.eqb v) bnd = true) by (apply existsb_exists; exists v; rewrite Nat.eqb_refl; auto).
      congruence.
  - rewrite !in_app_iff, IHk1, (IHk2 (x :: bnd)), (IHk2 [x]).
    cbn. split.
    + intros [[Hb H1] | [Hnx H2]].
      * split; [exact Hb | left; exact H1].
      * split; [intro Hin; apply Hnx; now right | right; split; [intros [-> | []]; apply Hnx; now left | exact H2]].
    + intros [Hb [H1 | [Hnx H2]]]; [left; split; assumption |].
      right. split; [intros [<- | ?]; [apply Hnx; now left | contradiction] | exact H2].
Qed.

Lemma canonical_type_congr_names : forall arg names1 names2 bnd,
  length names1 = length names2 ->
  (forall v, In v (ty_free_vars bnd arg) -> ~ In v (map fst names1) /\ ~ In v (map fst names2)) ->
  (forall v, In v (ty_free_index_vars bnd arg) -> ~ In v (map fst names1) /\ ~ In v (map fst names2)) ->
  (forall v, In v bnd -> find (fun p => Nat.eqb v (fst p)) names1 = find (fun p => Nat.eqb v (fst p)) names2) ->
  canonical_type names1 arg = canonical_type names2 arg.
Proof.
  intros arg. induction arg; intros names1 names2 bnd Hlen Hfv Hidx Hbnd; cbn in *.
  - reflexivity.
  - f_equal. induction length; cbn in *; try reflexivity.
    + destruct (existsb (Nat.eqb x) bnd) eqn:Eex.
      * apply existsb_exists in Eex as [z [Hz Heq]]. apply Nat.eqb_eq in Heq. subst z.
        unfold canonical_index. now rewrite (Hbnd x Hz).
      * unfold canonical_index.
        destruct (Hidx x (or_introl eq_refl)) as [H1 H2].
        destruct (find (fun p => Nat.eqb x (fst p)) names1) eqn:F1;
        destruct (find (fun p => Nat.eqb x (fst p)) names2) eqn:F2; try reflexivity; exfalso.
        -- apply H1. apply find_some in F1 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
        -- apply H1. apply find_some in F1 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
        -- apply H2. apply find_some in F2 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
    + f_equal; [apply IHlength1 | apply IHlength2]; intros v Hv;
        apply Hidx; rewrite !filter_In in *; rewrite in_app_iff; tauto.
  - rewrite Hlen. f_equal.
    + eapply IHarg1; eauto; intros v Hv; [apply Hfv | apply Hidx]; apply in_or_app; now left.
    + eapply IHarg2 with (bnd := x :: bnd).
      * cbn. congruence.
      * intros v Hv. apply in_ty_free_vars_gen in Hv as [Hnbnd H0].
        assert (Hvnx : v <> x) by (intro; apply Hnbnd; now left).
        assert (Hfv_v : ~ In v (map fst names1) /\ ~ In v (map fst names2)).
        { apply Hfv. apply in_or_app. right. apply in_ty_free_vars_gen.
          split; [intros [<- | Hin]; [congruence | apply Hnbnd; now right] | exact H0]. }
        cbn. destruct Hfv_v as [H1 H2].
        split; [intros [-> | Hin]; [congruence | exact (H1 Hin)] | intros [-> | Hin]; [congruence | exact (H2 Hin)]].
      * intros v Hv. apply in_ty_free_index_vars_gen in Hv as [Hnbnd H0].
        assert (Hvnx : v <> x) by (intro; apply Hnbnd; now left).
        assert (Hidx_v : ~ In v (map fst names1) /\ ~ In v (map fst names2)).
        { apply Hidx. apply in_or_app. right. apply in_ty_free_index_vars_gen.
          split; [intros [<- | Hin]; [congruence | apply Hnbnd; now right] | exact H0]. }
        cbn. destruct Hidx_v as [H1 H2].
        split; [intros [-> | Hin]; [congruence | exact (H1 Hin)] | intros [-> | Hin]; [congruence | exact (H2 Hin)]].
      * intros v [<- | Hv]; cbn.
        -- rewrite Nat.eqb_refl. congruence.
        -- destruct (Nat.eqb v x); [congruence | apply Hbnd; exact Hv].
  - reflexivity.
  - destruct (existsb (Nat.eqb x) bnd) eqn:Eex.
    + apply existsb_exists in Eex as [z [Hz Heq]]. apply Nat.eqb_eq in Heq. subst z.
      unfold canonical_index. now rewrite (Hbnd x Hz).
    + unfold canonical_index.
      destruct (Hfv x (or_introl eq_refl)) as [H1 H2].
      destruct (find (fun p => Nat.eqb x (fst p)) names1) eqn:F1;
      destruct (find (fun p => Nat.eqb x (fst p)) names2) eqn:F2; try reflexivity; exfalso.
      * apply H1. apply find_some in F1 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
      * apply H1. apply find_some in F1 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
      * apply H2. apply find_some in F2 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
Qed.

Lemma canonical_type_subst_tvar_preserves : forall k1 k2 names1 names2 x arg,
  length names1 = length names2 ->
  ~ In x (map fst names1) -> ~ In x (map fst names2) ->
  (forall b, In b (map fst names1) -> ~ In b (ty_free_vars [] arg) /\ ~ In b (ty_index_vars arg)) ->
  (forall b, In b (map fst names2) -> ~ In b (ty_free_vars [] arg) /\ ~ In b (ty_index_vars arg)) ->
  (forall b, In b (ty_binders k1) -> b <> x /\ ~ In b (ty_free_vars [] arg) /\ ~ In b (ty_index_vars arg)) ->
  (forall b, In b (ty_binders k2) -> b <> x /\ ~ In b (ty_free_vars [] arg) /\ ~ In b (ty_index_vars arg)) ->
  canonical_type names1 k1 = canonical_type names2 k2 ->
  canonical_type names1 (substitute_type_variable x arg k1) =
  canonical_type names2 (substitute_type_variable x arg k2).
Proof.
  intros k1.
  induction k1 as [| len1 | x0 allow1 d1 IH1 c1 IH2 | l1 | x0];
    intros k2 names1 names2 x arg Hlen Hx1 Hx2 Hn1 Hn2 Hk1 Hk2 Hcanon;
    destruct k2; cbn in *; try discriminate; try reflexivity.
  - inversion Hcanon; subst. reflexivity.
  - inversion Hcanon; subst.
    assert (Hx0_1 : x0 <> x) by (destruct (Hk1 x0 (or_introl eq_refl)); assumption).
    assert (Hx1_2 : x1 <> x) by (destruct (Hk2 x1 (or_introl eq_refl)); assumption).
    assert (Ex0 : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    assert (Ex1 : Nat.eqb x x1 = false) by (apply Nat.eqb_neq; congruence).
    rewrite Ex0, Ex1. cbn [substitute_type_variable canonical_type]. f_equal.
    + eapply IH1; eauto; intros b Hb; [apply Hk1 | apply Hk2]; right; apply in_or_app; now left.
    + eapply IH2; eauto; cbn.
      * congruence.
      * intros [-> | Hin]; [congruence | auto].
      * intros [-> | Hin]; [congruence | auto].
      * intros b [<- | Hin]; [destruct (Hk1 x0 (or_introl eq_refl)); tauto | auto].
      * intros b [<- | Hin]; [destruct (Hk2 x1 (or_introl eq_refl)); tauto | auto].
      * intros b Hb. apply Hk1. right. apply in_or_app. now right.
      * intros b Hb. apply Hk2. right. apply in_or_app. now right.
  - inversion Hcanon; subst. reflexivity.
  - inversion Hcanon as [Hci].
    destruct (Nat.eqb x x0) eqn:Ex0; destruct (Nat.eqb x x1) eqn:Ex1.
    + eapply canonical_type_congr_names with (bnd := []); eauto.
      * intros v Hv. split; intro Hin; [exact (proj1 (Hn1 v Hin) Hv) | exact (proj1 (Hn2 v Hin) Hv)].
      * intros v Hv.
        assert (Hv_idx : In v (ty_index_vars arg)).
        { clear -Hv. induction arg; cbn in *; try contradiction.
          - apply filter_In in Hv as [Hv _]. exact Hv.
          - apply in_app_or in Hv as [H | H]; apply in_or_app; [left; auto |].
            apply in_ty_free_index_vars_gen in H as [_ H0]. right; auto. }
        split; intro Hin; [exact (proj2 (Hn1 v Hin) Hv_idx) | exact (proj2 (Hn2 v Hin) Hv_idx)].
      * intros v [].
    + exfalso. apply Nat.eqb_eq in Ex0. subst x0.
      unfold canonical_index in Hci.
      destruct (find (fun b => Nat.eqb x (fst b)) names1) eqn:F1.
      * apply Hx1. apply find_some in F1 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
      * destruct (find (fun b => Nat.eqb x1 (fst b)) names2); try lia.
        apply Nat.eqb_neq in Ex1. lia.
    + exfalso. apply Nat.eqb_eq in Ex1. subst x1.
      unfold canonical_index in Hci.
      destruct (find (fun b => Nat.eqb x (fst b)) names2) eqn:F2.
      * apply Hx2. apply find_some in F2 as [Hin Hm]. apply Nat.eqb_eq in Hm. rewrite Hm. apply in_map, Hin.
      * destruct (find (fun b => Nat.eqb x0 (fst b)) names1); try lia.
        apply Nat.eqb_neq in Ex0. lia.
    + cbn. now rewrite Hci.
Qed.

Lemma ty_binders_subst_nat : forall x i k,
  ty_binders (substitute_type x i k) = ty_binders k.
Proof.
  intros x i k. induction k; cbn; try reflexivity.
  f_equal. rewrite IHk1. destruct (Nat.eqb x x0); [reflexivity | f_equal; exact IHk2].
Qed.

Lemma in_ty_binders_subst_tvar : forall y x arg k,
  In y (ty_binders (substitute_type_variable x arg k)) ->
  In y (ty_binders k) \/ In y (ty_binders arg).
Proof.
  intros y x arg k. induction k; cbn; try tauto.
  - intros [<- | H]; [left; now left |].
    apply in_app_or in H as [H | H].
    + destruct (IHk1 H); [left; right; apply in_or_app; now left | now right].
    + destruct (Nat.eqb x x0).
      * left; right; apply in_or_app; now right.
      * destruct (IHk2 H); [left; right; apply in_or_app; now right | now right].
  - destruct (Nat.eqb x x0); [intros; now right | cbn; contradiction].
Qed.

Lemma type_demand_lookup_not_bound : forall env k d y,
  TypeDemand env k d ->
  lookup env y <> None ->
  ~ In y (ty_binders k).
Proof.
  intros env k d y Hd Hlkp Hin.
  apply (type_demand_ty_binders_fresh _ _ _ y Hd) in Hin.
  unfold fresh in Hin. destruct (lookup env y); [discriminate | congruence].
Qed.

Lemma same_demand_subst_unfold_compat : forall d1 x z d2,
  same_demand d1 (filter (fun entry : nat * nat => negb (x =? fst entry)) d2 ++ scale (uses d2 x) z) ->
  same_demand d1 (substitute_demand x z d2).
Proof. intros d1 x z d2 H y. apply H. Qed.

Lemma scale_zero_uses : forall d k, uses (scale 0 d) k = 0.
Proof.
  intros d k. induction d as [| [? ?] rest IH]; cbn; [reflexivity | now destruct (Nat.eqb k _)].
Qed.

Theorem type_substitution_derives : forall allows outer arg z inner x level t res,
  context_wf outer ->
  TypeDemand outer arg z ->
  UniverseLevel outer arg level ->
  fresh outer x = true ->
  fresh inner x = true ->
  (forall y, lookup outer y <> None -> fresh inner y = true) ->
  (forall y, In y (ty_binders arg) ->
    fresh inner y = true /\
    ~ In y (term_binders t) /\
    ~ In y (context_ty_binders (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))) ->
  term_var_free x t = false ->
  DerivesWith allows (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) t res ->
  exists res',
    DerivesWith allows (map (rewrite_type_binding x arg z) inner ++ outer) (substitute_type_var_in_term x arg t) res' /\
    result_type res' = substitute_type_variable x arg (result_type res) /\
    same_demand (computation_demand res') (substitute_demand x z (computation_demand res)) /\
    same_demand (type_demand_row res') (substitute_demand x z (type_demand_row res)).
Proof.
  intros allows outer arg z inner x level t res Hwf Harg Hlvl Hfx_o Hfx_i Hnoshad Htb_arg Htvf Hderiv.
  remember (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) as env eqn:Eenv.
  revert inner Hfx_i Hnoshad Htb_arg Htvf Eenv.
  induction Hderiv; intros inner Hfx_i Hnoshad Htb_arg Htvf Eenv; subst; cbn in *.
  - (* GradeVar *)
    destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe level; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    destruct (Nat.eqb x x0) eqn:Exx0; [discriminate Htvf |].
    apply Nat.eqb_neq in Exx0.
    assert (Hx0neq : x0 <> x) by congruence.
    destruct (Hneq Hx0neq) as [Hnone Hsome].
    destruct (lookup inner x0) as [ei |] eqn:Hi.
    + destruct (Hsome ei eq_refl) as [H1' H2']. rewrite H in H1'. inversion H1'; subst.
      assert (Htb_entry : forall y, In y (ty_binders arg) ->
        fresh inner y = true /\ ~ In y (ty_binders (annotation ei))).
      { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [_ Hci]]. split; [exact Hfi |].
        eapply not_in_context_ty_binders_lookup; [exact Hci | exact H]. }
      destruct (subst_type_var_demand outer arg z inner x level (annotation ei) row Harg Hfx_o Hfx_i Hnoshad Htb_entry H0)
        as [row' [Hrow' Hsrow]].
      eexists. split.
      * eapply GradeVar; [exact H2' | exact Hrow' |].
        cbn. eapply same_demand_trans;
          [apply same_demand_substitute_compat; [apply same_demand_refl | exact H1] | apply same_demand_sym; exact Hsrow].
      * split; [cbn; reflexivity | split].
        -- intro k. cbn [computation_demand]. rewrite uses_append. cbn [negb Nat.add]. rewrite scale_zero_uses. lia.
        -- cbn [type_demand_row]. apply same_demand_refl.
    + destruct (Hnone eq_refl) as [H1' H2']. rewrite H in H1'.
      destruct (Hwf x0 entry (eq_sym H1')) as [ro [Htd_o Hsd_o]].
      assert (Hx_none_o : lookup outer x = None) by (unfold fresh in Hfx_o; now destruct (lookup outer x)).
      assert (Hux_ro : uses ro x = 0) by (eapply type_demand_absent_use; eassumption).
      assert (Hux_tu : uses (type_uses entry) x = 0) by (rewrite Hsd_o; exact Hux_ro).
      assert (Hsubst_ann : substitute_type_variable x arg (annotation entry) = annotation entry)
        by (eapply zero_type_var_use_local; eassumption).
      assert (Hweak_row : TypeDemand (map (rewrite_type_binding x arg z) inner ++ outer) (annotation entry) ro).
      { apply type_demand_weaken_app.
        - apply no_shad_map; [intro; reflexivity | exact Hnoshad].
        - intros k Hk. apply (type_demand_ty_binders_fresh _ _ _ k H0) in Hk.
          unfold fresh in Hk. rewrite lookup_app_head in Hk.
          assert (Hki : fresh inner k = true) by (unfold fresh; destruct (lookup inner k); [discriminate | reflexivity]).
          clear -Hki. induction inner as [| p rest IH]; [reflexivity |].
          unfold fresh in Hki |- *. unfold lookup in Hki |- *. cbn [map find binder] in Hki |- *.
          unfold rewrite_type_binding, rewrite_binding_with at 1. cbn [binder].
          destruct (Nat.eqb k (binder p)) eqn:Ek; try rewrite Ek in Hki; [discriminate | apply IH; exact Hki].
        - exact Htd_o. }
      eexists. split.
      * eapply GradeVar; [rewrite H2', <- H1'; reflexivity | exact Hweak_row | exact Hsd_o].
      * split; [cbn; congruence |].
        split.
        -- intro k. cbn [computation_demand].
           replace (x =? x0) with false by (symmetry; apply Nat.eqb_neq; congruence).
           cbn [negb Nat.add]. rewrite uses_append, scale_zero_uses. lia.
        -- cbn [type_demand_row].
           fold (substitute_demand x z (type_uses entry)).
           apply same_demand_sym, zero_use_preserves_row_local; exact Hux_tu.
  - (* GradeNat *)
    assert (Hid : IndexDemand (map (rewrite_type_binding x arg z) inner ++ outer) i d)
      by (eapply index_demand_subst_tvar_env; eassumption).
    assert (Hd_ux : uses d x = 0).
    { eapply index_demand_absent_use; [exact Hid |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe level; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq' _].
      destruct (Heq' eq_refl) as [_ H2']. rewrite H2'. unfold fresh in Hfx_o. now destruct (lookup outer x). }
    eexists. split; [apply GradeNat; exact Hid |].
    split; [cbn; reflexivity | split].
    + cbn [computation_demand]. fold (substitute_demand x z d).
      apply same_demand_sym, zero_use_preserves_row_local; exact Hd_ux.
    + cbn [type_demand_row].
      intro y. clear. induction z as [| [k m] rest IH]; cbn; [reflexivity | now destruct (Nat.eqb y k)].
  - (* GradeLambda *)
    destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe level; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Htvf |- *.
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_type_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0) by (eapply type_demand_absent_use; eassumption).
    assert (Htb_dom : forall y, In y (ty_binders arg) -> fresh inner y = true /\ ~ In y (ty_binders domain)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti _]]. split; [exact Hfi |].
      intro Hin. apply Hti. right. apply in_or_app. now left. }
    destruct (subst_type_var_demand outer arg z inner x level domain a Harg Hfx_o Hfx_i Hnoshad Htb_dom H0)
      as [a' [Ha' Hsa]].
    assert (Hfx_i' : fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    assert (Htb_arg' : forall y, In y (ty_binders arg) ->
      fresh ({| binder := x0; annotation := domain; type_uses := a |} :: inner) y = true /\
      ~ In y (term_binders body) /\
      ~ In y (context_ty_binders ({| binder := x0; annotation := domain; type_uses := a |} :: inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. repeat split.
      - apply fresh_cons_intro; [| exact Hfi].
        intro E. cbn in E. subst y. apply Hti. now left.
      - intro Hin. apply Hti. right. apply in_or_app. now right.
      - unfold context_ty_binders in *. cbn [flat_map annotation].
        intro Hin. apply in_app_or in Hin as [Hin | Hin]; [apply Hti; right; apply in_or_app; now left | apply Hci; exact Hin]. }
    destruct (IHHderiv ({| binder := x0; annotation := domain; type_uses := a |} :: inner)
                Hfx_i' Hnoshad' Htb_arg' Htvf eq_refl)
      as [[cod' u' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    cbn in Hrt', Hcd', Htd'.
    apply same_demand_subst_unfold_compat in Hcd'.
    apply same_demand_subst_unfold_compat in Htd'.
    destruct (derives_same_type_uses allows
      (rewrite_type_binding x arg z {| binder := x0; annotation := domain; type_uses := a |} :: map (rewrite_type_binding x arg z) inner ++ outer)
      ({| binder := x0; annotation := substitute_type_variable x arg domain; type_uses := a' |} :: map (rewrite_type_binding x arg z) inner ++ outer)
      (substitute_type_var_in_term x arg body)
      {| result_type := cod'; computation_demand := u'; type_demand_row := v' |})
      as [[cod'' u'' v''] [Hd'' [Hrt'' [Hcd'' Htd'']]]].
    + apply lookup_rel_cons; [reflexivity | reflexivity | apply same_demand_sym; exact Hsa |].
      apply lookup_rel_refl.
    + exact Hd'.
    + cbn in Hrt'', Hcd'', Htd''.
      eexists. split.
      * eapply GradeLambda; [exact Hx0_fresh_after | exact Ha' | exact Hd'' |].
        rewrite Hcd'', Hcd', uses_substitute_demand, Hx0_notin_z, Nat.mul_0_r, Nat.add_0_r.
        cbn. rewrite Nat.eqb_sym, HEq_nx. exact H1.
      * split; [cbn; rewrite Hrt'', Hrt'; reflexivity | split; cbn].
        -- eapply same_demand_trans.
           ++ apply same_demand_without_compat. eapply same_demand_trans; eassumption.
           ++ apply same_demand_sym, substitute_demand_without; [congruence | exact Hx0_notin_z].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [exact Hsa | apply same_demand_without_compat; eapply same_demand_trans; eassumption].
           ++ eapply same_demand_trans.
              ** apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_without; [congruence | exact Hx0_notin_z]].
              ** apply same_demand_sym, substitute_demand_app.
  - (* GradeApplyNat *)
    destruct (IHHderiv inner Hfx_i Hnoshad Htb_arg Htvf eq_refl) as [[rt_c' w' v'] [Hdc' [Hrtc' [Hcdc' Htdc']]]].
    apply same_demand_subst_unfold_compat in Hcdc'.
    apply same_demand_subst_unfold_compat in Htdc'.
    cbn in Hrtc', Hcdc', Htdc'. rewrite Hrtc' in Hdc'. cbn in Hdc'.
    destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe level; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_type_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0) by (eapply type_demand_absent_use; eassumption).
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Hdc'.
    assert (Hz0' : IndexDemand (map (rewrite_type_binding x arg z) inner ++ outer) argument z0)
      by (eapply index_demand_subst_tvar_env; eassumption).
    assert (Hfx_i' : fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    assert (Hcod_tb : forall y, In y (ty_binders arg) -> ~ In y (ty_binders codomain)).
    { intros y Hy Hin. destruct (Htb_arg y Hy) as [_ [Hti Hci]].
      destruct (ty_binders_derives_sub _ _ _ _ y Hderiv) as [Hd | Hd].
      - cbn. right. exact Hin.
      - exact (Hti Hd).
      - exact (Hci Hd). }
    assert (Htb_arg' : forall y, In y (ty_binders arg) ->
      fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) y = true /\
      ~ In y (ty_binders codomain)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. split; [| apply Hcod_tb; exact Hy].
      apply fresh_cons_intro; [| exact Hfi].
      intro E. cbn in E. subst y.
      destruct (ty_binders_derives_sub _ _ _ _ x0 Hderiv) as [Hd | Hd]; [cbn; now left | exact (Hti Hd) | exact (Hci Hd)]. }
    assert (Htb_sub : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\ ~ In y (ty_binders (substitute_type x0 argument codomain))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi _]. split; [exact Hfi |].
      rewrite ty_binders_subst_nat. apply Hcod_tb; exact Hy. }
    destruct (subst_type_var_demand outer arg z ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) x level codomain b Harg Hfx_o Hfx_i' Hnoshad' Htb_arg' H1)
      as [b' [Hb' Hsb]].
    destruct (subst_type_var_demand outer arg z inner x level (substitute_type x0 argument codomain) output Harg Hfx_o Hfx_i Hnoshad Htb_sub H2)
      as [output' [Houtput' Hsout]].
    cbn in Hb'.
    assert (Hnx_cod : ~ In x (ty_binders codomain)).
    { eapply type_demand_lookup_not_bound; [exact H1 |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe level; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq' _].
      destruct (Heq' eq_refl) as [Hlkp' _].
      unfold lookup at 1. cbn [find binder]. rewrite HEq_nx.
      fold (lookup (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) x).
      rewrite Hlkp'. discriminate. }
    assert (Hnx0_cod : ~ In x0 (ty_binders codomain)).
    { eapply type_demand_lookup_not_bound; [exact H1 |].
      unfold lookup at 1. cbn [find binder]. rewrite Nat.eqb_refl. discriminate. }
    assert (Hfix_arg : substitute_type x0 argument arg = arg)
      by (eapply type_demand_subst_nat_absent; [exact Harg | exact Hx0_fresh_outer]).
    rewrite substitute_type_and_var_comm2 in Houtput'
      by (assumption || congruence).
    assert (Hz0_ux : uses z0 x = 0).
    { eapply index_demand_absent_use; [exact Hz0' |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe level; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq' _].
      destruct (Heq' eq_refl) as [_ H2']. rewrite H2'. unfold fresh in Hfx_o. now destruct (lookup outer x). }
    assert (Hsz0 : same_demand (substitute_demand x z z0) z0).
    { intro k. rewrite uses_substitute_demand, Hz0_ux, Nat.mul_0_l, Nat.add_0_r.
      destruct (Nat.eqb k x) eqn:Ekx; [apply Nat.eqb_eq in Ekx; subst k; symmetry; exact Hz0_ux | reflexivity]. }
    assert (Hb'' : TypeDemand ({| binder := x0; annotation := Natural; type_uses := [] |} :: map (rewrite_type_binding x arg z) inner ++ outer)
      (substitute_type_variable x arg codomain) b').
    { eapply type_demand_ann_equiv; [| exact Hb'].
      intro k. unfold lookup. cbn [find binder annotation rewrite_type_binding rewrite_binding_with substitute_type_variable].
      destruct (Nat.eqb k x0); [split; reflexivity |].
      destruct (find (fun entry => k =? binder entry) (map (rewrite_type_binding x arg z) inner ++ outer)); [split; reflexivity | exact I]. }
    eexists. split.
    + eapply GradeApplyNat; [exact Hdc' | exact Hx0_fresh_after | exact Hz0' | exact Hb'' | exact Houtput' |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Hsb] |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_sym; exact Hsz0 | apply same_demand_refl] |].
      eapply same_demand_trans; [apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z] |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact H3] | apply same_demand_sym; exact Hsout].
    + split; [cbn; symmetry; apply substitute_type_and_var_comm2; assumption || congruence | split; cbn].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [exact Hcdc' | apply same_demand_scale_compat; apply same_demand_sym; exact Hsz0].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_scale].
           ++ apply same_demand_sym, substitute_demand_app.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Hsb] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_sym; exact Hsz0 | apply same_demand_refl] |].
        apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z].
  - (* GradeApplyValue *)
    apply orb_false_elim in Htvf as [Htvf1 Htvf2].
    assert (Htb_callee : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\
      ~ In y (term_binders callee) /\
      ~ In y (context_ty_binders (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. repeat split; auto.
      intro Hin. apply Hti. apply in_or_app. now left. }
    assert (Htb_arg_term : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\
      ~ In y (term_binders argument) /\
      ~ In y (context_ty_binders (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. repeat split; auto.
      intro Hin. apply Hti. apply in_or_app. now right. }
    destruct (IHHderiv1 inner Hfx_i Hnoshad Htb_callee Htvf1 eq_refl) as [[rt_c' w' v'] [Hdc' [Hrtc' [Hcdc' Htdc']]]].
    destruct (IHHderiv2 inner Hfx_i Hnoshad Htb_arg_term Htvf2 eq_refl) as [[rt_a' z' a'] [Hda' [Hrta' [Hcda' Htda']]]].
    apply same_demand_subst_unfold_compat in Hcdc'.
    apply same_demand_subst_unfold_compat in Hcda'.
    cbn in *. rewrite Hrtc' in Hdc'. rewrite Hrta' in Hda'. cbn in Hdc'.
    destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe level; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H0. rewrite Hlkp in H0. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H0. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H0. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H0. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H0.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_type_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Hdc'.
    assert (Htb_cod : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\ ~ In y (ty_binders codomain)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. split; [exact Hfi |].
      intro Hin.
      destruct (ty_binders_derives_sub _ _ _ _ y Hderiv1) as [Hd | Hd]; [cbn; right; apply in_or_app; now right | | exact (Hci Hd)].
      apply Hti. apply in_or_app. now left. }
    destruct (subst_type_var_demand outer arg z inner x level codomain b Harg Hfx_o Hfx_i Hnoshad Htb_cod H1)
      as [b' [Hb' Hsb]].
    assert (Hcanon : canonical_type [] (substitute_type_variable x arg kind) = canonical_type [] (substitute_type_variable x arg domain)).
    { destruct (derives_type_demand _ _ _ _ Hderiv1) as [row_pi [Htd_pi _]].
      destruct (derives_type_demand _ _ _ _ Hderiv2) as [row_k [Htd_k _]].
      inversion Htd_pi; subst.
      assert (Hfx' : fresh (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) x = false).
      { destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
          {| binder := x; annotation := Universe level; type_uses := [] |} outer x
          (fun _ => eq_refl) Hfx_i eq_refl) as [Hqq _].
        destruct (Hqq eq_refl) as [Hqq1 _]. unfold fresh. now rewrite Hqq1. }
      assert (Harg_fresh : forall T r b_name,
        TypeDemand (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) T r ->
        (In b_name (term_binders (ApplyValue callee argument)) \/
         In b_name (context_ty_binders (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))) ->
        In b_name (ty_binders T) ->
        b_name <> x /\ ~ In b_name (ty_free_vars [] arg) /\ ~ In b_name (ty_index_vars arg)).
      { intros T r b_name HtdT Hloc Hbm.
        apply (type_demand_ty_binders_fresh _ _ _ b_name HtdT) in Hbm.
        assert (Hbn_neq : b_name <> x) by (intro E; subst; rewrite Hfx' in Hbm; discriminate).
        assert (Hbn_none_o : lookup outer b_name = None).
        { unfold fresh in Hbm. rewrite lookup_app_head in Hbm.
          destruct (lookup inner b_name); [discriminate |].
          unfold lookup at 1 in Hbm. cbn [find binder] in Hbm.
          apply Nat.eqb_neq in Hbn_neq. rewrite Hbn_neq in Hbm.
          fold (lookup outer b_name) in Hbm.
          destruct (lookup outer b_name); [discriminate | reflexivity]. }
        repeat split; try exact Hbn_neq.
        - eapply type_demand_absent_tvar; eassumption.
        - intro Hin_idx. destruct (type_demand_index_vars_lookup _ _ _ _ Harg Hin_idx) as [Hin_tb | [eo Heo]].
          + destruct (Htb_arg b_name Hin_tb) as [_ [Hti Hci]]. destruct Hloc as [Hl | Hl]; [exact (Hti Hl) | exact (Hci Hl)].
          + congruence. }
      eapply canonical_type_subst_tvar_preserves with (names1 := []) (names2 := []); eauto; cbn; try tauto.
      - intros b_name Hbm. eapply Harg_fresh; [exact Htd_k | | exact Hbm].
        destruct (ty_binders_derives_sub _ _ _ _ b_name Hderiv2) as [Htb | Hcb];
          [exact Hbm | left; apply in_or_app; now right | right; exact Hcb].
      - intros b_name Hbm. eapply Harg_fresh; [exact Htd_pi | | cbn; right; apply in_or_app; now left].
        destruct (ty_binders_derives_sub _ _ _ _ b_name Hderiv1) as [Htb | Hcb];
          [cbn; right; apply in_or_app; now left | left; apply in_or_app; now left | right; exact Hcb]. }
    eexists. split.
    + eapply GradeApplyValue; [exact Hdc' | exact Hda' | exact Hcanon | exact Hx0_fresh_after | exact Hb'].
    + split; [cbn; reflexivity | split; cbn].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [exact Hcdc' | apply same_demand_scale_compat; exact Hcda'].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_scale].
           ++ apply same_demand_sym, substitute_demand_app.
      * exact Hsb.
  - (* GradeLetNat *)
    destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe level; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Htvf |- *.
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_type_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0) by (eapply type_demand_absent_use; eassumption).
    assert (Hz0' : IndexDemand (map (rewrite_type_binding x arg z) inner ++ outer) initializer z0)
      by (eapply index_demand_subst_tvar_env; eassumption).
    assert (Hfx_i' : fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    assert (Htb_arg' : forall y, In y (ty_binders arg) ->
      fresh ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner) y = true /\
      ~ In y (term_binders body) /\
      ~ In y (context_ty_binders ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. repeat split.
      - apply fresh_cons_intro; [| exact Hfi].
        intro E. cbn in E. subst y. apply Hti. now left.
      - intro Hin. apply Hti. now right.
      - exact Hci. }
    destruct (IHHderiv ({| binder := x0; annotation := Natural; type_uses := [] |} :: inner)
                Hfx_i' Hnoshad' Htb_arg' Htvf eq_refl)
      as [[kind' u' v'] [Hd' [Hrt' [Hcd' Htd']]]].
    cbn in *. subst kind'.
    apply same_demand_subst_unfold_compat in Hcd'.
    apply same_demand_subst_unfold_compat in Htd'.
    assert (Hkind_tb : forall y, In y (ty_binders arg) -> ~ In y (ty_binders kind)).
    { intros y Hy Hin. destruct (Htb_arg y Hy) as [_ [Hti Hci]].
      destruct (ty_binders_derives_sub _ _ _ _ y Hderiv Hin) as [Hd | Hd].
      - apply Hti. now right.
      - apply Hci; exact Hd. }
    assert (Htb_sub : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\ ~ In y (ty_binders (substitute_type x0 initializer kind))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi _]. split; [exact Hfi |].
      rewrite ty_binders_subst_nat. apply Hkind_tb; exact Hy. }
    destruct (subst_type_var_demand outer arg z inner x level (substitute_type x0 initializer kind) output Harg Hfx_o Hfx_i Hnoshad Htb_sub H2)
      as [output' [Houtput' Hsout]].
    assert (Hnx_kind : ~ In x (ty_binders kind)).
    { destruct (derives_type_demand _ _ _ _ Hderiv) as [rkind [Htd_kind _]].
      eapply type_demand_lookup_not_bound; [exact Htd_kind |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe level; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq' _].
      destruct (Heq' eq_refl) as [Hlkp' _].
      unfold lookup at 1. cbn [find binder]. rewrite HEq_nx.
      fold (lookup (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) x).
      rewrite Hlkp'. discriminate. }
    assert (Hnx0_kind : ~ In x0 (ty_binders kind)).
    { destruct (derives_type_demand _ _ _ _ Hderiv) as [rkind [Htd_kind _]].
      eapply type_demand_lookup_not_bound; [exact Htd_kind |].
      unfold lookup at 1. cbn [find binder]. rewrite Nat.eqb_refl. discriminate. }
    assert (Hfix_arg : substitute_type x0 initializer arg = arg)
      by (eapply type_demand_subst_nat_absent; [exact Harg | exact Hx0_fresh_outer]).
    rewrite substitute_type_and_var_comm2 in Houtput'
      by (assumption || congruence).
    assert (Hz0_ux : uses z0 x = 0).
    { eapply index_demand_absent_use; [exact Hz0' |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe level; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq' _].
      destruct (Heq' eq_refl) as [_ H2']. rewrite H2'. unfold fresh in Hfx_o. now destruct (lookup outer x). }
    assert (Hsz0 : same_demand (substitute_demand x z z0) z0).
    { intro k. rewrite uses_substitute_demand, Hz0_ux, Nat.mul_0_l, Nat.add_0_r.
      destruct (Nat.eqb k x) eqn:Ekx; [apply Nat.eqb_eq in Ekx; subst k; symmetry; exact Hz0_ux | reflexivity]. }
    assert (Hnil_sd : same_demand (type_uses (rewrite_type_binding x arg z {| binder := x0; annotation := Natural; type_uses := [] |})) []).
    { intro k. unfold rewrite_type_binding, rewrite_binding_with. cbn [type_uses]. rewrite uses_substitute_demand. cbn. now destruct (Nat.eqb k x). }
    destruct (derives_same_type_uses allows
      (rewrite_type_binding x arg z {| binder := x0; annotation := Natural; type_uses := [] |} :: map (rewrite_type_binding x arg z) inner ++ outer)
      ({| binder := x0; annotation := Natural; type_uses := [] |} :: map (rewrite_type_binding x arg z) inner ++ outer)
      (substitute_type_var_in_term x arg body)
      {| result_type := substitute_type_variable x arg kind; computation_demand := u'; type_demand_row := v' |})
      as [[kind'' u'' v''] [Hd'' [Hrt'' [Hcd'' Htd'']]]].
    { apply lookup_rel_cons; [reflexivity | reflexivity | exact Hnil_sd | apply lookup_rel_refl]. }
    { exact Hd'. }
    cbn in Hrt'', Hcd'', Htd''. subst kind''.
    eexists. split.
    + eapply GradeLetNat; [exact Hx0_fresh_after | exact Hz0' | exact Hd'' | | exact Houtput' |].
      * rewrite Hcd'', Hcd', uses_substitute_demand, Hx0_notin_z, Nat.mul_0_r, Nat.add_0_r.
        cbn. rewrite Nat.eqb_sym, HEq_nx. exact H1.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Htd''] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Htd'] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_sym; exact Hsz0 | apply same_demand_refl] |].
        eapply same_demand_trans; [apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact H3] | apply same_demand_sym; exact Hsout].
    + split; [cbn; symmetry; apply substitute_type_and_var_comm2; assumption || congruence | split; cbn].
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [apply same_demand_sym; exact Hsz0 |].
           eapply same_demand_trans; [apply same_demand_without_compat; eapply same_demand_trans; eassumption |].
           apply same_demand_sym, substitute_demand_without; [congruence | exact Hx0_notin_z].
        -- apply same_demand_sym, substitute_demand_app.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Htd''] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact Htd'] |].
        eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_sym; exact Hsz0 | apply same_demand_refl] |].
        apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z].
  - (* GradeApplyType *)
    assert (Htb_callee : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\
      ~ In y (term_binders callee) /\
      ~ In y (context_ty_binders (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. repeat split; auto.
      intro Hin. apply Hti. apply in_or_app. now left. }
    destruct (IHHderiv inner Hfx_i Hnoshad Htb_callee Htvf eq_refl) as [[rt_c' w' v'] [Hdc' [Hrtc' [Hcdc' Htdc']]]].
    apply same_demand_subst_unfold_compat in Hcdc'.
    apply same_demand_subst_unfold_compat in Htdc'.
    cbn in *. rewrite Hrtc' in Hdc'. cbn in Hdc'.
    destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
      {| binder := x; annotation := Universe level; type_uses := [] |} outer x0
      (fun _ => eq_refl) Hfx_i eq_refl) as [Heq Hneq].
    assert (Hx0_neq : x0 <> x).
    { intro E. subst x0. destruct (Heq eq_refl) as [Hlkp _].
      unfold fresh in H. rewrite Hlkp in H. discriminate. }
    assert (Hx0_fresh_inner : lookup inner x0 = None).
    { unfold fresh in H. destruct (lookup inner x0) eqn:E; [| reflexivity].
      destruct (Hneq Hx0_neq) as [_ Hsome]. destruct (Hsome b0 eq_refl) as [H1' _].
      rewrite H1' in H. discriminate. }
    assert (Hx0_fresh_outer : lookup outer x0 = None).
    { unfold fresh in H. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [H1' _]. rewrite H1' in H.
      destruct (lookup outer x0); [discriminate | reflexivity]. }
    assert (Hx0_fresh_after : fresh (map (rewrite_type_binding x arg z) inner ++ outer) x0 = true).
    { unfold fresh. destruct (Hneq Hx0_neq) as [Hnone _].
      destruct (Hnone Hx0_fresh_inner) as [_ H2']. rewrite H2', Hx0_fresh_outer. reflexivity. }
    assert (Hx0_notin_z : uses z x0 = 0) by (eapply type_demand_absent_use; eassumption).
    assert (Hx0_notin_arg : ~ In x0 (ty_free_vars [] arg)) by (eapply type_demand_absent_tvar; eassumption).
    assert (HEq_nx : Nat.eqb x x0 = false) by (apply Nat.eqb_neq; congruence).
    rewrite HEq_nx in Hdc'.
    assert (Htb_tvar_arg : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\ ~ In y (ty_binders argument)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti _]]. split; [exact Hfi |].
      intro Hin. apply Hti. apply in_or_app. now right. }
    destruct (subst_type_var_demand outer arg z inner x level argument z0 Harg Hfx_o Hfx_i Hnoshad Htb_tvar_arg H0)
      as [z0' [Hz0' Hsz0]].
    assert (Hul' : UniverseLevel (map (rewrite_type_binding x arg z) inner ++ outer) (substitute_type_variable x arg argument) level0)
      by (eapply subst_universe_level; eassumption).
    assert (Hfx_i' : fresh ({| binder := x0; annotation := Universe level0; type_uses := [] |} :: inner) x = true)
      by (apply fresh_cons_intro; [cbn; congruence | exact Hfx_i]).
    assert (Hnoshad' : forall y, lookup outer y <> None ->
      fresh ({| binder := x0; annotation := Universe level0; type_uses := [] |} :: inner) y = true).
    { intros y Hy. apply fresh_cons_intro; [| apply Hnoshad; exact Hy].
      intro E. cbn in E. subst y. rewrite Hx0_fresh_outer in Hy. contradiction. }
    assert (Hcod_tb : forall y, In y (ty_binders arg) -> ~ In y (ty_binders codomain)).
    { intros y Hy Hin. destruct (Htb_arg y Hy) as [_ [Hti Hci]].
      destruct (ty_binders_derives_sub _ _ _ _ y Hderiv) as [Hd | Hd].
      - cbn. right. exact Hin.
      - apply Hti. apply in_or_app. now left.
      - exact (Hci Hd). }
    assert (Htb_arg' : forall y, In y (ty_binders arg) ->
      fresh ({| binder := x0; annotation := Universe level0; type_uses := [] |} :: inner) y = true /\
      ~ In y (ty_binders codomain)).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti Hci]]. split; [| apply Hcod_tb; exact Hy].
      apply fresh_cons_intro; [| exact Hfi].
      intro E. cbn in E. subst y.
      destruct (ty_binders_derives_sub _ _ _ _ x0 Hderiv) as [Hd | Hd].
      - cbn. now left.
      - apply Hti. apply in_or_app. now left.
      - exact (Hci Hd). }
    assert (Htb_sub : forall y, In y (ty_binders arg) ->
      fresh inner y = true /\ ~ In y (ty_binders (substitute_type_variable x0 argument codomain))).
    { intros y Hy. destruct (Htb_arg y Hy) as [Hfi [Hti _]]. split; [exact Hfi |].
      intro Hin. apply in_ty_binders_subst_tvar in Hin as [Hin | Hin].
      - exact (Hcod_tb y Hy Hin).
      - apply Hti. apply in_or_app. now right. }
    destruct (subst_type_var_demand outer arg z ({| binder := x0; annotation := Universe level0; type_uses := [] |} :: inner) x level codomain b Harg Hfx_o Hfx_i' Hnoshad' Htb_arg' H2)
      as [b' [Hb' Hsb]].
    destruct (subst_type_var_demand outer arg z inner x level (substitute_type_variable x0 argument codomain) output Harg Hfx_o Hfx_i Hnoshad Htb_sub H3)
      as [output' [Houtput' Hsout]].
    cbn in Hb'.
    assert (Hnx_cod : ~ In x (ty_binders codomain)).
    { eapply type_demand_lookup_not_bound; [exact H2 |].
      destruct (lookup_split_three (rewrite_type_binding x arg z) inner x
        {| binder := x; annotation := Universe level; type_uses := [] |} outer x
        (fun _ => eq_refl) Hfx_i eq_refl) as [Heq' _].
      destruct (Heq' eq_refl) as [Hlkp' _].
      unfold lookup at 1. cbn [find binder]. rewrite HEq_nx.
      fold (lookup (inner ++ {| binder := x; annotation := Universe level; type_uses := [] |} :: outer) x).
      rewrite Hlkp'. discriminate. }
    assert (Hnx0_cod : ~ In x0 (ty_binders codomain)).
    { eapply type_demand_lookup_not_bound; [exact H2 |].
      unfold lookup at 1. cbn [find binder]. rewrite Nat.eqb_refl. discriminate. }
    rewrite subst_tvar_distr in Houtput' by (assumption || congruence).
    assert (Hb'' : TypeDemand ({| binder := x0; annotation := Universe level0; type_uses := [] |} :: map (rewrite_type_binding x arg z) inner ++ outer)
      (substitute_type_variable x arg codomain) b').
    { eapply type_demand_ann_equiv; [| exact Hb'].
      intro k. unfold lookup. cbn [find binder annotation rewrite_type_binding rewrite_binding_with substitute_type_variable].
      destruct (Nat.eqb k x0); [split; reflexivity |].
      destruct (find (fun entry => k =? binder entry) (map (rewrite_type_binding x arg z) inner ++ outer)); [split; reflexivity | exact I]. }
    eexists. split.
    + eapply GradeApplyType; [exact Hdc' | exact Hx0_fresh_after | exact Hz0' | exact Hul' | exact Hb'' | exact Houtput' |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | exact Hsb] |].
      eapply same_demand_trans; [apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z] |].
      eapply same_demand_trans; [apply same_demand_substitute_compat; [apply same_demand_refl | exact H4] | apply same_demand_sym; exact Hsout].
    + repeat split; cbn.
      * symmetry. apply subst_tvar_distr; assumption || congruence.
      * eapply same_demand_trans.
        -- apply same_demand_app_compat; [exact Hcdc' | apply same_demand_scale_compat; exact Hsz0].
        -- eapply same_demand_trans.
           ++ apply same_demand_app_compat; [apply same_demand_refl | apply same_demand_sym, substitute_demand_scale].
           ++ apply same_demand_sym, substitute_demand_app.
      * eapply same_demand_trans; [apply same_demand_substitute_compat; [exact Hsz0 | exact Hsb] |].
        apply same_demand_sym, substitute_demand_distr; [congruence | exact Hx0_notin_z].
Qed.

(* Contraction for pure Natural indices *)

Lemma contraction_index : forall env i d x y entry_x,
  x <> y ->
  lookup env x = Some entry_x ->
  annotation entry_x = Natural ->
  IndexDemand env i d ->
  exists d',
    IndexDemand env (substitute_index y (IndexVar x) i) d' /\
    uses d' x = uses d x + uses d y /\
    uses d' y = 0 /\
    (forall z, z <> x -> z <> y -> uses d' z = uses d z).
Proof.
  intros env i d x y entry_x Hneq Hlkp Hann Hd.
  induction Hd; cbn.
  - destruct (Nat.eqb y x0) eqn:Eyx0.
    + apply Nat.eqb_eq in Eyx0. subst x0.
      exists [(x, 1)]. repeat split; cbn.
      * eapply NaturalVariable; eassumption.
      * rewrite Nat.eqb_refl. assert (Hxy : Nat.eqb x y = false) by (apply Nat.eqb_neq; exact Hneq).
        rewrite Hxy. lia.
      * assert (Hyx : Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence).
        now rewrite Hyx.
      * intros z Hzx Hzy.
        apply Nat.eqb_neq in Hzx. apply Nat.eqb_neq in Hzy.
        now rewrite Hzx, Hzy.
    + exists [(x0, 1)].
      split; [eapply NaturalVariable; eassumption |].
      split; [| split].
      * cbn. destruct (Nat.eqb x x0) eqn:Exx0.
        -- apply Nat.eqb_eq in Exx0. subst x0.
           replace (y =? x) with false by (symmetry; apply Nat.eqb_neq; apply Nat.eqb_neq in Eyx0; congruence).
           reflexivity.
        -- apply Nat.eqb_neq in Eyx0.
           replace (y =? x0) with false by (symmetry; apply Nat.eqb_neq; congruence). lia.
      * cbn. apply Nat.eqb_neq in Eyx0.
        replace (y =? x0) with false by (symmetry; apply Nat.eqb_neq; congruence). reflexivity.
      * intros z Hzx Hzy. reflexivity.
  - exists []. split; [constructor | split; [reflexivity | split; [reflexivity | reflexivity]]].
  - destruct IHHd1 as [d1 [Hd1' [Hx1 [Hy1 Hz1]]]], IHHd2 as [d2 [Hd2' [Hx2 [Hy2 Hz2]]]].
    exists (d1 ++ d2). repeat split.
    + constructor; assumption.
    + rewrite !uses_append. lia.
    + rewrite uses_append. lia.
    + intros z Hzx Hzy. rewrite !uses_append. now rewrite Hz1, Hz2.
Qed.

(* ================================================================= *)
(* Part 2: Full GrTT Explicit (s, r) Core Calculus                   *)
(* ================================================================= *)

Module GrttCore.

Inductive gty : Type :=
| GNat
| GVec (length : index)
| GUniv (level : nat)
| GTVar (x : nat)
| GPi (x s r : nat) (domain codomain : gty)
| GSigma (x r : nat) (domain codomain : gty)
| GBox (q : nat) (payload : gty)
| GSum (left right : gty).

Scheme Equality for gty.

Inductive gterm : Type :=
| GVar (x : nat)
| GNatVal (i : index)
| GLam (x s r : nat) (domain : gty) (body : gterm)
| GAppNat (callee : gterm) (arg : index)
| GAppVal (callee arg : gterm)
| GAppType (callee : gterm) (arg : gty)
| GPair (x r : nat) (fst_ty snd_ty : gty) (left right : gterm)
| GLetPair (x y s : nat) (motive : gty) (pair body : gterm)
| GPromote (q : nat) (body : gterm)
| GLetBox (x : nat) (motive : gty) (box_term body : gterm)
| GInl (right_ty : gty) (body : gterm)
| GInr (left_ty : gty) (body : gterm)
| GMatchSum (x y : nat) (motive : gty) (scrutinee left_branch right_branch : gterm).

Record gbinding := {
  gbinder : nat;
  gannotation : gty;
  gtype_uses : demand;
}.

Definition gcontext := list gbinding.

Definition glookup (env : gcontext) (x : nat) : option gbinding :=
  find (fun entry => Nat.eqb x (gbinder entry)) env.

Definition gfresh (env : gcontext) (x : nat) : bool :=
  match glookup env x with None => true | Some _ => false end.

Fixpoint g_to_pure_ctx (env : gcontext) : context :=
  match env with
  | [] => []
  | {| gbinder := x; gannotation := GNat; gtype_uses := r |} :: rest =>
      {| binder := x; annotation := Natural; type_uses := r |} :: g_to_pure_ctx rest
  | _ :: rest => g_to_pure_ctx rest
  end.

Fixpoint gsubst_nat (x : nat) (val : index) (k : gty) : gty :=
  match k with
  | GNat => GNat
  | GVec len => GVec (substitute_index x val len)
  | GUniv lvl => GUniv lvl
  | GTVar y => GTVar y
  | GPi y s r dom cod =>
      GPi y s r (gsubst_nat x val dom) (if Nat.eqb x y then cod else gsubst_nat x val cod)
  | GSigma y r dom cod =>
      GSigma y r (gsubst_nat x val dom) (if Nat.eqb x y then cod else gsubst_nat x val cod)
  | GBox q payload => GBox q (gsubst_nat x val payload)
  | GSum l r => GSum (gsubst_nat x val l) (gsubst_nat x val r)
  end.

Fixpoint gsubst_tvar (x : nat) (val k : gty) : gty :=
  match k with
  | GTVar y => if Nat.eqb x y then val else k
  | GPi y s r dom cod =>
      GPi y s r (gsubst_tvar x val dom) (if Nat.eqb x y then cod else gsubst_tvar x val cod)
  | GSigma y r dom cod =>
      GSigma y r (gsubst_tvar x val dom) (if Nat.eqb x y then cod else gsubst_tvar x val cod)
  | GBox q payload => GBox q (gsubst_tvar x val payload)
  | GSum l r => GSum (gsubst_tvar x val l) (gsubst_tvar x val r)
  | _ => k
  end.

Fixpoint gcanonical_ty (names : list (nat * nat)) (k : gty) : gty :=
  match k with
  | GNat => GNat
  | GVec len => GVec (canonical_value names len)
  | GUniv lvl => GUniv lvl
  | GTVar x => GTVar (canonical_index names x)
  | GPi x s r dom cod =>
      let d := length names in
      GPi (2 * d) s r (gcanonical_ty names dom) (gcanonical_ty ((x, d) :: names) cod)
  | GSigma x r dom cod =>
      let d := length names in
      GSigma (2 * d) r (gcanonical_ty names dom) (gcanonical_ty ((x, d) :: names) cod)
  | GBox q payload => GBox q (gcanonical_ty names payload)
  | GSum l r => GSum (gcanonical_ty names l) (gcanonical_ty names r)
  end.

Definition gsubst_for_term (x : nat) (dom : gty) (arg : gterm) (k : gty) : gty :=
  match dom, arg with
  | GNat, GNatVal idx => gsubst_nat x idx k
  | GNat, GVar v => gsubst_nat x (IndexVar v) k
  | _, _ => k
  end.

Definition gsubst_demand_for_term (env : gcontext) (x : nat) (dom : gty) (arg : gterm) (b : demand) : option demand :=
  match dom, arg with
  | GNat, GNatVal idx => option_map (fun z => substitute_demand x z b) (index_demand (g_to_pure_ctx env) idx)
  | GNat, GVar v => Some (substitute_demand x [(v, 1)] b)
  | _, _ => if Nat.eqb (uses b x) 0 then Some (without x b) else None
  end.

Inductive GTypeDemand (allows : nat -> nat -> Prop) (env : gcontext) : gty -> demand -> Prop :=
| GTypeNat : GTypeDemand allows env GNat []
| GTypeVec : forall len d,
    IndexDemand (g_to_pure_ctx env) len d ->
    GTypeDemand allows env (GVec len) d
| GTypeUniv : forall lvl, GTypeDemand allows env (GUniv lvl) []
| GTypeTVar : forall x entry lvl,
    glookup env x = Some entry -> gannotation entry = GUniv lvl ->
    GTypeDemand allows env (GTVar x) [(x, 1)]
| GTypePi : forall x s r dom cod a b,
    gfresh env x = true ->
    GTypeDemand allows env dom a ->
    GTypeDemand allows ({| gbinder := x; gannotation := dom; gtype_uses := a |} :: env) cod b ->
    allows (uses b x) r ->
    GTypeDemand allows env (GPi x s r dom cod) (a ++ without x b)
| GTypeSigma : forall x r dom cod a b,
    gfresh env x = true ->
    GTypeDemand allows env dom a ->
    GTypeDemand allows ({| gbinder := x; gannotation := dom; gtype_uses := a |} :: env) cod b ->
    allows (uses b x) r ->
    GTypeDemand allows env (GSigma x r dom cod) (a ++ without x b)
| GTypeBox : forall q payload d,
    GTypeDemand allows env payload d ->
    GTypeDemand allows env (GBox q payload) d
| GTypeSum : forall l r dl dr,
    GTypeDemand allows env l dl ->
    GTypeDemand allows env r dr ->
    GTypeDemand allows env (GSum l r) (dl ++ dr).

Fixpoint gtype_demand (allowsb : nat -> nat -> bool) (env : gcontext) (k : gty) : option demand :=
  match k with
  | GNat => Some []
  | GVec len => index_demand (g_to_pure_ctx env) len
  | GUniv _ => Some []
  | GTVar x =>
      match glookup env x with
      | Some {| gannotation := GUniv _ |} => Some [(x, 1)]
      | _ => None
      end
  | GPi x _ r dom cod =>
      if gfresh env x then
        match gtype_demand allowsb env dom with
        | None => None
        | Some a =>
            match gtype_demand allowsb ({| gbinder := x; gannotation := dom; gtype_uses := a |} :: env) cod with
            | Some b => if allowsb (uses b x) r then Some (a ++ without x b) else None
            | None => None
            end
        end
      else None
  | GSigma x r dom cod =>
      if gfresh env x then
        match gtype_demand allowsb env dom with
        | None => None
        | Some a =>
            match gtype_demand allowsb ({| gbinder := x; gannotation := dom; gtype_uses := a |} :: env) cod with
            | Some b => if allowsb (uses b x) r then Some (a ++ without x b) else None
            | None => None
            end
        end
      else None
  | GBox _ payload => gtype_demand allowsb env payload
  | GSum l r =>
      match gtype_demand allowsb env l, gtype_demand allowsb env r with
      | Some dl, Some dr => Some (dl ++ dr)
      | _, _ => None
      end
  end.

Lemma gtype_demand_sound : forall allows allowsb,
  (forall a b, allowsb a b = true -> allows a b) ->
  forall k env d, gtype_demand allowsb env k = Some d -> GTypeDemand allows env k d.
Proof.
  intros allows allowsb Hsound k.
  induction k; intros env d Hchk; cbn in Hchk.
  - inversion Hchk; subst; constructor.
  - constructor. now apply index_demand_sound.
  - inversion Hchk; subst; constructor.
  - destruct (glookup env x) as [[? [] ?] |] eqn:Flkp; inversion Hchk; subst.
    eapply GTypeTVar; [exact Flkp | reflexivity].
  - destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (gtype_demand allowsb env k1) as [a |] eqn:Hdom; try discriminate.
    destruct (gtype_demand allowsb ({| gbinder := x; gannotation := k1; gtype_uses := a |} :: env) k2)
      as [b |] eqn:Hcod; try discriminate.
    destruct (allowsb (uses b x) r) eqn:Hr; inversion Hchk; subst.
    constructor; auto.
  - destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (gtype_demand allowsb env k1) as [a |] eqn:Hdom; try discriminate.
    destruct (gtype_demand allowsb ({| gbinder := x; gannotation := k1; gtype_uses := a |} :: env) k2)
      as [b |] eqn:Hcod; try discriminate.
    destruct (allowsb (uses b x) r) eqn:Hr; inversion Hchk; subst.
    constructor; auto.
  - constructor. auto.
  - destruct (gtype_demand allowsb env k1) as [dl |] eqn:Hl; try discriminate.
    destruct (gtype_demand allowsb env k2) as [dr |] eqn:Hr; inversion Hchk; subst.
    constructor; auto.
Qed.

Inductive GUniverseLevel (env : gcontext) : gty -> nat -> Prop :=
| GLevelNat : GUniverseLevel env GNat 0
| GLevelVec : forall len, GUniverseLevel env (GVec len) 0
| GLevelUniv : forall i, GUniverseLevel env (GUniv i) (S i)
| GLevelTVar : forall x entry i,
    glookup env x = Some entry -> gannotation entry = GUniv i -> GUniverseLevel env (GTVar x) i
| GLevelPi : forall x s r dom cod i j,
    GUniverseLevel env dom i ->
    GUniverseLevel ({| gbinder := x; gannotation := dom; gtype_uses := [] |} :: env) cod j ->
    GUniverseLevel env (GPi x s r dom cod) (Nat.max i j)
| GLevelSigma : forall x r dom cod i j,
    GUniverseLevel env dom i ->
    GUniverseLevel ({| gbinder := x; gannotation := dom; gtype_uses := [] |} :: env) cod j ->
    GUniverseLevel env (GSigma x r dom cod) (Nat.max i j)
| GLevelBox : forall q payload i,
    GUniverseLevel env payload i -> GUniverseLevel env (GBox q payload) i
| GLevelSum : forall l r i j,
    GUniverseLevel env l i -> GUniverseLevel env r j -> GUniverseLevel env (GSum l r) (Nat.max i j).

Fixpoint guniverse_level (env : gcontext) (k : gty) : option nat :=
  match k with
  | GNat | GVec _ => Some 0
  | GUniv i => Some (S i)
  | GTVar x =>
      match glookup env x with
      | Some {| gannotation := GUniv i |} => Some i
      | _ => None
      end
  | GPi x _ _ dom cod | GSigma x _ dom cod =>
      match guniverse_level env dom,
            guniverse_level ({| gbinder := x; gannotation := dom; gtype_uses := [] |} :: env) cod with
      | Some i, Some j => Some (Nat.max i j)
      | _, _ => None
      end
  | GBox _ payload => guniverse_level env payload
  | GSum l r =>
      match guniverse_level env l, guniverse_level env r with
      | Some i, Some j => Some (Nat.max i j)
      | _, _ => None
      end
  end.

Lemma guniverse_level_sound : forall k env lvl,
  guniverse_level env k = Some lvl -> GUniverseLevel env k lvl.
Proof.
  induction k; intros env lvl Hchk; cbn in Hchk.
  - inversion Hchk; constructor.
  - inversion Hchk; constructor.
  - inversion Hchk; constructor.
  - destruct (glookup env x) as [[? [] ?] |] eqn:Flkp; inversion Hchk; subst.
    eapply GLevelTVar; [exact Flkp | reflexivity].
  - destruct (guniverse_level env k1) as [i |] eqn:Hi; try discriminate.
    destruct (guniverse_level ({| gbinder := x; gannotation := k1; gtype_uses := [] |} :: env) k2)
      as [j |] eqn:Hj; inversion Hchk; subst; constructor; auto.
  - destruct (guniverse_level env k1) as [i |] eqn:Hi; try discriminate.
    destruct (guniverse_level ({| gbinder := x; gannotation := k1; gtype_uses := [] |} :: env) k2)
      as [j |] eqn:Hj; inversion Hchk; subst; constructor; auto.
  - constructor; auto.
  - destruct (guniverse_level env k1) as [i |] eqn:Hi; try discriminate.
    destruct (guniverse_level env k2) as [j |] eqn:Hj; inversion Hchk; subst; constructor; auto.
Qed.

Definition join_demand (d1 d2 : demand) : demand :=
  map (fun x => (x, Nat.max (uses d1 x) (uses d2 x)))
    (nodup Nat.eq_dec (map fst (d1 ++ d2))).

Lemma uses_join_demand : forall d1 d2 k,
  uses (join_demand d1 d2) k = Nat.max (uses d1 k) (uses d2 k).
Proof.
  intros d1 d2 k. unfold join_demand.
  assert (Hnodup_map : forall l, NoDup l ->
    uses (map (fun x => (x, Nat.max (uses d1 x) (uses d2 x))) l) k =
    if in_dec Nat.eq_dec k l then Nat.max (uses d1 k) (uses d2 k) else 0).
  { induction l as [| h rest IH]; intros Hnd; cbn [map uses].
    - reflexivity.
    - inversion Hnd; subst. rewrite (IH H2).
      destruct (Nat.eq_dec k h) as [<- | Hkh].
      + rewrite Nat.eqb_refl. destruct (in_dec Nat.eq_dec k rest); [contradiction |].
        destruct (in_dec Nat.eq_dec k (k :: rest)); [rewrite Nat.add_0_r; reflexivity | exfalso; apply n0; now left].
      + assert (Hkhb : Nat.eqb k h = false) by (apply Nat.eqb_neq; exact Hkh).
        rewrite Hkhb. destruct (in_dec Nat.eq_dec k rest) as [Hin | Hnin].
        * destruct (in_dec Nat.eq_dec k (h :: rest)); [reflexivity | exfalso; apply n; now right].
        * destruct (in_dec Nat.eq_dec k (h :: rest)) as [[<- | ?] | ?]; [congruence | contradiction | reflexivity]. }
  rewrite Hnodup_map by apply NoDup_nodup.
  destruct (in_dec Nat.eq_dec k (nodup Nat.eq_dec (map fst (d1 ++ d2)))) as [Hin | Hnin].
  - reflexivity.
  - assert (Hnin' : ~ In k (map fst (d1 ++ d2))) by (intro H; apply Hnin; now apply nodup_In).
    rewrite map_app, in_app_iff in Hnin'.
    rewrite !absent_use by tauto. reflexivity.
Qed.

Record gjudgment := {
  gresult_type : gty;
  gcomputation_demand : demand;
  gtype_demand_row : demand;
}.

Definition subst_sigma_second (x : nat) (dom : gty) (y : nat) (cod : gty) : gty :=
  match dom with
  | GNat => gsubst_nat x (IndexVar y) cod
  | GUniv _ => gsubst_tvar x (GTVar y) cod
  | _ => cod
  end.

Inductive GrttDerivesWith (allows : nat -> nat -> Prop) (join_branches : bool) (env : gcontext)
  : gterm -> gjudgment -> Prop :=
| GGradeVar : forall x entry row,
    glookup env x = Some entry ->
    GTypeDemand allows env (gannotation entry) row ->
    same_demand (gtype_uses entry) row ->
    GrttDerivesWith allows join_branches env (GVar x)
      {| gresult_type := gannotation entry; gcomputation_demand := [(x, 1)]; gtype_demand_row := gtype_uses entry |}
| GGradeNat : forall i d,
    IndexDemand (g_to_pure_ctx env) i d ->
    GrttDerivesWith allows join_branches env (GNatVal i)
      {| gresult_type := GNat; gcomputation_demand := d; gtype_demand_row := [] |}
| GGradeLam : forall x s r dom body cod a u v,
    gfresh env x = true ->
    GTypeDemand allows env dom a ->
    GrttDerivesWith allows join_branches ({| gbinder := x; gannotation := dom; gtype_uses := a |} :: env) body
      {| gresult_type := cod; gcomputation_demand := u; gtype_demand_row := v |} ->
    allows (uses u x) s ->
    allows (uses v x) r ->
    GrttDerivesWith allows join_branches env (GLam x s r dom body)
      {| gresult_type := GPi x s r dom cod;
         gcomputation_demand := without x u;
         gtype_demand_row := a ++ without x v |}
| GGradeAppNat : forall callee arg x s r cod w v z b output,
    GrttDerivesWith allows join_branches env callee
      {| gresult_type := GPi x s r GNat cod; gcomputation_demand := w; gtype_demand_row := v |} ->
    gfresh env x = true ->
    IndexDemand (g_to_pure_ctx env) arg z ->
    GTypeDemand allows ({| gbinder := x; gannotation := GNat; gtype_uses := [] |} :: env) cod b ->
    allows (uses b x) r ->
    GTypeDemand allows env (gsubst_nat x arg cod) output ->
    same_demand (substitute_demand x z b) output ->
    GrttDerivesWith allows join_branches env (GAppNat callee arg)
      {| gresult_type := gsubst_nat x arg cod;
         gcomputation_demand := w ++ scale s z;
         gtype_demand_row := substitute_demand x z b |}
| GGradeAppVal : forall callee arg x s r dom cod kind w v z a b,
    GrttDerivesWith allows join_branches env callee
      {| gresult_type := GPi x s r dom cod; gcomputation_demand := w; gtype_demand_row := v |} ->
    GrttDerivesWith allows join_branches env arg
      {| gresult_type := kind; gcomputation_demand := z; gtype_demand_row := a |} ->
    gcanonical_ty [] kind = gcanonical_ty [] dom ->
    gfresh env x = true ->
    GTypeDemand allows env cod b ->
    allows 0 r ->
    GrttDerivesWith allows join_branches env (GAppVal callee arg)
      {| gresult_type := cod;
         gcomputation_demand := w ++ scale s z;
         gtype_demand_row := b |}
| GGradeAppType : forall callee arg x s r level cod w v z b output,
    GrttDerivesWith allows join_branches env callee
      {| gresult_type := GPi x s r (GUniv level) cod; gcomputation_demand := w; gtype_demand_row := v |} ->
    gfresh env x = true ->
    GTypeDemand allows env arg z ->
    GUniverseLevel env arg level ->
    GTypeDemand allows ({| gbinder := x; gannotation := GUniv level; gtype_uses := [] |} :: env) cod b ->
    allows (uses b x) r ->
    GTypeDemand allows env (gsubst_tvar x arg cod) output ->
    same_demand (substitute_demand x z b) output ->
    GrttDerivesWith allows join_branches env (GAppType callee arg)
      {| gresult_type := gsubst_tvar x arg cod;
         gcomputation_demand := w ++ scale s z;
         gtype_demand_row := substitute_demand x z b |}
| GGradePair : forall x r fst_ty snd_ty left right ul ur al ar actual_snd a b exp_row out_row,
    gfresh env x = true ->
    GTypeDemand allows env fst_ty a ->
    GTypeDemand allows ({| gbinder := x; gannotation := fst_ty; gtype_uses := a |} :: env) snd_ty b ->
    allows (uses b x) r ->
    GrttDerivesWith allows join_branches env left
      {| gresult_type := fst_ty; gcomputation_demand := ul; gtype_demand_row := al |} ->
    GrttDerivesWith allows join_branches env right
      {| gresult_type := actual_snd; gcomputation_demand := ur; gtype_demand_row := ar |} ->
    gcanonical_ty [] actual_snd = gcanonical_ty [] (gsubst_for_term x fst_ty left snd_ty) ->
    gsubst_demand_for_term env x fst_ty left b = Some exp_row ->
    same_demand ar exp_row ->
    GTypeDemand allows env (GSigma x r fst_ty snd_ty) out_row ->
    GrttDerivesWith allows join_branches env (GPair x r fst_ty snd_ty left right)
      {| gresult_type := GSigma x r fst_ty snd_ty;
         gcomputation_demand := ul ++ ur;
         gtype_demand_row := out_row |}
| GGradeLetPair : forall x y s motive pair body z r A B w v a b u bv actual_motive mot_row,
    gfresh env x = true ->
    gfresh ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) y = true ->
    GrttDerivesWith allows join_branches env pair
      {| gresult_type := GSigma z r A B; gcomputation_demand := w; gtype_demand_row := v |} ->
    GTypeDemand allows env A a ->
    GTypeDemand allows ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) (subst_sigma_second z A x B) b ->
    GTypeDemand allows env motive mot_row ->
    GrttDerivesWith allows join_branches
      ({| gbinder := y; gannotation := subst_sigma_second z A x B; gtype_uses := b |} ::
       {| gbinder := x; gannotation := A; gtype_uses := a |} :: env)
      body {| gresult_type := actual_motive; gcomputation_demand := u; gtype_demand_row := bv |} ->
    gcanonical_ty [] actual_motive = gcanonical_ty [] motive ->
    allows (uses u x) s ->
    allows (uses u y) s ->
    same_demand bv mot_row ->
    GrttDerivesWith allows join_branches env (GLetPair x y s motive pair body)
      {| gresult_type := motive;
         gcomputation_demand := without x (without y u) ++ scale s w;
         gtype_demand_row := mot_row |}
| GGradePromote : forall q body A u v,
    GrttDerivesWith allows join_branches env body
      {| gresult_type := A; gcomputation_demand := u; gtype_demand_row := v |} ->
    GrttDerivesWith allows join_branches env (GPromote q body)
      {| gresult_type := GBox q A;
         gcomputation_demand := scale q u;
         gtype_demand_row := v |}
| GGradeLetBox : forall x motive box_term body q A z vz a mot_row w bw actual_motive,
    gfresh env x = true ->
    GrttDerivesWith allows join_branches env box_term
      {| gresult_type := GBox q A; gcomputation_demand := z; gtype_demand_row := vz |} ->
    GTypeDemand allows env A a ->
    GTypeDemand allows env motive mot_row ->
    GrttDerivesWith allows join_branches ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) body
      {| gresult_type := actual_motive; gcomputation_demand := w; gtype_demand_row := bw |} ->
    gcanonical_ty [] actual_motive = gcanonical_ty [] motive ->
    allows (uses w x) q ->
    same_demand bw mot_row ->
    GrttDerivesWith allows join_branches env (GLetBox x motive box_term body)
      {| gresult_type := motive;
         gcomputation_demand := without x w ++ z;
         gtype_demand_row := mot_row |}
| GGradeInl : forall right_ty body A u a b,
    GrttDerivesWith allows join_branches env body
      {| gresult_type := A; gcomputation_demand := u; gtype_demand_row := a |} ->
    GTypeDemand allows env right_ty b ->
    GrttDerivesWith allows join_branches env (GInl right_ty body)
      {| gresult_type := GSum A right_ty;
         gcomputation_demand := u;
         gtype_demand_row := a ++ b |}
| GGradeInr : forall left_ty body B u b a,
    GTypeDemand allows env left_ty a ->
    GrttDerivesWith allows join_branches env body
      {| gresult_type := B; gcomputation_demand := u; gtype_demand_row := b |} ->
    GrttDerivesWith allows join_branches env (GInr left_ty body)
      {| gresult_type := GSum left_ty B;
         gcomputation_demand := u;
         gtype_demand_row := a ++ b |}
| GGradeMatchSum : forall x y motive scrutinee lb rb A B w vs a b mot_row u1 b1 t1 u2 b2 t2 branch_d,
    gfresh env x = true ->
    gfresh env y = true ->
    GrttDerivesWith allows join_branches env scrutinee
      {| gresult_type := GSum A B; gcomputation_demand := w; gtype_demand_row := vs |} ->
    GTypeDemand allows env A a ->
    GTypeDemand allows env B b ->
    GTypeDemand allows env motive mot_row ->
    GrttDerivesWith allows join_branches ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) lb
      {| gresult_type := t1; gcomputation_demand := u1; gtype_demand_row := b1 |} ->
    GrttDerivesWith allows join_branches ({| gbinder := y; gannotation := B; gtype_uses := b |} :: env) rb
      {| gresult_type := t2; gcomputation_demand := u2; gtype_demand_row := b2 |} ->
    gcanonical_ty [] t1 = gcanonical_ty [] motive ->
    gcanonical_ty [] t2 = gcanonical_ty [] motive ->
    allows (uses u1 x) 1 ->
    allows (uses u2 y) 1 ->
    same_demand b1 mot_row ->
    same_demand b2 mot_row ->
    (join_branches = false -> same_demand (without x u1) (without y u2)) ->
    branch_d = (if join_branches then join_demand (without x u1) (without y u2) else without x u1) ->
    GrttDerivesWith allows join_branches env (GMatchSum x y motive scrutinee lb rb)
      {| gresult_type := motive;
         gcomputation_demand := w ++ branch_d;
         gtype_demand_row := mot_row |}.

Fixpoint grtt_infer_with (allowsb : nat -> nat -> bool) (join_branches : bool)
    (env : gcontext) (subject : gterm) : option gjudgment :=
  match subject with
  | GVar x =>
      match glookup env x with
      | None => None
      | Some entry =>
          match gtype_demand allowsb env (gannotation entry) with
          | Some row =>
              if demand_eqb (gtype_uses entry) row then
                Some {| gresult_type := gannotation entry;
                        gcomputation_demand := [(x, 1)];
                        gtype_demand_row := gtype_uses entry |}
              else None
          | None => None
          end
      end
  | GNatVal i =>
      option_map (fun d => {| gresult_type := GNat; gcomputation_demand := d; gtype_demand_row := [] |})
        (index_demand (g_to_pure_ctx env) i)
  | GLam x s r dom body =>
      if gfresh env x then
        match gtype_demand allowsb env dom with
        | None => None
        | Some a =>
            match grtt_infer_with allowsb join_branches
                    ({| gbinder := x; gannotation := dom; gtype_uses := a |} :: env) body with
            | Some res =>
                if allowsb (uses (gcomputation_demand res) x) s &&
                   allowsb (uses (gtype_demand_row res) x) r then
                  Some {| gresult_type := GPi x s r dom (gresult_type res);
                          gcomputation_demand := without x (gcomputation_demand res);
                          gtype_demand_row := a ++ without x (gtype_demand_row res) |}
                else None
            | None => None
            end
        end
      else None
  | GAppNat callee arg =>
      match grtt_infer_with allowsb join_branches env callee with
      | Some {| gresult_type := GPi x s r GNat cod; gcomputation_demand := w |} =>
          if gfresh env x then
            let spec := gsubst_nat x arg cod in
            let ext := {| gbinder := x; gannotation := GNat; gtype_uses := [] |} :: env in
            match index_demand (g_to_pure_ctx env) arg,
                  gtype_demand allowsb ext cod,
                  gtype_demand allowsb env spec with
            | Some z, Some b, Some output =>
                let v := substitute_demand x z b in
                if allowsb (uses b x) r && demand_eqb v output then
                  Some {| gresult_type := spec;
                          gcomputation_demand := w ++ scale s z;
                          gtype_demand_row := v |}
                else None
            | _, _, _ => None
            end
          else None
      | _ => None
      end
  | GAppVal callee arg =>
      match grtt_infer_with allowsb join_branches env callee,
            grtt_infer_with allowsb join_branches env arg with
      | Some {| gresult_type := GPi x s r dom cod; gcomputation_demand := w |},
        Some {| gresult_type := kind; gcomputation_demand := z |} =>
          if gfresh env x then
            if gty_eq_dec (gcanonical_ty [] kind) (gcanonical_ty [] dom) then
              if allowsb 0 r then
                option_map (fun b => {| gresult_type := cod;
                                        gcomputation_demand := w ++ scale s z;
                                        gtype_demand_row := b |})
                  (gtype_demand allowsb env cod)
              else None
            else None
          else None
      | _, _ => None
      end
  | GAppType callee arg =>
      match grtt_infer_with allowsb join_branches env callee with
      | Some {| gresult_type := GPi x s r (GUniv level) cod; gcomputation_demand := w |} =>
          if gfresh env x then
            let spec := gsubst_tvar x arg cod in
            let ext := {| gbinder := x; gannotation := GUniv level; gtype_uses := [] |} :: env in
            match gtype_demand allowsb env arg, guniverse_level env arg,
                  gtype_demand allowsb ext cod, gtype_demand allowsb env spec with
            | Some z, Some actual, Some b, Some output =>
                let v := substitute_demand x z b in
                if Nat.eqb actual level && allowsb (uses b x) r && demand_eqb v output then
                  Some {| gresult_type := spec;
                          gcomputation_demand := w ++ scale s z;
                          gtype_demand_row := v |}
                else None
            | _, _, _, _ => None
            end
          else None
      | _ => None
      end
  | GPair x r fst_ty snd_ty lhs rhs =>
      if gfresh env x then
        match gtype_demand allowsb env fst_ty with
        | None => None
        | Some a =>
            let ext := {| gbinder := x; gannotation := fst_ty; gtype_uses := a |} :: env in
            match gtype_demand allowsb ext snd_ty,
                  gtype_demand allowsb env (GSigma x r fst_ty snd_ty),
                  grtt_infer_with allowsb join_branches env lhs,
                  grtt_infer_with allowsb join_branches env rhs with
            | Some b, Some out_row,
              Some {| gresult_type := actual_fst; gcomputation_demand := ul |},
              Some {| gresult_type := actual_snd; gcomputation_demand := ur; gtype_demand_row := ar |} =>
                if gty_eq_dec actual_fst fst_ty then
                  if allowsb (uses b x) r then
                    let exp_snd := gsubst_for_term x fst_ty lhs snd_ty in
                    if gty_eq_dec (gcanonical_ty [] actual_snd) (gcanonical_ty [] exp_snd) then
                      match gsubst_demand_for_term env x fst_ty lhs b with
                      | Some exp_row =>
                          if demand_eqb ar exp_row then
                            Some {| gresult_type := GSigma x r fst_ty snd_ty;
                                    gcomputation_demand := ul ++ ur;
                                    gtype_demand_row := out_row |}
                          else None
                      | None => None
                      end
                    else None
                  else None
                else None
            | _, _, _, _ => None
            end
        end
      else None
  | GLetPair x y s motive pr body =>
      if gfresh env x then
        match grtt_infer_with allowsb join_branches env pr with
        | Some {| gresult_type := GSigma z r A B; gcomputation_demand := w |} =>
            match gtype_demand allowsb env A, gtype_demand allowsb env motive with
            | Some a, Some mot_row =>
                let env1 := {| gbinder := x; gannotation := A; gtype_uses := a |} :: env in
                if gfresh env1 y then
                  let B_xy := subst_sigma_second z A x B in
                  match gtype_demand allowsb env1 B_xy with
                  | Some b =>
                      let env2 := {| gbinder := y; gannotation := B_xy; gtype_uses := b |} :: env1 in
                      match grtt_infer_with allowsb join_branches env2 body with
                      | Some {| gresult_type := actual_motive; gcomputation_demand := u; gtype_demand_row := bv |} =>
                          if gty_eq_dec (gcanonical_ty [] actual_motive) (gcanonical_ty [] motive) then
                            if allowsb (uses u x) s && allowsb (uses u y) s && demand_eqb bv mot_row then
                              Some {| gresult_type := motive;
                                      gcomputation_demand := without x (without y u) ++ scale s w;
                                      gtype_demand_row := mot_row |}
                            else None
                          else None
                      | None => None
                      end
                  | None => None
                  end
                else None
            | _, _ => None
            end
        | _ => None
        end
      else None
  | GPromote q body =>
      match grtt_infer_with allowsb join_branches env body with
      | Some {| gresult_type := A; gcomputation_demand := u; gtype_demand_row := v |} =>
          Some {| gresult_type := GBox q A;
                  gcomputation_demand := scale q u;
                  gtype_demand_row := v |}
      | None => None
      end
  | GLetBox x motive box_term body =>
      if gfresh env x then
        match grtt_infer_with allowsb join_branches env box_term with
        | Some {| gresult_type := GBox q A; gcomputation_demand := z |} =>
            match gtype_demand allowsb env A, gtype_demand allowsb env motive with
            | Some a, Some mot_row =>
                let ext := {| gbinder := x; gannotation := A; gtype_uses := a |} :: env in
                match grtt_infer_with allowsb join_branches ext body with
                | Some {| gresult_type := actual_motive; gcomputation_demand := w; gtype_demand_row := bw |} =>
                    if gty_eq_dec (gcanonical_ty [] actual_motive) (gcanonical_ty [] motive) then
                      if allowsb (uses w x) q && demand_eqb bw mot_row then
                        Some {| gresult_type := motive;
                                gcomputation_demand := without x w ++ z;
                                gtype_demand_row := mot_row |}
                      else None
                    else None
                | None => None
                end
            | _, _ => None
            end
        | _ => None
        end
      else None
  | GInl right_ty body =>
      match grtt_infer_with allowsb join_branches env body, gtype_demand allowsb env right_ty with
      | Some {| gresult_type := A; gcomputation_demand := u; gtype_demand_row := a |}, Some b =>
          Some {| gresult_type := GSum A right_ty;
                  gcomputation_demand := u;
                  gtype_demand_row := a ++ b |}
      | _, _ => None
      end
  | GInr left_ty body =>
      match gtype_demand allowsb env left_ty, grtt_infer_with allowsb join_branches env body with
      | Some a, Some {| gresult_type := B; gcomputation_demand := u; gtype_demand_row := b |} =>
          Some {| gresult_type := GSum left_ty B;
                  gcomputation_demand := u;
                  gtype_demand_row := a ++ b |}
      | _, _ => None
      end
  | GMatchSum x y motive scrutinee lb rb =>
      if gfresh env x && gfresh env y then
        match grtt_infer_with allowsb join_branches env scrutinee with
        | Some {| gresult_type := GSum A B; gcomputation_demand := w |} =>
            match gtype_demand allowsb env A,
                  gtype_demand allowsb env B,
                  gtype_demand allowsb env motive with
            | Some a, Some b, Some mot_row =>
                match grtt_infer_with allowsb join_branches
                        ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) lb,
                      grtt_infer_with allowsb join_branches
                        ({| gbinder := y; gannotation := B; gtype_uses := b |} :: env) rb with
                | Some {| gresult_type := t1; gcomputation_demand := u1; gtype_demand_row := b1 |},
                  Some {| gresult_type := t2; gcomputation_demand := u2; gtype_demand_row := b2 |} =>
                    if gty_eq_dec (gcanonical_ty [] t1) (gcanonical_ty [] motive) then
                      if gty_eq_dec (gcanonical_ty [] t2) (gcanonical_ty [] motive) then
                        if allowsb (uses u1 x) 1 && allowsb (uses u2 y) 1 &&
                           demand_eqb b1 mot_row && demand_eqb b2 mot_row then
                          let d1 := without x u1 in
                          let d2 := without y u2 in
                          if join_branches then
                            Some {| gresult_type := motive;
                                    gcomputation_demand := w ++ join_demand d1 d2;
                                    gtype_demand_row := mot_row |}
                          else
                            if demand_eqb d1 d2 then
                              Some {| gresult_type := motive;
                                      gcomputation_demand := w ++ d1;
                                      gtype_demand_row := mot_row |}
                            else None
                        else None
                      else None
                    else None
                | _, _ => None
                end
            | _, _, _ => None
            end
        | _ => None
        end
      else None
  end.

Theorem grtt_infer_with_sound : forall allows allowsb,
  (forall a b, allowsb a b = true -> allows a b) ->
  forall join_branches subject env result,
    grtt_infer_with allowsb join_branches env subject = Some result ->
    GrttDerivesWith allows join_branches env subject result.
Proof.
  intros allows allowsb Hsound join_branches subject.
  induction subject; intros env res Hchk; cbn in Hchk.
  - destruct (glookup env x) as [entry |] eqn:Hlkp; try discriminate.
    destruct (gtype_demand allowsb env (gannotation entry)) as [row |] eqn:Htd; try discriminate.
    destruct (demand_eqb (gtype_uses entry) row) eqn:Heq; inversion Hchk; subst.
    eapply GGradeVar; eauto using gtype_demand_sound, demand_eqb_sound.
  - destruct (index_demand (g_to_pure_ctx env) i) eqn:Hid; inversion Hchk; subst.
    constructor. now apply index_demand_sound.
  - destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (gtype_demand allowsb env domain) as [a |] eqn:Hdom; try discriminate.
    destruct (grtt_infer_with allowsb join_branches
                ({| gbinder := x; gannotation := domain; gtype_uses := a |} :: env) subject)
      as [[cod u v] |] eqn:Hbody; try discriminate.
    cbn in Hchk.
    destruct (allowsb (uses u x) s && allowsb (uses v x) r) eqn:Hall; inversion Hchk; subst.
    apply andb_true_iff in Hall as [Hs Hr].
    eapply GGradeLam; eauto using gtype_demand_sound.
  - destruct (grtt_infer_with allowsb join_branches env subject) as [[rt w v] |] eqn:Hc; try discriminate.
    destruct rt as [| | | | x s r dom cod | | |]; try discriminate.
    destruct dom; try discriminate.
    destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (index_demand (g_to_pure_ctx env) arg) as [z |] eqn:Harg; try discriminate.
    destruct (gtype_demand allowsb ({| gbinder := x; gannotation := GNat; gtype_uses := [] |} :: env) cod)
      as [b |] eqn:Hcod; try discriminate.
    destruct (gtype_demand allowsb env (gsubst_nat x arg cod)) as [output |] eqn:Hout; try discriminate.
    destruct (allowsb (uses b x) r && demand_eqb (substitute_demand x z b) output) eqn:Hok;
      inversion Hchk; subst.
    apply andb_true_iff in Hok as [Hr Hdem].
    eapply GGradeAppNat; eauto using index_demand_sound, gtype_demand_sound, demand_eqb_sound.
  - destruct (grtt_infer_with allowsb join_branches env subject1) as [[rt1 w v] |] eqn:Hc; try discriminate.
    destruct rt1 as [| | | | x s r dom cod | | |]; try discriminate.
    destruct (grtt_infer_with allowsb join_branches env subject2) as [[rt2 z a] |] eqn:Ha; try discriminate.
    destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (gty_eq_dec (gcanonical_ty [] rt2) (gcanonical_ty [] dom)); try discriminate.
    destruct (allowsb 0 r) eqn:Hr; try discriminate.
    destruct (gtype_demand allowsb env cod) as [b |] eqn:Hcod; cbn in Hchk; try discriminate; inversion Hchk; subst.
    eapply GGradeAppVal; [apply IHsubject1; exact Hc | apply IHsubject2; exact Ha | exact e | exact Hfr | eapply gtype_demand_sound; eauto | now apply Hsound].
  - destruct (grtt_infer_with allowsb join_branches env subject) as [[rt w v] |] eqn:Hc; try discriminate.
    destruct rt as [| | | | x s r dom cod | | |]; try discriminate.
    destruct dom as [| | lvl | | | | |]; try discriminate.
    destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (gtype_demand allowsb env arg) as [z |] eqn:Harg; try discriminate.
    destruct (guniverse_level env arg) as [actual |] eqn:Hlvl; try discriminate.
    destruct (gtype_demand allowsb ({| gbinder := x; gannotation := GUniv lvl; gtype_uses := [] |} :: env) cod)
      as [b |] eqn:Hcod; try discriminate.
    destruct (gtype_demand allowsb env (gsubst_tvar x arg cod)) as [output |] eqn:Hout; try discriminate.
    destruct (Nat.eqb actual lvl && allowsb (uses b x) r && demand_eqb (substitute_demand x z b) output)
      eqn:Hok; inversion Hchk; subst.
    apply andb_true_iff in Hok as [Hok1 Hdem].
    apply andb_true_iff in Hok1 as [Hlvl_eq Hr].
    apply Nat.eqb_eq in Hlvl_eq. subst actual.
    eapply GGradeAppType; eauto using gtype_demand_sound, guniverse_level_sound, demand_eqb_sound.
  - destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (gtype_demand allowsb env fst_ty) as [a |] eqn:Hfst; try discriminate.
    destruct (gtype_demand allowsb ({| gbinder := x; gannotation := fst_ty; gtype_uses := a |} :: env) snd_ty)
      as [b |] eqn:Hsnd; try discriminate.
    destruct (allowsb (uses b x) r) eqn:Hr; cbn in Hchk; try discriminate.
    destruct (grtt_infer_with allowsb join_branches env subject1) as [[afst ul al] |] eqn:Hl; try discriminate.
    destruct (grtt_infer_with allowsb join_branches env subject2) as [[asnd ur ar] |] eqn:Hri; try discriminate.
    destruct (gty_eq_dec afst fst_ty); try discriminate. subst afst.
    destruct (gty_eq_dec (gcanonical_ty [] asnd) (gcanonical_ty [] (gsubst_for_term x fst_ty subject1 snd_ty))); try discriminate.
    destruct (gsubst_demand_for_term env x fst_ty subject1 b) as [exp_row |] eqn:Hexp; try discriminate.
    destruct (demand_eqb ar exp_row) eqn:Har; try discriminate; inversion Hchk; subst.
    eapply GGradePair;
      [exact Hfr
      | eapply gtype_demand_sound; [exact Hsound | exact Hfst]
      | eapply gtype_demand_sound; [exact Hsound | exact Hsnd]
      | apply Hsound; exact Hr
      | apply IHsubject1; exact Hl
      | apply IHsubject2; exact Hri
      | exact e
      | exact Hexp
      | apply demand_eqb_sound; exact Har
      | constructor; [exact Hfr | eapply gtype_demand_sound; [exact Hsound | exact Hfst]
          | eapply gtype_demand_sound; [exact Hsound | exact Hsnd] | apply Hsound; exact Hr]].
  - destruct (gfresh env x) eqn:Hfrx; try discriminate.
    destruct (grtt_infer_with allowsb join_branches env subject1) as [[prt w v] |] eqn:Hp; try discriminate.
    destruct prt as [| | | | | z r A B | |]; try discriminate.
    destruct (gtype_demand allowsb env A) as [a |] eqn:HA; try discriminate.
    destruct (gtype_demand allowsb env motive) as [mot_row |] eqn:Hm; try discriminate.
    destruct (gfresh ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) y) eqn:Hfry; try discriminate.
    destruct (gtype_demand allowsb ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env)
                (subst_sigma_second z A x B)) as [b |] eqn:HB; try discriminate.
    destruct (grtt_infer_with allowsb join_branches
                ({| gbinder := y; gannotation := subst_sigma_second z A x B; gtype_uses := b |} ::
                 {| gbinder := x; gannotation := A; gtype_uses := a |} :: env) subject2)
      as [[act_mot u bv] |] eqn:Hbdy; try discriminate.
    destruct (gty_eq_dec (gcanonical_ty [] act_mot) (gcanonical_ty [] motive)); try discriminate.
    destruct (allowsb (uses u x) s && allowsb (uses u y) s && demand_eqb bv mot_row) eqn:Hok;
      inversion Hchk; subst.
    apply andb_true_iff in Hok as [Hok1 Hbv].
    apply andb_true_iff in Hok1 as [Hsx Hsy].
    eapply GGradeLetPair; eauto using gtype_demand_sound, demand_eqb_sound.
  - destruct (grtt_infer_with allowsb join_branches env subject) as [[A u v] |] eqn:Hb; inversion Hchk; subst.
    constructor; auto.
  - destruct (gfresh env x) eqn:Hfr; try discriminate.
    destruct (grtt_infer_with allowsb join_branches env subject1) as [[brt z vz] |] eqn:Hbx; try discriminate.
    destruct brt as [| | | | | | q A |]; try discriminate.
    destruct (gtype_demand allowsb env A) as [a |] eqn:HA; try discriminate.
    destruct (gtype_demand allowsb env motive) as [mot_row |] eqn:Hm; try discriminate.
    destruct (grtt_infer_with allowsb join_branches
                ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) subject2)
      as [[act_mot w bw] |] eqn:Hbdy; try discriminate.
    destruct (gty_eq_dec (gcanonical_ty [] act_mot) (gcanonical_ty [] motive)); try discriminate.
    destruct (allowsb (uses w x) q && demand_eqb bw mot_row) eqn:Hok; inversion Hchk; subst.
    apply andb_true_iff in Hok as [Hw Hbw].
    eapply GGradeLetBox; eauto using gtype_demand_sound, demand_eqb_sound.
  - destruct (grtt_infer_with allowsb join_branches env subject) as [[A u a] |] eqn:Hb; try discriminate.
    destruct (gtype_demand allowsb env right_ty) as [b |] eqn:Hr; inversion Hchk; subst.
    constructor; eauto using gtype_demand_sound.
  - destruct (gtype_demand allowsb env left_ty) as [a |] eqn:Hl; try discriminate.
    destruct (grtt_infer_with allowsb join_branches env subject) as [[B u b] |] eqn:Hb; inversion Hchk; subst.
    constructor; eauto using gtype_demand_sound.
  - destruct (gfresh env x && gfresh env y) eqn:Hfr; try discriminate.
    apply andb_true_iff in Hfr as [Hfrx Hfry].
    destruct (grtt_infer_with allowsb join_branches env subject1) as [[srt w vs] |] eqn:Hs; try discriminate.
    destruct srt as [| | | | | | | A B]; try discriminate.
    destruct (gtype_demand allowsb env A) as [a |] eqn:HA; try discriminate.
    destruct (gtype_demand allowsb env B) as [b |] eqn:HB; try discriminate.
    destruct (gtype_demand allowsb env motive) as [mot_row |] eqn:Hm; try discriminate.
    destruct (grtt_infer_with allowsb join_branches
                ({| gbinder := x; gannotation := A; gtype_uses := a |} :: env) subject2)
      as [[t1 u1 b1] |] eqn:Hl; try discriminate.
    destruct (grtt_infer_with allowsb join_branches
                ({| gbinder := y; gannotation := B; gtype_uses := b |} :: env) subject3)
      as [[t2 u2 b2] |] eqn:Hr; try discriminate.
    destruct (gty_eq_dec (gcanonical_ty [] t1) (gcanonical_ty [] motive)); try discriminate.
    destruct (gty_eq_dec (gcanonical_ty [] t2) (gcanonical_ty [] motive)); try discriminate.
    destruct (allowsb (uses u1 x) 1 && allowsb (uses u2 y) 1 &&
              demand_eqb b1 mot_row && demand_eqb b2 mot_row) eqn:Hok; try discriminate.
    apply andb_true_iff in Hok as [Hok1 Hb2].
    apply andb_true_iff in Hok1 as [Hok2 Hb1].
    apply andb_true_iff in Hok2 as [Hu1 Hu2].
    destruct join_branches eqn:Ejb.
    + inversion Hchk; subst.
      eapply GGradeMatchSum; eauto using gtype_demand_sound, demand_eqb_sound; try discriminate.
    + destruct (demand_eqb (without x u1) (without y u2)) eqn:Hbr; inversion Hchk; subst.
      eapply GGradeMatchSum; eauto using gtype_demand_sound, demand_eqb_sound.
Qed.

(* Verified GrTT Core Examples *)

Definition grtt_id (r_outer s_inner : nat) : gterm :=
  GLam 1 0 r_outer (GUniv 0) (GLam 2 s_inner 0 (GTVar 1) (GVar 2)).

Example grtt_pure_dependent_id :
  (match grtt_infer_with Nat.eqb false [] (grtt_id 2 1) with
   | Some res => gresult_type res = GPi 1 0 2 (GUniv 0) (GPi 2 1 0 (GTVar 1) (GTVar 1))
   | None => False
   end) /\
  grtt_infer_with Nat.eqb false [] (grtt_id 1 1) = None /\
  grtt_infer_with Nat.eqb false [] (grtt_id 2 0) = None /\
  grtt_infer_with Nat.eqb false [] (grtt_id 2 2) = None.
Proof. repeat split; reflexivity. Qed.

Definition sigma_env : gcontext :=
  [{| gbinder := 1;
      gannotation := GPi 2 1 1 GNat (GVec (IndexVar 2));
      gtype_uses := [] |};
   {| gbinder := 3;
      gannotation := GPi 4 1 1 GNat (GPi 5 2 0 (GVec (IndexVar 4)) GNat);
      gtype_uses := [] |}].

Definition sigma_box_ty : gty :=
  GSigma 10 1 GNat (GBox 2 (GVec (IndexVar 10))).

Definition sigma_intro_ok : gterm :=
  GPair 10 1 GNat (GBox 2 (GVec (IndexVar 10)))
    (GNatVal (IndexLit 3))
    (GPromote 2 (GAppNat (GVar 1) (IndexLit 3))).

Definition sigma_intro_bad_idx : gterm :=
  GPair 10 1 GNat (GBox 2 (GVec (IndexVar 10)))
    (GNatVal (IndexLit 3))
    (GPromote 2 (GAppNat (GVar 1) (IndexLit 4))).

Definition sigma_elim_ok : gterm :=
  GLetPair 11 12 1 GNat sigma_intro_ok
    (GLetBox 13 GNat (GVar 12)
      (GAppVal (GAppNat (GVar 3) (IndexVar 11)) (GVar 13))).

Definition sigma_elim_bad_idx : gterm :=
  GLetPair 11 12 1 GNat sigma_intro_ok
    (GLetBox 13 GNat (GVar 12)
      (GAppVal (GAppNat (GVar 3) (IndexLit 4)) (GVar 13))).

Example grtt_sigma_asymmetric_box :
  (match grtt_infer_with Nat.eqb false sigma_env sigma_intro_ok with
   | Some res => gresult_type res = sigma_box_ty
   | None => False
   end) /\
  grtt_infer_with Nat.eqb false sigma_env sigma_intro_bad_idx = None /\
  (match grtt_infer_with Nat.eqb false sigma_env sigma_elim_ok with
   | Some res => gresult_type res = GNat
   | None => False
   end) /\
  grtt_infer_with Nat.eqb false sigma_env sigma_elim_bad_idx = None.
Proof. repeat split; reflexivity. Qed.

Definition sum_env : gcontext :=
  [{| gbinder := 10; gannotation := GSum GNat GNat; gtype_uses := [] |}].

Definition sum_branch_test (s : nat) : gterm :=
  GLam 1 s 0 GNat
    (GMatchSum 2 3 GNat (GVar 10)
      (GNatVal (IndexAdd (IndexVar 1) (IndexVar 2)))
      (GNatVal (IndexAdd (IndexAdd (IndexVar 1) (IndexVar 1)) (IndexVar 3)))).

Example grtt_sum_exact_vs_bound :
  grtt_infer_with Nat.eqb false sum_env (sum_branch_test 1) = None /\
  grtt_infer_with Nat.eqb false sum_env (sum_branch_test 2) = None /\
  (exists res, grtt_infer_with Nat.leb true sum_env (sum_branch_test 2) = Some res) /\
  grtt_infer_with Nat.leb true sum_env (sum_branch_test 1) = None.
Proof. split; [reflexivity | split; [reflexivity | split; [eexists; reflexivity | reflexivity]]]. Qed.

End GrttCore.

End GradedMetatheory.
