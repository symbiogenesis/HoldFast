(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Require Import graded_pure graded_domains graded_cbv graded_type_irrelevance.
Import ListNotations GradedPure GradedTypeIrrelevance.

Module GradedErasure.

(* ================================================================= *)
(* Part 1: CBV Evaluator, Erased Syntax, and Type Extraction         *)
(* ================================================================= *)

Inductive rval : Type :=
| RNat (n : nat)
| RClos (x allowance : nat) (body : term) (env : nat -> rval)
| RErased.

Definition upd_rval (rho : nat -> rval) (x : nat) (v : rval) : nat -> rval :=
  fun y => if Nat.eqb y x then v else rho y.

Fixpoint eval_index_rval (rho : nat -> rval) (i : index) : option nat :=
  match i with
  | IndexVar x =>
      match rho x with
      | RNat n => Some n
      | _ => None
      end
  | IndexLit n => Some n
  | IndexAdd l r =>
      match eval_index_rval rho l, eval_index_rval rho r with
      | Some a, Some b => Some (a + b)
      | _, _ => None
      end
  end.

Fixpoint eval_term (fuel : nat) (rho : nat -> rval) (t : term) : option rval :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      | Var x => Some (rho x)
      | NatValue i => option_map RNat (eval_index_rval rho i)
      | Lambda x allowance _ body => Some (RClos x allowance body rho)
      | ApplyNat callee arg =>
          match eval_term fuel' rho callee, eval_index_rval rho arg with
          | Some (RClos x _ body env_c), Some n =>
              eval_term fuel' (upd_rval env_c x (RNat n)) body
          | _, _ => None
          end
      | ApplyValue callee arg =>
          match eval_term fuel' rho callee, eval_term fuel' rho arg with
          | Some (RClos x _ body env_c), Some v =>
              eval_term fuel' (upd_rval env_c x v) body
          | _, _ => None
          end
      | LetNat x _ init body =>
          match eval_index_rval rho init with
          | Some n => eval_term fuel' (upd_rval rho x (RNat n)) body
          | None => None
          end
      | ApplyType callee _ =>
          match eval_term fuel' rho callee with
          | Some (RClos x _ body env_c) =>
              eval_term fuel' (upd_rval env_c x RErased) body
          | _ => None
          end
      end
  end.

Inductive eterm : Type :=
| EVar (x : nat)
| ENat (i : index)
| ELam (bx : option nat) (body : eterm)
| EApp (callee arg : eterm)
| ELet (bind : option (nat * index)) (body : eterm)
| EErased.

Inductive eval_rval : Type :=
| EVNat (n : nat)
| EVClos (bx : option nat) (body : eterm) (env : nat -> eval_rval)
| EVErased.

Definition upd_erval (erho : nat -> eval_rval) (x : nat) (v : eval_rval) : nat -> eval_rval :=
  fun y => if Nat.eqb y x then v else erho y.

Fixpoint eval_index_erval (erho : nat -> eval_rval) (i : index) : option nat :=
  match i with
  | IndexVar x =>
      match erho x with
      | EVNat n => Some n
      | _ => None
      end
  | IndexLit n => Some n
  | IndexAdd l r =>
      match eval_index_erval erho l, eval_index_erval erho r with
      | Some a, Some b => Some (a + b)
      | _, _ => None
      end
  end.

Fixpoint eval_erased (fuel : nat) (erho : nat -> eval_rval) (t : eterm) : option eval_rval :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      | EVar x => Some (erho x)
      | ENat i => option_map EVNat (eval_index_erval erho i)
      | ELam bx body => Some (EVClos bx body erho)
      | EApp callee arg =>
          match eval_erased fuel' erho callee, eval_erased fuel' erho arg with
          | Some (EVClos None body eenv), Some _ =>
              eval_erased fuel' eenv body
          | Some (EVClos (Some x) body eenv), Some ev =>
              eval_erased fuel' (upd_erval eenv x ev) body
          | _, _ => None
          end
      | ELet None body => eval_erased fuel' erho body
      | ELet (Some (x, init)) body =>
          match eval_index_erval erho init with
          | Some n => eval_erased fuel' (upd_erval erho x (EVNat n)) body
          | None => None
          end
      | EErased => Some EVErased
      end
  end.

(* Lightweight structural type extractor ignoring type_uses so erasure is type_uses-invariant *)
Fixpoint expr_type (env : context) (t : term) : option ty :=
  match t with
  | Var x => option_map annotation (lookup env x)
  | NatValue _ => Some Natural
  | Lambda x allowance domain body =>
      option_map (Pi x allowance domain)
        (expr_type ({| binder := x; annotation := domain; type_uses := [] |} :: env) body)
  | ApplyNat callee arg =>
      match expr_type env callee with
      | Some (Pi x _ Natural cod) => Some (substitute_type x arg cod)
      | _ => None
      end
  | ApplyValue callee _ =>
      match expr_type env callee with
      | Some (Pi _ _ _ cod) => Some cod
      | _ => None
      end
  | LetNat x _ init body =>
      match expr_type ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body with
      | Some kind => Some (substitute_type x init kind)
      | None => None
      end
  | ApplyType callee arg =>
      match expr_type env callee with
      | Some (Pi x _ (Universe _) cod) => Some (substitute_type_variable x arg cod)
      | _ => None
      end
  end.

Lemma expr_type_ann_equiv : forall env1 env2 t,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2
             | None, None => True
             | _, _ => False
             end) ->
  expr_type env1 t = expr_type env2 t.
Proof.
  intros env1 env2 t. revert env1 env2.
  induction t; intros env1 env2 Hrel; cbn [expr_type].
  - specialize (Hrel x).
    destruct (lookup env1 x), (lookup env2 x); try contradiction; try reflexivity.
    destruct Hrel as [_ Hann]. cbn [option_map]. now rewrite Hann.
  - reflexivity.
  - erewrite IHt; [reflexivity |].
    intro y. unfold lookup. cbn [find binder].
    destruct (Nat.eqb y x); [split; reflexivity |].
    fold (lookup env1 y). fold (lookup env2 y). exact (Hrel y).
  - rewrite (IHt _ _ Hrel). reflexivity.
  - rewrite (IHt1 _ _ Hrel). reflexivity.
  - erewrite IHt; [reflexivity |].
    intro y. unfold lookup. cbn [find binder].
    destruct (Nat.eqb y x); [split; reflexivity |].
    fold (lookup env1 y). fold (lookup env2 y). exact (Hrel y).
  - rewrite (IHt _ _ Hrel). reflexivity.
Qed.

Lemma derives_expr_type : forall allows env t res,
  DerivesWith allows env t res ->
  expr_type env t = Some (result_type res).
Proof.
  intros allows env t res Hd.
  induction Hd; cbn in *.
  - rewrite H. reflexivity.
  - reflexivity.
  - erewrite expr_type_ann_equiv; [|].
    + rewrite IHHd. reflexivity.
    + intro y. unfold lookup. cbn [find binder].
      destruct (Nat.eqb y x); [split; reflexivity |].
      fold (lookup env y). destruct (lookup env y); [split; reflexivity | exact I].
  - rewrite IHHd. reflexivity.
  - rewrite IHHd1. reflexivity.
  - rewrite IHHd. reflexivity.
  - rewrite IHHd. reflexivity.
Qed.

Definition callee_allowance (env : context) (callee : term) : option nat :=
  match expr_type env callee with
  | Some (Pi _ allowance _ _) => Some allowance
  | _ => None
  end.

Fixpoint erase_term (env : context) (t : term) : eterm :=
  match t with
  | Var x => EVar x
  | NatValue i => ENat i
  | Lambda x allowance domain body =>
      ELam (if Nat.eqb allowance 0 then None else Some x)
        (erase_term ({| binder := x; annotation := domain; type_uses := [] |} :: env) body)
  | ApplyNat callee arg =>
      match callee_allowance env callee with
      | Some 0 => EApp (erase_term env callee) EErased
      | _ => EApp (erase_term env callee) (ENat arg)
      end
  | ApplyValue callee arg =>
      match callee_allowance env callee with
      | Some 0 => EApp (erase_term env callee) EErased
      | _ => EApp (erase_term env callee) (erase_term env arg)
      end
  | LetNat x allowance init body =>
      let env' := {| binder := x; annotation := Natural; type_uses := [] |} :: env in
      if Nat.eqb allowance 0 then ELet None (erase_term env' body)
      else ELet (Some (x, init)) (erase_term env' body)
  | ApplyType callee _ =>
      EApp (erase_term env callee) EErased
  end.

Lemma erase_term_ann_equiv : forall env1 env2 t,
  (forall y, match lookup env1 y, lookup env2 y with
             | Some e1, Some e2 => binder e1 = binder e2 /\ annotation e1 = annotation e2
             | None, None => True
             | _, _ => False
             end) ->
  erase_term env1 t = erase_term env2 t.
Proof.
  intros env1 env2 t. revert env1 env2.
  induction t; intros env1 env2 Hrel; cbn; try reflexivity.
  - f_equal. apply IHt. intro y. unfold lookup. cbn [find binder].
    destruct (Nat.eqb y x); [split; reflexivity |].
    fold (lookup env1 y). fold (lookup env2 y). exact (Hrel y).
  - unfold callee_allowance. erewrite expr_type_ann_equiv by exact Hrel.
    rewrite (IHt _ _ Hrel). reflexivity.
  - unfold callee_allowance. erewrite expr_type_ann_equiv by exact Hrel.
    rewrite (IHt1 _ _ Hrel), (IHt2 _ _ Hrel). reflexivity.
  - destruct (Nat.eqb allowance 0); f_equal; apply IHt; intro y; unfold lookup; cbn [find binder];
      destruct (Nat.eqb y x); [split; reflexivity | fold (lookup env1 y); fold (lookup env2 y); exact (Hrel y)
                             | split; reflexivity | fold (lookup env1 y); fold (lookup env2 y); exact (Hrel y)].
  - rewrite (IHt _ _ Hrel). reflexivity.
Qed.

Lemma erase_term_head_type_uses : forall x dom a1 a2 env t,
  erase_term ({| binder := x; annotation := dom; type_uses := a1 |} :: env) t =
  erase_term ({| binder := x; annotation := dom; type_uses := a2 |} :: env) t.
Proof.
  intros x dom a1 a2 env t. apply erase_term_ann_equiv.
  intro y. unfold lookup. cbn [find binder].
  destruct (Nat.eqb y x); [split; reflexivity |].
  fold (lookup env y). destruct (lookup env y); [split; reflexivity | exact I].
Qed.

(* ================================================================= *)
(* Part 2: Alpha-Invariant Shape Types (De Bruijn for TypeVar)       *)
(* ================================================================= *)

Inductive dty : Type :=
| DNat
| DVec
| DUniv
| DBound (idx : nat)
| DPi (allowance : nat) (dom cod : dty).

Fixpoint lift_dty (cutoff delta : nat) (d : dty) : dty :=
  match d with
  | DNat | DVec | DUniv => d
  | DBound k => if Nat.ltb k cutoff then DBound k else DBound (k + delta)
  | DPi al dom cod => DPi al (lift_dty cutoff delta dom) (lift_dty (S cutoff) delta cod)
  end.

Fixpoint subst_dty (k : nat) (arg d : dty) : dty :=
  match d with
  | DNat | DVec | DUniv => d
  | DBound i =>
      if Nat.eqb i k then lift_dty 0 k arg
      else if Nat.ltb i k then DBound i
      else DBound (i - 1)
  | DPi al dom cod => DPi al (subst_dty k arg dom) (subst_dty (S k) arg cod)
  end.

Fixpoint bound_pos (bound : list nat) (x : nat) : option nat :=
  match bound with
  | [] => None
  | y :: rest =>
      if Nat.eqb x y then Some 0
      else option_map S (bound_pos rest x)
  end.

Fixpoint eval_dty (bound : list nat) (theta : nat -> dty) (t : ty) : dty :=
  match t with
  | Natural => DNat
  | Vector _ => DVec
  | Universe _ => DUniv
  | TypeVar y =>
      match bound_pos bound y with
      | Some k => DBound k
      | None => lift_dty 0 (length bound) (theta y)
      end
  | Pi x allowance dom cod =>
      DPi allowance (eval_dty bound theta dom) (eval_dty (x :: bound) theta cod)
  end.

Definition upd_theta (theta : nat -> dty) (x : nat) (d : dty) : nat -> dty :=
  fun y => if Nat.eqb y x then d else theta y.

Lemma lift_dty_0 : forall c d, lift_dty c 0 d = d.
Proof.
  intros c d. revert c.
  induction d; intros c; cbn [lift_dty]; try reflexivity.
  - destruct (Nat.ltb idx c); [reflexivity | f_equal; lia].
  - now rewrite IHd1, IHd2.
Qed.

Lemma lift_dty_shift : forall c1 c2 d1 d2 t,
  c1 <= c2 -> c2 <= c1 + d1 ->
  lift_dty c2 d2 (lift_dty c1 d1 t) = lift_dty c1 (d1 + d2) t.
Proof.
  intros c1 c2 d1 d2 t. revert c1 c2 d1 d2.
  induction t; intros c1 c2 d1 d2 H1 H2; cbn [lift_dty]; try reflexivity.
  - destruct (idx <? c1) eqn:Hlt1; cbn [lift_dty].
    + assert (Hlt2 : (idx <? c2) = true) by (apply Nat.ltb_lt; apply Nat.ltb_lt in Hlt1; lia).
      rewrite Hlt2. reflexivity.
    + apply Nat.ltb_ge in Hlt1.
      assert (Hlt2 : (idx + d1 <? c2) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt2. f_equal. lia.
  - rewrite IHt1 by assumption. f_equal. apply IHt2; lia.
Qed.

Lemma subst_lift_cancel : forall c k arg d,
  c <= k ->
  subst_dty k arg (lift_dty c (S (k - c)) d) = lift_dty c (k - c) d.
Proof.
  intros c k arg d. revert c k arg.
  induction d; intros c k arg Hle; cbn [lift_dty subst_dty]; try reflexivity.
  - destruct (idx <? c) eqn:Hlt.
    + cbn [subst_dty].
      assert (Hnk : Nat.eqb idx k = false) by (apply Nat.eqb_neq; apply Nat.ltb_lt in Hlt; lia).
      assert (Hlk : (idx <? k) = true) by (apply Nat.ltb_lt; apply Nat.ltb_lt in Hlt; lia).
      rewrite Hnk, Hlk. reflexivity.
    + cbn [subst_dty]. apply Nat.ltb_ge in Hlt.
      assert (Hnk : Nat.eqb (idx + S (k - c)) k = false) by (apply Nat.eqb_neq; lia).
      assert (Hlk : (idx + S (k - c) <? k) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hnk, Hlk. f_equal. lia.
  - rewrite IHd1 by exact Hle. f_equal.
    specialize (IHd2 (S c) (S k) arg ltac:(lia)).
    replace (S k - S c) with (k - c) in IHd2 by lia.
    exact IHd2.
Qed.

Lemma eval_dty_subst_index : forall bound theta x arg t,
  eval_dty bound theta (substitute_type x arg t) = eval_dty bound theta t.
Proof.
  intros bound theta x arg t. revert bound.
  induction t; intros bound; cbn; try reflexivity.
  rewrite IHt1. f_equal.
  destruct (Nat.eqb x x0); [reflexivity | apply IHt2].
Qed.

Fixpoint valid_names (names : list (nat * nat)) : Prop :=
  match names with
  | [] => True
  | (_, d) :: rest => d = length rest /\ valid_names rest
  end.

Lemma valid_names_snd_lt : forall names a b,
  valid_names names ->
  In (a, b) names ->
  b < length names.
Proof.
  induction names as [| [x d] rest IH]; intros a b Hval Hin; cbn in *.
  - contradiction.
  - destruct Hval as [Hd Hrest]. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. lia.
    + specialize (IH a b Hrest Hin). lia.
Qed.

Lemma bound_pos_canonical_valid : forall names y,
  valid_names names ->
  bound_pos (map (fun p => 2 * snd p) names) (canonical_index names y) =
  bound_pos (map fst names) y.
Proof.
  induction names as [| [x d] rest IH]; intros y Hval; cbn [map bound_pos].
  - reflexivity.
  - destruct Hval as [Hd Hrest].
    unfold canonical_index. cbn [find fst snd map bound_pos].
    destruct (Nat.eqb y x) eqn:Ey; cbn [snd bound_pos].
    + rewrite Nat.eqb_refl. reflexivity.
    + destruct (find (fun binding => Nat.eqb y (fst binding)) rest) as [[a b] |] eqn:Hf; cbn [snd bound_pos].
      * assert (Hin : In (a, b) rest) by (eapply find_some; exact Hf).
        assert (Hlt : b < length rest) by (eapply valid_names_snd_lt; eauto).
        assert (Hne : Nat.eqb (2 * b) (2 * d) = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne. f_equal.
        specialize (IH y Hrest). unfold canonical_index in IH. rewrite Hf in IH. exact IH.
      * assert (Hodd : Nat.eqb (2 * y + 1) (2 * d) = false) by (apply Nat.eqb_neq; lia).
        rewrite Hodd. f_equal.
        specialize (IH y Hrest). unfold canonical_index in IH. rewrite Hf in IH. exact IH.
Qed.

Lemma eval_dty_canon_valid : forall names theta t,
  valid_names names ->
  eval_dty (map fst names) theta t =
  eval_dty (map (fun p => 2 * snd p) names) (fun z => theta ((z - 1) / 2)) (canonical_type names t).
Proof.
  intros names theta t. revert names.
  induction t; intros names Hval; cbn [eval_dty canonical_type].
  - reflexivity.
  - reflexivity.
  - rewrite IHt1 by exact Hval. f_equal.
    apply (IHt2 ((x, length names) :: names)). cbn [valid_names]. split; [reflexivity | exact Hval].
  - reflexivity.
  - rewrite bound_pos_canonical_valid by exact Hval.
    rewrite !length_map.
    destruct (bound_pos (map fst names) x) eqn:Hbp; [reflexivity |].
    unfold canonical_index.
    destruct (find (fun binding => Nat.eqb x (fst binding)) names) as [[a b] |] eqn:Hf.
    + assert (Hin : In (a, b) names) by (eapply find_some; exact Hf).
      assert (Hxa : x = a).
      { apply find_some in Hf as [_ Heq]. cbn in Heq. apply Nat.eqb_eq in Heq. exact Heq. }
      subst a. exfalso.
      clear -Hin Hbp.
      induction names as [| [u v] r IHr]; cbn in *; [contradiction |].
      destruct (Nat.eqb x u) eqn:Eu; [discriminate |].
      destruct (bound_pos (map fst r) x) eqn:Hr; [discriminate |].
      destruct Hin as [Heq | Hin].
      * inversion Heq; subst. rewrite Nat.eqb_refl in Eu. discriminate.
      * exact (IHr eq_refl Hin).
    + replace (2 * x + 1 - 1) with (x * 2) by lia.
      rewrite Nat.div_mul by lia. reflexivity.
Qed.

Lemma eval_dty_canonical : forall theta t1 t2,
  canonical_type [] t1 = canonical_type [] t2 ->
  eval_dty [] theta t1 = eval_dty [] theta t2.
Proof.
  intros theta t1 t2 Hcan.
  change (eval_dty [] theta t1) with (eval_dty (map (@fst nat nat) []) theta t1).
  change (eval_dty [] theta t2) with (eval_dty (map (@fst nat nat) []) theta t2).
  rewrite (eval_dty_canon_valid [] theta t1 I).
  rewrite (eval_dty_canon_valid [] theta t2 I).
  cbn. rewrite Hcan. reflexivity.
Qed.

Fixpoint type_var_free (y : nat) (t : ty) : bool :=
  match t with
  | Natural | Vector _ | Universe _ => false
  | TypeVar z => Nat.eqb y z
  | Pi x _ dom cod => type_var_free y dom || (if Nat.eqb x y then false else type_var_free y cod)
  end.

Lemma fresh_type_demand_not_free : forall env kind row y,
  fresh env y = true ->
  TypeDemand env kind row ->
  type_var_free y kind = false.
Proof.
  intros env kind row y Hfr Hd. revert y Hfr.
  induction Hd; intros y Hfr; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHHd1 by exact Hfr. cbn.
    destruct (Nat.eqb x y) eqn:Exy; [reflexivity |].
    apply IHHd2. unfold fresh, lookup in *. cbn [find binder].
    rewrite Nat.eqb_sym, Exy. exact Hfr.
  - reflexivity.
  - apply Nat.eqb_neq. intro Heq. subst y.
    unfold fresh in Hfr. rewrite H in Hfr. discriminate.
Qed.

Lemma nat_type_demand_not_free : forall env kind row y,
  (forall entry, lookup env y = Some entry -> forall lvl, annotation entry <> Universe lvl) ->
  TypeDemand env kind row ->
  type_var_free y kind = false.
Proof.
  intros env kind row y Hnu Hd. revert y Hnu.
  induction Hd; intros y Hnu; cbn [type_var_free].
  - reflexivity.
  - reflexivity.
  - rewrite IHHd1 by exact Hnu. cbn [orb].
    destruct (Nat.eqb x y) eqn:Exy; [reflexivity |].
    apply IHHd2. intros entry Hlook lvl.
    unfold lookup in Hlook. cbn [find binder] in Hlook.
    rewrite Nat.eqb_sym, Exy in Hlook. exact (Hnu entry Hlook lvl).
  - reflexivity.
  - destruct (Nat.eqb y x) eqn:Eyx; [| reflexivity].
    apply Nat.eqb_eq in Eyx. subst y.
    exfalso. eapply Hnu; eauto.
Qed.

Lemma bound_pos_in_some : forall bound y,
  In y bound -> exists k, bound_pos bound y = Some k.
Proof.
  induction bound as [| a rest IH]; intros y Hin; cbn [bound_pos In] in *.
  - contradiction.
  - destruct (Nat.eqb y a) eqn:Eya.
    + eexists; reflexivity.
    + destruct Hin as [Heq | Hin]; [subst; rewrite Nat.eqb_refl in Eya; discriminate |].
      destruct (IH y Hin) as [k Hk]. rewrite Hk. eexists; reflexivity.
Qed.

Lemma bound_pos_none_not_in : forall bound y,
  bound_pos bound y = None -> ~ In y bound.
Proof.
  intros bound y Hnone Hin.
  destruct (bound_pos_in_some bound y Hin) as [k Hk]. congruence.
Qed.

Lemma bound_pos_lt : forall bound y k,
  bound_pos bound y = Some k -> k < length bound.
Proof.
  induction bound as [| a rest IH]; intros y k Hbp; cbn [bound_pos length] in *; [discriminate |].
  destruct (Nat.eqb y a).
  - inversion Hbp; lia.
  - destruct (bound_pos rest y) eqn:Hr; inversion Hbp; subst.
    specialize (IH y n Hr). lia.
Qed.

Lemma bound_pos_some_in : forall bound y k,
  bound_pos bound y = Some k -> In y bound.
Proof.
  induction bound as [| a rest IH]; intros y k Hbp; cbn [bound_pos In] in *; [discriminate |].
  destruct (Nat.eqb y a) eqn:Ea.
  - left. apply Nat.eqb_eq in Ea. symmetry. exact Ea.
  - destruct (bound_pos rest y) as [n |] eqn:Hr; [| discriminate].
    right. exact (IH y n Hr).
Qed.

Lemma eval_dty_not_free_upd : forall bound theta y d t,
  (In y bound \/ type_var_free y t = false) ->
  eval_dty bound (upd_theta theta y d) t = eval_dty bound theta t.
Proof.
  intros bound theta y d t. revert bound.
  induction t; intros bound Hcond; cbn [eval_dty type_var_free] in *; try reflexivity.
  - assert (Hdom : In y bound \/ type_var_free y t1 = false).
    { destruct Hcond as [Hin | Hnf]; [left; exact Hin |].
      apply orb_false_elim in Hnf as [Hd _]. right; exact Hd. }
    assert (Hcod : In y (x :: bound) \/ type_var_free y t2 = false).
    { destruct Hcond as [Hin | Hnf]; [left; right; exact Hin |].
      apply orb_false_elim in Hnf as [_ Hc].
      destruct (Nat.eqb x y) eqn:Exy.
      - apply Nat.eqb_eq in Exy. left. left. exact Exy.
      - right; exact Hc. }
    rewrite (IHt1 _ Hdom), (IHt2 _ Hcod). reflexivity.
  - destruct Hcond as [Hin | Hnf].
    + destruct (bound_pos_in_some bound y Hin) as [k Hk].
      destruct (Nat.eqb x y) eqn:Exy.
      * apply Nat.eqb_eq in Exy. subst x. rewrite Hk. reflexivity.
      * destruct (bound_pos bound x); [reflexivity |].
        unfold upd_theta. rewrite Exy. reflexivity.
    + destruct (bound_pos bound x); [reflexivity |].
      unfold upd_theta. rewrite Nat.eqb_sym, Hnf. reflexivity.
Qed.

Lemma bound_pos_app_single : forall bound x y,
  match bound_pos bound y with
  | Some k => bound_pos (bound ++ [x]) y = Some k
  | None =>
      bound_pos (bound ++ [x]) y =
      if Nat.eqb y x then Some (length bound) else None
  end.
Proof.
  induction bound as [| a rest IH]; intros x y; cbn [app bound_pos length].
  - reflexivity.
  - destruct (Nat.eqb y a) eqn:Eya; [reflexivity |].
    specialize (IH x y).
    destruct (bound_pos rest y); cbn [bound_pos] in *; rewrite IH; [reflexivity |].
    destruct (Nat.eqb y x); reflexivity.
Qed.

Lemma bound_pos_app_left : forall inner extra z,
  match bound_pos inner z with
  | Some k => bound_pos (inner ++ extra) z = Some k
  | None =>
      bound_pos (inner ++ extra) z =
      option_map (fun j => length inner + j) (bound_pos extra z)
  end.
Proof.
  induction inner as [| a rest IH]; intros extra z; cbn [app bound_pos length].
  - destruct (bound_pos extra z); reflexivity.
  - destruct (Nat.eqb z a); [reflexivity |].
    specialize (IH extra z). destruct (bound_pos rest z); rewrite IH; [reflexivity |].
    destruct (bound_pos extra z); cbn [option_map]; reflexivity.
Qed.

Lemma eval_dty_lift_extra : forall inner extra theta t,
  (forall b, In b extra -> type_var_free b t = false \/ In b inner) ->
  eval_dty (inner ++ extra) theta t =
  lift_dty (length inner) (length extra) (eval_dty inner theta t).
Proof.
  intros inner extra theta t. revert inner.
  induction t; intros inner Hcond; cbn [eval_dty lift_dty]; try reflexivity.
  - assert (Hdom : forall b, In b extra -> type_var_free b t1 = false \/ In b inner).
    { intros b Hb. destruct (Hcond b Hb) as [Hnf | Hin]; [| right; exact Hin].
      apply orb_false_elim in Hnf as [Hd _]. left; exact Hd. }
    assert (Hcod : forall b, In b extra -> type_var_free b t2 = false \/ In b (x :: inner)).
    { intros b Hb. destruct (Hcond b Hb) as [Hnf | Hin]; [| right; right; exact Hin].
      apply orb_false_elim in Hnf as [_ Hc].
      destruct (Nat.eqb x b) eqn:Exb.
      - apply Nat.eqb_eq in Exb. subst x. right. left. reflexivity.
      - left; exact Hc. }
    rewrite (IHt1 _ Hdom). f_equal. exact (IHt2 (x :: inner) Hcod).
  - pose proof (bound_pos_app_left inner extra x) as Hbp.
    destruct (bound_pos inner x) as [k |] eqn:Hk.
    + rewrite Hbp. cbn [lift_dty].
      apply bound_pos_lt in Hk.
      apply Nat.ltb_lt in Hk. rewrite Hk. reflexivity.
    + rewrite Hbp.
      destruct (bound_pos extra x) as [j |] eqn:Hj.
      * exfalso.
        assert (Hin_ex : In x extra) by (eapply bound_pos_some_in; exact Hj).
        destruct (Hcond x Hin_ex) as [Hnf | Hin_in].
        -- cbn [type_var_free] in Hnf. rewrite Nat.eqb_refl in Hnf. discriminate.
        -- exact (bound_pos_none_not_in _ _ Hk Hin_in).
      * cbn [lift_dty]. rewrite length_app.
        symmetry. apply lift_dty_shift; lia.
Qed.

Lemma eval_dty_subst_open : forall bound theta x d t,
  eval_dty bound (upd_theta theta x d) t =
  subst_dty (length bound) d (eval_dty (bound ++ [x]) theta t).
Proof.
  intros bound theta x d t. revert bound.
  induction t; intros bound; cbn [eval_dty subst_dty]; try reflexivity.
  - rewrite IHt1. f_equal. exact (IHt2 (x0 :: bound)).
  - pose proof (bound_pos_app_single bound x x0) as Hbp.
    destruct (bound_pos bound x0) as [k |] eqn:Hk.
    + rewrite Hbp. cbn [subst_dty].
      apply bound_pos_lt in Hk.
      assert (Hne : Nat.eqb k (length bound) = false) by (apply Nat.eqb_neq; lia).
      assert (Hlt : (k <? length bound) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hne, Hlt. reflexivity.
    + rewrite Hbp. destruct (Nat.eqb x0 x) eqn:Ex.
      * unfold upd_theta. rewrite Ex. cbn [subst_dty].
        rewrite Nat.eqb_refl. reflexivity.
      * unfold upd_theta. rewrite Ex. cbn [subst_dty].
        rewrite length_app. cbn [length].
        replace (length bound + 1) with (S (length bound - 0)) by lia.
        pose proof (subst_lift_cancel 0 (length bound) d (theta x0) (Nat.le_0_l _)) as Hcan.
        rewrite !Nat.sub_0_r in Hcan |- *.
        symmetry. exact Hcan.
Qed.

Lemma eval_dty_subst_type_var : forall env theta x level arg cod b z,
  fresh env x = true ->
  TypeDemand env arg z ->
  TypeDemand ({| binder := x; annotation := Universe level; type_uses := [] |} :: env) cod b ->
  eval_dty [] theta (substitute_type_variable x arg cod) =
  subst_dty 0 (eval_dty [] theta arg) (eval_dty [x] theta cod).
Proof.
  intros env theta x level arg cod b z Hfrx Harg Hcod.
  change 0 with (length (@nil nat)). change [x] with (@nil nat ++ [x]).
  rewrite <- (eval_dty_subst_open [] theta x (eval_dty [] theta arg) cod).
  assert (Hgen : forall cod0 bound env_c b0,
    (forall y, In y bound -> fresh env y = true) ->
    ~ In x bound ->
    (forall y, fresh env_c y = true -> fresh env y = true) ->
    TypeDemand env_c cod0 b0 ->
    eval_dty bound theta (substitute_type_variable x arg cod0) =
    eval_dty bound (upd_theta theta x (eval_dty [] theta arg)) cod0).
  { clear -Hfrx Harg.
    induction cod0; intros bound env_c b0 Hfrb Hnx Hfrc Htd;
      cbn [eval_dty substitute_type_variable]; try reflexivity.
    - inversion Htd; subst.
      lazymatch goal with
      | Htd1 : TypeDemand env_c cod0_1 ?a_dom,
        Htd2 : TypeDemand ({| binder := x0; annotation := cod0_1; type_uses := ?a_dom |} :: env_c) cod0_2 ?b_cod,
        Hfr0 : fresh env_c x0 = true |- _ =>
          rewrite (IHcod0_1 bound env_c a_dom Hfrb Hnx Hfrc Htd1); f_equal;
          destruct (Nat.eqb x x0) eqn:Ex;
          [ apply Nat.eqb_eq in Ex; subst x0;
            rewrite eval_dty_not_free_upd; [reflexivity | left; now left]
          | eapply IHcod0_2; [| | | exact Htd2];
            [ intros y [-> | Hin]; [exact (Hfrc _ Hfr0) | exact (Hfrb y Hin)]
            | intros [Heq | Hin]; [apply Nat.eqb_neq in Ex; congruence | exact (Hnx Hin)]
            | intros y Hy; apply Hfrc; unfold fresh, lookup in *; cbn [find binder] in Hy;
              destruct (Nat.eqb y x0); [discriminate | exact Hy] ] ]
      end.
    - destruct (Nat.eqb x x0) eqn:Ex.
      + apply Nat.eqb_eq in Ex. subst x0.
        destruct (bound_pos bound x) as [k |] eqn:Hk.
        * exfalso.
          assert (Hinx : In x bound) by (eapply bound_pos_some_in; exact Hk).
          exact (Hnx Hinx).
        * unfold upd_theta. rewrite Nat.eqb_refl.
          pose proof (eval_dty_lift_extra [] bound theta arg) as Hlift.
          cbn [app length] in Hlift. apply Hlift.
          intros y Hy. left. eapply fresh_type_demand_not_free; [exact (Hfrb y Hy) | exact Harg].
      + cbn [eval_dty]. destruct (bound_pos bound x0); [reflexivity |].
        unfold upd_theta. rewrite Nat.eqb_sym, Ex. reflexivity. }
  eapply Hgen; [| | | exact Hcod].
  - intros y [].
  - intros [].
  - intros y Hy. unfold fresh, lookup in *. cbn [find binder] in Hy.
    destruct (Nat.eqb y x); [discriminate | exact Hy].
Qed.

Lemma eval_dty_unused_subst : forall env theta x dom cod b d,
  fresh env x = true ->
  type_var_free x cod = false ->
  TypeDemand ({| binder := x; annotation := dom; type_uses := [] |} :: env) cod b ->
  subst_dty 0 d (eval_dty [x] theta cod) = eval_dty [] theta cod.
Proof.
  intros env theta x dom cod b d Hfr Hnf Htd.
  change 0 with (length (@nil nat)). change [x] with (@nil nat ++ [x]).
  rewrite <- eval_dty_subst_open.
  rewrite eval_dty_not_free_upd; [reflexivity | right; exact Hnf].
Qed.

(* ================================================================= *)
(* Part 3: Strictly Positive Simulation & Erasure Soundness          *)
(* ================================================================= *)

Definition allows_le (allows : nat -> nat -> Prop) : Prop :=
  forall a b, allows a b -> a <= b.

Lemma exact_allows_le : allows_le (@eq nat).
Proof. intros a b ->. lia. Qed.

Lemma bound_allows_le : allows_le le.
Proof. intros a b H. exact H. Qed.

Definition ctx_closed (env : context) : Prop :=
  forall y entry, lookup env y = Some entry ->
    forall z, fresh env z = true -> type_var_free z (annotation entry) = false.

Lemma ctx_closed_cons : forall env x dom a,
  fresh env x = true ->
  (exists row, TypeDemand env dom row) ->
  ctx_closed env ->
  ctx_closed ({| binder := x; annotation := dom; type_uses := a |} :: env).
Proof.
  intros env x dom a _ [rdom Hdom] Hwf y entry Hlook z Hfrz.
  unfold fresh, lookup in Hfrz. cbn [find binder] in Hfrz.
  destruct (Nat.eqb z x) eqn:Ezx; [discriminate |].
  fold (lookup env z) in Hfrz.
  assert (Hfrz_env : fresh env z = true) by exact Hfrz.
  unfold lookup in Hlook. cbn [find binder] in Hlook.
  destruct (Nat.eqb y x) eqn:Eyx.
  - inversion Hlook; subst. cbn [annotation].
    eapply fresh_type_demand_not_free; eauto.
  - fold (lookup env y) in Hlook.
    exact (Hwf y entry Hlook z Hfrz_env).
Qed.

Lemma ctx_closed_empty : ctx_closed [].
Proof. intros y e H. discriminate. Qed.

Lemma ctx_closed_extends : forall prefix env,
  Extends [] prefix env ->
  ctx_closed env.
Proof.
  intros prefix env Hext.
  assert (Hgen : forall base lst res,
    ctx_closed base -> Extends base lst res -> ctx_closed res).
  { intros base lst res Hbase H. induction H; [exact Hbase |].
    apply IHExtends. apply ctx_closed_cons; [exact H | eexists; exact H0 | exact Hbase]. }
  apply (Hgen [] prefix env); [exact ctx_closed_empty | exact Hext].
Qed.

Inductive ValRel : dty -> rval -> eval_rval -> Prop :=
| VR_Nat : forall n, ValRel DNat (RNat n) (EVNat n)
| VR_Vec : forall v ev, ValRel DVec v ev
| VR_Univ : forall v ev, ValRel DUniv v ev
| VR_Bound : forall k v ev, ValRel (DBound k) v ev
| VR_Clos : forall allows env0 x allowance dom0 cod0 a0 u0 v0 body rho0 erho0 theta0,
    allows_le allows ->
    fresh env0 x = true ->
    ctx_closed env0 ->
    (exists rdom, TypeDemand env0 dom0 rdom) ->
    DerivesWith allows ({| binder := x; annotation := dom0; type_uses := a0 |} :: env0)
      body {| result_type := cod0; computation_demand := u0; type_demand_row := v0 |} ->
    allows (uses u0 x) allowance ->
    (forall y, uses (without x u0) y > 0 ->
      exists entry, lookup env0 y = Some entry /\
        ValRel (eval_dty [] theta0 (annotation entry)) (rho0 y) (erho0 y)) ->
    ValRel (DPi allowance (eval_dty [] theta0 dom0) (eval_dty [x] theta0 cod0))
      (RClos x allowance body rho0)
      (EVClos (if Nat.eqb allowance 0 then None else Some x)
        (erase_term ({| binder := x; annotation := dom0; type_uses := [] |} :: env0) body) erho0).

Definition EnvRel (theta : nat -> dty) (env : context) (d : demand)
    (rho : nat -> rval) (erho : nat -> eval_rval) : Prop :=
  forall y, uses d y > 0 ->
    exists entry, lookup env y = Some entry /\
      ValRel (eval_dty [] theta (annotation entry)) (rho y) (erho y).

Lemma env_rel_app_left : forall theta env d1 d2 rho erho,
  EnvRel theta env (d1 ++ d2) rho erho -> EnvRel theta env d1 rho erho.
Proof.
  intros theta env d1 d2 rho erho H y Hy. apply H. rewrite uses_append. lia.
Qed.

Lemma env_rel_app_right : forall theta env d1 d2 rho erho,
  EnvRel theta env (d1 ++ d2) rho erho -> EnvRel theta env d2 rho erho.
Proof.
  intros theta env d1 d2 rho erho H y Hy. apply H. rewrite uses_append. lia.
Qed.

Lemma uses_scale_nat : forall n d y, uses (scale n d) y = n * uses d y.
Proof.
  intros n d y. induction d as [| [k m] rest IH].
  - cbn. lia.
  - change (scale n ((k, m) :: rest)) with ((k, n * m) :: scale n rest).
    cbn [uses]. rewrite IH, Nat.mul_add_distr_l.
    destruct (Nat.eqb y k); [| rewrite Nat.mul_0_r]; reflexivity.
Qed.

Lemma env_rel_scale_pos : forall theta env k d rho erho,
  EnvRel theta env (scale (S k) d) rho erho -> EnvRel theta env d rho erho.
Proof.
  intros theta env k d rho erho H y Hy. apply H. rewrite uses_scale_nat. lia.
Qed.

Lemma index_demand_erased_eval : forall theta env i d rho erho n,
  IndexDemand env i d ->
  EnvRel theta env d rho erho ->
  eval_index_rval rho i = Some n ->
  eval_index_erval erho i = Some n.
Proof.
  intros theta env i d rho erho n Hd. revert n.
  induction Hd; intros m Henv Heval; cbn [eval_index_rval eval_index_erval] in *.
  - assert (Hy : uses [(x, 1)] x > 0) by (cbn [uses]; rewrite Nat.eqb_refl; lia).
    destruct (Henv x Hy) as [entry' [Hlookup Hrel]].
    rewrite H in Hlookup. inversion Hlookup; subst entry'.
    rewrite H0 in Hrel. cbn [eval_dty] in Hrel.
    destruct (rho x), (erho x); inversion Hrel; inversion Heval; subst; reflexivity.
  - inversion Heval. reflexivity.
  - destruct (eval_index_rval rho left) eqn:Hl; try discriminate.
    destruct (eval_index_rval rho right) eqn:Hr; try discriminate.
    inversion Heval; subst.
    rewrite (IHHd1 _ (env_rel_app_left _ _ _ _ _ _ Henv) eq_refl).
    rewrite (IHHd2 _ (env_rel_app_right _ _ _ _ _ _ Henv) eq_refl).
    reflexivity.
Qed.

Lemma upd_env_rel_zero : forall theta0 x dom a env0 u0 rho0 erho0 w,
  uses u0 x = 0 ->
  (forall y, uses (without x u0) y > 0 ->
    exists entry, lookup env0 y = Some entry /\
      ValRel (eval_dty [] theta0 (annotation entry)) (rho0 y) (erho0 y)) ->
  EnvRel theta0 ({| binder := x; annotation := dom; type_uses := a |} :: env0)
    u0 (upd_rval rho0 x w) erho0.
Proof.
  intros theta0 x dom a env0 u0 rho0 erho0 w Hzero Henv y Hy.
  assert (Hne : Nat.eqb y x = false).
  { destruct (Nat.eqb y x) eqn:Heq; [| reflexivity].
    apply Nat.eqb_eq in Heq. subst y. lia. }
  assert (Hy' : uses (without x u0) y > 0) by (rewrite uses_without, Hne; exact Hy).
  destruct (Henv y Hy') as [entry [Hlook Hrel]].
  exists entry. split; [| unfold upd_rval; rewrite Hne; exact Hrel].
  unfold lookup. cbn [find binder]. rewrite Hne. exact Hlook.
Qed.

Lemma upd_env_rel_val : forall theta0 x dom a env0 u0 rho0 erho0 v ev,
  ValRel (eval_dty [] theta0 dom) v ev ->
  (forall y, uses (without x u0) y > 0 ->
    exists entry, lookup env0 y = Some entry /\
      ValRel (eval_dty [] theta0 (annotation entry)) (rho0 y) (erho0 y)) ->
  EnvRel theta0 ({| binder := x; annotation := dom; type_uses := a |} :: env0)
    u0 (upd_rval rho0 x v) (upd_erval erho0 x ev).
Proof.
  intros theta0 x dom a env0 u0 rho0 erho0 v ev Hval Henv y Hy.
  unfold lookup. cbn [find binder]. unfold upd_rval, upd_erval.
  destruct (Nat.eqb y x) eqn:Heq.
  - eexists. split; [reflexivity | exact Hval].
  - assert (Hy' : uses (without x u0) y > 0) by (rewrite uses_without, Heq; exact Hy).
    exact (Henv y Hy').
Qed.

Lemma upd_theta_env0_rel : forall theta0 x d_arg env0 u0 rho0 erho0,
  fresh env0 x = true ->
  ctx_closed env0 ->
  (forall y, uses (without x u0) y > 0 ->
    exists entry, lookup env0 y = Some entry /\
      ValRel (eval_dty [] theta0 (annotation entry)) (rho0 y) (erho0 y)) ->
  (forall y, uses (without x u0) y > 0 ->
    exists entry, lookup env0 y = Some entry /\
      ValRel (eval_dty [] (upd_theta theta0 x d_arg) (annotation entry)) (rho0 y) (erho0 y)).
Proof.
  intros theta0 x d_arg env0 u0 rho0 erho0 Hfr Hwf Henv y Hy.
  destruct (Henv y Hy) as [entry [Hlook Hrel]].
  exists entry. split; [exact Hlook |].
  rewrite eval_dty_not_free_upd; [exact Hrel | right; exact (Hwf y entry Hlook x Hfr)].
Qed.

Theorem erasure_simulation : forall fuel allows theta env t res rho erho v,
  allows_le allows ->
  ctx_closed env ->
  DerivesWith allows env t res ->
  EnvRel theta env (computation_demand res) rho erho ->
  eval_term fuel rho t = Some v ->
  exists ev, eval_erased fuel erho (erase_term env t) = Some ev /\
    ValRel (eval_dty [] theta (result_type res)) v ev.
Proof.
  induction fuel as [| fuel' IH]; intros allows theta env t res rho erho v Hale Hwf Hder Henv Heval;
    [discriminate |].
  inversion Hder; subst; cbn [erase_term eval_term eval_erased eval_dty result_type computation_demand] in *.
  - inversion Heval; subst.
    assert (Hy : uses [(x, 1)] x > 0) by (cbn [uses]; rewrite Nat.eqb_refl; lia).
    destruct (Henv x Hy) as [entry' [Hlook Hrel]].
    rewrite H in Hlook. inversion Hlook; subst entry'.
    exists (erho x). split; [reflexivity | exact Hrel].
  - destruct (eval_index_rval rho i) eqn:Hi; [| discriminate].
    inversion Heval; subst.
    erewrite index_demand_erased_eval by eauto.
    eexists. split; [reflexivity | constructor].
  - inversion Heval; subst.
    eexists. split; [reflexivity |].
    econstructor; eauto.
  - (* ApplyNat *)
    destruct (eval_term fuel' rho callee) as [vc |] eqn:Hcal; [| discriminate].
    destruct vc as [| xc alc bodyc rhoc |]; try discriminate.
    destruct (eval_index_rval rho argument) as [narg |] eqn:Harg; [| discriminate].
    assert (Hcal_exp : callee_allowance env callee = Some allowance).
    { unfold callee_allowance.
      lazymatch goal with
      | Hcal_der : DerivesWith allows env callee {| result_type := Pi x allowance Natural codomain; computation_demand := _; type_demand_row := _ |} |- _ =>
          erewrite derives_expr_type by exact Hcal_der; reflexivity
      end. }
    rewrite Hcal_exp.
    lazymatch goal with
    | Hcal_der : DerivesWith allows env callee {| result_type := Pi x allowance Natural codomain; computation_demand := _; type_demand_row := _ |} |- _ =>
        destruct (IH allows theta env callee _ rho erho _ Hale Hwf Hcal_der
          (env_rel_app_left _ _ _ _ _ _ Henv) Hcal) as [evc [Hevc Hrelc]]
    end.
    cbn [result_type eval_dty] in Hrelc.
    inversion Hrelc; subst.
    lazymatch goal with
    | Hale0 : allows_le ?allows0,
      Hfr0 : fresh ?env0 xc = true,
      Hwf0_base : ctx_closed ?env0,
      Htd_dom0 : exists rdom, TypeDemand ?env0 ?dom0 rdom,
      Hder0 : DerivesWith ?allows0 ({| binder := xc; annotation := ?dom0; type_uses := ?a0 |} :: ?env0) bodyc
        {| result_type := ?cod0; computation_demand := ?u0; type_demand_row := ?v0 |},
      Hall0 : ?allows0 (uses ?u0 xc) alc,
      Henv0_rel : forall y, uses (without xc ?u0) y > 0 ->
        exists entry, lookup ?env0 y = Some entry /\
          ValRel (eval_dty [] ?theta0 (annotation entry)) (rhoc y) (?erho0 y),
      Hdom_eq : eval_dty [] ?theta0 ?dom0 = DNat,
      Hcod_shape : eval_dty [xc] ?theta0 ?cod0 = eval_dty [x] theta codomain,
      Hfr_x : fresh env x = true,
      Hind_arg : IndexDemand env argument z,
      Htd_cod : TypeDemand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) codomain b |- _ =>
        assert (Hwf0 : ctx_closed ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)) by (apply ctx_closed_cons; assumption);
        assert (Hcod_eq : eval_dty [] (upd_theta theta0 xc DNat) cod0 =
                          eval_dty [] theta (substitute_type x argument codomain)) by
          (change 0 with (length (@nil nat)); change [xc] with (@nil nat ++ [xc]) in Hcod_shape;
           rewrite eval_dty_subst_index, eval_dty_subst_open; cbn [length];
           rewrite Hcod_shape;
           rewrite (eval_dty_unused_subst env theta x Natural codomain b DNat);
           [reflexivity | exact Hfr_x | | exact Htd_cod];
           eapply nat_type_demand_not_free; [| exact Htd_cod];
           unfold lookup; cbn [find binder]; rewrite Nat.eqb_refl;
           intros entry Heq lvl; inversion Heq; discriminate);
        destruct alc as [| k]; cbn [Nat.eqb eval_erased upd_erval] in *;
        [ assert (Hzero : uses u0 xc = 0) by (pose proof (Hale0 _ _ Hall0) as Hle; lia);
          assert (Hrel_body : EnvRel (upd_theta theta0 xc DNat)
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            u0 (upd_rval rhoc xc (RNat narg)) erho0) by
            (eapply upd_env_rel_zero; [exact Hzero | apply upd_theta_env0_rel; assumption]);
          destruct (IH allows0 (upd_theta theta0 xc DNat)
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            bodyc _ (upd_rval rhoc xc (RNat narg)) erho0 v Hale0 Hwf0 Hder0 Hrel_body Heval)
            as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          rewrite Hevc; cbn [eval_erased];
          erewrite (erase_term_head_type_uses xc dom0 [] a0 env0 bodyc);
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hcod_eq; exact Hrel]
        | assert (Hn_eval : eval_index_erval erho argument = Some narg) by
            (eapply index_demand_erased_eval; [exact Hind_arg | eapply env_rel_scale_pos, env_rel_app_right; exact Henv | exact Harg]);
          assert (Harg_rel : ValRel (eval_dty [] (upd_theta theta0 xc DNat) dom0) (RNat narg) (EVNat narg)) by
            (rewrite eval_dty_not_free_upd;
             [ rewrite Hdom_eq; apply VR_Nat
             | right; destruct Htd_dom0 as [rdom Htd_dom]; eapply fresh_type_demand_not_free; eauto ]);
          assert (Hrel_body : EnvRel (upd_theta theta0 xc DNat)
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            u0 (upd_rval rhoc xc (RNat narg)) (upd_erval erho0 xc (EVNat narg))) by
            (eapply upd_env_rel_val; [exact Harg_rel | apply upd_theta_env0_rel; assumption]);
          destruct (IH allows0 (upd_theta theta0 xc DNat)
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            bodyc _ (upd_rval rhoc xc (RNat narg)) (upd_erval erho0 xc (EVNat narg))
            v Hale0 Hwf0 Hder0 Hrel_body Heval) as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          rewrite Hevc; cbn [eval_erased]; rewrite Hn_eval;
          erewrite (erase_term_head_type_uses xc dom0 [] a0 env0 bodyc);
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hcod_eq; exact Hrel] ]
    end.
  - (* ApplyValue *)
    destruct (eval_term fuel' rho callee) as [vc |] eqn:Hcal; [| discriminate].
    destruct vc as [| xc alc bodyc rhoc |]; try discriminate.
    destruct (eval_term fuel' rho argument) as [varg |] eqn:Harg; [| discriminate].
    assert (Hcal_exp : callee_allowance env callee = Some allowance).
    { unfold callee_allowance.
      lazymatch goal with
      | Hcal_der : DerivesWith allows env callee {| result_type := Pi x allowance domain codomain; computation_demand := _; type_demand_row := _ |} |- _ =>
          erewrite derives_expr_type by exact Hcal_der; reflexivity
      end. }
    rewrite Hcal_exp.
    lazymatch goal with
    | Hcal_der : DerivesWith allows env callee {| result_type := Pi x allowance domain codomain; computation_demand := _; type_demand_row := _ |} |- _ =>
        destruct (IH allows theta env callee _ rho erho _ Hale Hwf Hcal_der
          (env_rel_app_left _ _ _ _ _ _ Henv) Hcal) as [evc [Hevc Hrelc]]
    end.
    cbn [result_type eval_dty] in Hrelc.
    inversion Hrelc; subst.
    lazymatch goal with
    | Hale0 : allows_le ?allows0,
      Hfr0 : fresh ?env0 xc = true,
      Hwf0_base : ctx_closed ?env0,
      Htd_dom0 : exists rdom, TypeDemand ?env0 ?dom0 rdom,
      Hder0 : DerivesWith ?allows0 ({| binder := xc; annotation := ?dom0; type_uses := ?a0 |} :: ?env0) bodyc
        {| result_type := ?cod0; computation_demand := ?u0; type_demand_row := ?v0 |},
      Hall0 : ?allows0 (uses ?u0 xc) alc,
      Henv0_rel : forall y, uses (without xc ?u0) y > 0 ->
        exists entry, lookup ?env0 y = Some entry /\
          ValRel (eval_dty [] ?theta0 (annotation entry)) (rhoc y) (?erho0 y),
      Hdom_eq : eval_dty [] ?theta0 ?dom0 = eval_dty [] theta domain,
      Hcod_shape : eval_dty [xc] ?theta0 ?cod0 = eval_dty [x] theta codomain,
      Harg_der : DerivesWith allows env argument {| result_type := ?kind; computation_demand := z; type_demand_row := ?arg_tr |},
      Hcanon_dom : canonical_type [] ?kind = canonical_type [] domain,
      Hfr_x : fresh env x = true,
      Htd_cod : TypeDemand env codomain ?b |- _ =>
        assert (Hwf0 : ctx_closed ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)) by (apply ctx_closed_cons; assumption);
        assert (Hcod_eq : eval_dty [] (upd_theta theta0 xc (eval_dty [] theta domain)) cod0 =
                          eval_dty [] theta codomain) by
          (change 0 with (length (@nil nat)); change [xc] with (@nil nat ++ [xc]) in Hcod_shape;
           rewrite eval_dty_subst_open; cbn [length]; rewrite Hcod_shape;
           pose proof (eval_dty_lift_extra [] [x] theta codomain) as Hlift;
           cbn [app length] in Hlift;
           assert (Hnf : type_var_free x codomain = false) by (eapply fresh_type_demand_not_free; [exact Hfr_x | exact Htd_cod]);
           rewrite Hlift by (intros v_b [-> | []]; left; exact Hnf);
           rewrite (subst_lift_cancel 0 0 _ _ (Nat.le_0_l _)); apply lift_dty_0);
        destruct alc as [| k]; cbn [Nat.eqb eval_erased upd_erval] in *;
        [ assert (Hzero : uses u0 xc = 0) by (pose proof (Hale0 _ _ Hall0) as Hle; lia);
          assert (Hrel_body : EnvRel (upd_theta theta0 xc (eval_dty [] theta domain))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            u0 (upd_rval rhoc xc varg) erho0) by
            (eapply upd_env_rel_zero; [exact Hzero | apply upd_theta_env0_rel; assumption]);
          destruct (IH allows0 (upd_theta theta0 xc (eval_dty [] theta domain))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            bodyc _ (upd_rval rhoc xc varg) erho0 v Hale0 Hwf0 Hder0 Hrel_body Heval)
            as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          rewrite Hevc; cbn [eval_erased];
          erewrite (erase_term_head_type_uses xc dom0 [] a0 env0 bodyc);
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hcod_eq; exact Hrel]
        | destruct (IH allows theta env argument _ rho erho varg Hale Hwf Harg_der
            (env_rel_scale_pos _ _ _ _ _ _ (env_rel_app_right _ _ _ _ _ _ Henv)) Harg)
            as [evarg [Hevarg Hrelarg]];
          assert (Harg_rel : ValRel (eval_dty [] (upd_theta theta0 xc (eval_dty [] theta domain)) dom0)
            varg evarg) by
            (rewrite eval_dty_not_free_upd;
             [ cbn [result_type] in Hrelarg; rewrite Hdom_eq;
               rewrite (eval_dty_canonical theta domain _ (eq_sym Hcanon_dom)); exact Hrelarg
             | right; destruct Htd_dom0 as [rdom Htd_dom]; eapply fresh_type_demand_not_free; eauto ]);
          assert (Hrel_body : EnvRel (upd_theta theta0 xc (eval_dty [] theta domain))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            u0 (upd_rval rhoc xc varg) (upd_erval erho0 xc evarg)) by
            (eapply upd_env_rel_val; [exact Harg_rel | apply upd_theta_env0_rel; assumption]);
          destruct (IH allows0 (upd_theta theta0 xc (eval_dty [] theta domain))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            bodyc _ (upd_rval rhoc xc varg) (upd_erval erho0 xc evarg)
            v Hale0 Hwf0 Hder0 Hrel_body Heval) as [ev [Hev Hrel]];
          rewrite Hevc, Hevarg; cbn [eval_erased];
          erewrite (erase_term_head_type_uses xc dom0 [] a0 env0 bodyc);
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hcod_eq; exact Hrel] ]
    end.
  - (* LetNat *)
    destruct (eval_index_rval rho initializer) as [ninit |] eqn:Hinit; [| discriminate].
    lazymatch goal with
    | Hfr : fresh env x = true,
      Hind_init : IndexDemand env initializer z,
      Hder_body : DerivesWith allows ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body
        {| result_type := kind; computation_demand := u; type_demand_row := ?b |},
      Hall : allows (uses u x) allowance |- _ =>
        assert (Hwf' : ctx_closed ({| binder := x; annotation := Natural; type_uses := [] |} :: env)) by
          (apply ctx_closed_cons; [exact Hfr | eexists; apply TypeNatural | exact Hwf]);
        assert (Henv_body_base : forall y, uses (without x u) y > 0 ->
          exists entry, lookup env y = Some entry /\
            ValRel (eval_dty [] theta (annotation entry)) (rho y) (erho y)) by
          (intros y Hy; assert (Hy' : uses (z ++ without x u) y > 0) by (rewrite uses_append; lia); exact (Henv y Hy'));
        assert (Hkind_eq : eval_dty [] theta kind = eval_dty [] theta (substitute_type x initializer kind)) by
          (symmetry; apply eval_dty_subst_index);
        destruct allowance as [| k]; cbn [Nat.eqb eval_erased upd_erval] in *;
        [ assert (Hzero : uses u x = 0) by (pose proof (Hale _ _ Hall) as Hle; lia);
          destruct (IH allows theta ({| binder := x; annotation := Natural; type_uses := [] |} :: env)
            body _ (upd_rval rho x (RNat ninit)) erho v Hale Hwf' Hder_body
            (upd_env_rel_zero _ _ _ _ _ _ _ _ _ Hzero Henv_body_base) Heval) as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          cbn [eval_erased];
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hkind_eq; exact Hrel]
        | assert (Hn_eval : eval_index_erval erho initializer = Some ninit) by
            (eapply index_demand_erased_eval; [exact Hind_init | exact (env_rel_app_left _ _ _ _ _ _ Henv) | exact Hinit]);
          destruct (IH allows theta ({| binder := x; annotation := Natural; type_uses := [] |} :: env)
            body _ (upd_rval rho x (RNat ninit)) (upd_erval erho x (EVNat ninit))
            v Hale Hwf' Hder_body
            (upd_env_rel_val theta x Natural [] env u rho erho (RNat ninit) (EVNat ninit)
               (VR_Nat ninit) Henv_body_base) Heval)
            as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          cbn [eval_erased]; rewrite Hn_eval;
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hkind_eq; exact Hrel] ]
    end.
  - (* ApplyType *)
    destruct (eval_term fuel' rho callee) as [vc |] eqn:Hcal; [| discriminate].
    destruct vc as [| xc alc bodyc rhoc |]; try discriminate.
    lazymatch goal with
    | Hcal_der : DerivesWith allows env callee {| result_type := Pi x allowance (Universe level) codomain; computation_demand := _; type_demand_row := _ |} |- _ =>
        destruct (IH allows theta env callee _ rho erho _ Hale Hwf Hcal_der
          (env_rel_app_left _ _ _ _ _ _ Henv) Hcal) as [evc [Hevc Hrelc]]
    end.
    cbn [result_type eval_dty] in Hrelc.
    inversion Hrelc; subst.
    lazymatch goal with
    | Hale0 : allows_le ?allows0,
      Hfr0 : fresh ?env0 xc = true,
      Hwf0_base : ctx_closed ?env0,
      Htd_dom0 : exists rdom, TypeDemand ?env0 ?dom0 rdom,
      Hder0 : DerivesWith ?allows0 ({| binder := xc; annotation := ?dom0; type_uses := ?a0 |} :: ?env0) bodyc
        {| result_type := ?cod0; computation_demand := ?u0; type_demand_row := ?v0 |},
      Hall0 : ?allows0 (uses ?u0 xc) alc,
      Henv0_rel : forall y, uses (without xc ?u0) y > 0 ->
        exists entry, lookup ?env0 y = Some entry /\
          ValRel (eval_dty [] ?theta0 (annotation entry)) (rhoc y) (?erho0 y),
      Hdom_eq : eval_dty [] ?theta0 ?dom0 = DUniv,
      Hcod_shape : eval_dty [xc] ?theta0 ?cod0 = eval_dty [x] theta codomain,
      Hfr_x : fresh env x = true,
      Htd_arg : TypeDemand env argument z,
      Htd_cod : TypeDemand ({| binder := x; annotation := Universe level; type_uses := [] |} :: env) codomain b |- _ =>
        assert (Hwf0 : ctx_closed ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)) by (apply ctx_closed_cons; assumption);
        assert (Hcod_eq : eval_dty [] (upd_theta theta0 xc (eval_dty [] theta argument)) cod0 =
                          eval_dty [] theta (substitute_type_variable x argument codomain)) by
          (change 0 with (length (@nil nat)); change [xc] with (@nil nat ++ [xc]) in Hcod_shape;
           rewrite eval_dty_subst_open; cbn [length]; rewrite Hcod_shape;
           symmetry; eapply eval_dty_subst_type_var; eauto);
        destruct alc as [| k]; cbn [Nat.eqb eval_erased upd_erval] in *;
        [ assert (Hzero : uses u0 xc = 0) by (pose proof (Hale0 _ _ Hall0) as Hle; lia);
          assert (Hrel_body : EnvRel (upd_theta theta0 xc (eval_dty [] theta argument))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            u0 (upd_rval rhoc xc RErased) erho0) by
            (eapply upd_env_rel_zero; [exact Hzero | apply upd_theta_env0_rel; assumption]);
          destruct (IH allows0 (upd_theta theta0 xc (eval_dty [] theta argument))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            bodyc _ (upd_rval rhoc xc RErased) erho0 v Hale0 Hwf0 Hder0 Hrel_body Heval)
            as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          rewrite Hevc; cbn [eval_erased];
          erewrite (erase_term_head_type_uses xc dom0 [] a0 env0 bodyc);
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hcod_eq; exact Hrel]
        | assert (Harg_rel : ValRel (eval_dty [] (upd_theta theta0 xc (eval_dty [] theta argument)) dom0)
            RErased EVErased) by
            (rewrite eval_dty_not_free_upd;
             [ rewrite Hdom_eq; apply VR_Univ
             | right; destruct Htd_dom0 as [rdom Htd_dom]; eapply fresh_type_demand_not_free; eauto ]);
          assert (Hrel_body : EnvRel (upd_theta theta0 xc (eval_dty [] theta argument))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            u0 (upd_rval rhoc xc RErased) (upd_erval erho0 xc EVErased)) by
            (eapply upd_env_rel_val; [exact Harg_rel | apply upd_theta_env0_rel; assumption]);
          destruct (IH allows0 (upd_theta theta0 xc (eval_dty [] theta argument))
            ({| binder := xc; annotation := dom0; type_uses := a0 |} :: env0)
            bodyc _ (upd_rval rhoc xc RErased) (upd_erval erho0 xc EVErased)
            v Hale0 Hwf0 Hder0 Hrel_body Heval) as [ev [Hev Hrel]];
          destruct fuel' as [| fuel''] eqn:Hfuel; [discriminate |];
          rewrite Hevc; cbn [eval_erased];
          erewrite (erase_term_head_type_uses xc dom0 [] a0 env0 bodyc);
          eexists; split; [exact Hev | cbn [result_type] in Hrel; rewrite <- Hcod_eq; exact Hrel] ]
    end.
Qed.

Lemma index_demand_uses_in_env : forall env i d y,
  IndexDemand env i d ->
  uses d y > 0 ->
  exists entry, lookup env y = Some entry.
Proof.
  intros env i d y Hd. induction Hd; intro Hy; cbn [uses] in *.
  - destruct (Nat.eqb y x) eqn:Eyx; [| lia].
    apply Nat.eqb_eq in Eyx. subst y. eauto.
  - lia.
  - rewrite uses_append in Hy. destruct (uses p y) eqn:Hp; [apply IHHd2; lia | apply IHHd1; lia].
Qed.

Lemma type_demand_uses_in_env : forall env kind row y,
  TypeDemand env kind row ->
  uses row y > 0 ->
  exists entry, lookup env y = Some entry.
Proof.
  intros env kind row y Ht. induction Ht; intro Hy; cbn [uses] in *; try lia.
  - eapply index_demand_uses_in_env; eauto.
  - rewrite uses_append, uses_without in Hy.
    destruct (uses a y) eqn:Ha; [| apply IHHt1; lia].
    destruct (Nat.eqb y x) eqn:Eyx; [lia |].
    assert (Hb : uses b y > 0) by lia.
    destruct (IHHt2 Hb) as [e He].
    unfold lookup in He. cbn [find binder] in He. rewrite Eyx in He. eauto.
  - destruct (Nat.eqb y x) eqn:Eyx; [apply Nat.eqb_eq in Eyx; subst; eauto | lia].
Qed.

Lemma derives_uses_in_env : forall allows env t res y,
  DerivesWith allows env t res ->
  uses (computation_demand res) y > 0 ->
  exists entry, lookup env y = Some entry.
Proof.
  intros allows env t res y Hd. induction Hd; intro Hy; cbn [computation_demand uses] in *.
  - destruct (Nat.eqb y x) eqn:Eyx; [| lia].
    apply Nat.eqb_eq in Eyx. subst y. eauto.
  - eapply index_demand_uses_in_env; eauto.
  - rewrite uses_without in Hy. destruct (Nat.eqb y x) eqn:Eyx; [lia |].
    destruct (IHHd Hy) as [entry Hlook].
    unfold lookup in Hlook. cbn [find binder] in Hlook. rewrite Eyx in Hlook. eauto.
  - rewrite uses_append, uses_scale_nat in Hy.
    destruct (uses w y) eqn:Hw; [| apply IHHd; lia].
    eapply index_demand_uses_in_env; [eassumption | lia].
  - rewrite uses_append, uses_scale_nat in Hy.
    destruct (uses w y) eqn:Hw; [apply IHHd2; lia | apply IHHd1; lia].
  - rewrite uses_append, uses_without in Hy.
    destruct (uses z y) eqn:Hz; [| eapply index_demand_uses_in_env; [eassumption | lia]].
    destruct (Nat.eqb y x) eqn:Eyx; [lia |].
    assert (Hy' : uses u y > 0) by lia.
    destruct (IHHd Hy') as [entry Hlook].
    unfold lookup in Hlook. cbn [find binder] in Hlook. rewrite Eyx in Hlook. eauto.
  - rewrite uses_append, uses_scale_nat in Hy.
    destruct (uses w y) eqn:Hw; [| apply IHHd; lia].
    lazymatch goal with
    | Htd : TypeDemand env _ z |- _ => eapply type_demand_uses_in_env; [exact Htd | lia]
    end.
Qed.

Theorem closed_erasure_sound : forall fuel allows t res v,
  allows_le allows ->
  DerivesWith allows [] t res ->
  eval_term fuel (fun _ => RErased) t = Some v ->
  exists ev,
    eval_erased fuel (fun _ => EVErased) (erase_term [] t) = Some ev /\
    ValRel (eval_dty [] (fun _ => DUniv) (result_type res)) v ev.
Proof.
  intros fuel allows t res v Hale Hder Heval.
  eapply (erasure_simulation fuel allows (fun _ => DUniv) [] t res); eauto.
  - intros y entry Hlook. discriminate.
  - intros y Hy. destruct (derives_uses_in_env _ _ _ _ y Hder Hy) as [entry Hlook].
    discriminate.
Qed.

Theorem zero_computation_irrelevance :
  forall allows env callee x dom cod u_c v_c arg1 arg2,
    DerivesWith allows env callee
      {| result_type := Pi x 0 dom cod; computation_demand := u_c; type_demand_row := v_c |} ->
    erase_term env (ApplyValue callee arg1) = erase_term env (ApplyValue callee arg2) /\
    (forall y, lookup env y <> None ->
      forall env1, expr_type env1 (ApplyValue callee arg1) = expr_type env1 (ApplyValue callee arg2)).
Proof.
  intros allows env callee x dom cod u_c v_c arg1 arg2 Hcal.
  split.
  - cbn [erase_term]. unfold callee_allowance.
    erewrite derives_expr_type by exact Hcal.
    cbn [erase_term]. reflexivity.
  - intros y _ env1. cbn [expr_type]. reflexivity.
Qed.

Lemma env_rel_upd_unused : forall theta env d x rho erho w,
  uses d x = 0 ->
  EnvRel theta env d rho erho ->
  EnvRel theta env d (upd_rval rho x w) erho.
Proof.
  intros theta env d x rho erho w Hzero Hrel y Hy.
  destruct (Hrel y Hy) as [entry [Hlook Hval]].
  exists entry. split; [exact Hlook |].
  unfold upd_rval. destruct (Nat.eqb y x) eqn:Eyx.
  - apply Nat.eqb_eq in Eyx. subst y. lia.
  - exact Hval.
Qed.

Theorem zero_var_non_interference :
  forall fuel allows theta env t res rho erho x w1 w2 n1 n2,
    allows_le allows ->
    ctx_closed env ->
    DerivesWith allows env t res ->
    result_type res = Natural ->
    uses (computation_demand res) x = 0 ->
    EnvRel theta env (computation_demand res) rho erho ->
    eval_term fuel (upd_rval rho x w1) t = Some (RNat n1) ->
    eval_term fuel (upd_rval rho x w2) t = Some (RNat n2) ->
    n1 = n2.
Proof.
  intros fuel allows theta env t res rho erho x w1 w2 n1 n2 Hale Hwf Hder Hnat Hzero Hrel Hev1 Hev2.
  destruct (erasure_simulation fuel allows theta env t res (upd_rval rho x w1) erho (RNat n1)
    Hale Hwf Hder (env_rel_upd_unused theta env _ x rho erho w1 Hzero Hrel) Hev1)
    as [ev1 [E1 V1]].
  destruct (erasure_simulation fuel allows theta env t res (upd_rval rho x w2) erho (RNat n2)
    Hale Hwf Hder (env_rel_upd_unused theta env _ x rho erho w2 Hzero Hrel) Hev2)
    as [ev2 [E2 V2]].
  rewrite E1 in E2. inversion E2; subst ev2.
  rewrite Hnat in V1, V2. cbn in V1, V2.
  inversion V1; subst. inversion V2; subst. reflexivity.
Qed.

(* ================================================================= *)
(* Part 5: Q25cb Zero-Type-Use Substitution Skipping                 *)
(* ================================================================= *)

Definition apply_nat_spec (env : context) (x allowance : nat) (cod : ty)
    (callee_u : demand) (arg : index) : option judgment :=
  match type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) cod,
        index_demand env arg with
  | Some cod_row, Some arg_row =>
      Some {|
        result_type := substitute_type x arg cod;
        computation_demand := callee_u ++ scale allowance arg_row;
        type_demand_row := substitute_demand x arg_row cod_row;
      |}
  | _, _ => None
  end.

Definition apply_nat_skip (env : context) (x allowance : nat) (cod : ty)
    (callee_u : demand) (arg : index) : option judgment :=
  match type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) cod,
        index_demand env arg with
  | Some cod_row, Some arg_row =>
      if Nat.eqb (uses cod_row x) 0 then
        Some {|
          result_type := cod;
          computation_demand := callee_u ++ scale allowance arg_row;
          type_demand_row := cod_row;
        |}
      else
        Some {|
          result_type := substitute_type x arg cod;
          computation_demand := callee_u ++ scale allowance arg_row;
          type_demand_row := substitute_demand x arg_row cod_row;
        |}
  | _, _ => None
  end.

Theorem apply_nat_skip_agrees : forall env x allowance cod callee_u arg,
  match apply_nat_spec env x allowance cod callee_u arg,
        apply_nat_skip env x allowance cod callee_u arg with
  | Some r1, Some r2 =>
      result_type r1 = result_type r2 /\
      computation_demand r1 = computation_demand r2 /\
      same_demand (type_demand_row r1) (type_demand_row r2)
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros env x allowance cod callee_u arg.
  unfold apply_nat_spec, apply_nat_skip.
  destruct (type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) cod)
    as [cod_row |] eqn:Hcod; [| exact I].
  destruct (index_demand env arg) as [arg_row |] eqn:Harg; [| exact I].
  destruct (Nat.eqb (uses cod_row x) 0) eqn:Hx.
  - apply Nat.eqb_eq in Hx.
    apply type_demand_sound in Hcod.
    repeat split; try reflexivity.
    + cbn. eapply zero_type_use; eauto.
    + cbn. apply zero_use_preserves_row. exact Hx.
  - repeat split; try reflexivity; intro y; reflexivity.
Qed.

Definition apply_type_spec (env : context) (x allowance : nat) (cod : ty)
    (callee_u : demand) (arg : ty) : option judgment :=
  match type_demand ({| binder := x; annotation := Universe 0; type_uses := [] |} :: env) cod,
        type_demand env arg with
  | Some cod_row, Some arg_row =>
      Some {|
        result_type := substitute_type_variable x arg cod;
        computation_demand := callee_u ++ scale allowance arg_row;
        type_demand_row := substitute_demand x arg_row cod_row;
      |}
  | _, _ => None
  end.

Definition apply_type_skip (env : context) (x allowance : nat) (cod : ty)
    (callee_u : demand) (arg : ty) : option judgment :=
  match type_demand ({| binder := x; annotation := Universe 0; type_uses := [] |} :: env) cod,
        type_demand env arg with
  | Some cod_row, Some arg_row =>
      if Nat.eqb (uses cod_row x) 0 then
        Some {|
          result_type := cod;
          computation_demand := callee_u ++ scale allowance arg_row;
          type_demand_row := cod_row;
        |}
      else
        Some {|
          result_type := substitute_type_variable x arg cod;
          computation_demand := callee_u ++ scale allowance arg_row;
          type_demand_row := substitute_demand x arg_row cod_row;
        |}
  | _, _ => None
  end.

Theorem apply_type_skip_agrees : forall env x allowance cod callee_u arg,
  match apply_type_spec env x allowance cod callee_u arg,
        apply_type_skip env x allowance cod callee_u arg with
  | Some r1, Some r2 =>
      result_type r1 = result_type r2 /\
      computation_demand r1 = computation_demand r2 /\
      same_demand (type_demand_row r1) (type_demand_row r2)
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros env x allowance cod callee_u arg.
  unfold apply_type_spec, apply_type_skip.
  destruct (type_demand ({| binder := x; annotation := Universe 0; type_uses := [] |} :: env) cod)
    as [cod_row |] eqn:Hcod; [| exact I].
  destruct (type_demand env arg) as [arg_row |] eqn:Harg; [| exact I].
  destruct (Nat.eqb (uses cod_row x) 0) eqn:Hx.
  - apply Nat.eqb_eq in Hx.
    apply type_demand_sound in Hcod.
    repeat split; try reflexivity.
    + cbn. eapply zero_type_var_use; eauto.
    + cbn. apply zero_use_preserves_row. exact Hx.
  - repeat split; try reflexivity; intro y; reflexivity.
Qed.

Definition let_nat_spec (env : context) (x : nat) (init : index)
    (body_ty : ty) (body_u : demand) : option judgment :=
  match type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body_ty,
        index_demand env init with
  | Some body_row, Some init_row =>
      Some {|
        result_type := substitute_type x init body_ty;
        computation_demand := without x body_u ++ init_row;
        type_demand_row := substitute_demand x init_row body_row;
      |}
  | _, _ => None
  end.

Definition let_nat_skip (env : context) (x : nat) (init : index)
    (body_ty : ty) (body_u : demand) : option judgment :=
  match type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body_ty,
        index_demand env init with
  | Some body_row, Some init_row =>
      if Nat.eqb (uses body_row x) 0 then
        Some {|
          result_type := body_ty;
          computation_demand := without x body_u ++ init_row;
          type_demand_row := body_row;
        |}
      else
        Some {|
          result_type := substitute_type x init body_ty;
          computation_demand := without x body_u ++ init_row;
          type_demand_row := substitute_demand x init_row body_row;
        |}
  | _, _ => None
  end.

Theorem let_nat_skip_agrees : forall env x init body_ty body_u,
  match let_nat_spec env x init body_ty body_u,
        let_nat_skip env x init body_ty body_u with
  | Some r1, Some r2 =>
      result_type r1 = result_type r2 /\
      computation_demand r1 = computation_demand r2 /\
      same_demand (type_demand_row r1) (type_demand_row r2)
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros env x init body_ty body_u.
  unfold let_nat_spec, let_nat_skip.
  destruct (type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body_ty)
    as [body_row |] eqn:Hbody; [| exact I].
  destruct (index_demand env init) as [init_row |] eqn:Hinit; [| exact I].
  destruct (Nat.eqb (uses body_row x) 0) eqn:Hx.
  - apply Nat.eqb_eq in Hx.
    apply type_demand_sound in Hbody.
    repeat split; try reflexivity.
    + cbn. eapply zero_type_use; eauto.
    + cbn. apply zero_use_preserves_row. exact Hx.
  - repeat split; try reflexivity; intro y; reflexivity.
Qed.

Example erasure_unused_nat_example :
  let t := ApplyNat (Lambda 1 0 Natural (NatValue (IndexLit 42))) (IndexLit 7) in
  erase_term [] t = EApp (ELam None (ENat (IndexLit 42))) EErased /\
  eval_erased 10 (fun _ => EVErased) (erase_term [] t) = Some (EVNat 42).
Proof.
  split; reflexivity.
Qed.

Example erasure_polymorphic_identity_example :
  let tid := Lambda 1 0 (Universe 0) (Lambda 2 1 (TypeVar 1) (Var 2)) in
  let app := ApplyValue (ApplyType tid Natural) (NatValue (IndexLit 9)) in
  erase_term [] app =
    EApp (EApp (ELam None (ELam (Some 2) (EVar 2))) EErased) (ENat (IndexLit 9)) /\
  eval_erased 10 (fun _ => EVErased) (erase_term [] app) = Some (EVNat 9).
Proof.
  split; reflexivity.
Qed.

End GradedErasure.
