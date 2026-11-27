(* SPDX-License-Identifier: Apache-2.0 *)

From Corelib Require Import Init.Datatypes.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
Require Import graded_pure graded_domains.
Import ListNotations GradedDomains.

Module GradedCore.

(* ================================================================= *)
(* Part 1: Result, Errors, Syntax, and Hint-Free Alpha Equality      *)
(* ================================================================= *)

Inductive result (A E : Type) : Type :=
| Ok (val : A)
| Err (err : E).

Arguments Ok {A E} val.
Arguments Err {A E} err.

Definition bind_res {A B E : Type} (r : result A E) (f : A -> result B E) : result B E :=
  match r with
  | Ok v => f v
  | Err e => Err e
  end.

Notation "'let*' x ':=' a 'in' b" := (bind_res a (fun x => b))
  (at level 10, x name, a at level 100, b at level 200).

Inductive cidx (D : JoinDomain) : Type :=
| CIdxVar (x : nat)
| CIdxLit (n : nat)
| CIdxAdd (lhs rhs : cidx D)
| CIdxProm (q : grade D) (i : cidx D)
| CIdxUnbox (b : nat)
| CIdxFst (p : nat)
| CIdxSnd (p : nat)
| CIdxCase (s : nat) (l r : cidx D).

Arguments CIdxVar {D} x.
Arguments CIdxLit {D} n.
Arguments CIdxAdd {D} lhs rhs.
Arguments CIdxProm {D} q i.
Arguments CIdxUnbox {D} b.
Arguments CIdxFst {D} p.
Arguments CIdxSnd {D} p.
Arguments CIdxCase {D} s l r.

Unset Elimination Schemes.

Inductive cty (D : JoinDomain) : Type :=
| CNat
| CBool
| CVec (elem : cty D) (len : cidx D)
| CUniv (lvl : nat)
| CTVar (x : nat)
| CTProm (q : grade D) (inner : cty D)
| CTUnbox (b : nat)
| CPi (x : nat) (s r : grade D) (dom cod : cty D)
| CSigma (x : nat) (r : grade D) (fst_ty snd_ty : cty D)
| CBox (q : grade D) (inner : cty D)
| CSum (lhs rhs : cty D)
| CRecord (id : nat) (fields : list (nat * grade D * cty D))
| CInd (id : nat) (indices : list (cidx D)).

Arguments CNat {D}.
Arguments CBool {D}.
Arguments CVec {D} elem len.
Arguments CUniv {D} lvl.
Arguments CTVar {D} x.
Arguments CTProm {D} q inner.
Arguments CTUnbox {D} b.
Arguments CPi {D} x s r dom cod.
Arguments CSigma {D} x r fst_ty snd_ty.
Arguments CBox {D} q inner.
Arguments CSum {D} lhs rhs.
Arguments CRecord {D} id fields.
Arguments CInd {D} id indices.

Definition cty_ind_nested (D : JoinDomain) (P : cty D -> Prop)
  (HNat : P CNat)
  (HBool : P CBool)
  (HVec : forall elem len, P elem -> P (CVec elem len))
  (HUniv : forall lvl, P (CUniv lvl))
  (HTVar : forall x, P (CTVar x))
  (HTProm : forall q inner, P inner -> P (CTProm q inner))
  (HTUnbox : forall b, P (CTUnbox b))
  (HPi : forall x s r dom cod, P dom -> P cod -> P (CPi x s r dom cod))
  (HSigma : forall x r fst_ty snd_ty, P fst_ty -> P snd_ty -> P (CSigma x r fst_ty snd_ty))
  (HBox : forall q inner, P inner -> P (CBox q inner))
  (HSum : forall lhs rhs, P lhs -> P rhs -> P (CSum lhs rhs))
  (HRecord : forall id fields, Forall (fun f => P (snd f)) fields -> P (CRecord id fields))
  (HInd : forall id indices, P (CInd id indices))
  : forall T : cty D, P T :=
  fix go (T : cty D) : P T :=
    match T with
    | CNat => HNat
    | CBool => HBool
    | CVec elem len => HVec elem len (go elem)
    | CUniv lvl => HUniv lvl
    | CTVar x => HTVar x
    | CTProm q inner => HTProm q inner (go inner)
    | CTUnbox b => HTUnbox b
    | CPi x s r dom cod => HPi x s r dom cod (go dom) (go cod)
    | CSigma x r fst_ty snd_ty => HSigma x r fst_ty snd_ty (go fst_ty) (go snd_ty)
    | CBox q inner => HBox q inner (go inner)
    | CSum lhs rhs => HSum lhs rhs (go lhs) (go rhs)
    | CRecord id fields =>
        HRecord id fields
          ((fix go_fields (fs : list (nat * grade D * cty D)) : Forall (fun f => P (snd f)) fs :=
              match fs with
              | [] => Forall_nil _
              | (fn, fg, ft) :: rest => Forall_cons (fn, fg, ft) (go ft) (go_fields rest)
              end) fields)
    | CInd id indices => HInd id indices
    end.

Inductive cterm (D : JoinDomain) : Type :=
| CVar (x : nat)
| CNatVal (i : cidx D)
| CBoolVal (b : bool)
| CTypeVal (T : cty D)
| CLam (x : nat) (s r : grade D) (dom : cty D) (body : cterm D)
| CApp (fn arg : cterm D)
| CLet (x : nat) (s r : grade D) (ann : cty D) (rhs body : cterm D)
| CPair (x : nat) (r : grade D) (fst_ty snd_ty : cty D) (fst_val snd_val : cterm D)
| CLetPair (x y : nat) (s kappa : grade D) (motive : cty D) (pair body : cterm D)
| CPromote (q : grade D) (val : cterm D)
| CLetBox (x : nat) (kappa : grade D) (motive : cty D) (box_term body : cterm D)
| CInl (rhs_ty : cty D) (val : cterm D)
| CInr (lhs_ty : cty D) (val : cterm D)
| CMatchSum (x y : nat) (s kappa : grade D) (motive : cty D) (scrut lbranch rbranch : cterm D)
| CIf (cond th el : cterm D)
| CRecordMk (id : nat) (fields : list (nat * grade D * cty D * cterm D))
| CMatchRecord (id : nat) (s : grade D) (motive : cty D) (scrut : cterm D) (binders : list nat) (body : cterm D)
| CSubgrade (target : cty D) (body : cterm D)
| CFix (x_n x_rec : nat) (s_rec : grade D) (motive : cty D) (scrut base step : cterm D).

Arguments CVar {D} x.
Arguments CNatVal {D} i.
Arguments CBoolVal {D} b.
Arguments CTypeVal {D} T.
Arguments CLam {D} x s r dom body.
Arguments CApp {D} fn arg.
Arguments CLet {D} x s r ann rhs body.
Arguments CPair {D} x r fst_ty snd_ty fst_val snd_val.
Arguments CLetPair {D} x y s kappa motive pair body.
Arguments CPromote {D} q val.
Arguments CLetBox {D} x kappa motive box_term body.
Arguments CInl {D} rhs_ty val.
Arguments CInr {D} lhs_ty val.
Arguments CMatchSum {D} x y s kappa motive scrut lbranch rbranch.
Arguments CIf {D} cond th el.
Arguments CRecordMk {D} id fields.
Arguments CMatchRecord {D} id s motive scrut binders body.
Arguments CSubgrade {D} target body.
Arguments CFix {D} x_n x_rec s_rec motive scrut base step.

Definition cterm_ind_nested (D : JoinDomain) (P : cterm D -> Prop)
  (HVar : forall x, P (CVar x))
  (HNatVal : forall i, P (CNatVal i))
  (HBoolVal : forall b, P (CBoolVal b))
  (HTypeVal : forall T, P (CTypeVal T))
  (HLam : forall x s r dom body, P body -> P (CLam x s r dom body))
  (HApp : forall fn arg, P fn -> P arg -> P (CApp fn arg))
  (HLet : forall x s r ann rhs body, P rhs -> P body -> P (CLet x s r ann rhs body))
  (HPair : forall x r fst_ty snd_ty fst_val snd_val, P fst_val -> P snd_val -> P (CPair x r fst_ty snd_ty fst_val snd_val))
  (HLetPair : forall x y s kappa motive pr body, P pr -> P body -> P (CLetPair x y s kappa motive pr body))
  (HPromote : forall q val, P val -> P (CPromote q val))
  (HLetBox : forall x kappa motive box_term body, P box_term -> P body -> P (CLetBox x kappa motive box_term body))
  (HInl : forall rhs_ty val, P val -> P (CInl rhs_ty val))
  (HInr : forall lhs_ty val, P val -> P (CInr lhs_ty val))
  (HMatchSum : forall x y s kappa motive scrut lbranch rbranch,
     P scrut -> P lbranch -> P rbranch -> P (CMatchSum x y s kappa motive scrut lbranch rbranch))
  (HIf : forall cond th el, P cond -> P th -> P el -> P (CIf cond th el))
  (HRecordMk : forall id fields, Forall (fun f => P (snd f)) fields -> P (CRecordMk id fields))
  (HMatchRecord : forall id s motive scrut binders body, P scrut -> P body -> P (CMatchRecord id s motive scrut binders body))
  (HSubgrade : forall target body, P body -> P (CSubgrade target body))
  (HFix : forall x_n x_rec s_rec motive scrut base step,
     P scrut -> P base -> P step -> P (CFix x_n x_rec s_rec motive scrut base step))
  : forall t : cterm D, P t :=
  fix go (t : cterm D) : P t :=
    match t with
    | CVar x => HVar x
    | CNatVal i => HNatVal i
    | CBoolVal b => HBoolVal b
    | CTypeVal T => HTypeVal T
    | CLam x s r dom body => HLam x s r dom body (go body)
    | CApp fn arg => HApp fn arg (go fn) (go arg)
    | CLet x s r ann rhs body => HLet x s r ann rhs body (go rhs) (go body)
    | CPair x r fst_ty snd_ty fst_val snd_val => HPair x r fst_ty snd_ty fst_val snd_val (go fst_val) (go snd_val)
    | CLetPair x y s kappa mot pr body => HLetPair x y s kappa mot pr body (go pr) (go body)
    | CPromote q val => HPromote q val (go val)
    | CLetBox x kappa motive box_term body => HLetBox x kappa motive box_term body (go box_term) (go body)
    | CInl rhs_ty val => HInl rhs_ty val (go val)
    | CInr lhs_ty val => HInr lhs_ty val (go val)
    | CMatchSum x y s kappa motive scrut lbranch rbranch =>
        HMatchSum x y s kappa motive scrut lbranch rbranch (go scrut) (go lbranch) (go rbranch)
    | CIf cond th el => HIf cond th el (go cond) (go th) (go el)
    | CRecordMk id fields =>
        HRecordMk id fields
          ((fix go_fields (fs : list (nat * grade D * cty D * cterm D)) : Forall (fun f => P (snd f)) fs :=
              match fs with
              | [] => Forall_nil _
              | (fn, fg, ft, fv) :: rest => Forall_cons (fn, fg, ft, fv) (go fv) (go_fields rest)
              end) fields)
    | CMatchRecord id s motive scrut binders body =>
        HMatchRecord id s motive scrut binders body (go scrut) (go body)
    | CSubgrade target body => HSubgrade target body (go body)
    | CFix x_n x_rec s_rec motive scrut base step =>
        HFix x_n x_rec s_rec motive scrut base step (go scrut) (go base) (go step)
    end.

Set Elimination Schemes.

Inductive grade_error (D : JoinDomain) : Type :=
| ErrUnbound (idx : nat)
| ErrBinderCompMismatch (binder : nat) (actual expected : grade D)
| ErrBinderTypeMismatch (binder : nat) (actual expected : grade D)
| ErrBranchMismatch (tag : nat)
| ErrMotiveMismatch (expected actual : cty D)
| ErrSubgradeFailed (actual expected : cty D)
| ErrUniverseLevel (actual expected : nat)
| ErrTypeMismatch (actual expected : cty D)
| ErrNotCallable (actual : cty D)
| ErrNotBox (actual : cty D)
| ErrNotPair (actual : cty D)
| ErrNotSum (actual : cty D).

Arguments ErrUnbound {D} idx.
Arguments ErrBinderCompMismatch {D} binder actual expected.
Arguments ErrBinderTypeMismatch {D} binder actual expected.
Arguments ErrBranchMismatch {D} tag.
Arguments ErrMotiveMismatch {D} expected actual.
Arguments ErrSubgradeFailed {D} actual expected.
Arguments ErrUniverseLevel {D} actual expected.
Arguments ErrTypeMismatch {D} actual expected.
Arguments ErrNotCallable {D} actual.
Arguments ErrNotBox {D} actual.
Arguments ErrNotPair {D} actual.
Arguments ErrNotSum {D} actual.

Fixpoint cidx_eqb {D : JoinDomain} (i1 i2 : cidx D) : bool :=
  match i1, i2 with
  | CIdxVar x1, CIdxVar x2 => Nat.eqb x1 x2
  | CIdxLit n1, CIdxLit n2 => Nat.eqb n1 n2
  | CIdxAdd l1 r1, CIdxAdd l2 r2 => cidx_eqb l1 l2 && cidx_eqb r1 r2
  | CIdxProm q1 i1', CIdxProm q2 i2' => grade_eqb q1 q2 && cidx_eqb i1' i2'
  | CIdxUnbox b1, CIdxUnbox b2 => Nat.eqb b1 b2
  | CIdxFst p1, CIdxFst p2 => Nat.eqb p1 p2
  | CIdxSnd p1, CIdxSnd p2 => Nat.eqb p1 p2
  | CIdxCase s1 l1 r1, CIdxCase s2 l2 r2 => Nat.eqb s1 s2 && cidx_eqb l1 l2 && cidx_eqb r1 r2
  | _, _ => false
  end.

Lemma cidx_eqb_refl : forall (D : JoinDomain) (i : cidx D), cidx_eqb i i = true.
Proof.
  intros D i. induction i; cbn; rewrite ?Nat.eqb_refl; try reflexivity;
    try (rewrite IHi1, IHi2; reflexivity).
  destruct (grade_eqb_spec D q q); [exact IHi | congruence].
Qed.

Lemma cidx_eqb_sound : forall (D : JoinDomain) (i1 i2 : cidx D),
  cidx_eqb i1 i2 = true -> i1 = i2.
Proof.
  intros D i1. induction i1; intros i2 H; destruct i2; cbn in H; try discriminate.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - apply andb_true_iff in H as [H1 H2]. rewrite (IHi1_1 _ H1), (IHi1_2 _ H2). reflexivity.
  - apply andb_true_iff in H as [Hq Hi].
    destruct (grade_eqb_spec D q q0); [| discriminate].
    subst. rewrite (IHi1 _ Hi). reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - apply andb_true_iff in H as [H1 Hr].
    apply andb_true_iff in H1 as [Hs Hl].
    apply Nat.eqb_eq in Hs. subst.
    rewrite (IHi1_1 _ Hl), (IHi1_2 _ Hr). reflexivity.
Qed.

Fixpoint cidx_list_eqb {D : JoinDomain} (l1 l2 : list (cidx D)) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1', b :: l2' => cidx_eqb a b && cidx_list_eqb l1' l2'
  | _, _ => false
  end.

Lemma cidx_list_eqb_refl : forall (D : JoinDomain) (l : list (cidx D)),
  cidx_list_eqb l l = true.
Proof.
  intros D l. induction l as [| a l IH]; cbn; [reflexivity | now rewrite cidx_eqb_refl, IH].
Qed.

Lemma cidx_list_eqb_sound : forall (D : JoinDomain) (l1 l2 : list (cidx D)),
  cidx_list_eqb l1 l2 = true -> l1 = l2.
Proof.
  intros D l1. induction l1 as [| a l1 IH]; intros [| b l2] H; cbn in H; try discriminate; [reflexivity |].
  apply andb_true_iff in H as [Ha Hl]. apply cidx_eqb_sound in Ha. subst.
  f_equal. apply IH; exact Hl.
Qed.

Fixpoint erase_hints {D : JoinDomain} (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (erase_hints elem) len
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar x
  | CTProm q inner => CTProm q (erase_hints inner)
  | CTUnbox b => CTUnbox b
  | CPi _ s r dom cod => CPi 0 s r (erase_hints dom) (erase_hints cod)
  | CSigma _ r fst_ty snd_ty => CSigma 0 r (erase_hints fst_ty) (erase_hints snd_ty)
  | CBox q inner => CBox q (erase_hints inner)
  | CSum lhs rhs => CSum (erase_hints lhs) (erase_hints rhs)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, erase_hints ft)) fields)
  | CInd id indices => CInd id indices
  end.

Definition cty_alpha_eq {D : JoinDomain} (T1 T2 : cty D) : Prop :=
  erase_hints T1 = erase_hints T2.

Lemma cty_alpha_eq_refl : forall (D : JoinDomain) (T : cty D), cty_alpha_eq T T.
Proof. intros. reflexivity. Qed.

Lemma cty_alpha_eq_sym : forall (D : JoinDomain) (T1 T2 : cty D),
  cty_alpha_eq T1 T2 -> cty_alpha_eq T2 T1.
Proof. intros D T1 T2 H. unfold cty_alpha_eq in *. symmetry. exact H. Qed.

Lemma cty_alpha_eq_trans : forall (D : JoinDomain) (T1 T2 T3 : cty D),
  cty_alpha_eq T1 T2 -> cty_alpha_eq T2 T3 -> cty_alpha_eq T1 T3.
Proof. intros D T1 T2 T3 H12 H23. unfold cty_alpha_eq in *. etransitivity; eauto. Qed.

Fixpoint cty_alpha_eqb {D : JoinDomain} (T1 T2 : cty D) : bool :=
  match T1, T2 with
  | CNat, CNat => true
  | CBool, CBool => true
  | CVec e1 l1, CVec e2 l2 => cty_alpha_eqb e1 e2 && cidx_eqb l1 l2
  | CUniv l1, CUniv l2 => Nat.eqb l1 l2
  | CTVar x1, CTVar x2 => Nat.eqb x1 x2
  | CTProm q1 i1, CTProm q2 i2 => grade_eqb q1 q2 && cty_alpha_eqb i1 i2
  | CTUnbox b1, CTUnbox b2 => Nat.eqb b1 b2
  | CPi _ s1 r1 d1 c1, CPi _ s2 r2 d2 c2 =>
      grade_eqb s1 s2 && grade_eqb r1 r2 && cty_alpha_eqb d1 d2 && cty_alpha_eqb c1 c2
  | CSigma _ r1 f1 s1, CSigma _ r2 f2 s2 =>
      grade_eqb r1 r2 && cty_alpha_eqb f1 f2 && cty_alpha_eqb s1 s2
  | CBox q1 i1, CBox q2 i2 => grade_eqb q1 q2 && cty_alpha_eqb i1 i2
  | CSum l1 r1, CSum l2 r2 => cty_alpha_eqb l1 l2 && cty_alpha_eqb r1 r2
  | CRecord id1 fs1, CRecord id2 fs2 =>
      Nat.eqb id1 id2 &&
      (fix eq_fs (a b : list (nat * grade D * cty D)) : bool :=
         match a, b with
         | [], [] => true
         | (n1, g1, t1) :: a', (n2, g2, t2) :: b' =>
             Nat.eqb n1 n2 && grade_eqb g1 g2 && cty_alpha_eqb t1 t2 && eq_fs a' b'
         | _, _ => false
         end) fs1 fs2
  | CInd id1 is1, CInd id2 is2 => Nat.eqb id1 id2 && cidx_list_eqb is1 is2
  | _, _ => false
  end.

Lemma cty_alpha_eqb_refl : forall (D : JoinDomain) (T : cty D),
  cty_alpha_eqb T T = true.
Proof.
  intros D T. induction T using cty_ind_nested; cbn; rewrite ?Nat.eqb_refl; try reflexivity.
  - rewrite IHT, cidx_eqb_refl. reflexivity.
  - destruct (grade_eqb_spec D q q); [exact IHT | congruence].
  - destruct (grade_eqb_spec D s s), (grade_eqb_spec D r r); try congruence.
    cbn. rewrite IHT1, IHT2. reflexivity.
  - destruct (grade_eqb_spec D r r); try congruence.
    cbn. rewrite IHT1, IHT2. reflexivity.
  - destruct (grade_eqb_spec D q q); [exact IHT | congruence].
  - rewrite IHT1, IHT2. reflexivity.
  - induction fields as [| [[fn fg] ft] rest IHf]; cbn in *; [reflexivity |].
    inversion H; subst. cbn in H2.
    rewrite Nat.eqb_refl. destruct (grade_eqb_spec D fg fg); [| congruence].
    cbn. rewrite H2. apply IHf; exact H3.
  - rewrite cidx_list_eqb_refl. reflexivity.
Qed.

Lemma cty_alpha_eqb_sound : forall (D : JoinDomain) (T1 T2 : cty D),
  cty_alpha_eqb T1 T2 = true -> cty_alpha_eq T1 T2.
Proof.
  intros D T1. induction T1 using cty_ind_nested; intros T2 Hchk; destruct T2; cbn in Hchk;
    try discriminate; unfold cty_alpha_eq in *; cbn.
  - reflexivity.
  - reflexivity.
  - apply andb_true_iff in Hchk as [He Hl].
    apply IHT1 in He. apply cidx_eqb_sound in Hl. congruence.
  - apply Nat.eqb_eq in Hchk; subst; reflexivity.
  - apply Nat.eqb_eq in Hchk; subst; reflexivity.
  - apply andb_true_iff in Hchk as [Hq Hi].
    destruct (grade_eqb_spec D q q0); [| discriminate].
    apply IHT1 in Hi. congruence.
  - apply Nat.eqb_eq in Hchk; subst; reflexivity.
  - apply andb_true_iff in Hchk as [Hchk Hc].
    apply andb_true_iff in Hchk as [Hchk Hd].
    apply andb_true_iff in Hchk as [Hs Hr].
    destruct (grade_eqb_spec D s s0), (grade_eqb_spec D r r0); try discriminate.
    apply IHT1_1 in Hd. apply IHT1_2 in Hc. congruence.
  - apply andb_true_iff in Hchk as [Hchk Hs].
    apply andb_true_iff in Hchk as [Hr Hf].
    destruct (grade_eqb_spec D r r0); try discriminate.
    apply IHT1_1 in Hf. apply IHT1_2 in Hs. congruence.
  - apply andb_true_iff in Hchk as [Hq Hi].
    destruct (grade_eqb_spec D q q0); [| discriminate].
    apply IHT1 in Hi. congruence.
  - apply andb_true_iff in Hchk as [Hl Hr].
    apply IHT1_1 in Hl. apply IHT1_2 in Hr. congruence.
  - apply andb_true_iff in Hchk as [Hid Hfs].
    apply Nat.eqb_eq in Hid. subst id0. f_equal.
    revert fields0 Hfs.
    induction fields as [| [[fn fg] ft] rest IHf]; intros [| [[fn' fg'] ft'] rest'] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion H; subst. cbn in H2.
    apply andb_true_iff in Hfs as [Hhd Htl].
    apply andb_true_iff in Hhd as [Hhd Ht].
    apply andb_true_iff in Hhd as [Hn Hg].
    apply Nat.eqb_eq in Hn. destruct (grade_eqb_spec D fg fg'); try discriminate.
    subst. apply H2 in Ht. rewrite Ht. f_equal. apply IHf; assumption.
  - apply andb_true_iff in Hchk as [Hid His].
    apply Nat.eqb_eq in Hid. apply cidx_list_eqb_sound in His. congruence.
Qed.

(* ================================================================= *)
(* Part 2: Grade Vectors & Semiring Vector Algebra                   *)
(* ================================================================= *)

Definition vec_zero {D : JoinDomain} (n : nat) : list (grade D) :=
  repeat zero n.

Fixpoint vec_single {D : JoinDomain} (n x : nat) (q : grade D) : list (grade D) :=
  match n, x with
  | 0, _ => []
  | S n', 0 => q :: vec_zero n'
  | S n', S x' => zero :: vec_single n' x' q
  end.

Fixpoint vec_add {D : JoinDomain} (u v : list (grade D)) : list (grade D) :=
  match u, v with
  | a :: u', b :: v' => add a b :: vec_add u' v'
  | _, _ => []
  end.

Definition vec_scale {D : JoinDomain} (q : grade D) (u : list (grade D)) : list (grade D) :=
  map (mul q) u.

Fixpoint vec_join {D : JoinDomain} (j : grade D -> grade D -> grade D) (u v : list (grade D)) : list (grade D) :=
  match u, v with
  | a :: u', b :: v' => j a b :: vec_join j u' v'
  | _, _ => []
  end.

Definition vec_allows {D : JoinDomain} (u v : list (grade D)) : Prop :=
  Forall2 (@allows D) u v.

Fixpoint vec_allowsb {D : JoinDomain} (u v : list (grade D)) : bool :=
  match u, v with
  | [], [] => true
  | a :: u', b :: v' => allowsb a b && vec_allowsb u' v'
  | _, _ => false
  end.

Fixpoint vec_eqb {D : JoinDomain} (u v : list (grade D)) : bool :=
  match u, v with
  | [], [] => true
  | a :: u', b :: v' => grade_eqb a b && vec_eqb u' v'
  | _, _ => false
  end.

Definition vec_is_zero {D : JoinDomain} (u : list (grade D)) : bool :=
  forallb (fun q => grade_eqb q zero) u.

Definition nth_grade {D : JoinDomain} (u : list (grade D)) (k : nat) : grade D :=
  nth_default zero u k.

Fixpoint vec_insert_zero {D : JoinDomain} (k : nat) (u : list (grade D)) : list (grade D) :=
  match k, u with
  | 0, _ => zero :: u
  | S k', a :: u' => a :: vec_insert_zero k' u'
  | S _, [] => [zero]
  end.

Fixpoint vec_swap {D : JoinDomain} (k : nat) (u : list (grade D)) : list (grade D) :=
  match k, u with
  | 0, a :: b :: rest => b :: a :: rest
  | S k', a :: rest => a :: vec_swap k' rest
  | _, _ => u
  end.

Fixpoint vec_subst {D : JoinDomain} (k : nat) (z u : list (grade D)) : list (grade D) :=
  match k, u with
  | 0, uk :: u_outer => vec_add u_outer (vec_scale uk z)
  | S k', a :: u' => a :: vec_subst k' z u'
  | _, _ => []
  end.

Fixpoint vec_remove {D : JoinDomain} (k : nat) (u : list (grade D)) : list (grade D) :=
  match k, u with
  | 0, _ :: u' => u'
  | S k', a :: u' => a :: vec_remove k' u'
  | _, _ => []
  end.

Definition BranchVec {D : JoinDomain} (u1 u2 u : list (grade D)) : Prop :=
  match grade_join D with
  | Some j => u = vec_join j u1 u2
  | None => u1 = u2 /\ u = u1
  end.

Definition branch_vec {D : JoinDomain} (tag : nat) (u1 u2 : list (grade D))
  : result (list (grade D)) (grade_error D) :=
  match grade_join D with
  | Some j => Ok (vec_join j u1 u2)
  | None => if vec_eqb u1 u2 then Ok u1 else Err (ErrBranchMismatch tag)
  end.

Lemma vec_zero_length : forall (D : JoinDomain) n,
  length (vec_zero (D := D) n) = n.
Proof. intros D n. apply repeat_length. Qed.

Lemma vec_single_length : forall (D : JoinDomain) n x q,
  length (vec_single (D := D) n x q) = n.
Proof.
  intros D n. induction n as [| n IH]; intros [| x'] q; cbn;
    rewrite ?vec_zero_length, ?IH; reflexivity.
Qed.

Lemma vec_add_length : forall (D : JoinDomain) (u v : list (grade D)),
  length u = length v -> length (vec_add u v) = length u.
Proof.
  intros D u. induction u as [| a u IH]; intros [| b v] H; cbn in *; try discriminate; [reflexivity |].
  f_equal. apply IH. congruence.
Qed.

Lemma vec_scale_length : forall (D : JoinDomain) (q : grade D) u,
  length (vec_scale q u) = length u.
Proof. intros D q u. apply length_map. Qed.

Lemma vec_join_length : forall (D : JoinDomain) j (u v : list (grade D)),
  length u = length v -> length (vec_join j u v) = length u.
Proof.
  intros D j u. induction u as [| a u IH]; intros [| b v] H; cbn in *; try discriminate; [reflexivity |].
  f_equal. apply IH. congruence.
Qed.

Lemma vec_allowsb_spec : forall (D : JoinDomain) (u v : list (grade D)),
  vec_allowsb u v = true <-> vec_allows u v.
Proof.
  intros D u. unfold vec_allows.
  induction u as [| a u IH]; intros [| b v]; cbn.
  - split; [intros _; constructor | intro; reflexivity].
  - split; [discriminate | inversion 1].
  - split; [discriminate | inversion 1].
  - rewrite andb_true_iff, IH. destruct (allows_reflect D a b); split; intro H.
    + constructor; tauto.
    + inversion H; tauto.
    + destruct H as [Hc _]; discriminate.
    + inversion H; contradiction.
Qed.

Lemma vec_eqb_refl : forall (D : JoinDomain) (u : list (grade D)),
  vec_eqb u u = true.
Proof.
  intros D u. induction u as [| a u IH]; cbn; [reflexivity |].
  destruct (grade_eqb_spec D a a); [exact IH | congruence].
Qed.

Lemma vec_eqb_sound : forall (D : JoinDomain) (u v : list (grade D)),
  vec_eqb u v = true -> u = v.
Proof.
  intros D u. induction u as [| a u IH]; intros [| b v] H; cbn in H; try discriminate; [reflexivity |].
  apply andb_true_iff in H as [Hab Huv].
  destruct (grade_eqb_spec D a b); [| discriminate].
  subst. f_equal. apply IH; exact Huv.
Qed.

Lemma vec_is_zero_spec : forall (D : JoinDomain) (u : list (grade D)),
  vec_is_zero u = true <-> u = vec_zero (length u).
Proof.
  intros D u. induction u as [| a u IH]; cbn; [split; reflexivity |].
  unfold vec_is_zero in *. cbn. rewrite andb_true_iff, IH.
  destruct (grade_eqb_spec D a zero); split; intro H.
  - destruct H as [_ Hu]. subst a. cbn. rewrite Hu at 1. reflexivity.
  - inversion H; subst. split; [reflexivity |]. rewrite repeat_length. reflexivity.
  - destruct H as [Hc _]; discriminate.
  - inversion H; contradiction.
Qed.

Lemma branch_vec_sound : forall (D : JoinDomain) tag (u1 u2 u : list (grade D)),
  branch_vec tag u1 u2 = Ok u -> BranchVec u1 u2 u.
Proof.
  intros D tag u1 u2 u H. unfold branch_vec, BranchVec in *.
  destruct (grade_join D) as [j |].
  - inversion H; reflexivity.
  - destruct (vec_eqb u1 u2) eqn:E; inversion H; subst.
    split; [apply vec_eqb_sound; exact E | reflexivity].
Qed.

Lemma vec_allows_refl : forall (D : JoinDomain) (u : list (grade D)),
  vec_allows u u.
Proof.
  intros D u. induction u; constructor; [apply allows_refl | exact IHu].
Qed.

Lemma vec_allows_trans : forall (D : JoinDomain) (u1 u2 u3 : list (grade D)),
  vec_allows u1 u2 -> vec_allows u2 u3 -> vec_allows u1 u3.
Proof.
  intros D u1 u2 u3 H12. revert u3.
  induction H12; intros u3 H23; inversion H23; subst; constructor.
  - eapply allows_trans; eassumption.
  - apply IHForall2; assumption.
Qed.

Lemma vec_allows_length : forall (D : JoinDomain) (u v : list (grade D)),
  vec_allows u v -> length u = length v.
Proof.
  intros D u v H. induction H; cbn; congruence.
Qed.

Lemma vec_allows_add : forall (D : JoinDomain) (u1 u2 v1 v2 : list (grade D)),
  vec_allows u1 u2 -> vec_allows v1 v2 -> vec_allows (vec_add u1 v1) (vec_add u2 v2).
Proof.
  intros D u1 u2 v1 v2 Hu. revert v1 v2.
  induction Hu; intros v1 v2 Hv; inversion Hv; subst; cbn; constructor;
    [apply add_monotone; assumption | apply IHHu; assumption].
Qed.

Lemma vec_allows_scale : forall (D : JoinDomain) (q1 q2 : grade D) (u1 u2 : list (grade D)),
  allows q1 q2 -> vec_allows u1 u2 -> vec_allows (vec_scale q1 u1) (vec_scale q2 u2).
Proof.
  intros D q1 q2 u1 u2 Hq Hu. induction Hu; cbn; constructor;
    [apply mul_monotone; assumption | exact IHHu].
Qed.

Lemma vec_add_comm : forall (D : JoinDomain) (u v : list (grade D)),
  vec_add u v = vec_add v u.
Proof.
  intros D u. induction u as [| a u IH]; intros [| b v]; cbn; try reflexivity.
  rewrite add_comm, IH. reflexivity.
Qed.

Lemma vec_add_assoc : forall (D : JoinDomain) (u v w : list (grade D)),
  vec_add u (vec_add v w) = vec_add (vec_add u v) w.
Proof.
  intros D u. induction u as [| a u IH]; intros [| b v] [| c w]; cbn; try reflexivity.
  rewrite add_assoc, IH. reflexivity.
Qed.

Lemma vec_add_zero_l : forall (D : JoinDomain) (u : list (grade D)),
  vec_add (vec_zero (length u)) u = u.
Proof.
  intros D u. unfold vec_zero in *.
  induction u as [| a u IH]; cbn; [reflexivity |].
  rewrite add_zero, IH. reflexivity.
Qed.

Lemma vec_add_zero_r : forall (D : JoinDomain) (u : list (grade D)),
  vec_add u (vec_zero (length u)) = u.
Proof.
  intros D u. rewrite vec_add_comm. apply vec_add_zero_l.
Qed.

Lemma vec_scale_zero : forall (D : JoinDomain) (u : list (grade D)),
  vec_scale zero u = vec_zero (length u).
Proof.
  intros D u. unfold vec_zero, vec_scale in *.
  induction u as [| a u IH]; cbn; [reflexivity |].
  rewrite mul_zero, IH. reflexivity.
Qed.

Lemma vec_scale_one : forall (D : JoinDomain) (u : list (grade D)),
  vec_scale one u = u.
Proof.
  intros D u. unfold vec_scale in *.
  induction u as [| a u IH]; cbn; [reflexivity |].
  rewrite mul_one, IH. reflexivity.
Qed.

Lemma vec_scale_add : forall (D : JoinDomain) (q : grade D) (u v : list (grade D)),
  vec_scale q (vec_add u v) = vec_add (vec_scale q u) (vec_scale q v).
Proof.
  intros D q u. unfold vec_scale in *.
  induction u as [| a u IH]; intros [| b v]; cbn; try reflexivity.
  rewrite mul_add, IH. reflexivity.
Qed.

Lemma vec_scale_mul : forall (D : JoinDomain) (q r : grade D) (u : list (grade D)),
  vec_scale q (vec_scale r u) = vec_scale (mul q r) u.
Proof.
  intros D q r u. unfold vec_scale in *.
  induction u as [| a u IH]; cbn; [reflexivity |].
  rewrite mul_assoc, IH. reflexivity.
Qed.

(* ================================================================= *)
(* Part 3: Context, Renaming, Lifting, and Dependent Specialization  *)
(* ================================================================= *)

Record cbinding (D : JoinDomain) := {
  cbinder : nat;
  cannotation : cty D;
  ctype_uses : list (grade D)
}.

Arguments Build_cbinding {D} cbinder cannotation ctype_uses.
Arguments cbinder {D} _.
Arguments cannotation {D} _.
Arguments ctype_uses {D} _.

Definition cenv (D : JoinDomain) := list (cbinding D).

Definition clookup {D : JoinDomain} (env : cenv D) (x : nat) : option (cbinding D) :=
  nth_error env x.

Definition ren_lift (c d i : nat) : nat :=
  if i <? c then i else i + d.

Definition ren_shift (rho : nat -> nat) (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => S (rho i')
  end.

Fixpoint ren_cidx {D : JoinDomain} (rho : nat -> nat) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar (rho x)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (ren_cidx rho l) (ren_cidx rho r)
  | CIdxProm q i' => CIdxProm q (ren_cidx rho i')
  | CIdxUnbox b => CIdxUnbox (rho b)
  | CIdxFst p => CIdxFst (rho p)
  | CIdxSnd p => CIdxSnd (rho p)
  | CIdxCase s l r => CIdxCase (rho s) (ren_cidx (ren_shift rho) l) (ren_cidx (ren_shift rho) r)
  end.

Fixpoint ren_cty {D : JoinDomain} (rho : nat -> nat) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (ren_cty rho elem) (ren_cidx rho len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (rho x)
  | CTProm q inner => CTProm q (ren_cty rho inner)
  | CTUnbox b => CTUnbox (rho b)
  | CPi x s r dom cod => CPi x s r (ren_cty rho dom) (ren_cty (ren_shift rho) cod)
  | CSigma x r fst_ty snd_ty => CSigma x r (ren_cty rho fst_ty) (ren_cty (ren_shift rho) snd_ty)
  | CBox q inner => CBox q (ren_cty rho inner)
  | CSum lhs rhs => CSum (ren_cty rho lhs) (ren_cty rho rhs)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, ren_cty rho ft)) fields)
  | CInd id indices => CInd id (map (ren_cidx rho) indices)
  end.

Fixpoint ren_cterm {D : JoinDomain} (rho : nat -> nat) (t : cterm D) : cterm D :=
  match t with
  | CVar x => CVar (rho x)
  | CNatVal i => CNatVal (ren_cidx rho i)
  | CBoolVal b => CBoolVal b
  | CTypeVal T => CTypeVal (ren_cty rho T)
  | CLam x s r dom body => CLam x s r (ren_cty rho dom) (ren_cterm (ren_shift rho) body)
  | CApp fn arg => CApp (ren_cterm rho fn) (ren_cterm rho arg)
  | CLet x s r ann rhs body =>
      CLet x s r (ren_cty rho ann) (ren_cterm rho rhs) (ren_cterm (ren_shift rho) body)
  | CPair x r fst_ty snd_ty fst_val snd_val =>
      CPair x r (ren_cty rho fst_ty) (ren_cty (ren_shift rho) snd_ty)
        (ren_cterm rho fst_val) (ren_cterm rho snd_val)
  | CLetPair x y s kappa mot pr body =>
      CLetPair x y s kappa (ren_cty (ren_shift rho) mot)
        (ren_cterm rho pr) (ren_cterm (ren_shift (ren_shift rho)) body)
  | CPromote q val => CPromote q (ren_cterm rho val)
  | CLetBox x kappa mot box_term body =>
      CLetBox x kappa (ren_cty (ren_shift rho) mot)
        (ren_cterm rho box_term) (ren_cterm (ren_shift rho) body)
  | CInl rhs_ty val => CInl (ren_cty rho rhs_ty) (ren_cterm rho val)
  | CInr lhs_ty val => CInr (ren_cty rho lhs_ty) (ren_cterm rho val)
  | CMatchSum x y s kappa mot scrut lb rb =>
      CMatchSum x y s kappa (ren_cty (ren_shift rho) mot)
        (ren_cterm rho scrut) (ren_cterm (ren_shift rho) lb) (ren_cterm (ren_shift rho) rb)
  | CIf cond th el => CIf (ren_cterm rho cond) (ren_cterm rho th) (ren_cterm rho el)
  | CRecordMk id fields =>
      CRecordMk id (map (fun '(fn, fg, ft, fv) => (fn, fg, ren_cty rho ft, ren_cterm rho fv)) fields)
  | CMatchRecord id s mot scrut bs body =>
      CMatchRecord id s (ren_cty rho mot) (ren_cterm rho scrut) bs
        (ren_cterm (Nat.iter (length bs) ren_shift rho) body)
  | CSubgrade target body => CSubgrade (ren_cty rho target) (ren_cterm rho body)
  | CFix xn xr sr mot scrut base step =>
      CFix xn xr sr (ren_cty (ren_shift rho) mot)
        (ren_cterm rho scrut) (ren_cterm rho base) (ren_cterm (ren_shift (ren_shift rho)) step)
  end.

Definition lift_cidx {D : JoinDomain} (c d : nat) : cidx D -> cidx D := ren_cidx (ren_lift c d).
Definition lift_cty {D : JoinDomain} (c d : nat) : cty D -> cty D := ren_cty (ren_lift c d).
Definition lift_cterm {D : JoinDomain} (c d : nat) : cterm D -> cterm D := ren_cterm (ren_lift c d).

Definition unshift_var (k x : nat) : nat :=
  if x <? k then x else x - 1.

Definition unshift_cidx {D : JoinDomain} (k : nat) : cidx D -> cidx D :=
  ren_cidx (Nat.iter k ren_shift (fun i => match i with 0 => 0 | S i' => i' end)).

Definition unshift_cty {D : JoinDomain} (k : nat) : cty D -> cty D :=
  ren_cty (Nat.iter k ren_shift (fun i => match i with 0 => 0 | S i' => i' end)).

Fixpoint subst_cidx {D : JoinDomain} (k : nat) (val : cidx D) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x =>
      if Nat.eqb x k then val
      else if Nat.ltb x k then CIdxVar x
      else CIdxVar (x - 1)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (subst_cidx k val l) (subst_cidx k val r)
  | CIdxProm q i' => CIdxProm q (subst_cidx k val i')
  | CIdxUnbox b => CIdxUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CIdxFst p => CIdxFst (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxSnd p => CIdxSnd (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxCase s l r =>
      CIdxCase (if s <? k then s else if s =? k then 0 else s - 1)
        (subst_cidx (S k) (lift_cidx 0 1 val) l)
        (subst_cidx (S k) (lift_cidx 0 1 val) r)
  end.

Fixpoint subst_cidx_in_cty {D : JoinDomain} (k : nat) (val : cidx D) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (subst_cidx_in_cty k val elem) (subst_cidx k val len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CTProm q inner => CTProm q (subst_cidx_in_cty k val inner)
  | CTUnbox b => CTUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CPi x s r dom cod =>
      CPi x s r (subst_cidx_in_cty k val dom) (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) cod)
  | CSigma x r fst_ty snd_ty =>
      CSigma x r (subst_cidx_in_cty k val fst_ty) (subst_cidx_in_cty (S k) (lift_cidx 0 1 val) snd_ty)
  | CBox q inner => CBox q (subst_cidx_in_cty k val inner)
  | CSum lhs rhs => CSum (subst_cidx_in_cty k val lhs) (subst_cidx_in_cty k val rhs)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, subst_cidx_in_cty k val ft)) fields)
  | CInd id indices => CInd id (map (subst_cidx k val) indices)
  end.

Fixpoint subst_tvar_in_cidx {D : JoinDomain} (k : nat) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (subst_tvar_in_cidx k l) (subst_tvar_in_cidx k r)
  | CIdxProm q i' => CIdxProm q (subst_tvar_in_cidx k i')
  | CIdxUnbox b => CIdxUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CIdxFst p => CIdxFst (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxSnd p => CIdxSnd (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxCase s l r =>
      CIdxCase (if s <? k then s else if s =? k then 0 else s - 1)
        (subst_tvar_in_cidx (S k) l) (subst_tvar_in_cidx (S k) r)
  end.

Fixpoint subst_tvar_in_cty {D : JoinDomain} (k : nat) (U T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (subst_tvar_in_cty k U elem) (subst_tvar_in_cidx k len)
  | CUniv lvl => CUniv lvl
  | CTVar x =>
      if Nat.eqb x k then U
      else if Nat.ltb x k then CTVar x
      else CTVar (x - 1)
  | CTProm q inner => CTProm q (subst_tvar_in_cty k U inner)
  | CTUnbox b => CTUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CPi x s r dom cod =>
      CPi x s r (subst_tvar_in_cty k U dom) (subst_tvar_in_cty (S k) (lift_cty 0 1 U) cod)
  | CSigma x r fst_ty snd_ty =>
      CSigma x r (subst_tvar_in_cty k U fst_ty) (subst_tvar_in_cty (S k) (lift_cty 0 1 U) snd_ty)
  | CBox q inner => CBox q (subst_tvar_in_cty k U inner)
  | CSum lhs rhs => CSum (subst_tvar_in_cty k U lhs) (subst_tvar_in_cty k U rhs)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, subst_tvar_in_cty k U ft)) fields)
  | CInd id indices => CInd id (map (subst_tvar_in_cidx k) indices)
  end.

(* Specialization helpers for dependent elimination motives *)

Fixpoint map_cidx_in_cty {D : JoinDomain} (f : nat -> cidx D -> cidx D) (k : nat) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (map_cidx_in_cty f k elem) (f k len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CTProm q inner => CTProm q (map_cidx_in_cty f k inner)
  | CTUnbox b => CTUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CPi x s r dom cod => CPi x s r (map_cidx_in_cty f k dom) (map_cidx_in_cty f (S k) cod)
  | CSigma x r fst_ty snd_ty => CSigma x r (map_cidx_in_cty f k fst_ty) (map_cidx_in_cty f (S k) snd_ty)
  | CBox q inner => CBox q (map_cidx_in_cty f k inner)
  | CSum lhs rhs => CSum (map_cidx_in_cty f k lhs) (map_cidx_in_cty f k rhs)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, map_cidx_in_cty f k ft)) fields)
  | CInd id indices => CInd id (map (f k) indices)
  end.

(* For CLetBox body in (x : A) :: env: replace unboxed 0 with Promoted 0, keep outer >= 1 *)
Fixpoint spec_box_body_cidx {D : JoinDomain} (q : grade D) (k : nat) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar x
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (spec_box_body_cidx q k l) (spec_box_body_cidx q k r)
  | CIdxProm p i' => CIdxProm p (spec_box_body_cidx q k i')
  | CIdxUnbox b => if Nat.eqb b k then CIdxProm q (CIdxVar k) else CIdxUnbox b
  | CIdxFst p => CIdxFst p
  | CIdxSnd p => CIdxSnd p
  | CIdxCase s l r => CIdxCase s (spec_box_body_cidx q (S k) l) (spec_box_body_cidx q (S k) r)
  end.

Fixpoint spec_box_body_cty {D : JoinDomain} (q : grade D) (k : nat) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (spec_box_body_cty q k elem) (spec_box_body_cidx q k len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar x
  | CTProm p inner => CTProm p (spec_box_body_cty q k inner)
  | CTUnbox b => if Nat.eqb b k then CTProm q (CTVar k) else CTUnbox b
  | CPi x s r dom cod => CPi x s r (spec_box_body_cty q k dom) (spec_box_body_cty q (S k) cod)
  | CSigma x r f s => CSigma x r (spec_box_body_cty q k f) (spec_box_body_cty q (S k) s)
  | CBox p inner => CBox p (spec_box_body_cty q k inner)
  | CSum l r => CSum (spec_box_body_cty q k l) (spec_box_body_cty q k r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, spec_box_body_cty q k ft)) fields)
  | CInd id indices => CInd id (map (spec_box_body_cidx q k) indices)
  end.

Fixpoint subst_box_nat_cidx {D : JoinDomain} (k : nat) (q : grade D) (val : cidx D) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (subst_box_nat_cidx k q val l) (subst_box_nat_cidx k q val r)
  | CIdxProm p i' => CIdxProm p (subst_box_nat_cidx k q val i')
  | CIdxUnbox b =>
      if b =? k then CIdxProm q val
      else if b <? k then CIdxUnbox b
      else CIdxUnbox (b - 1)
  | CIdxFst p => CIdxFst (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxSnd p => CIdxSnd (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxCase s l r =>
      CIdxCase (if s <? k then s else if s =? k then 0 else s - 1)
        (subst_box_nat_cidx (S k) q (lift_cidx 0 1 val) l)
        (subst_box_nat_cidx (S k) q (lift_cidx 0 1 val) r)
  end.

Fixpoint subst_box_nat_cty {D : JoinDomain} (k : nat) (q : grade D) (val : cidx D) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (subst_box_nat_cty k q val elem) (subst_box_nat_cidx k q val len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CTProm p inner => CTProm p (subst_box_nat_cty k q val inner)
  | CTUnbox b => CTUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CPi x s r dom cod =>
      CPi x s r (subst_box_nat_cty k q val dom) (subst_box_nat_cty (S k) q (lift_cidx 0 1 val) cod)
  | CSigma x r f s =>
      CSigma x r (subst_box_nat_cty k q val f) (subst_box_nat_cty (S k) q (lift_cidx 0 1 val) s)
  | CBox p inner => CBox p (subst_box_nat_cty k q val inner)
  | CSum l r => CSum (subst_box_nat_cty k q val l) (subst_box_nat_cty k q val r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, subst_box_nat_cty k q val ft)) fields)
  | CInd id indices => CInd id (map (subst_box_nat_cidx k q val) indices)
  end.

Fixpoint subst_box_ty_cty {D : JoinDomain} (k : nat) (q : grade D) (U T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (subst_box_ty_cty k q U elem) (subst_tvar_in_cidx k len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CTProm p inner => CTProm p (subst_box_ty_cty k q U inner)
  | CTUnbox b =>
      if b =? k then CTProm q U
      else if b <? k then CTUnbox b
      else CTUnbox (b - 1)
  | CPi x s r dom cod =>
      CPi x s r (subst_box_ty_cty k q U dom) (subst_box_ty_cty (S k) q (lift_cty 0 1 U) cod)
  | CSigma x r f s =>
      CSigma x r (subst_box_ty_cty k q U f) (subst_box_ty_cty (S k) q (lift_cty 0 1 U) s)
  | CBox p inner => CBox p (subst_box_ty_cty k q U inner)
  | CSum l r => CSum (subst_box_ty_cty k q U l) (subst_box_ty_cty k q U r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, subst_box_ty_cty k q U ft)) fields)
  | CInd id indices => CInd id (map (subst_tvar_in_cidx k) indices)
  end.

Definition subst_var_in_cidx {D : JoinDomain} (k y : nat) : cidx D -> cidx D :=
  ren_cidx (Nat.iter k ren_shift (fun i => match i with 0 => y | S i' => i' end)).

Definition subst_var_in_cty {D : JoinDomain} (k y : nat) : cty D -> cty D :=
  ren_cty (Nat.iter k ren_shift (fun i => match i with 0 => y | S i' => i' end)).

Definition spec_box_subj_cty {D : JoinDomain} (box_term : cterm D) (mot : cty D) : cty D :=
  match box_term with
  | CPromote q (CNatVal i) => subst_box_nat_cty 0 q i mot
  | CPromote q (CTypeVal T) => subst_box_ty_cty 0 q T mot
  | CPromote q (CVar y) => subst_var_in_cty 0 y (spec_box_body_cty q 0 mot)
  | CVar y => subst_var_in_cty 0 y mot
  | _ => unshift_cty 0 mot
  end.

(* For CLetPair body in (y : B) :: (x : A) :: env: fst 0 -> x (1), snd 0 -> y (0), outer >= 1 -> S i *)
Fixpoint spec_pair_body_cidx {D : JoinDomain} (k : nat) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar (if x <? k then x else S x)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (spec_pair_body_cidx k l) (spec_pair_body_cidx k r)
  | CIdxProm q i' => CIdxProm q (spec_pair_body_cidx k i')
  | CIdxUnbox b => CIdxUnbox (if b <? k then b else S b)
  | CIdxFst p => if p =? k then CIdxVar (S k) else CIdxFst (if p <? k then p else S p)
  | CIdxSnd p => if p =? k then CIdxVar k else CIdxSnd (if p <? k then p else S p)
  | CIdxCase s l r =>
      CIdxCase (if s <? k then s else S s)
        (spec_pair_body_cidx (S k) l) (spec_pair_body_cidx (S k) r)
  end.

Fixpoint spec_pair_body_cty {D : JoinDomain} (k : nat) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (spec_pair_body_cty k elem) (spec_pair_body_cidx k len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else S x)
  | CTProm q inner => CTProm q (spec_pair_body_cty k inner)
  | CTUnbox b => CTUnbox (if b <? k then b else S b)
  | CPi x s r dom cod => CPi x s r (spec_pair_body_cty k dom) (spec_pair_body_cty (S k) cod)
  | CSigma x r f s => CSigma x r (spec_pair_body_cty k f) (spec_pair_body_cty (S k) s)
  | CBox q inner => CBox q (spec_pair_body_cty k inner)
  | CSum l r => CSum (spec_pair_body_cty k l) (spec_pair_body_cty k r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, spec_pair_body_cty k ft)) fields)
  | CInd id indices => CInd id (map (spec_pair_body_cidx k) indices)
  end.

Definition term_as_cidx {D : JoinDomain} (t : cterm D) : option (cidx D) :=
  match t with
  | CNatVal i => Some i
  | CVar y => Some (CIdxVar y)
  | _ => None
  end.

Fixpoint subst_pair_cidx {D : JoinDomain} (k : nat) (fst_i snd_i : cidx D) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (subst_pair_cidx k fst_i snd_i l) (subst_pair_cidx k fst_i snd_i r)
  | CIdxProm q i' => CIdxProm q (subst_pair_cidx k fst_i snd_i i')
  | CIdxUnbox b => CIdxUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CIdxFst p => if p =? k then fst_i else CIdxFst (if p <? k then p else p - 1)
  | CIdxSnd p => if p =? k then snd_i else CIdxSnd (if p <? k then p else p - 1)
  | CIdxCase s l r =>
      CIdxCase (if s <? k then s else if s =? k then 0 else s - 1)
        (subst_pair_cidx (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) l)
        (subst_pair_cidx (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) r)
  end.

Fixpoint subst_pair_cty {D : JoinDomain} (k : nat) (fst_i snd_i : cidx D) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (subst_pair_cty k fst_i snd_i elem) (subst_pair_cidx k fst_i snd_i len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CTProm q inner => CTProm q (subst_pair_cty k fst_i snd_i inner)
  | CTUnbox b => CTUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CPi x s r dom cod =>
      CPi x s r (subst_pair_cty k fst_i snd_i dom)
        (subst_pair_cty (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) cod)
  | CSigma x r f s =>
      CSigma x r (subst_pair_cty k fst_i snd_i f)
        (subst_pair_cty (S k) (lift_cidx 0 1 fst_i) (lift_cidx 0 1 snd_i) s)
  | CBox q inner => CBox q (subst_pair_cty k fst_i snd_i inner)
  | CSum l r => CSum (subst_pair_cty k fst_i snd_i l) (subst_pair_cty k fst_i snd_i r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, subst_pair_cty k fst_i snd_i ft)) fields)
  | CInd id indices => CInd id (map (subst_pair_cidx k fst_i snd_i) indices)
  end.

Definition spec_pair_subj_cty {D : JoinDomain} (pr : cterm D) (mot : cty D) : cty D :=
  match pr with
  | CPair _ _ _ _ fv sv =>
      match term_as_cidx fv, term_as_cidx sv with
      | Some fi, Some si => subst_pair_cty 0 fi si mot
      | _, _ => unshift_cty 0 mot
      end
  | CVar y => subst_var_in_cty 0 y mot
  | _ => unshift_cty 0 mot
  end.

Fixpoint subst_sum_cidx {D : JoinDomain} (is_left : bool) (k : nat) (val : cidx D) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (subst_sum_cidx is_left k val l) (subst_sum_cidx is_left k val r)
  | CIdxProm q i' => CIdxProm q (subst_sum_cidx is_left k val i')
  | CIdxUnbox b => CIdxUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CIdxFst p => CIdxFst (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxSnd p => CIdxSnd (if p <? k then p else if p =? k then 0 else p - 1)
  | CIdxCase s l r =>
      if s =? k then
        subst_cidx 0 val (subst_sum_cidx is_left (S k) (lift_cidx 0 1 val) (if is_left then l else r))
      else CIdxCase (if s <? k then s else s - 1)
             (subst_sum_cidx is_left (S k) (lift_cidx 0 1 val) l)
             (subst_sum_cidx is_left (S k) (lift_cidx 0 1 val) r)
  end.

(* For CMatchSum: branch-specific refinement of CIdxCase 0 l r *)
Definition sum_branch_rot (k x : nat) : nat :=
  if x =? 0 then k else if x <=? k then x - 1 else x.

Fixpoint spec_sum_branch_cidx {D : JoinDomain} (is_left : bool) (k : nat) (i : cidx D) : cidx D :=
  match i with
  | CIdxVar x => CIdxVar x
  | CIdxLit n => CIdxLit n
  | CIdxAdd l r => CIdxAdd (spec_sum_branch_cidx is_left k l) (spec_sum_branch_cidx is_left k r)
  | CIdxProm q i' => CIdxProm q (spec_sum_branch_cidx is_left k i')
  | CIdxUnbox b => CIdxUnbox b
  | CIdxFst p => CIdxFst p
  | CIdxSnd p => CIdxSnd p
  | CIdxCase s l r =>
      if s =? k then
        ren_cidx (sum_branch_rot k)
          (subst_sum_cidx is_left (S k) (CIdxVar 0) (if is_left then l else r))
      else CIdxCase s (spec_sum_branch_cidx is_left (S k) l) (spec_sum_branch_cidx is_left (S k) r)
  end.

Fixpoint spec_sum_branch_cty {D : JoinDomain} (is_left : bool) (k : nat) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (spec_sum_branch_cty is_left k elem) (spec_sum_branch_cidx is_left k len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar x
  | CTProm q inner => CTProm q (spec_sum_branch_cty is_left k inner)
  | CTUnbox b => CTUnbox b
  | CPi x s r dom cod => CPi x s r (spec_sum_branch_cty is_left k dom) (spec_sum_branch_cty is_left (S k) cod)
  | CSigma x r f s => CSigma x r (spec_sum_branch_cty is_left k f) (spec_sum_branch_cty is_left (S k) s)
  | CBox q inner => CBox q (spec_sum_branch_cty is_left k inner)
  | CSum l r => CSum (spec_sum_branch_cty is_left k l) (spec_sum_branch_cty is_left k r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, spec_sum_branch_cty is_left k ft)) fields)
  | CInd id indices => CInd id (map (spec_sum_branch_cidx is_left k) indices)
  end.

Fixpoint subst_sum_cty {D : JoinDomain} (is_left : bool) (k : nat) (val : cidx D) (T : cty D) : cty D :=
  match T with
  | CNat => CNat
  | CBool => CBool
  | CVec elem len => CVec (subst_sum_cty is_left k val elem) (subst_sum_cidx is_left k val len)
  | CUniv lvl => CUniv lvl
  | CTVar x => CTVar (if x <? k then x else if x =? k then 0 else x - 1)
  | CTProm q inner => CTProm q (subst_sum_cty is_left k val inner)
  | CTUnbox b => CTUnbox (if b <? k then b else if b =? k then 0 else b - 1)
  | CPi x s r dom cod =>
      CPi x s r (subst_sum_cty is_left k val dom) (subst_sum_cty is_left (S k) (lift_cidx 0 1 val) cod)
  | CSigma x r f s =>
      CSigma x r (subst_sum_cty is_left k val f) (subst_sum_cty is_left (S k) (lift_cidx 0 1 val) s)
  | CBox q inner => CBox q (subst_sum_cty is_left k val inner)
  | CSum l r => CSum (subst_sum_cty is_left k val l) (subst_sum_cty is_left k val r)
  | CRecord id fields =>
      CRecord id (map (fun '(fn, fg, ft) => (fn, fg, subst_sum_cty is_left k val ft)) fields)
  | CInd id indices => CInd id (map (subst_sum_cidx is_left k val) indices)
  end.

Definition spec_sum_subj_cty {D : JoinDomain} (scrut : cterm D) (mot : cty D) : cty D :=
  match scrut with
  | CInl _ v =>
      match term_as_cidx v with
      | Some vi => subst_sum_cty true 0 vi mot
      | None => unshift_cty 0 mot
      end
  | CInr _ v =>
      match term_as_cidx v with
      | Some vi => subst_sum_cty false 0 vi mot
      | None => unshift_cty 0 mot
      end
  | CVar y => subst_var_in_cty 0 y mot
  | _ => unshift_cty 0 mot
  end.

(* For CFix step in (x_rec : mot) :: (x_n : CNat) :: env:
   replace index 0 in mot by (CIdxVar 1 + 1), outer >= 1 by S i *)
Definition spec_fix_step_cty {D : JoinDomain} (mot : cty D) : cty D :=
  subst_cidx_in_cty 0 (CIdxAdd (CIdxVar 1) (CIdxLit 1)) (ren_cty (ren_lift 1 2) mot).

Definition spec_fix_subj_cty {D : JoinDomain} (scrut : cterm D) (mot : cty D) : cty D :=
  match term_as_cidx scrut with
  | Some i => subst_cidx_in_cty 0 i mot
  | None => unshift_cty 0 mot
  end.

(* Free-variable checks for zero-type-use irrelevance and non-dependent specialization *)
Fixpoint cidx_uses_var {D : JoinDomain} (k : nat) (i : cidx D) : bool :=
  match i with
  | CIdxVar x => Nat.eqb x k
  | CIdxLit _ => false
  | CIdxAdd l r => cidx_uses_var k l || cidx_uses_var k r
  | CIdxProm _ i' => cidx_uses_var k i'
  | CIdxUnbox b => Nat.eqb b k
  | CIdxFst p => Nat.eqb p k
  | CIdxSnd p => Nat.eqb p k
  | CIdxCase s l r => Nat.eqb s k || cidx_uses_var (S k) l || cidx_uses_var (S k) r
  end.

Fixpoint cty_uses_var {D : JoinDomain} (k : nat) (T : cty D) : bool :=
  match T with
  | CNat | CBool | CUniv _ => false
  | CVec elem len => cty_uses_var k elem || cidx_uses_var k len
  | CTVar x => Nat.eqb x k
  | CTProm _ inner => cty_uses_var k inner
  | CTUnbox b => Nat.eqb b k
  | CPi _ _ _ dom cod => cty_uses_var k dom || cty_uses_var (S k) cod
  | CSigma _ _ f s => cty_uses_var k f || cty_uses_var (S k) s
  | CBox _ inner => cty_uses_var k inner
  | CSum l r => cty_uses_var k l || cty_uses_var k r
  | CRecord _ fields => existsb (fun '(_, _, ft) => cty_uses_var k ft) fields
  | CInd _ indices => existsb (cidx_uses_var k) indices
  end.

(* ================================================================= *)
(* Part 4: Index, Type, Universe, and Subtype Checking               *)
(* ================================================================= *)

Inductive CIdxDemand {D : JoinDomain} (env : cenv D) : cidx D -> list (grade D) -> Prop :=
| CIdxDemandVar : forall x e,
    clookup env x = Some e ->
    cty_alpha_eq (cannotation e) CNat ->
    CIdxDemand env (CIdxVar x) (vec_single (length env) x one)
| CIdxDemandLit : forall n,
    CIdxDemand env (CIdxLit n) (vec_zero (length env))
| CIdxDemandAdd : forall l r dl dr,
    CIdxDemand env l dl ->
    CIdxDemand env r dr ->
    CIdxDemand env (CIdxAdd l r) (vec_add dl dr)
| CIdxDemandProm : forall q i di,
    CIdxDemand env i di ->
    CIdxDemand env (CIdxProm q i) (vec_scale q di)
| CIdxDemandUnbox : forall b e q,
    clookup env b = Some e ->
    cty_alpha_eq (cannotation e) (CBox q CNat) ->
    CIdxDemand env (CIdxUnbox b) (vec_single (length env) b one)
| CIdxDemandFst : forall p e z r snd_ty,
    clookup env p = Some e ->
    cty_alpha_eq (cannotation e) (CSigma z r CNat snd_ty) ->
    CIdxDemand env (CIdxFst p) (vec_single (length env) p one)
| CIdxDemandSnd : forall p e z r fst_ty,
    clookup env p = Some e ->
    cty_alpha_eq (cannotation e) (CSigma z r fst_ty CNat) ->
    CIdxDemand env (CIdxSnd p) (vec_single (length env) p one)
| CIdxDemandCase : forall s e A B l r dl dr d_br,
    clookup env s = Some e ->
    cty_alpha_eq (ren_cty (plus (S s)) (cannotation e)) (CSum A B) ->
    CIdxDemand ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length env) |} :: env) l dl ->
    CIdxDemand ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length env) |} :: env) r dr ->
    BranchVec (tl dl) (tl dr) d_br ->
    CIdxDemand env (CIdxCase s l r) (vec_add (vec_single (length env) s one) d_br).

Fixpoint cidx_demand {D : JoinDomain} (env : cenv D) (i : cidx D)
  : result (list (grade D)) (grade_error D) :=
  match i with
  | CIdxVar x =>
      match clookup env x with
      | None => Err (ErrUnbound x)
      | Some e =>
          if cty_alpha_eqb (cannotation e) CNat
          then Ok (vec_single (length env) x one)
          else Err (ErrTypeMismatch (cannotation e) CNat)
      end
  | CIdxLit _ => Ok (vec_zero (length env))
  | CIdxAdd l r =>
      let* dl := cidx_demand env l in
      let* dr := cidx_demand env r in
      Ok (vec_add dl dr)
  | CIdxProm q i' =>
      let* di := cidx_demand env i' in
      Ok (vec_scale q di)
  | CIdxUnbox b =>
      match clookup env b with
      | None => Err (ErrUnbound b)
      | Some e =>
          match cannotation e with
          | CBox _ CNat => Ok (vec_single (length env) b one)
          | _ => Err (ErrNotBox (cannotation e))
          end
      end
  | CIdxFst p =>
      match clookup env p with
      | None => Err (ErrUnbound p)
      | Some e =>
          match cannotation e with
          | CSigma _ _ CNat _ => Ok (vec_single (length env) p one)
          | _ => Err (ErrNotPair (cannotation e))
          end
      end
  | CIdxSnd p =>
      match clookup env p with
      | None => Err (ErrUnbound p)
      | Some e =>
          match cannotation e with
          | CSigma _ _ _ CNat => Ok (vec_single (length env) p one)
          | _ => Err (ErrNotPair (cannotation e))
          end
      end
  | CIdxCase s l r =>
      match clookup env s with
      | None => Err (ErrUnbound s)
      | Some e =>
          match ren_cty (plus (S s)) (cannotation e) with
          | CSum A B =>
              let* dl := cidx_demand ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length env) |} :: env) l in
              let* dr := cidx_demand ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length env) |} :: env) r in
              let* d_br := branch_vec 0 (tl dl) (tl dr) in
              Ok (vec_add (vec_single (length env) s one) d_br)
          | actual => Err (ErrNotSum actual)
          end
      end
  end.

Lemma cidx_demand_sound : forall (D : JoinDomain) (i : cidx D) env d,
  cidx_demand env i = Ok d -> CIdxDemand env i d.
Proof.
  intros D i. induction i; intros env d H; cbn in H.
  - destruct (clookup env x) as [e |] eqn:Hl; [| discriminate].
    destruct (cty_alpha_eqb (cannotation e) CNat) eqn:Heq; inversion H; subst.
    eapply CIdxDemandVar; [exact Hl | apply cty_alpha_eqb_sound; exact Heq].
  - inversion H; subst; constructor.
  - destruct (cidx_demand env i1) as [dl |] eqn:H1; [| discriminate].
    cbn in H. destruct (cidx_demand env i2) as [dr |] eqn:H2; inversion H; subst.
    constructor; auto.
  - destruct (cidx_demand env i) as [di |] eqn:Hi; inversion H; subst.
    constructor; auto.
  - destruct (clookup env b) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | | | | | | | q inner | | |] eqn:Hann; try discriminate.
    destruct inner; inversion H; subst.
    eapply CIdxDemandUnbox; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - destruct (clookup env p) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | | | | | | z r fst_ty snd_ty | | | |] eqn:Hann; try discriminate.
    destruct fst_ty; inversion H; subst.
    eapply CIdxDemandFst; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - destruct (clookup env p) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | | | | | | z r fst_ty snd_ty | | | |] eqn:Hann; try discriminate.
    destruct snd_ty; inversion H; subst.
    eapply CIdxDemandSnd; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - destruct (clookup env s) as [e |] eqn:Hl; [| discriminate].
    match type of H with
    | match ren_cty ?f (cannotation e) with _ => _ end = Ok d =>
        destruct (ren_cty f (cannotation e)) as [| | | | | | | | | | A B | |] eqn:Hsum
    end; try discriminate.
    destruct (cidx_demand ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length env) |} :: env) i1)
      as [dl |] eqn:Hdl; [| discriminate].
    cbn in H.
    destruct (cidx_demand ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length env) |} :: env) i2)
      as [dr |] eqn:Hdr; [| discriminate].
    cbn in H.
    destruct (branch_vec 0 (tl dl) (tl dr)) as [d_br |] eqn:Hbr; inversion H; subst.
    eapply CIdxDemandCase; eauto using branch_vec_sound.
    change (ren_cty (plus (S s)) (cannotation e)) with (ren_cty (fun m : nat => S (s + m)) (cannotation e)).
    rewrite Hsum. apply cty_alpha_eq_refl.
Qed.

Inductive CTypeDemand {D : JoinDomain} : cenv D -> cty D -> list (grade D) -> Prop :=
| CTypeNat : forall env, CTypeDemand env CNat (vec_zero (length env))
| CTypeBool : forall env, CTypeDemand env CBool (vec_zero (length env))
| CTypeVec : forall env elem len de dl,
    CTypeDemand env elem de ->
    CIdxDemand env len dl ->
    CTypeDemand env (CVec elem len) (vec_add de dl)
| CTypeUniv : forall env lvl, CTypeDemand env (CUniv lvl) (vec_zero (length env))
| CTypeTVar : forall env x e lvl,
    clookup env x = Some e ->
    cty_alpha_eq (cannotation e) (CUniv lvl) ->
    CTypeDemand env (CTVar x) (vec_single (length env) x one)
| CTypeTProm : forall env q inner di,
    CTypeDemand env inner di ->
    CTypeDemand env (CTProm q inner) (vec_scale q di)
| CTypeTUnbox : forall env b e q lvl,
    clookup env b = Some e ->
    cty_alpha_eq (cannotation e) (CBox q (CUniv lvl)) ->
    CTypeDemand env (CTUnbox b) (vec_single (length env) b one)
| CTypePi : forall env x s r dom cod a b,
    CTypeDemand env dom a ->
    CTypeDemand ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) cod b ->
    allows (nth_grade b 0) r ->
    CTypeDemand env (CPi x s r dom cod) (vec_add a (tl b))
| CTypeSigma : forall env x r f s a b,
    CTypeDemand env f a ->
    CTypeDemand ({| cbinder := x; cannotation := f; ctype_uses := a |} :: env) s b ->
    allows (nth_grade b 0) r ->
    CTypeDemand env (CSigma x r f s) (vec_add a (tl b))
| CTypeBox : forall env q inner d,
    CTypeDemand env inner d ->
    CTypeDemand env (CBox q inner) d
| CTypeSum : forall env l r dl dr,
    CTypeDemand env l dl ->
    CTypeDemand env r dr ->
    CTypeDemand env (CSum l r) (vec_add dl dr)
| CTypeRecord : forall env id fields df,
    CRecordFieldDemand env fields df ->
    CTypeDemand env (CRecord id fields) df
| CTypeInd : forall env id indices di,
    CIdxListDemand env indices di ->
    CTypeDemand env (CInd id indices) di

with CRecordFieldDemand {D : JoinDomain} : cenv D -> list (nat * grade D * cty D) -> list (grade D) -> Prop :=
| CRecordFieldNil : forall env,
    CRecordFieldDemand env [] (vec_zero (length env))
| CRecordFieldCons : forall env fn fg ft rest dt drest,
    CTypeDemand env ft dt ->
    CRecordFieldDemand env rest drest ->
    CRecordFieldDemand env ((fn, fg, ft) :: rest) (vec_add dt drest)

with CIdxListDemand {D : JoinDomain} : cenv D -> list (cidx D) -> list (grade D) -> Prop :=
| CIdxListNil : forall env,
    CIdxListDemand env [] (vec_zero (length env))
| CIdxListCons : forall env idx rest di drest,
    CIdxDemand env idx di ->
    CIdxListDemand env rest drest ->
    CIdxListDemand env (idx :: rest) (vec_add di drest).

Fixpoint cidx_list_demand {D : JoinDomain} (env : cenv D) (indices : list (cidx D))
  : result (list (grade D)) (grade_error D) :=
  match indices with
  | [] => Ok (vec_zero (length env))
  | idx :: rest =>
      let* di := cidx_demand env idx in
      let* drest := cidx_list_demand env rest in
      Ok (vec_add di drest)
  end.

Lemma cidx_list_demand_sound : forall (D : JoinDomain) (indices : list (cidx D)) env d,
  cidx_list_demand env indices = Ok d -> CIdxListDemand env indices d.
Proof.
  intros D indices. induction indices as [| idx rest IH]; intros env d H; cbn in H.
  - inversion H; constructor.
  - destruct (cidx_demand env idx) as [di |] eqn:Hi; [| discriminate].
    cbn in H. destruct (cidx_list_demand env rest) as [drest |] eqn:Hr; inversion H; subst.
    constructor; [apply cidx_demand_sound; exact Hi | apply IH; exact Hr].
Qed.

Fixpoint ctype_demand {D : JoinDomain} (env : cenv D) (T : cty D)
  : result (list (grade D)) (grade_error D) :=
  match T with
  | CNat | CBool | CUniv _ => Ok (vec_zero (length env))
  | CVec elem len =>
      let* de := ctype_demand env elem in
      let* dl := cidx_demand env len in
      Ok (vec_add de dl)
  | CTVar x =>
      match clookup env x with
      | None => Err (ErrUnbound x)
      | Some e =>
          match cannotation e with
          | CUniv _ => Ok (vec_single (length env) x one)
          | _ => Err (ErrTypeMismatch (cannotation e) (CUniv 0))
          end
      end
  | CTProm q inner =>
      let* di := ctype_demand env inner in
      Ok (vec_scale q di)
  | CTUnbox b =>
      match clookup env b with
      | None => Err (ErrUnbound b)
      | Some e =>
          match cannotation e with
          | CBox _ (CUniv _) => Ok (vec_single (length env) b one)
          | _ => Err (ErrNotBox (cannotation e))
          end
      end
  | CPi x _ r dom cod =>
      let* a := ctype_demand env dom in
      let* b := ctype_demand ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) cod in
      if allowsb (nth_grade b 0) r then Ok (vec_add a (tl b))
      else Err (ErrBinderTypeMismatch x (nth_grade b 0) r)
  | CSigma x r f s =>
      let* a := ctype_demand env f in
      let* b := ctype_demand ({| cbinder := x; cannotation := f; ctype_uses := a |} :: env) s in
      if allowsb (nth_grade b 0) r then Ok (vec_add a (tl b))
      else Err (ErrBinderTypeMismatch x (nth_grade b 0) r)
  | CBox _ inner => ctype_demand env inner
  | CSum l r =>
      let* dl := ctype_demand env l in
      let* dr := ctype_demand env r in
      Ok (vec_add dl dr)
  | CRecord _ fields =>
      (fix go_fields (fs : list (nat * grade D * cty D)) : result (list (grade D)) (grade_error D) :=
         match fs with
         | [] => Ok (vec_zero (length env))
         | (_, _, ft) :: rest =>
             let* dt := ctype_demand env ft in
             let* drest := go_fields rest in
             Ok (vec_add dt drest)
         end) fields
  | CInd _ indices => cidx_list_demand env indices
  end.

Lemma ctype_demand_sound : forall (D : JoinDomain) (T : cty D) env d,
  ctype_demand env T = Ok d -> CTypeDemand env T d.
Proof.
  intros D T. induction T using cty_ind_nested; intros env d Hchk; cbn in Hchk.
  - inversion Hchk; constructor.
  - inversion Hchk; constructor.
  - destruct (ctype_demand env T) as [de |] eqn:He; [| discriminate].
    cbn in Hchk. destruct (cidx_demand env len) as [dl |] eqn:Hl; inversion Hchk; subst.
    constructor; [apply IHT; exact He | apply cidx_demand_sound; exact Hl].
  - inversion Hchk; constructor.
  - destruct (clookup env x) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | lvl | | | | | | | | |] eqn:Hann; try discriminate.
    inversion Hchk; subst.
    eapply CTypeTVar; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - destruct (ctype_demand env T) as [di |] eqn:Hi; inversion Hchk; subst.
    constructor; auto.
  - destruct (clookup env b) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | | | | | | | q inner | | |] eqn:Hann; try discriminate.
    destruct inner; inversion Hchk; subst.
    eapply CTypeTUnbox; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - destruct (ctype_demand env T1) as [a |] eqn:Ha; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := x; cannotation := T1; ctype_uses := a |} :: env) T2)
      as [b |] eqn:Hb; [| discriminate].
    cbn in Hchk.
    destruct (allowsb (nth_grade b 0) r) eqn:Hr; inversion Hchk; subst.
    destruct (allows_reflect D (nth_grade b 0) r); [| discriminate].
    constructor; [apply IHT1; exact Ha | apply IHT2; exact Hb | assumption].
  - destruct (ctype_demand env T1) as [a |] eqn:Ha; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := x; cannotation := T1; ctype_uses := a |} :: env) T2)
      as [b |] eqn:Hb; [| discriminate].
    cbn in Hchk.
    destruct (allowsb (nth_grade b 0) r) eqn:Hr; inversion Hchk; subst.
    destruct (allows_reflect D (nth_grade b 0) r); [| discriminate].
    constructor; [apply IHT1; exact Ha | apply IHT2; exact Hb | assumption].
  - constructor; apply IHT; exact Hchk.
  - destruct (ctype_demand env T1) as [dl |] eqn:Hl; [| discriminate].
    cbn in Hchk. destruct (ctype_demand env T2) as [dr |] eqn:Hr; inversion Hchk; subst.
    constructor; [apply IHT1; exact Hl | apply IHT2; exact Hr].
  - constructor. revert d Hchk.
    induction fields as [| [[fn fg] ft] rest IHf]; intros d Hchk; cbn in Hchk.
    + inversion Hchk; constructor.
    + inversion H; subst. cbn in H2.
      destruct (ctype_demand env ft) as [dt |] eqn:Hft; [| discriminate].
      cbn in Hchk.
      match type of Hchk with
      | bind_res (?g rest) _ = Ok d => destruct (g rest) as [drest |] eqn:Hrest
      end; inversion Hchk; subst.
      constructor; [apply H2; exact Hft | apply IHf; [exact H3 | reflexivity]].
  - constructor. apply cidx_list_demand_sound; exact Hchk.
Qed.

Inductive CUniverseLevel {D : JoinDomain} : cenv D -> cty D -> nat -> Prop :=
| CLevelNat : forall env, CUniverseLevel env CNat 0
| CLevelBool : forall env, CUniverseLevel env CBool 0
| CLevelVec : forall env elem len i,
    CUniverseLevel env elem i -> CUniverseLevel env (CVec elem len) i
| CLevelUniv : forall env lvl, CUniverseLevel env (CUniv lvl) (S lvl)
| CLevelTVar : forall env x e lvl,
    clookup env x = Some e -> cty_alpha_eq (cannotation e) (CUniv lvl) ->
    CUniverseLevel env (CTVar x) lvl
| CLevelTProm : forall env q inner i,
    CUniverseLevel env inner i -> CUniverseLevel env (CTProm q inner) i
| CLevelTUnbox : forall env b e q lvl,
    clookup env b = Some e -> cty_alpha_eq (cannotation e) (CBox q (CUniv lvl)) ->
    CUniverseLevel env (CTUnbox b) lvl
| CLevelPi : forall env x s r dom cod i j,
    CUniverseLevel env dom i ->
    CUniverseLevel ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env) cod j ->
    CUniverseLevel env (CPi x s r dom cod) (Nat.max i j)
| CLevelSigma : forall env x r f s i j,
    CUniverseLevel env f i ->
    CUniverseLevel ({| cbinder := x; cannotation := f; ctype_uses := [] |} :: env) s j ->
    CUniverseLevel env (CSigma x r f s) (Nat.max i j)
| CLevelBox : forall env q inner i,
    CUniverseLevel env inner i -> CUniverseLevel env (CBox q inner) i
| CLevelSum : forall env l r i j,
    CUniverseLevel env l i -> CUniverseLevel env r j -> CUniverseLevel env (CSum l r) (Nat.max i j)
| CLevelRecord : forall env id fields i,
    CRecordFieldLevel env fields i -> CUniverseLevel env (CRecord id fields) i
| CLevelInd : forall env id indices, CUniverseLevel env (CInd id indices) 0

with CRecordFieldLevel {D : JoinDomain} : cenv D -> list (nat * grade D * cty D) -> nat -> Prop :=
| CRecordLevelNil : forall env, CRecordFieldLevel env [] 0
| CRecordLevelCons : forall env fn fg ft rest i j,
    CUniverseLevel env ft i ->
    CRecordFieldLevel env rest j ->
    CRecordFieldLevel env ((fn, fg, ft) :: rest) (Nat.max i j).

Fixpoint cuniverse_level {D : JoinDomain} (env : cenv D) (T : cty D)
  : result nat (grade_error D) :=
  match T with
  | CNat | CBool | CInd _ _ => Ok 0
  | CVec elem _ | CTProm _ elem | CBox _ elem => cuniverse_level env elem
  | CUniv lvl => Ok (S lvl)
  | CTVar x =>
      match clookup env x with
      | None => Err (ErrUnbound x)
      | Some e =>
          match cannotation e with
          | CUniv lvl => Ok lvl
          | _ => Err (ErrTypeMismatch (cannotation e) (CUniv 0))
          end
      end
  | CTUnbox b =>
      match clookup env b with
      | None => Err (ErrUnbound b)
      | Some e =>
          match cannotation e with
          | CBox _ (CUniv lvl) => Ok lvl
          | _ => Err (ErrNotBox (cannotation e))
          end
      end
  | CPi x _ _ dom cod | CSigma x _ dom cod =>
      let* i := cuniverse_level env dom in
      let* j := cuniverse_level ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env) cod in
      Ok (Nat.max i j)
  | CSum l r =>
      let* i := cuniverse_level env l in
      let* j := cuniverse_level env r in
      Ok (Nat.max i j)
  | CRecord _ fields =>
      (fix go_fields (fs : list (nat * grade D * cty D)) : result nat (grade_error D) :=
         match fs with
         | [] => Ok 0
         | (_, _, ft) :: rest =>
             let* i := cuniverse_level env ft in
             let* j := go_fields rest in
             Ok (Nat.max i j)
         end) fields
  end.

Lemma cuniverse_level_sound : forall (D : JoinDomain) (T : cty D) env lvl,
  cuniverse_level env T = Ok lvl -> CUniverseLevel env T lvl.
Proof.
  intros D T. induction T using cty_ind_nested; intros env lvl0 Hchk; cbn in Hchk.
  - inversion Hchk; constructor.
  - inversion Hchk; constructor.
  - constructor; apply IHT; exact Hchk.
  - inversion Hchk; constructor.
  - destruct (clookup env x) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | lvl | | | | | | | | |] eqn:Hann; try discriminate.
    inversion Hchk; subst. eapply CLevelTVar; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - constructor; apply IHT; exact Hchk.
  - destruct (clookup env b) as [e |] eqn:Hl; [| discriminate].
    destruct (cannotation e) as [| | | | | | | | | q inner | | |] eqn:Hann; try discriminate.
    destruct inner; inversion Hchk; subst.
    eapply CLevelTUnbox; [exact Hl | rewrite Hann; apply cty_alpha_eq_refl].
  - destruct (cuniverse_level env T1) as [i |] eqn:Hi; [| discriminate].
    cbn in Hchk. destruct (cuniverse_level ({| cbinder := x; cannotation := T1; ctype_uses := [] |} :: env) T2)
      as [j |] eqn:Hj; inversion Hchk; subst.
    constructor; auto.
  - destruct (cuniverse_level env T1) as [i |] eqn:Hi; [| discriminate].
    cbn in Hchk. destruct (cuniverse_level ({| cbinder := x; cannotation := T1; ctype_uses := [] |} :: env) T2)
      as [j |] eqn:Hj; inversion Hchk; subst.
    constructor; auto.
  - constructor; apply IHT; exact Hchk.
  - destruct (cuniverse_level env T1) as [i |] eqn:Hi; [| discriminate].
    cbn in Hchk. destruct (cuniverse_level env T2) as [j |] eqn:Hj; inversion Hchk; subst.
    constructor; auto.
  - constructor. revert lvl0 Hchk.
    induction fields as [| [[fn fg] ft] rest IHf]; intros lvl0 Hchk; cbn in Hchk.
    + inversion Hchk; constructor.
    + inversion H; subst. cbn in H2.
      destruct (cuniverse_level env ft) as [i |] eqn:Hi; [| discriminate].
      cbn in Hchk.
      match type of Hchk with
      | bind_res (?g rest) _ = Ok lvl0 => destruct (g rest) as [j |] eqn:Hj
      end; inversion Hchk; subst.
      constructor; [apply H2; exact Hi | apply IHf; [exact H3 | reflexivity]].
  - inversion Hchk; constructor.
Qed.

Inductive CEnvWf {D : JoinDomain} : cenv D -> Prop :=
| CEnvNil : CEnvWf []
| CEnvCons : forall env x T row,
    CEnvWf env ->
    CTypeDemand env T row ->
    CEnvWf ({| cbinder := x; cannotation := T; ctype_uses := row |} :: env).

Fixpoint check_cenv {D : JoinDomain} (env : cenv D) : result unit (grade_error D) :=
  match env with
  | [] => Ok tt
  | entry :: rest =>
      let* _ := check_cenv rest in
      let* row := ctype_demand rest (cannotation entry) in
      if vec_eqb (ctype_uses entry) row then Ok tt
      else Err (ErrTypeMismatch (cannotation entry) (cannotation entry))
  end.

Lemma check_cenv_sound : forall (D : JoinDomain) (env : cenv D),
  check_cenv env = Ok tt -> CEnvWf env.
Proof.
  intros D env. induction env as [| [x T u] rest IH]; intro H; cbn in H.
  - constructor.
  - destruct (check_cenv rest) as [[] |] eqn:Hr; [| discriminate].
    cbn in H. destruct (ctype_demand rest T) as [row |] eqn:Ht; [| discriminate].
    cbn in H. destruct (vec_eqb u row) eqn:Heq; inversion H; subst.
    apply vec_eqb_sound in Heq. subst u.
    constructor; [apply IH; reflexivity | apply ctype_demand_sound; exact Ht].
Qed.

(* Subtyping & subgrading:
   - Box covariance in capability order (q' <= q, i.e., allows q' q)
   - Pi contravariance in domain type and domain capability grade (allows s s', allows r r') *)
Inductive Subty {D : JoinDomain} : cenv D -> cty D -> cty D -> Prop :=
| SubRefl : forall env A B,
    cty_alpha_eq A B -> Subty env A B
| SubBox : forall env q q' A B,
    allows q' q ->
    Subty env A B ->
    Subty env (CBox q A) (CBox q' B)
| SubPi : forall env x x' s s' r r' A A' B B',
    allows s s' ->
    allows r r' ->
    Subty env A' A ->
    Subty ({| cbinder := x'; cannotation := A'; ctype_uses := vec_zero (length env) |} :: env) B B' ->
    Subty env (CPi x s r A B) (CPi x' s' r' A' B')
| SubSigma : forall env x x' r r' A A' B B',
    allows r r' ->
    Subty env A A' ->
    Subty ({| cbinder := x; cannotation := A; ctype_uses := vec_zero (length env) |} :: env) B B' ->
    Subty env (CSigma x r A B) (CSigma x' r' A' B')
| SubSum : forall env A A' B B',
    Subty env A A' ->
    Subty env B B' ->
    Subty env (CSum A B) (CSum A' B')
| SubVec : forall env A A' l l',
    cidx_eqb l l' = true ->
    Subty env A A' ->
    Subty env (CVec A l) (CVec A' l').

Fixpoint cty_size {D : JoinDomain} (T : cty D) : nat :=
  match T with
  | CNat | CBool | CUniv _ | CTVar _ | CTUnbox _ | CInd _ _ => 1
  | CVec elem _ | CTProm _ elem | CBox _ elem => S (cty_size elem)
  | CPi _ _ _ dom cod | CSigma _ _ dom cod | CSum dom cod => S (cty_size dom + cty_size cod)
  | CRecord _ fields =>
      S ((fix go_sz (fs : list (nat * grade D * cty D)) : nat :=
            match fs with
            | [] => 0
            | (_, _, ft) :: rest => cty_size ft + go_sz rest
            end) fields)
  end.

Fixpoint subtyb_fuel {D : JoinDomain} (fuel : nat) (env : cenv D) (A B : cty D) : bool :=
  if cty_alpha_eqb A B then true
  else match fuel with
       | 0 => false
       | S fuel' =>
           match A, B with
           | CBox q A1, CBox q' B1 =>
               allowsb q' q && subtyb_fuel fuel' env A1 B1
           | CPi _ s r A1 B1, CPi x' s' r' A2 B2 =>
               allowsb s s' && allowsb r r' && subtyb_fuel fuel' env A2 A1 &&
               subtyb_fuel fuel' ({| cbinder := x'; cannotation := A2; ctype_uses := vec_zero (length env) |} :: env) B1 B2
           | CSigma x r A1 B1, CSigma _ r' A2 B2 =>
               allowsb r r' && subtyb_fuel fuel' env A1 A2 &&
               subtyb_fuel fuel' ({| cbinder := x; cannotation := A1; ctype_uses := vec_zero (length env) |} :: env) B1 B2
           | CSum A1 B1, CSum A2 B2 =>
               subtyb_fuel fuel' env A1 A2 && subtyb_fuel fuel' env B1 B2
           | CVec A1 l1, CVec A2 l2 =>
               cidx_eqb l1 l2 && subtyb_fuel fuel' env A1 A2
           | _, _ => false
           end
       end.

Definition subtyb {D : JoinDomain} (env : cenv D) (A B : cty D) : bool :=
  subtyb_fuel (cty_size A + cty_size B) env A B.

Lemma subtyb_fuel_sound : forall (D : JoinDomain) fuel (A B : cty D) env,
  subtyb_fuel fuel env A B = true ->
  Subty env A B.
Proof.
  intros D fuel. induction fuel as [| fuel' IH]; intros A B env Hchk; cbn in Hchk.
  - destruct (cty_alpha_eqb A B) eqn:Heq; [| discriminate].
    apply SubRefl. apply cty_alpha_eqb_sound; exact Heq.
  - destruct (cty_alpha_eqb A B) eqn:Heq.
    + apply SubRefl. apply cty_alpha_eqb_sound; exact Heq.
    + destruct A, B; try discriminate.
      * apply andb_true_iff in Hchk as [Hl HA].
        apply SubVec; [exact Hl | apply IH; exact HA].
      * apply andb_true_iff in Hchk as [H1 HB].
        apply andb_true_iff in H1 as [H2 HA].
        apply andb_true_iff in H2 as [Hs Hr].
        destruct (allows_reflect D s s0); [| discriminate].
        destruct (allows_reflect D r r0); [| discriminate].
        eapply SubPi; eauto.
      * apply andb_true_iff in Hchk as [H1 HB].
        apply andb_true_iff in H1 as [Hr HA].
        destruct (allows_reflect D r r0); [| discriminate].
        eapply SubSigma; eauto.
      * apply andb_true_iff in Hchk as [Hq HA].
        destruct (allows_reflect D q0 q); [| discriminate].
        eapply SubBox; eauto.
      * apply andb_true_iff in Hchk as [HA HB].
        apply SubSum; apply IH; assumption.
Qed.

Lemma subtyb_sound : forall (D : JoinDomain) (A B : cty D) env,
  subtyb env A B = true -> Subty env A B.
Proof.
  intros D A B env H. unfold subtyb in H. eapply subtyb_fuel_sound; exact H.
Qed.

(* ================================================================= *)
(* Part 5: Unified Core Judgment & Executable Type/Grade Checker     *)
(* ================================================================= *)

Record cjudgment (D : JoinDomain) := {
  cresult_type : cty D;
  ccomp_demand : list (grade D);
  ctype_demand_row : list (grade D)
}.

Arguments Build_cjudgment {D} cresult_type ccomp_demand ctype_demand_row.
Arguments cresult_type {D} _.
Arguments ccomp_demand {D} _.
Arguments ctype_demand_row {D} _.

Definition app_result_ty {D : JoinDomain} (dom cod : cty D) (arg : cterm D) : option (cty D) :=
  match dom, term_as_cidx arg with
  | CNat, Some idx => Some (subst_cidx_in_cty 0 idx cod)
  | CUniv _, _ =>
      match arg with
      | CTypeVal T => Some (subst_tvar_in_cty 0 T cod)
      | CVar y => Some (subst_tvar_in_cty 0 (CTVar y) cod)
      | _ => if cty_uses_var 0 cod then None else Some (unshift_cty 0 cod)
      end
  | _, _ => if cty_uses_var 0 cod then None else Some (unshift_cty 0 cod)
  end.

Definition app_type_arg_demand {D : JoinDomain} (dom : cty D) (arg : cterm D)
  (u_arg v_arg : list (grade D)) : list (grade D) :=
  match dom, arg with
  | CUniv _, CTypeVal _ => v_arg
  | _, _ => u_arg
  end.

Definition fix_recurrence_ok {D : JoinDomain} (s_rec : grade D) (u_step_outer : list (grade D)) : Prop :=
  if vec_is_zero u_step_outer then True
  else allows one s_rec /\ allows (add s_rec s_rec) s_rec /\ allows (mul s_rec s_rec) s_rec.

Definition fix_recurrence_okb {D : JoinDomain} (s_rec : grade D) (u_step_outer : list (grade D)) : bool :=
  if vec_is_zero u_step_outer then true
  else allowsb one s_rec && allowsb (add s_rec s_rec) s_rec && allowsb (mul s_rec s_rec) s_rec.

Lemma fix_recurrence_okb_sound : forall (D : JoinDomain) (s_rec : grade D) u_step_outer,
  fix_recurrence_okb s_rec u_step_outer = true -> fix_recurrence_ok s_rec u_step_outer.
Proof.
  intros D s_rec u H. unfold fix_recurrence_okb, fix_recurrence_ok in *.
  destruct (vec_is_zero u); [exact I |].
  apply andb_true_iff in H as [H1 Hmul].
  apply andb_true_iff in H1 as [Hone Hadd].
  destruct (allows_reflect D one s_rec), (allows_reflect D (add s_rec s_rec) s_rec),
           (allows_reflect D (mul s_rec s_rec) s_rec); try discriminate.
  auto.
Qed.

Inductive CoreDerives {D : JoinDomain} : cenv D -> cterm D -> cjudgment D -> Prop :=
| CoreVar : forall env x e row,
    clookup env x = Some e ->
    CTypeDemand (skipn (S x) env) (cannotation e) row ->
    vec_allows row (ctype_uses e) ->
    CoreDerives env (CVar x)
      {| cresult_type := ren_cty (plus (S x)) (cannotation e);
         ccomp_demand := vec_single (length env) x one;
         ctype_demand_row := vec_zero (S x) ++ ctype_uses e |}
| CoreNatVal : forall env i d,
    CIdxDemand env i d ->
    CoreDerives env (CNatVal i)
      {| cresult_type := CNat;
         ccomp_demand := d;
         ctype_demand_row := vec_zero (length env) |}
| CoreBoolVal : forall env b,
    CoreDerives env (CBoolVal b)
      {| cresult_type := CBool;
         ccomp_demand := vec_zero (length env);
         ctype_demand_row := vec_zero (length env) |}
| CoreTypeVal : forall env T lvl v,
    CTypeDemand env T v ->
    CUniverseLevel env T lvl ->
    CoreDerives env (CTypeVal T)
      {| cresult_type := CUniv lvl;
         ccomp_demand := vec_zero (length env);
         ctype_demand_row := v |}
| CoreLam : forall env x s r dom a body cod u v,
    CTypeDemand env dom a ->
    CoreDerives ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) body
      {| cresult_type := cod; ccomp_demand := u; ctype_demand_row := v |} ->
    allows (nth_grade u 0) s ->
    allows (nth_grade v 0) r ->
    CoreDerives env (CLam x s r dom body)
      {| cresult_type := CPi x s r dom cod;
         ccomp_demand := tl u;
         ctype_demand_row := vec_add a (tl v) |}
| CoreApp : forall env fn arg x s r dom cod kind w v_fn u_arg v_arg a_dom b res_ty z_type,
    CoreDerives env fn {| cresult_type := CPi x s r dom cod; ccomp_demand := w; ctype_demand_row := v_fn |} ->
    CoreDerives env arg {| cresult_type := kind; ccomp_demand := u_arg; ctype_demand_row := v_arg |} ->
    cty_alpha_eq kind dom ->
    CTypeDemand env dom a_dom ->
    CTypeDemand ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env) cod b ->
    allows (nth_grade b 0) r ->
    (forall lvl arg_ty, dom = CUniv lvl ->
       (arg = CTypeVal arg_ty \/ (exists y, arg = CVar y /\ arg_ty = CTVar y)) ->
       CUniverseLevel env arg_ty lvl) ->
    app_result_ty dom cod arg = Some res_ty ->
    z_type = app_type_arg_demand dom arg u_arg v_arg ->
    CoreDerives env (CApp fn arg)
      {| cresult_type := res_ty;
         ccomp_demand := vec_add w (vec_scale s u_arg);
         ctype_demand_row := vec_add (tl b) (vec_scale r z_type) |}
| CoreLet : forall env x s r ann rhs body a_ann rhs_ty u_rhs v_rhs bod_ty u_bod v_bod,
    CTypeDemand env ann a_ann ->
    CoreDerives env rhs {| cresult_type := rhs_ty; ccomp_demand := u_rhs; ctype_demand_row := v_rhs |} ->
    cty_alpha_eq rhs_ty ann ->
    CoreDerives ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env) body
      {| cresult_type := bod_ty; ccomp_demand := u_bod; ctype_demand_row := v_bod |} ->
    allows (nth_grade u_bod 0) s ->
    allows (nth_grade v_bod 0) r ->
    cty_uses_var 0 bod_ty = false ->
    CoreDerives env (CLet x s r ann rhs body)
      {| cresult_type := unshift_cty 0 bod_ty;
         ccomp_demand := vec_add (tl u_bod) (vec_scale s u_rhs);
         ctype_demand_row := vec_add (tl v_bod) (vec_scale r (app_type_arg_demand ann rhs u_rhs v_rhs)) |}
| CorePair : forall env x r fst_ty snd_ty fst_val snd_val a b u_l v_l u_r v_r fst_act snd_act exp_snd,
    CTypeDemand env fst_ty a ->
    CTypeDemand ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env) snd_ty b ->
    allows (nth_grade b 0) r ->
    CoreDerives env fst_val {| cresult_type := fst_act; ccomp_demand := u_l; ctype_demand_row := v_l |} ->
    cty_alpha_eq fst_act fst_ty ->
    CoreDerives env snd_val {| cresult_type := snd_act; ccomp_demand := u_r; ctype_demand_row := v_r |} ->
    app_result_ty fst_ty snd_ty fst_val = Some exp_snd ->
    cty_alpha_eq snd_act exp_snd ->
    CoreDerives env (CPair x r fst_ty snd_ty fst_val snd_val)
      {| cresult_type := CSigma x r fst_ty snd_ty;
         ccomp_demand := vec_add u_l u_r;
         ctype_demand_row := vec_add a (tl b) |}
| CoreLetPair : forall env x y s kappa mot pr body z r A B w v_p a b v_mot u_b v_b act_mot exp_mot res_ty,
    CoreDerives env pr {| cresult_type := CSigma z r A B; ccomp_demand := w; ctype_demand_row := v_p |} ->
    CTypeDemand env A a ->
    CTypeDemand ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) B b ->
    CTypeDemand ({| cbinder := 0; cannotation := CSigma z r A B; ctype_uses := vec_add a (tl b) |} :: env) mot v_mot ->
    allows (nth_grade v_mot 0) kappa ->
    CoreDerives
      ({| cbinder := y; cannotation := B; ctype_uses := b |} ::
       {| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
      body {| cresult_type := act_mot; ccomp_demand := u_b; ctype_demand_row := v_b |} ->
    exp_mot = spec_pair_body_cty 0 mot ->
    cty_alpha_eq act_mot exp_mot ->
    allows (nth_grade u_b 1) s ->
    allows (nth_grade u_b 0) s ->
    (match pr with
     | CPair _ _ _ _ fv sv =>
         match term_as_cidx fv, term_as_cidx sv with
         | Some _, Some _ => True
         | _, _ => cty_uses_var 0 mot = false
         end
     | CVar _ => True
     | _ => cty_uses_var 0 mot = false
     end) ->
    res_ty = spec_pair_subj_cty pr mot ->
    CoreDerives env (CLetPair x y s kappa mot pr body)
      {| cresult_type := res_ty;
         ccomp_demand := vec_add (tl (tl u_b)) (vec_scale s w);
         ctype_demand_row := vec_add (tl v_mot) (vec_scale kappa w) |}
| CorePromote : forall env q val A u v,
    CoreDerives env val {| cresult_type := A; ccomp_demand := u; ctype_demand_row := v |} ->
    CoreDerives env (CPromote q val)
      {| cresult_type := CBox q A;
         ccomp_demand := vec_scale q u;
         ctype_demand_row := v |}
| CoreLetBox : forall env x kappa mot box_term body q A z_b vz a v_mot w bw act_mot exp_mot res_ty z_ty,
    CoreDerives env box_term {| cresult_type := CBox q A; ccomp_demand := z_b; ctype_demand_row := vz |} ->
    CTypeDemand env A a ->
    CTypeDemand ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env) mot v_mot ->
    allows (nth_grade v_mot 0) kappa ->
    CoreDerives ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) body
      {| cresult_type := act_mot; ccomp_demand := w; ctype_demand_row := bw |} ->
    exp_mot = spec_box_body_cty q 0 mot ->
    cty_alpha_eq act_mot exp_mot ->
    allows (nth_grade w 0) q ->
    allows (nth_grade bw 0) (mul q kappa) ->
    (match box_term with
     | CPromote _ (CNatVal _) | CPromote _ (CTypeVal _) | CPromote _ (CVar _) | CVar _ => True
     | _ => cty_uses_var 0 mot = false
     end) ->
    res_ty = spec_box_subj_cty box_term mot ->
    z_ty = (match box_term with
            | CPromote q' (CTypeVal _) => vec_scale q' vz
            | _ => z_b
            end) ->
    CoreDerives env (CLetBox x kappa mot box_term body)
      {| cresult_type := res_ty;
         ccomp_demand := vec_add (tl w) z_b;
         ctype_demand_row := vec_add (tl v_mot) (vec_scale kappa z_ty) |}
| CoreInl : forall env rhs_ty val A u a b,
    CoreDerives env val {| cresult_type := A; ccomp_demand := u; ctype_demand_row := a |} ->
    CTypeDemand env rhs_ty b ->
    CoreDerives env (CInl rhs_ty val)
      {| cresult_type := CSum A rhs_ty;
         ccomp_demand := u;
         ctype_demand_row := vec_add a b |}
| CoreInr : forall env lhs_ty val B u b a,
    CTypeDemand env lhs_ty a ->
    CoreDerives env val {| cresult_type := B; ccomp_demand := u; ctype_demand_row := b |} ->
    CoreDerives env (CInr lhs_ty val)
      {| cresult_type := CSum lhs_ty B;
         ccomp_demand := u;
         ctype_demand_row := vec_add a b |}
| CoreMatchSum : forall env x y s kappa mot scrut lb rb A B w vs a b v_mot u1 b1 t1 u2 b2 t2 u_br res_ty,
    s <> zero ->
    CoreDerives env scrut {| cresult_type := CSum A B; ccomp_demand := w; ctype_demand_row := vs |} ->
    CTypeDemand env A a ->
    CTypeDemand env B b ->
    CTypeDemand ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b |} :: env) mot v_mot ->
    allows (nth_grade v_mot 0) kappa ->
    CoreDerives ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) lb
      {| cresult_type := t1; ccomp_demand := u1; ctype_demand_row := b1 |} ->
    CoreDerives ({| cbinder := y; cannotation := B; ctype_uses := b |} :: env) rb
      {| cresult_type := t2; ccomp_demand := u2; ctype_demand_row := b2 |} ->
    cty_alpha_eq t1 (spec_sum_branch_cty true 0 mot) ->
    cty_alpha_eq t2 (spec_sum_branch_cty false 0 mot) ->
    allows (nth_grade u1 0) s ->
    allows (nth_grade u2 0) s ->
    BranchVec (tl u1) (tl u2) u_br ->
    (match scrut with
     | CInl _ v =>
         match term_as_cidx v, A with
         | Some _, CNat => True
         | _, _ => cty_uses_var 0 mot = false
         end
     | CInr _ v =>
         match term_as_cidx v, B with
         | Some _, CNat => True
         | _, _ => cty_uses_var 0 mot = false
         end
     | CVar _ => True
     | _ => cty_uses_var 0 mot = false
     end) ->
    res_ty = spec_sum_subj_cty scrut mot ->
    CoreDerives env (CMatchSum x y s kappa mot scrut lb rb)
      {| cresult_type := res_ty;
         ccomp_demand := vec_add (vec_scale s w) u_br;
         ctype_demand_row := vec_add (tl v_mot) (vec_scale kappa w) |}
| CoreIf : forall env cond th el u_c v_c t1 u1 v1 t2 u2 v2 u_br v_br,
    CoreDerives env cond {| cresult_type := CBool; ccomp_demand := u_c; ctype_demand_row := v_c |} ->
    CoreDerives env th {| cresult_type := t1; ccomp_demand := u1; ctype_demand_row := v1 |} ->
    CoreDerives env el {| cresult_type := t2; ccomp_demand := u2; ctype_demand_row := v2 |} ->
    cty_alpha_eq t1 t2 ->
    BranchVec u1 u2 u_br ->
    BranchVec v1 v2 v_br ->
    CoreDerives env (CIf cond th el)
      {| cresult_type := t1;
         ccomp_demand := vec_add u_c u_br;
         ctype_demand_row := v_br |}
| CoreRecordMk : forall env id fields u v,
    CRecordElemDerives env fields u v ->
    CoreDerives env (CRecordMk id fields)
      {| cresult_type := CRecord id (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields);
         ccomp_demand := u;
         ctype_demand_row := v |}
| CoreMatchRecord : forall env id s mot scrut bs body fields w vs v_mot body_env u_b v_b t_b,
    s <> zero ->
    CoreDerives env scrut {| cresult_type := CRecord id fields; ccomp_demand := w; ctype_demand_row := vs |} ->
    CTypeDemand env mot v_mot ->
    length bs = length fields ->
    CRecordExtendEnv env bs fields body_env ->
    CoreDerives body_env body {| cresult_type := t_b; ccomp_demand := u_b; ctype_demand_row := v_b |} ->
    cty_alpha_eq t_b (lift_cty 0 (length fields) mot) ->
    CRecordFieldAllows s fields (firstn (length fields) u_b) ->
    CoreDerives env (CMatchRecord id s mot scrut bs body)
      {| cresult_type := mot;
         ccomp_demand := vec_add (vec_scale s w) (skipn (length fields) u_b);
         ctype_demand_row := v_mot |}
| CoreSubgrade : forall env target body actual u v vt,
    CoreDerives env body {| cresult_type := actual; ccomp_demand := u; ctype_demand_row := v |} ->
    Subty env actual target ->
    CTypeDemand env target vt ->
    CoreDerives env (CSubgrade target body)
      {| cresult_type := target;
         ccomp_demand := u;
         ctype_demand_row := vt |}
| CoreFix : forall env xn xr s_rec mot scrut base step u_s v_s v_mot t_b u_b v_b t_st u_st v_st res_ty,
    CoreDerives env scrut {| cresult_type := CNat; ccomp_demand := u_s; ctype_demand_row := v_s |} ->
    CTypeDemand ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env) mot v_mot ->
    CoreDerives env base {| cresult_type := t_b; ccomp_demand := u_b; ctype_demand_row := v_b |} ->
    cty_alpha_eq t_b (subst_cidx_in_cty 0 (CIdxLit 0) mot) ->
    CoreDerives
      ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
       {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env)
      step {| cresult_type := t_st; ccomp_demand := u_st; ctype_demand_row := v_st |} ->
    cty_alpha_eq t_st (spec_fix_step_cty mot) ->
    allows (nth_grade u_st 0) s_rec ->
    allows (nth_grade u_st 1) s_rec ->
    fix_recurrence_ok s_rec (tl (tl u_st)) ->
    (match term_as_cidx scrut with Some _ => True | None => cty_uses_var 0 mot = false end) ->
    res_ty = spec_fix_subj_cty scrut mot ->
    CoreDerives env (CFix xn xr s_rec mot scrut base step)
      {| cresult_type := res_ty;
         ccomp_demand := vec_add u_s (vec_add u_b (vec_scale s_rec (tl (tl u_st))));
         ctype_demand_row := vec_add (tl v_mot) (vec_scale (nth_grade v_mot 0) u_s) |}

with CRecordElemDerives {D : JoinDomain}
  : cenv D -> list (nat * grade D * cty D * cterm D) -> list (grade D) -> list (grade D) -> Prop :=
| CRecordElemNil : forall env,
    CRecordElemDerives env [] (vec_zero (length env)) (vec_zero (length env))
| CRecordElemCons : forall env fn fg ft fv rest t_v u_v v_v dt u_rest v_rest,
    CoreDerives env fv {| cresult_type := t_v; ccomp_demand := u_v; ctype_demand_row := v_v |} ->
    cty_alpha_eq t_v ft ->
    CTypeDemand env ft dt ->
    CRecordElemDerives env rest u_rest v_rest ->
    CRecordElemDerives env ((fn, fg, ft, fv) :: rest)
      (vec_add (vec_scale fg u_v) u_rest) (vec_add dt v_rest)

with CRecordExtendEnv {D : JoinDomain}
  : cenv D -> list nat -> list (nat * grade D * cty D) -> cenv D -> Prop :=
| CRecordExtNil : forall env, CRecordExtendEnv env [] [] env
| CRecordExtCons : forall env b bs fn fg ft rest row ext,
    CTypeDemand env ft row ->
    CRecordExtendEnv
      ({| cbinder := b; cannotation := ft; ctype_uses := row |} :: env)
      bs (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest) ext ->
    CRecordExtendEnv env (b :: bs) ((fn, fg, ft) :: rest) ext

with CRecordFieldAllows {D : JoinDomain}
  : grade D -> list (nat * grade D * cty D) -> list (grade D) -> Prop :=
| CRecordAllowsNil : forall s, CRecordFieldAllows s [] []
| CRecordAllowsCons : forall s fn fg ft rest u u_rest,
    allows u (mul s fg) ->
    CRecordFieldAllows s rest u_rest ->
    CRecordFieldAllows s ((fn, fg, ft) :: rest) (u :: u_rest).

Scheme CoreDerives_ind_mut := Induction for CoreDerives Sort Prop
  with CRecordElemDerives_ind_mut := Induction for CRecordElemDerives Sort Prop.

Fixpoint check_record_allows {D : JoinDomain} (s : grade D)
    (fields : list (nat * grade D * cty D)) (us : list (grade D)) : result unit (grade_error D) :=
  match fields, us with
  | [], [] => Ok tt
  | (_, fg, _) :: rest, u :: us' =>
      if allowsb u (mul s fg) then check_record_allows s rest us'
      else Err (ErrBinderCompMismatch 0 u (mul s fg))
  | _, _ => Err (ErrBranchMismatch 5)
  end.

Lemma check_record_allows_sound : forall (D : JoinDomain) s fields (us : list (grade D)),
  check_record_allows s fields us = Ok tt -> CRecordFieldAllows s fields us.
Proof.
  intros D s fields. induction fields as [| [[fn fg] ft] rest IH]; intros [| u us'] H; cbn in H;
    try discriminate; [constructor |].
  destruct (allowsb u (mul s fg)) eqn:Ha; [| discriminate].
  destruct (allows_reflect D u (mul s fg)); [| discriminate].
  constructor; [assumption | apply IH; exact H].
Qed.

Fixpoint extend_record_env {D : JoinDomain} (env : cenv D) (bs : list nat)
    (fields : list (nat * grade D * cty D)) : result (cenv D) (grade_error D) :=
  match bs, fields with
  | [], [] => Ok env
  | b :: bs', (_, _, ft) :: rest =>
      let* row := ctype_demand env ft in
      extend_record_env
        ({| cbinder := b; cannotation := ft; ctype_uses := row |} :: env)
        bs' (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)
  | _, _ => Err (ErrBranchMismatch 6)
  end.

Lemma extend_record_env_sound : forall (D : JoinDomain) (bs : list nat) fields env ext,
  extend_record_env env bs fields = Ok ext ->
  length bs = length fields /\ CRecordExtendEnv (D := D) env bs fields ext.
Proof.
  intros D bs. induction bs as [| b bs IH]; intros [| [[fn fg] ft] rest] env ext H; cbn in H;
    try discriminate.
  - inversion H; split; [reflexivity | constructor].
  - destruct (ctype_demand env ft) as [row |] eqn:Ht; [| discriminate].
    cbn in H.
    apply IH in H as [Hlen Hext].
    rewrite length_map in Hlen.
    split; [cbn; congruence |].
    eapply CRecordExtCons; [apply ctype_demand_sound; exact Ht | exact Hext].
Qed.

Fixpoint core_infer {D : JoinDomain} (env : cenv D) (t : cterm D)
  : result (cjudgment D) (grade_error D) :=
  match t with
  | CVar x =>
      match clookup env x with
      | None => Err (ErrUnbound x)
      | Some e =>
          let* row := ctype_demand (skipn (S x) env) (cannotation e) in
          if vec_eqb (ctype_uses e) row then
            Ok {| cresult_type := ren_cty (plus (S x)) (cannotation e);
                  ccomp_demand := vec_single (length env) x one;
                  ctype_demand_row := vec_zero (S x) ++ row |}
          else Err (ErrTypeMismatch (cannotation e) (cannotation e))
      end
  | CNatVal i =>
      let* d := cidx_demand env i in
      Ok {| cresult_type := CNat;
            ccomp_demand := d;
            ctype_demand_row := vec_zero (length env) |}
  | CBoolVal _ =>
      Ok {| cresult_type := CBool;
            ccomp_demand := vec_zero (length env);
            ctype_demand_row := vec_zero (length env) |}
  | CTypeVal T =>
      let* v := ctype_demand env T in
      let* lvl := cuniverse_level env T in
      Ok {| cresult_type := CUniv lvl;
            ccomp_demand := vec_zero (length env);
            ctype_demand_row := v |}
  | CLam x s r dom body =>
      let* a := ctype_demand env dom in
      let* res := core_infer ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) body in
      if allowsb (nth_grade (ccomp_demand res) 0) s then
        if allowsb (nth_grade (ctype_demand_row res) 0) r then
          Ok {| cresult_type := CPi x s r dom (cresult_type res);
                ccomp_demand := tl (ccomp_demand res);
                ctype_demand_row := vec_add a (tl (ctype_demand_row res)) |}
        else Err (ErrBinderTypeMismatch x (nth_grade (ctype_demand_row res) 0) r)
      else Err (ErrBinderCompMismatch x (nth_grade (ccomp_demand res) 0) s)
  | CApp fn arg =>
      let* j_fn := core_infer env fn in
      let* j_arg := core_infer env arg in
      match cresult_type j_fn with
      | CPi x s r dom cod =>
          if cty_alpha_eqb (cresult_type j_arg) dom then
            let* a_dom := ctype_demand env dom in
            let* b := ctype_demand ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env) cod in
            if allowsb (nth_grade b 0) r then
              let* _ :=
                match dom with
                | CUniv lvl =>
                    match arg with
                    | CTypeVal arg_ty =>
                        let* actual := cuniverse_level env arg_ty in
                        if Nat.eqb actual lvl then Ok tt else Err (ErrUniverseLevel actual lvl)
                    | CVar y =>
                        let* actual := cuniverse_level env (CTVar y) in
                        if Nat.eqb actual lvl then Ok tt else Err (ErrUniverseLevel actual lvl)
                    | _ => Ok tt
                    end
                | _ => Ok tt
                end in
              match app_result_ty dom cod arg with
              | Some res_ty =>
                  let z_type := app_type_arg_demand dom arg (ccomp_demand j_arg) (ctype_demand_row j_arg) in
                  Ok {| cresult_type := res_ty;
                        ccomp_demand := vec_add (ccomp_demand j_fn) (vec_scale s (ccomp_demand j_arg));
                        ctype_demand_row := vec_add (tl b) (vec_scale r z_type) |}
              | None => Err (ErrMotiveMismatch cod cod)
              end
            else Err (ErrBinderTypeMismatch x (nth_grade b 0) r)
          else Err (ErrTypeMismatch (cresult_type j_arg) dom)
      | actual => Err (ErrNotCallable actual)
      end
  | CLet x s r ann rhs body =>
      let* a_ann := ctype_demand env ann in
      let* j_rhs := core_infer env rhs in
      if cty_alpha_eqb (cresult_type j_rhs) ann then
        let* j_bod := core_infer ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env) body in
        if allowsb (nth_grade (ccomp_demand j_bod) 0) s then
          if allowsb (nth_grade (ctype_demand_row j_bod) 0) r then
            if negb (cty_uses_var 0 (cresult_type j_bod)) then
              let z_type := app_type_arg_demand ann rhs (ccomp_demand j_rhs) (ctype_demand_row j_rhs) in
              Ok {| cresult_type := unshift_cty 0 (cresult_type j_bod);
                    ccomp_demand := vec_add (tl (ccomp_demand j_bod)) (vec_scale s (ccomp_demand j_rhs));
                    ctype_demand_row := vec_add (tl (ctype_demand_row j_bod)) (vec_scale r z_type) |}
            else Err (ErrMotiveMismatch (cresult_type j_bod) (cresult_type j_bod))
          else Err (ErrBinderTypeMismatch x (nth_grade (ctype_demand_row j_bod) 0) r)
        else Err (ErrBinderCompMismatch x (nth_grade (ccomp_demand j_bod) 0) s)
      else Err (ErrTypeMismatch (cresult_type j_rhs) ann)
  | CPair x r fst_ty snd_ty fst_val snd_val =>
      let* a := ctype_demand env fst_ty in
      let* b := ctype_demand ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env) snd_ty in
      if allowsb (nth_grade b 0) r then
        let* j_l := core_infer env fst_val in
        if cty_alpha_eqb (cresult_type j_l) fst_ty then
          let* j_r := core_infer env snd_val in
          match app_result_ty fst_ty snd_ty fst_val with
          | Some exp_snd =>
              if cty_alpha_eqb (cresult_type j_r) exp_snd then
                Ok {| cresult_type := CSigma x r fst_ty snd_ty;
                      ccomp_demand := vec_add (ccomp_demand j_l) (ccomp_demand j_r);
                      ctype_demand_row := vec_add a (tl b) |}
              else Err (ErrTypeMismatch (cresult_type j_r) exp_snd)
          | None => Err (ErrMotiveMismatch snd_ty snd_ty)
          end
        else Err (ErrTypeMismatch (cresult_type j_l) fst_ty)
      else Err (ErrBinderTypeMismatch x (nth_grade b 0) r)
  | CLetPair x y s kappa mot pr body =>
      let* j_p := core_infer env pr in
      match cresult_type j_p with
      | CSigma z r A B =>
          let* a := ctype_demand env A in
          let* b := ctype_demand ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) B in
          let* v_mot := ctype_demand ({| cbinder := 0; cannotation := CSigma z r A B; ctype_uses := vec_add a (tl b) |} :: env) mot in
          if allowsb (nth_grade v_mot 0) kappa then
            let env_bod :=
              {| cbinder := y; cannotation := B; ctype_uses := b |} ::
              {| cbinder := x; cannotation := A; ctype_uses := a |} :: env in
            let* j_b := core_infer env_bod body in
            let exp_mot := spec_pair_body_cty 0 mot in
            if cty_alpha_eqb (cresult_type j_b) exp_mot then
              if allowsb (nth_grade (ccomp_demand j_b) 1) s then
                if allowsb (nth_grade (ccomp_demand j_b) 0) s then
                  let dep_ok :=
                    match pr with
                    | CPair _ _ _ _ fv sv =>
                        match term_as_cidx fv, term_as_cidx sv with
                        | Some _, Some _ => true
                        | _, _ => negb (cty_uses_var 0 mot)
                        end
                    | CVar _ => true
                    | _ => negb (cty_uses_var 0 mot)
                    end in
                  if dep_ok then
                    Ok {| cresult_type := spec_pair_subj_cty pr mot;
                          ccomp_demand := vec_add (tl (tl (ccomp_demand j_b))) (vec_scale s (ccomp_demand j_p));
                          ctype_demand_row := vec_add (tl v_mot) (vec_scale kappa (ccomp_demand j_p)) |}
                  else Err (ErrMotiveMismatch mot mot)
                else Err (ErrBinderCompMismatch y (nth_grade (ccomp_demand j_b) 0) s)
              else Err (ErrBinderCompMismatch x (nth_grade (ccomp_demand j_b) 1) s)
            else Err (ErrMotiveMismatch exp_mot (cresult_type j_b))
          else Err (ErrBinderTypeMismatch 0 (nth_grade v_mot 0) kappa)
      | actual => Err (ErrNotPair actual)
      end
  | CPromote q val =>
      let* j := core_infer env val in
      Ok {| cresult_type := CBox q (cresult_type j);
            ccomp_demand := vec_scale q (ccomp_demand j);
            ctype_demand_row := ctype_demand_row j |}
  | CLetBox x kappa mot box_term body =>
      let* j_bx := core_infer env box_term in
      match cresult_type j_bx with
      | CBox q A =>
          let* a := ctype_demand env A in
          let* v_mot := ctype_demand ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env) mot in
          if allowsb (nth_grade v_mot 0) kappa then
            let* j_b := core_infer ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) body in
            let exp_mot := spec_box_body_cty q 0 mot in
            if cty_alpha_eqb (cresult_type j_b) exp_mot then
              if allowsb (nth_grade (ccomp_demand j_b) 0) q then
                if allowsb (nth_grade (ctype_demand_row j_b) 0) (mul q kappa) then
                  let dep_ok :=
                    match box_term with
                    | CPromote _ (CNatVal _) | CPromote _ (CTypeVal _) | CPromote _ (CVar _) | CVar _ => true
                    | _ => negb (cty_uses_var 0 mot)
                    end in
                  if dep_ok then
                    let z_ty :=
                      match box_term with
                      | CPromote q' (CTypeVal _) => vec_scale q' (ctype_demand_row j_bx)
                      | _ => ccomp_demand j_bx
                      end in
                    Ok {| cresult_type := spec_box_subj_cty box_term mot;
                          ccomp_demand := vec_add (tl (ccomp_demand j_b)) (ccomp_demand j_bx);
                          ctype_demand_row := vec_add (tl v_mot) (vec_scale kappa z_ty) |}
                  else Err (ErrMotiveMismatch mot mot)
                else Err (ErrBinderTypeMismatch x (nth_grade (ctype_demand_row j_b) 0) (mul q kappa))
              else Err (ErrBinderCompMismatch x (nth_grade (ccomp_demand j_b) 0) q)
            else Err (ErrMotiveMismatch exp_mot (cresult_type j_b))
          else Err (ErrBinderTypeMismatch 0 (nth_grade v_mot 0) kappa)
      | actual => Err (ErrNotBox actual)
      end
  | CInl rhs_ty val =>
      let* j := core_infer env val in
      let* b := ctype_demand env rhs_ty in
      Ok {| cresult_type := CSum (cresult_type j) rhs_ty;
            ccomp_demand := ccomp_demand j;
            ctype_demand_row := vec_add (ctype_demand_row j) b |}
  | CInr lhs_ty val =>
      let* a := ctype_demand env lhs_ty in
      let* j := core_infer env val in
      Ok {| cresult_type := CSum lhs_ty (cresult_type j);
            ccomp_demand := ccomp_demand j;
            ctype_demand_row := vec_add a (ctype_demand_row j) |}
  | CMatchSum x y s kappa mot scrut lb rb =>
      if grade_eqb s zero then Err (ErrBranchMismatch 4)
      else
        let* j_s := core_infer env scrut in
        match cresult_type j_s with
        | CSum A B =>
            let* a := ctype_demand env A in
            let* b := ctype_demand env B in
            let* v_mot := ctype_demand ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b |} :: env) mot in
            if allowsb (nth_grade v_mot 0) kappa then
              let* j_l := core_infer ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) lb in
              let* j_r := core_infer ({| cbinder := y; cannotation := B; ctype_uses := b |} :: env) rb in
              if cty_alpha_eqb (cresult_type j_l) (spec_sum_branch_cty true 0 mot) then
                if cty_alpha_eqb (cresult_type j_r) (spec_sum_branch_cty false 0 mot) then
                  if allowsb (nth_grade (ccomp_demand j_l) 0) s then
                    if allowsb (nth_grade (ccomp_demand j_r) 0) s then
                      let* u_br := branch_vec 2 (tl (ccomp_demand j_l)) (tl (ccomp_demand j_r)) in
                      let dep_ok :=
                        match scrut with
                        | CInl _ v =>
                            match term_as_cidx v, A with
                            | Some _, CNat => true
                            | _, _ => negb (cty_uses_var 0 mot)
                            end
                        | CInr _ v =>
                            match term_as_cidx v, B with
                            | Some _, CNat => true
                            | _, _ => negb (cty_uses_var 0 mot)
                            end
                        | CVar _ => true
                        | _ => negb (cty_uses_var 0 mot)
                        end in
                      if dep_ok then
                        Ok {| cresult_type := spec_sum_subj_cty scrut mot;
                              ccomp_demand := vec_add (vec_scale s (ccomp_demand j_s)) u_br;
                              ctype_demand_row := vec_add (tl v_mot) (vec_scale kappa (ccomp_demand j_s)) |}
                      else Err (ErrMotiveMismatch mot mot)
                    else Err (ErrBinderCompMismatch y (nth_grade (ccomp_demand j_r) 0) s)
                  else Err (ErrBinderCompMismatch x (nth_grade (ccomp_demand j_l) 0) s)
                else Err (ErrMotiveMismatch (spec_sum_branch_cty false 0 mot) (cresult_type j_r))
              else Err (ErrMotiveMismatch (spec_sum_branch_cty true 0 mot) (cresult_type j_l))
            else Err (ErrBinderTypeMismatch 0 (nth_grade v_mot 0) kappa)
        | actual => Err (ErrNotSum actual)
        end
  | CIf cond th el =>
      let* j_c := core_infer env cond in
      match cresult_type j_c with
      | CBool =>
          let* j_t := core_infer env th in
          let* j_e := core_infer env el in
          if cty_alpha_eqb (cresult_type j_t) (cresult_type j_e) then
            let* u_br := branch_vec 0 (ccomp_demand j_t) (ccomp_demand j_e) in
            let* v_br := branch_vec 1 (ctype_demand_row j_t) (ctype_demand_row j_e) in
            Ok {| cresult_type := cresult_type j_t;
                  ccomp_demand := vec_add (ccomp_demand j_c) u_br;
                  ctype_demand_row := v_br |}
          else Err (ErrTypeMismatch (cresult_type j_t) (cresult_type j_e))
      | actual => Err (ErrTypeMismatch actual CBool)
      end
  | CRecordMk id fields =>
      let* uv :=
        (fix go_elems (fs : list (nat * grade D * cty D * cterm D))
          : result (list (grade D) * list (grade D)) (grade_error D) :=
           match fs with
           | [] => Ok (vec_zero (length env), vec_zero (length env))
           | (_, fg, ft, fv) :: rest =>
               let* jv := core_infer env fv in
               if cty_alpha_eqb (cresult_type jv) ft then
                 let* dt := ctype_demand env ft in
                 let* uv_r := go_elems rest in
                 let '(ur, vr) := uv_r in
                 Ok (vec_add (vec_scale fg (ccomp_demand jv)) ur, vec_add dt vr)
               else Err (ErrTypeMismatch (cresult_type jv) ft)
           end) fields in
      let '(u, v) := uv in
      Ok {| cresult_type := CRecord id (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields);
            ccomp_demand := u;
            ctype_demand_row := v |}
  | CMatchRecord id s mot scrut bs body =>
      if grade_eqb s zero then Err (ErrBranchMismatch 4)
      else
        let* j_s := core_infer env scrut in
        match cresult_type j_s with
        | CRecord id' fields =>
            if Nat.eqb id id' then
              let* v_mot := ctype_demand env mot in
              let* body_env := extend_record_env env bs fields in
              let* j_b := core_infer body_env body in
              if cty_alpha_eqb (cresult_type j_b) (lift_cty 0 (length fields) mot) then
                let* _ := check_record_allows s fields (firstn (length fields) (ccomp_demand j_b)) in
                Ok {| cresult_type := mot;
                      ccomp_demand := vec_add (vec_scale s (ccomp_demand j_s))
                                        (skipn (length fields) (ccomp_demand j_b));
                      ctype_demand_row := v_mot |}
              else Err (ErrMotiveMismatch (lift_cty 0 (length fields) mot) (cresult_type j_b))
            else Err (ErrTypeMismatch (CRecord id' fields) (CRecord id fields))
        | actual => Err (ErrTypeMismatch actual (CRecord id []))
        end
  | CSubgrade target body =>
      let* j := core_infer env body in
      if subtyb env (cresult_type j) target then
        let* vt := ctype_demand env target in
        Ok {| cresult_type := target;
              ccomp_demand := ccomp_demand j;
              ctype_demand_row := vt |}
      else Err (ErrSubgradeFailed (cresult_type j) target)
  | CFix xn xr s_rec mot scrut base step =>
      let* j_s := core_infer env scrut in
      match cresult_type j_s with
      | CNat =>
          let* v_mot := ctype_demand ({| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env) mot in
          let* j_b := core_infer env base in
          if cty_alpha_eqb (cresult_type j_b) (subst_cidx_in_cty 0 (CIdxLit 0) mot) then
            let env_st :=
              {| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
              {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env in
            let* j_st := core_infer env_st step in
            if cty_alpha_eqb (cresult_type j_st) (spec_fix_step_cty mot) then
              if allowsb (nth_grade (ccomp_demand j_st) 0) s_rec then
                if allowsb (nth_grade (ccomp_demand j_st) 1) s_rec then
                  if fix_recurrence_okb s_rec (tl (tl (ccomp_demand j_st))) then
                    let dep_ok :=
                      match term_as_cidx scrut with
                      | Some _ => true
                      | None => negb (cty_uses_var 0 mot)
                      end in
                    if dep_ok then
                      Ok {| cresult_type := spec_fix_subj_cty scrut mot;
                            ccomp_demand := vec_add (ccomp_demand j_s)
                              (vec_add (ccomp_demand j_b) (vec_scale s_rec (tl (tl (ccomp_demand j_st)))));
                            ctype_demand_row := vec_add (tl v_mot) (vec_scale (nth_grade v_mot 0) (ccomp_demand j_s)) |}
                    else Err (ErrMotiveMismatch mot mot)
                  else Err (ErrSubgradeFailed mot mot)
                else Err (ErrBinderCompMismatch xn (nth_grade (ccomp_demand j_st) 1) s_rec)
              else Err (ErrBinderCompMismatch xr (nth_grade (ccomp_demand j_st) 0) s_rec)
            else Err (ErrMotiveMismatch (spec_fix_step_cty mot) (cresult_type j_st))
          else Err (ErrMotiveMismatch (subst_cidx_in_cty 0 (CIdxLit 0) mot) (cresult_type j_b))
      | actual => Err (ErrTypeMismatch actual CNat)
      end
  end.

Theorem core_infer_sound : forall (D : JoinDomain) (t : cterm D) env res,
  core_infer env t = Ok res -> CoreDerives env t res.
Proof.
  intros D t. induction t using cterm_ind_nested; intros env res Hchk; cbn in Hchk.
  - destruct (clookup env x) as [e |] eqn:Hl; [| discriminate].
    cbn in Hchk.
    match type of Hchk with
    | bind_res (ctype_demand ?env' (cannotation e)) _ = Ok res =>
        destruct (ctype_demand env' (cannotation e)) as [row |] eqn:Ht
    end; [| discriminate].
    cbn in Hchk. destruct (vec_eqb (ctype_uses e) row) eqn:Heq; inversion Hchk; subst.
    apply vec_eqb_sound in Heq.
    rewrite <- Heq.
    eapply CoreVar; [exact Hl | apply ctype_demand_sound; exact Ht | rewrite Heq; apply vec_allows_refl].
  - destruct (cidx_demand env i) as [d |] eqn:Hd; inversion Hchk; subst.
    constructor; apply cidx_demand_sound; exact Hd.
  - inversion Hchk; constructor.
  - destruct (ctype_demand env T) as [v |] eqn:Hv; [| discriminate].
    cbn in Hchk. destruct (cuniverse_level env T) as [lvl |] eqn:Hlvl; inversion Hchk; subst.
    constructor; [apply ctype_demand_sound; exact Hv | apply cuniverse_level_sound; exact Hlvl].
  - destruct (ctype_demand env dom) as [a |] eqn:Ha; [| discriminate].
    cbn in Hchk.
    destruct (core_infer ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) t)
      as [[cod u v] |] eqn:Hb; [| discriminate].
    cbn in Hchk.
    destruct (allowsb (nth_grade u 0) s) eqn:Hs; [| discriminate].
    destruct (allowsb (nth_grade v 0) r) eqn:Hr; inversion Hchk; subst.
    destruct (allows_reflect D (nth_grade u 0) s); [| discriminate].
    destruct (allows_reflect D (nth_grade v 0) r); [| discriminate].
    eapply CoreLam; [apply ctype_demand_sound; exact Ha | apply IHt; exact Hb | assumption | assumption].
  - destruct (core_infer env t1) as [[rt1 w v_fn] |] eqn:Hfn; [| discriminate].
    cbn in Hchk. destruct (core_infer env t2) as [[rt2 u_arg v_arg] |] eqn:Harg; [| discriminate].
    cbn in Hchk. destruct rt1 as [| | | | | | | x s r dom cod | | | | |]; try discriminate.
    destruct (cty_alpha_eqb rt2 dom) eqn:Hdom_eq; [| discriminate].
    destruct (ctype_demand env dom) as [a_dom |] eqn:Ha_dom; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := x; cannotation := dom; ctype_uses := a_dom |} :: env) cod)
      as [b |] eqn:Hb; [| discriminate].
    cbn in Hchk. destruct (allowsb (nth_grade b 0) r) eqn:Hr; [| discriminate].
    destruct (allows_reflect D (nth_grade b 0) r); [| discriminate].
    match type of Hchk with
    | bind_res ?m _ = Ok res => destruct m as [[] |] eqn:Hm; [| discriminate]
    end.
    cbn in Hchk.
    destruct (app_result_ty dom cod t2) as [res_ty |] eqn:Hres; inversion Hchk; subst.
    eapply CoreApp with (kind := rt2);
      [apply IHt1; exact Hfn | apply IHt2; exact Harg | apply cty_alpha_eqb_sound; exact Hdom_eq
      | apply ctype_demand_sound; exact Ha_dom | apply ctype_demand_sound; exact Hb
      | assumption | | exact Hres | reflexivity].
    intros lvl arg_ty Hdom_u Harg_c. subst dom.
    destruct Harg_c as [-> | [y [-> ->]]]; cbn in Hm.
    + destruct (cuniverse_level env arg_ty) as [actual |] eqn:Ha; [| discriminate].
      cbn in Hm. destruct (Nat.eqb actual lvl) eqn:Hl; [| discriminate].
      apply Nat.eqb_eq in Hl. subst. apply cuniverse_level_sound; exact Ha.
    + change (bind_res (cuniverse_level env (CTVar y))
                (fun actual => if actual =? lvl then Ok tt else Err (ErrUniverseLevel actual lvl)) = Ok tt) in Hm.
      destruct (cuniverse_level env (CTVar y)) as [actual |] eqn:Ha; [| discriminate].
      cbn in Hm. destruct (Nat.eqb actual lvl) eqn:Hl; [| discriminate].
      apply Nat.eqb_eq in Hl. subst. apply cuniverse_level_sound; exact Ha.
  - (* CLet *)
    destruct (ctype_demand env ann) as [a_ann |] eqn:Ha; [| discriminate].
    cbn in Hchk. destruct (core_infer env t1) as [[rhs_ty u_rhs v_rhs] |] eqn:Hrhs; [| discriminate].
    cbn in Hchk. destruct (cty_alpha_eqb rhs_ty ann) eqn:Hrhs_eq; [| discriminate].
    destruct (core_infer ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env) t2)
      as [[bod_ty u_bod v_bod] |] eqn:Hbod; [| discriminate].
    cbn in Hchk. destruct (allowsb (nth_grade u_bod 0) s) eqn:Hs; [| discriminate].
    destruct (allowsb (nth_grade v_bod 0) r) eqn:Hr; [| discriminate].
    destruct (negb (cty_uses_var 0 bod_ty)) eqn:Hnf; inversion Hchk; subst.
    apply negb_true_iff in Hnf.
    destruct (allows_reflect D (nth_grade u_bod 0) s); [| discriminate].
    destruct (allows_reflect D (nth_grade v_bod 0) r); [| discriminate].
    eapply CoreLet;
      [apply ctype_demand_sound; exact Ha
      | apply IHt1; exact Hrhs
      | apply cty_alpha_eqb_sound; exact Hrhs_eq
      | apply IHt2; exact Hbod
      | assumption | assumption | exact Hnf].
  - (* CPair *)
    destruct (ctype_demand env fst_ty) as [a |] eqn:Ha; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := x; cannotation := fst_ty; ctype_uses := a |} :: env) snd_ty)
      as [b |] eqn:Hb; [| discriminate].
    cbn in Hchk. destruct (allowsb (nth_grade b 0) r) eqn:Hr; [| discriminate].
    destruct (allows_reflect D (nth_grade b 0) r); [| discriminate].
    destruct (core_infer env t1) as [[fst_act u_l v_l] |] eqn:Hl; [| discriminate].
    cbn in Hchk. destruct (cty_alpha_eqb fst_act fst_ty) eqn:Hf_eq; [| discriminate].
    destruct (core_infer env t2) as [[snd_act u_r v_r] |] eqn:Hri; [| discriminate].
    cbn in Hchk. destruct (app_result_ty fst_ty snd_ty t1) as [exp_snd |] eqn:Hexp; [| discriminate].
    destruct (cty_alpha_eqb snd_act exp_snd) eqn:Hs_eq; inversion Hchk; subst.
    eapply CorePair;
      [apply ctype_demand_sound; exact Ha
      | apply ctype_demand_sound; exact Hb
      | assumption
      | apply IHt1; exact Hl
      | apply cty_alpha_eqb_sound; exact Hf_eq
      | apply IHt2; exact Hri
      | exact Hexp
      | apply cty_alpha_eqb_sound; exact Hs_eq].
  - (* CLetPair *)
    destruct (core_infer env t1) as [[prt w v_p] |] eqn:Hp; [| discriminate].
    cbn in Hchk. destruct prt as [| | | | | | | | z r A B | | | |]; try discriminate.
    destruct (ctype_demand env A) as [a |] eqn:HA; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) B)
      as [b |] eqn:HB; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := 0; cannotation := CSigma z r A B; ctype_uses := vec_add a (tl b) |} :: env) motive)
      as [v_mot |] eqn:Hm; [| discriminate].
    cbn in Hchk. destruct (allowsb (nth_grade v_mot 0) kappa) eqn:Hk; [| discriminate].
    destruct (allows_reflect D (nth_grade v_mot 0) kappa); [| discriminate].
    destruct (core_infer ({| cbinder := y; cannotation := B; ctype_uses := b |} ::
                          {| cbinder := x; cannotation := A; ctype_uses := a |} :: env) t2)
      as [[act_mot u_b v_b] |] eqn:Hbdy; [| discriminate].
    cbn in Hchk.
    destruct (cty_alpha_eqb act_mot (spec_pair_body_cty 0 motive)) eqn:Hmot_eq; [| discriminate].
    destruct (allowsb (nth_grade u_b 1) s) eqn:Hs1; [| discriminate].
    destruct (allowsb (nth_grade u_b 0) s) eqn:Hs0; [| discriminate].
    destruct (allows_reflect D (nth_grade u_b 1) s); [| discriminate].
    destruct (allows_reflect D (nth_grade u_b 0) s); [| discriminate].
    match type of Hchk with
    | (if ?d then _ else _) = Ok res => destruct d eqn:Hdep; inversion Hchk; subst
    end.
    eapply CoreLetPair with (act_mot := act_mot);
      [apply IHt1; exact Hp
      | apply ctype_demand_sound; exact HA
      | apply ctype_demand_sound; exact HB
      | apply ctype_demand_sound; exact Hm
      | assumption
      | apply IHt2; exact Hbdy
      | reflexivity
      | apply cty_alpha_eqb_sound; exact Hmot_eq
      | assumption | assumption
      | (destruct t1 as [| | | | | | | ? ? ? ? fv sv | | | | | | | | | | |]; cbn in Hdep; try exact I; try (apply negb_true_iff; exact Hdep);
         destruct (term_as_cidx fv), (term_as_cidx sv); try exact I; apply negb_true_iff; exact Hdep)
      | reflexivity].
  - (* CPromote *)
    destruct (core_infer env t) as [[A u v] |] eqn:Hv; inversion Hchk; subst.
    constructor; apply IHt; exact Hv.
  - (* CLetBox *)
    destruct (core_infer env t1) as [[bx z_b vz] |] eqn:Hbx; [| discriminate].
    cbn in Hchk. destruct bx as [| | | | | | | | | q A | | |]; try discriminate.
    destruct (ctype_demand env A) as [a |] eqn:HA; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := 0; cannotation := CBox q A; ctype_uses := a |} :: env) motive)
      as [v_mot |] eqn:Hm; [| discriminate].
    cbn in Hchk. destruct (allowsb (nth_grade v_mot 0) kappa) eqn:Hk; [| discriminate].
    destruct (allows_reflect D (nth_grade v_mot 0) kappa); [| discriminate].
    destruct (core_infer ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) t2)
      as [[act_mot w bw] |] eqn:Hbdy; [| discriminate].
    cbn in Hchk.
    destruct (cty_alpha_eqb act_mot (spec_box_body_cty q 0 motive)) eqn:Hmot_eq; [| discriminate].
    destruct (allowsb (nth_grade w 0) q) eqn:Hq; [| discriminate].
    destruct (allowsb (nth_grade bw 0) (mul q kappa)) eqn:Hqk; [| discriminate].
    destruct (allows_reflect D (nth_grade w 0) q); [| discriminate].
    destruct (allows_reflect D (nth_grade bw 0) (mul q kappa)); [| discriminate].
    match type of Hchk with
    | (if ?d then _ else _) = Ok res => destruct d eqn:Hdep; inversion Hchk; subst
    end.
    eapply CoreLetBox with (act_mot := act_mot);
      [apply IHt1; exact Hbx
      | apply ctype_demand_sound; exact HA
      | apply ctype_demand_sound; exact Hm
      | assumption
      | apply IHt2; exact Hbdy
      | reflexivity
      | apply cty_alpha_eqb_sound; exact Hmot_eq
      | assumption | assumption
      | (destruct t1 as [| | | | | | | | | q0 bx | | | | | | | | |]; cbn in Hdep; try exact I; try (apply negb_true_iff; exact Hdep);
         destruct bx; try exact I; apply negb_true_iff; exact Hdep)
      | reflexivity | reflexivity].
  - (* CInl *)
    destruct (core_infer env t) as [[A u a] |] eqn:Hv; [| discriminate].
    cbn in Hchk. destruct (ctype_demand env rhs_ty) as [b |] eqn:Hr; inversion Hchk; subst.
    constructor; [apply IHt; exact Hv | apply ctype_demand_sound; exact Hr].
  - (* CInr *)
    destruct (ctype_demand env lhs_ty) as [a |] eqn:Hl; [| discriminate].
    cbn in Hchk. destruct (core_infer env t) as [[B u b] |] eqn:Hv; inversion Hchk; subst.
    constructor; [apply ctype_demand_sound; exact Hl | apply IHt; exact Hv].
  - (* CMatchSum *)
    destruct (grade_eqb s zero) eqn:Hs0; [discriminate |].
    assert (Hs_nz : s <> zero).
    { destruct (grade_eqb_spec D s zero); [discriminate | assumption]. }
    destruct (core_infer env t1) as [[srt w vs] |] eqn:Hs; [| discriminate].
    cbn in Hchk. destruct srt as [| | | | | | | | | | A B | |]; try discriminate.
    destruct (ctype_demand env A) as [a |] eqn:HA; [| discriminate].
    cbn in Hchk. destruct (ctype_demand env B) as [b |] eqn:HB; [| discriminate].
    cbn in Hchk.
    destruct (ctype_demand ({| cbinder := 0; cannotation := CSum A B; ctype_uses := vec_add a b |} :: env) motive)
      as [v_mot |] eqn:Hm; [| discriminate].
    cbn in Hchk. destruct (allowsb (nth_grade v_mot 0) kappa) eqn:Hk; [| discriminate].
    destruct (allows_reflect D (nth_grade v_mot 0) kappa); [| discriminate].
    destruct (core_infer ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) t2)
      as [[t_l u1 b1] |] eqn:Hl; [| discriminate].
    cbn in Hchk.
    destruct (core_infer ({| cbinder := y; cannotation := B; ctype_uses := b |} :: env) t3)
      as [[t_r u2 b2] |] eqn:Hr; [| discriminate].
    cbn in Hchk.
    destruct (cty_alpha_eqb t_l (spec_sum_branch_cty true 0 motive)) eqn:Hl_eq; [| discriminate].
    destruct (cty_alpha_eqb t_r (spec_sum_branch_cty false 0 motive)) eqn:Hr_eq; [| discriminate].
    destruct (allowsb (nth_grade u1 0) s) eqn:Hu1; [| discriminate].
    destruct (allowsb (nth_grade u2 0) s) eqn:Hu2; [| discriminate].
    destruct (allows_reflect D (nth_grade u1 0) s); [| discriminate].
    destruct (allows_reflect D (nth_grade u2 0) s); [| discriminate].
    destruct (branch_vec 2 (tl u1) (tl u2)) as [u_br |] eqn:Hubr; [| discriminate].
    cbn in Hchk.
    match type of Hchk with
    | (if ?d then _ else _) = Ok res => destruct d eqn:Hdep; inversion Hchk; subst
    end.
    eapply CoreMatchSum with (t1 := t_l) (t2 := t_r);
      [exact Hs_nz
      | apply IHt1; exact Hs
      | apply ctype_demand_sound; exact HA
      | apply ctype_demand_sound; exact HB
      | apply ctype_demand_sound; exact Hm
      | assumption
      | apply IHt2; exact Hl
      | apply IHt3; exact Hr
      | apply cty_alpha_eqb_sound; exact Hl_eq
      | apply cty_alpha_eqb_sound; exact Hr_eq
      | assumption | assumption
      | apply branch_vec_sound with (tag := 2); exact Hubr
      | (destruct t1 as [| | | | | | | | | | | ? v | ? v | | | | | |]; cbn in Hdep; try exact I; try (apply negb_true_iff; exact Hdep);
         [destruct (term_as_cidx v), A; try exact I; apply negb_true_iff; exact Hdep
         |destruct (term_as_cidx v), B; try exact I; apply negb_true_iff; exact Hdep])
      | reflexivity].
  - (* CIf *)
    destruct (core_infer env t1) as [[ct u_c v_c] |] eqn:Hc; [| discriminate].
    cbn in Hchk. destruct ct; try discriminate.
    destruct (core_infer env t2) as [[t_1 u1 v1] |] eqn:Ht; [| discriminate].
    cbn in Hchk. destruct (core_infer env t3) as [[t_2 u2 v2] |] eqn:He; [| discriminate].
    cbn in Hchk. destruct (cty_alpha_eqb t_1 t_2) eqn:Heq; [| discriminate].
    destruct (branch_vec 0 u1 u2) as [u_br |] eqn:Hubr; [| discriminate].
    cbn in Hchk. destruct (branch_vec 1 v1 v2) as [v_br |] eqn:Hvbr; inversion Hchk; subst.
    eapply CoreIf;
      [apply IHt1; exact Hc
      | apply IHt2; exact Ht
      | apply IHt3; exact He
      | apply cty_alpha_eqb_sound; exact Heq
      | apply branch_vec_sound with (tag := 0); exact Hubr
      | apply branch_vec_sound with (tag := 1); exact Hvbr].
  - (* CRecordMk *)
    match type of Hchk with
    | bind_res (?g fields) _ = Ok res => destruct (g fields) as [[u v] |] eqn:Hfs; [| discriminate]
    end.
    cbn in Hchk; inversion Hchk; subst. clear Hchk.
    constructor. revert u v Hfs.
    induction fields as [| [[[fn fg] ft] fv] rest IHf]; intros u v Hfs.
    + inversion Hfs; constructor.
    + inversion H; subst. cbn in H2.
      destruct (core_infer env fv) as [[t_v u_v v_v] |] eqn:Hv; [| discriminate].
      cbn in Hfs. destruct (cty_alpha_eqb t_v ft) eqn:Heq; [| discriminate].
      destruct (ctype_demand env ft) as [dt |] eqn:Hdt; [| discriminate].
      cbn in Hfs.
      match type of Hfs with
      | bind_res (?g rest) _ = Ok _ => destruct (g rest) as [[ur vr] |] eqn:Hr
      end; inversion Hfs; subst.
      eapply CRecordElemCons;
        [apply H2; exact Hv
        | apply cty_alpha_eqb_sound; exact Heq
        | apply ctype_demand_sound; exact Hdt
        | apply IHf; [exact H3 | reflexivity]].
  - (* CMatchRecord *)
    destruct (grade_eqb s zero) eqn:Hs0; [discriminate |].
    assert (Hs_nz : s <> zero).
    { destruct (grade_eqb_spec D s zero); [discriminate | assumption]. }
    destruct (core_infer env t1) as [[srt w vs] |] eqn:Hs; [| discriminate].
    cbn in Hchk. destruct srt as [| | | | | | | | | | | id' fields |]; try discriminate.
    destruct (Nat.eqb id id') eqn:Hid; [| discriminate].
    apply Nat.eqb_eq in Hid. subst id'.
    destruct (ctype_demand env motive) as [v_mot |] eqn:Hm; [| discriminate].
    cbn in Hchk. destruct (extend_record_env env binders fields) as [body_env |] eqn:Hext; [| discriminate].
    cbn in Hchk. destruct (core_infer body_env t2) as [[t_b u_b v_b] |] eqn:Hb; [| discriminate].
    cbn in Hchk.
    destruct (cty_alpha_eqb t_b (lift_cty 0 (length fields) motive)) eqn:Hmeq; [| discriminate].
    destruct (check_record_allows s fields (firstn (length fields) u_b)) as [[] |] eqn:Hal; [| discriminate].
    cbn in Hchk. inversion Hchk; subst.
    apply extend_record_env_sound in Hext as [Hlen Hext'].
    eapply CoreMatchRecord;
      [exact Hs_nz
      | apply IHt1; exact Hs
      | apply ctype_demand_sound; exact Hm
      | exact Hlen
      | exact Hext'
      | apply IHt2; exact Hb
      | apply cty_alpha_eqb_sound; exact Hmeq
      | apply check_record_allows_sound; exact Hal].
  - (* CSubgrade *)
    destruct (core_infer env t) as [[actual u v] |] eqn:Hb; [| discriminate].
    cbn in Hchk.
    match type of Hchk with
    | (if ?s then _ else _) = Ok res => destruct s eqn:Hsub
    end; [| discriminate].
    fold (subtyb env actual target) in Hsub.
    destruct (ctype_demand env target) as [vt |] eqn:Hvt; inversion Hchk; subst.
    eapply CoreSubgrade;
      [apply IHt; exact Hb
      | apply subtyb_sound; exact Hsub
      | apply ctype_demand_sound; exact Hvt].
  - (* CFix *)
    destruct (core_infer env t1) as [[st u_s v_s] |] eqn:Hs; [| discriminate].
    cbn in Hchk. destruct st; try discriminate.
    destruct (ctype_demand ({| cbinder := x_n; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env) motive)
      as [v_mot |] eqn:Hm; [| discriminate].
    cbn in Hchk. destruct (core_infer env t2) as [[t_b u_b v_b] |] eqn:Hb; [| discriminate].
    cbn in Hchk.
    destruct (cty_alpha_eqb t_b (subst_cidx_in_cty 0 (CIdxLit 0) motive)) eqn:Hbeq; [| discriminate].
    destruct (core_infer
                ({| cbinder := x_rec; cannotation := motive; ctype_uses := v_mot |} ::
                 {| cbinder := x_n; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env) t3)
      as [[t_st u_st v_st] |] eqn:Hst; [| discriminate].
    cbn in Hchk.
    destruct (cty_alpha_eqb t_st (spec_fix_step_cty motive)) eqn:Hsteq; [| discriminate].
    destruct (allowsb (nth_grade u_st 0) s_rec) eqn:Hrec0; [| discriminate].
    destruct (allowsb (nth_grade u_st 1) s_rec) eqn:Hrec1; [| discriminate].
    destruct (fix_recurrence_okb s_rec (tl (tl u_st))) eqn:Hrecok; [| discriminate].
    destruct (allows_reflect D (nth_grade u_st 0) s_rec); [| discriminate].
    destruct (allows_reflect D (nth_grade u_st 1) s_rec); [| discriminate].
    match type of Hchk with
    | (if ?d then _ else _) = Ok res => destruct d eqn:Hdep; inversion Hchk; subst
    end.
    eapply CoreFix with (t_b := t_b) (t_st := t_st);
      [apply IHt1; exact Hs
      | apply ctype_demand_sound; exact Hm
      | apply IHt2; exact Hb
      | apply cty_alpha_eqb_sound; exact Hbeq
      | apply IHt3; exact Hst
      | apply cty_alpha_eqb_sound; exact Hsteq
      | assumption | assumption
      | apply fix_recurrence_okb_sound; exact Hrecok
      | destruct (term_as_cidx t1); [exact I | apply negb_true_iff; exact Hdep]
      | reflexivity].
Qed.

End GradedCore.
