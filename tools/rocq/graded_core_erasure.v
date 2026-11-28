(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Arith.Compare_dec Bool.Bool Lia.
Require Import graded_domains graded_core graded_core_metatheory.
Import ListNotations GradedDomains GradedCore GradedCoreMetatheory.

Module GradedCoreErasure.

Local Arguments Nat.ltb !_ !_ : simpl nomatch.
Local Arguments Nat.eqb !_ !_ : simpl nomatch.

Lemma nat_eqb_trans : forall a b c : nat,
  Nat.eqb a b = true -> Nat.eqb b c = true -> Nat.eqb a c = true.
Proof. intros a b c H1 H2. apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; apply Nat.eqb_refl. Qed.

Lemma grade_eqb_refl : forall (D : JoinDomain) (g : grade D),
  grade_eqb g g = true.
Proof. intros D g. destruct (grade_eqb_spec D g g); [reflexivity | contradiction]. Qed.

Lemma grade_eqb_sound : forall (D : JoinDomain) (a b : grade D),
  grade_eqb a b = true -> a = b.
Proof. intros D a b H. destruct (grade_eqb_spec D a b); [assumption | discriminate]. Qed.

Lemma grade_eqb_sym : forall (D : JoinDomain) (a b : grade D),
  grade_eqb a b = grade_eqb b a.
Proof. intros D a b. destruct (grade_eqb_spec D a b), (grade_eqb_spec D b a); congruence. Qed.

Lemma cidx_eqb_sym : forall (D : JoinDomain) (a b : cidx D),
  cidx_eqb a b = cidx_eqb b a.
Proof.
  intros D a b. destruct (cidx_eqb a b) eqn:H1; destruct (cidx_eqb b a) eqn:H2; try reflexivity.
  - apply cidx_eqb_sound in H1; subst; rewrite cidx_eqb_refl in H2; discriminate.
  - apply cidx_eqb_sound in H2; subst; rewrite cidx_eqb_refl in H1; discriminate.
Qed.

Lemma cidx_eqb_trans : forall (D : JoinDomain) (a b c : cidx D),
  cidx_eqb a b = true -> cidx_eqb b c = true -> cidx_eqb a c = true.
Proof. intros D a b c H1 H2. apply cidx_eqb_sound in H1; apply cidx_eqb_sound in H2; subst; apply cidx_eqb_refl. Qed.

Lemma cidx_list_eqb_sym : forall (D : JoinDomain) (a b : list (cidx D)),
  cidx_list_eqb a b = cidx_list_eqb b a.
Proof.
  intros D a b. destruct (cidx_list_eqb a b) eqn:H1; destruct (cidx_list_eqb b a) eqn:H2; try reflexivity.
  - apply cidx_list_eqb_sound in H1; subst; rewrite cidx_list_eqb_refl in H2; discriminate.
  - apply cidx_list_eqb_sound in H2; subst; rewrite cidx_list_eqb_refl in H1; discriminate.
Qed.

Lemma cidx_list_eqb_trans : forall (D : JoinDomain) (a b c : list (cidx D)),
  cidx_list_eqb a b = true -> cidx_list_eqb b c = true -> cidx_list_eqb a c = true.
Proof. intros D a b c H1 H2. apply cidx_list_eqb_sound in H1; apply cidx_list_eqb_sound in H2; subst; apply cidx_list_eqb_refl. Qed.

Lemma Nat_iter_ren_shift_lt : forall (f : nat -> nat) (depth x : nat),
  x < depth -> Nat.iter depth ren_shift f x = x.
Proof.
  intros f depth. induction depth as [| depth' IH]; intros x Hlt; [lia |].
  destruct x as [| x']; [reflexivity |].
  change (Nat.iter (S depth') ren_shift f (S x')) with (S (Nat.iter depth' ren_shift f x')).
  f_equal. apply IH. lia.
Qed.

Lemma Nat_iter_ren_shift_ge : forall (f : nat -> nat) (depth x : nat),
  depth <= x -> Nat.iter depth ren_shift f x = depth + f (x - depth).
Proof.
  intros f depth. induction depth as [| depth' IH]; intros x Hge.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - destruct x as [| x']; [lia |].
    change (Nat.iter (S depth') ren_shift f (S x')) with (S (Nat.iter depth' ren_shift f x')).
    rewrite (IH x' ltac:(lia)). cbn. reflexivity.
Qed.

Lemma nth_skipn : forall {A : Type} (n k : nat) (l : list A) (d : A),
  nth (k + n) l d = nth n (skipn k l) d.
Proof.
  intros A n k. induction k as [| k IH]; intros l d; [reflexivity |].
  destruct l; cbn; [destruct n; reflexivity | apply IH].
Qed.

Abbreviation nth_grade_single_eq := nth_grade_single_same.

Lemma erase_hints_alpha_eq : forall (D : JoinDomain) (A B : cty D),
  cty_alpha_eq A B -> erase_hints A = erase_hints B.
Proof. intros D A B H. exact H. Qed.

(* ================================================================= *)
(* Part 1: Core CBV Evaluator, Erased AST, and Type-Uses Invariance  *)
(* ================================================================= *)

Inductive crval {D : JoinDomain} : Type :=
| RNat (n : nat)
| RBool (b : bool)
| RClos (body : cterm D) (env : list (@crval D))
| RPair (v1 v2 : @crval D)
| RBox (v : @crval D)
| RInl (v : @crval D)
| RInr (v : @crval D)
| RRecord (fields : list (nat * @crval D))
| RErased.

Fixpoint eval_cidx {D : JoinDomain} (rho : list (@crval D)) (i : cidx D) : option nat :=
  match i with
  | CIdxVar x =>
      match nth_error rho x with
      | Some (RNat n) => Some n
      | _ => None
      end
  | CIdxLit n => Some n
  | CIdxAdd l r =>
      match eval_cidx rho l, eval_cidx rho r with
      | Some a, Some b => Some (a + b)
      | _, _ => None
      end
  | CIdxProm q inner =>
      if grade_eqb q zero then None else eval_cidx rho inner
  | CIdxUnbox b =>
      match nth_error rho b with
      | Some (RBox (RNat n)) => Some n
      | _ => None
      end
  | CIdxFst p =>
      match nth_error rho p with
      | Some (RPair (RNat n) _) => Some n
      | _ => None
      end
  | CIdxSnd p =>
      match nth_error rho p with
      | Some (RPair _ (RNat n)) => Some n
      | _ => None
      end
  | CIdxCase s l r =>
      match nth_error rho s with
      | Some (RInl (RNat n)) => eval_cidx (RNat n :: rho) l
      | Some (RInr (RNat n)) => eval_cidx (RNat n :: rho) r
      | _ => None
      end
  end.

Fixpoint eval_cterm {D : JoinDomain} (fuel : nat) (rho : list (@crval D)) (t : cterm D)
  : option (@crval D) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      | CVar x => nth_error rho x
      | CNatVal i => option_map RNat (eval_cidx rho i)
      | CBoolVal b => Some (RBool b)
      | CTypeVal _ => Some RErased
      | CLam _ _ _ _ body => Some (RClos body rho)
      | CApp fn arg =>
          match eval_cterm fuel' rho fn, eval_cterm fuel' rho arg with
          | Some (RClos body env_c), Some varg =>
              eval_cterm fuel' (varg :: env_c) body
          | _, _ => None
          end
      | CLet _ _ _ _ rhs body =>
          match eval_cterm fuel' rho rhs with
          | Some vr => eval_cterm fuel' (vr :: rho) body
          | None => None
          end
      | CPair _ _ _ _ fst_val snd_val =>
          match eval_cterm fuel' rho fst_val, eval_cterm fuel' rho snd_val with
          | Some v1, Some v2 => Some (RPair v1 v2)
          | _, _ => None
          end
      | CLetPair _ _ _ _ _ pr body =>
          match eval_cterm fuel' rho pr with
          | Some (RPair v1 v2) => eval_cterm fuel' (v2 :: v1 :: rho) body
          | _ => None
          end
      | CPromote _ val =>
          match eval_cterm fuel' rho val with
          | Some v => Some (RBox v)
          | None => None
          end
      | CLetBox _ _ _ bx body =>
          match eval_cterm fuel' rho bx with
          | Some (RBox v) => eval_cterm fuel' (v :: rho) body
          | _ => None
          end
      | CInl _ val =>
          match eval_cterm fuel' rho val with
          | Some v => Some (RInl v)
          | None => None
          end
      | CInr _ val =>
          match eval_cterm fuel' rho val with
          | Some v => Some (RInr v)
          | None => None
          end
      | CMatchSum _ _ _ _ _ scrut lb rb =>
          match eval_cterm fuel' rho scrut with
          | Some (RInl v) => eval_cterm fuel' (v :: rho) lb
          | Some (RInr v) => eval_cterm fuel' (v :: rho) rb
          | _ => None
          end
      | CIf cond th el =>
          match eval_cterm fuel' rho cond with
          | Some (RBool true) => eval_cterm fuel' rho th
          | Some (RBool false) => eval_cterm fuel' rho el
          | _ => None
          end
      | CRecordMk _ fields =>
          let fix go_fields (fs : list (nat * grade D * cty D * cterm D))
            : option (list (nat * @crval D)) :=
            match fs with
            | [] => Some []
            | (fn, _, _, fv) :: rest =>
                match eval_cterm fuel' rho fv, go_fields rest with
                | Some v, Some rv => Some ((fn, v) :: rv)
                | _, _ => None
                end
            end in
          option_map RRecord (go_fields fields)
      | CMatchRecord _ _ _ scrut _ body =>
          match eval_cterm fuel' rho scrut with
          | Some (RRecord rfields) =>
              eval_cterm fuel' (rev (map snd rfields) ++ rho) body
          | _ => None
          end
      | CSubgrade _ body => eval_cterm fuel' rho body
      | CFix _ _ _ _ scrut base step =>
          match eval_cterm fuel' rho scrut with
          | Some (RNat n) =>
              let fix eval_fix (k : nat) : option (@crval D) :=
                match k with
                | 0 => eval_cterm fuel' rho base
                | S k' =>
                    match eval_fix k' with
                    | Some vr => eval_cterm fuel' (vr :: RNat k' :: rho) step
                    | None => None
                    end
                end in
              eval_fix n
          | _ => None
          end
      end
  end.

Inductive ecterm {D : JoinDomain} : Type :=
| ECVar (x : nat)
| ECNat (i : cidx D)
| ECBool (b : bool)
| ECErased
| ECLam (keep : bool) (body : @ecterm D)
| ECApp (fn arg : @ecterm D)
| ECLet (keep : bool) (rhs body : @ecterm D)
| ECPair (fst_v snd_v : @ecterm D)
| ECLetPair (keep : bool) (pr body : @ecterm D)
| ECBox (keep : bool) (val : @ecterm D)
| ECLetBox (keep : bool) (bx body : @ecterm D)
| ECInl (val : @ecterm D)
| ECInr (val : @ecterm D)
| ECMatchSum (scrut lbranch rbranch : @ecterm D)
| ECIf (cond th el : @ecterm D)
| ECRecord (fields : list (nat * bool * @ecterm D))
| ECMatchRecord (scrut body : @ecterm D)
| ECFix (scrut base step : @ecterm D).

Inductive ecval {D : JoinDomain} : Type :=
| EVNat (n : nat)
| EVBool (b : bool)
| EVClos (keep : bool) (body : @ecterm D) (env : list (@ecval D))
| EVPair (v1 v2 : @ecval D)
| EVBox (v : @ecval D)
| EVInl (v : @ecval D)
| EVInr (v : @ecval D)
| EVRecord (fields : list (nat * @ecval D))
| EVErased.

Fixpoint eval_ecidx {D : JoinDomain} (erho : list (@ecval D)) (i : cidx D) : option nat :=
  match i with
  | CIdxVar x =>
      match nth_error erho x with
      | Some (EVNat n) => Some n
      | _ => None
      end
  | CIdxLit n => Some n
  | CIdxAdd l r =>
      match eval_ecidx erho l, eval_ecidx erho r with
      | Some a, Some b => Some (a + b)
      | _, _ => None
      end
  | CIdxProm q inner =>
      if grade_eqb q zero then None else eval_ecidx erho inner
  | CIdxUnbox b =>
      match nth_error erho b with
      | Some (EVBox (EVNat n)) => Some n
      | _ => None
      end
  | CIdxFst p =>
      match nth_error erho p with
      | Some (EVPair (EVNat n) _) => Some n
      | _ => None
      end
  | CIdxSnd p =>
      match nth_error erho p with
      | Some (EVPair _ (EVNat n)) => Some n
      | _ => None
      end
  | CIdxCase s l r =>
      match nth_error erho s with
      | Some (EVInl (EVNat n)) => eval_ecidx (EVNat n :: erho) l
      | Some (EVInr (EVNat n)) => eval_ecidx (EVNat n :: erho) r
      | _ => None
      end
  end.

Fixpoint eval_ecterm {D : JoinDomain} (fuel : nat) (erho : list (@ecval D)) (t : @ecterm D)
  : option (@ecval D) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      | ECVar x => nth_error erho x
      | ECNat i => option_map EVNat (eval_ecidx erho i)
      | ECBool b => Some (EVBool b)
      | ECErased => Some EVErased
      | ECLam keep body => Some (EVClos keep body erho)
      | ECApp fn arg =>
          match eval_ecterm fuel' erho fn, eval_ecterm fuel' erho arg with
          | Some (EVClos false body eenv), Some _ =>
              eval_ecterm fuel' (EVErased :: eenv) body
          | Some (EVClos true body eenv), Some ev =>
              eval_ecterm fuel' (ev :: eenv) body
          | _, _ => None
          end
      | ECLet false _ body =>
          eval_ecterm fuel' (EVErased :: erho) body
      | ECLet true rhs body =>
          match eval_ecterm fuel' erho rhs with
          | Some ev => eval_ecterm fuel' (ev :: erho) body
          | None => None
          end
      | ECPair fst_v snd_v =>
          match eval_ecterm fuel' erho fst_v, eval_ecterm fuel' erho snd_v with
          | Some ev1, Some ev2 => Some (EVPair ev1 ev2)
          | _, _ => None
          end
      | ECLetPair false _ body =>
          eval_ecterm fuel' (EVErased :: EVErased :: erho) body
      | ECLetPair true pr body =>
          match eval_ecterm fuel' erho pr with
          | Some (EVPair ev1 ev2) => eval_ecterm fuel' (ev2 :: ev1 :: erho) body
          | _ => None
          end
      | ECBox false _ => Some (EVBox EVErased)
      | ECBox true val =>
          match eval_ecterm fuel' erho val with
          | Some ev => Some (EVBox ev)
          | None => None
          end
      | ECLetBox keep bx body =>
          match eval_ecterm fuel' erho bx with
          | Some (EVBox ev) =>
              eval_ecterm fuel' ((if keep then ev else EVErased) :: erho) body
          | _ => None
          end
      | ECInl val =>
          match eval_ecterm fuel' erho val with
          | Some ev => Some (EVInl ev)
          | None => None
          end
      | ECInr val =>
          match eval_ecterm fuel' erho val with
          | Some ev => Some (EVInr ev)
          | None => None
          end
      | ECMatchSum scrut lb rb =>
          match eval_ecterm fuel' erho scrut with
          | Some (EVInl ev) => eval_ecterm fuel' (ev :: erho) lb
          | Some (EVInr ev) => eval_ecterm fuel' (ev :: erho) rb
          | _ => None
          end
      | ECIf cond th el =>
          match eval_ecterm fuel' erho cond with
          | Some (EVBool true) => eval_ecterm fuel' erho th
          | Some (EVBool false) => eval_ecterm fuel' erho el
          | _ => None
          end
      | ECRecord fields =>
          let fix go_fields (fs : list (nat * bool * @ecterm D))
            : option (list (nat * @ecval D)) :=
            match fs with
            | [] => Some []
            | (fn, false, _) :: rest =>
                match go_fields rest with
                | Some rv => Some ((fn, EVErased) :: rv)
                | None => None
                end
            | (fn, true, fv) :: rest =>
                match eval_ecterm fuel' erho fv, go_fields rest with
                | Some ev, Some rv => Some ((fn, ev) :: rv)
                | _, _ => None
                end
            end in
          option_map EVRecord (go_fields fields)
      | ECMatchRecord scrut body =>
          match eval_ecterm fuel' erho scrut with
          | Some (EVRecord rfields) =>
              eval_ecterm fuel' (rev (map snd rfields) ++ erho) body
          | _ => None
          end
      | ECFix scrut base step =>
          match eval_ecterm fuel' erho scrut with
          | Some (EVNat n) =>
              let fix eval_efix (k : nat) : option (@ecval D) :=
                match k with
                | 0 => eval_ecterm fuel' erho base
                | S k' =>
                    match eval_efix k' with
                    | Some evr => eval_ecterm fuel' (evr :: EVNat k' :: erho) step
                    | None => None
                    end
                end in
              eval_efix n
          | _ => None
          end
      end
  end.

Lemma eval_ecterm_fuel_mono : forall (D : JoinDomain) f1 f2 erho (t : @ecterm D) v,
  f1 <= f2 ->
  eval_ecterm f1 erho t = Some v ->
  eval_ecterm f2 erho t = Some v.
Proof.
  intros D f1. induction f1 as [| f1' IH]; intros f2 erho t v Hle Hev; [discriminate |].
  destruct f2 as [| f2']; [lia |].
  assert (Hle' : f1' <= f2') by lia.
  destruct t as [x | i | b | | keep body | t1 t2 | b t1 t2 | t1 t2 | b t1 t2 | b t | b t1 t2 | t | t | t1 t2 t3 | t1 t2 t3 | fields | t1 t2 | t1 t2 t3];
    cbn [eval_ecterm] in *;
    try exact Hev.
  - destruct (eval_ecterm f1' erho t1) as [[| | retain0 body0 eenv0 | | | | | |] |] eqn:H1,
             (eval_ecterm f1' erho t2) as [ev2 |] eqn:H2; try discriminate;
    destruct retain0; try discriminate;
      erewrite (IH f2' erho t1 _ Hle' H1), (IH f2' erho t2 _ Hle' H2);
      (eapply IH; [exact Hle' | exact Hev]).
  - destruct b.
    + destruct (eval_ecterm f1' erho t1) as [ev1 |] eqn:H1; [| discriminate].
      erewrite (IH f2' erho t1 _ Hle' H1). eapply IH; [exact Hle' | exact Hev].
    + eapply IH; [exact Hle' | exact Hev].
  - destruct (eval_ecterm f1' erho t1) as [ev1 |] eqn:H1,
             (eval_ecterm f1' erho t2) as [ev2 |] eqn:H2; try discriminate.
    erewrite (IH f2' erho t1 _ Hle' H1), (IH f2' erho t2 _ Hle' H2). exact Hev.
  - destruct b.
    + destruct (eval_ecterm f1' erho t1) as [[| | | ev1 ev2 | | | | |] |] eqn:H1; try discriminate.
      erewrite (IH f2' erho t1 _ Hle' H1). eapply IH; [exact Hle' | exact Hev].
    + eapply IH; [exact Hle' | exact Hev].
  - destruct b; [| exact Hev].
    destruct (eval_ecterm f1' erho t) as [ev |] eqn:H1; [| discriminate].
    erewrite (IH f2' erho t _ Hle' H1). exact Hev.
  - destruct (eval_ecterm f1' erho t1) as [[| | | | ev0 | | | |] |] eqn:H1; try discriminate.
    erewrite (IH f2' erho t1 _ Hle' H1). eapply IH; [exact Hle' | exact Hev].
  - destruct (eval_ecterm f1' erho t) as [ev |] eqn:H1; [| discriminate].
    erewrite (IH f2' erho t _ Hle' H1). exact Hev.
  - destruct (eval_ecterm f1' erho t) as [ev |] eqn:H1; [| discriminate].
    erewrite (IH f2' erho t _ Hle' H1). exact Hev.
  - destruct (eval_ecterm f1' erho t1) as [[| | | | | ev | ev | |] |] eqn:H1; try discriminate;
      erewrite (IH f2' erho t1 _ Hle' H1); (eapply IH; [exact Hle' | exact Hev]).
  - destruct (eval_ecterm f1' erho t1) as [[| [] | | | | | | |] |] eqn:H1; try discriminate;
      erewrite (IH f2' erho t1 _ Hle' H1); (eapply IH; [exact Hle' | exact Hev]).
  - destruct ((fix go_fields (fs : list (nat * bool * ecterm)) : option (list (nat * ecval)) :=
                 match fs with
                 | [] => Some []
                 | (fn, false, _) :: rest =>
                     match go_fields rest with Some rv => Some ((fn, EVErased) :: rv) | None => None end
                 | (fn, true, fv) :: rest =>
                     match eval_ecterm f1' erho fv, go_fields rest with Some ev, Some rv => Some ((fn, ev) :: rv) | _, _ => None end
                 end) fields) as [rfs |] eqn:Hfs; [| discriminate].
    cbn in Hev. inversion Hev; subst.
    assert (Hmono : forall fs r,
      (fix go_fields (fs0 : list (nat * bool * ecterm)) : option (list (nat * ecval)) :=
         match fs0 with
         | [] => Some []
         | (fn, false, _) :: rest =>
             match go_fields rest with Some rv => Some ((fn, EVErased) :: rv) | None => None end
         | (fn, true, fv) :: rest =>
             match eval_ecterm f1' erho fv, go_fields rest with Some ev, Some rv => Some ((fn, ev) :: rv) | _, _ => None end
         end) fs = Some r ->
      (fix go_fields (fs0 : list (nat * bool * ecterm)) : option (list (nat * ecval)) :=
         match fs0 with
         | [] => Some []
         | (fn, false, _) :: rest =>
             match go_fields rest with Some rv => Some ((fn, EVErased) :: rv) | None => None end
         | (fn, true, fv) :: rest =>
             match eval_ecterm f2' erho fv, go_fields rest with Some ev, Some rv => Some ((fn, ev) :: rv) | _, _ => None end
         end) fs = Some r).
    { clear - IH Hle'. induction fs as [| [[fn kb] fv] rest IHr]; intros r Hg; [exact Hg |].
      destruct kb.
      - destruct (eval_ecterm f1' erho fv) as [ev |] eqn:Hfv,
                 ((fix go_fields (fs0 : list (nat * bool * ecterm)) : option (list (nat * ecval)) :=
                     match fs0 with
                     | [] => Some []
                     | (fn0, false, _) :: rest0 =>
                         match go_fields rest0 with Some rv => Some ((fn0, EVErased) :: rv) | None => None end
                     | (fn0, true, fv0) :: rest0 =>
                         match eval_ecterm f1' erho fv0, go_fields rest0 with Some ev0, Some rv => Some ((fn0, ev0) :: rv) | _, _ => None end
                     end) rest) as [rv |] eqn:Hrst; try discriminate.
        inversion Hg; subst.
        erewrite (IH f2' erho fv _ Hle' Hfv), (IHr rv eq_refl). reflexivity.
      - destruct ((fix go_fields (fs0 : list (nat * bool * ecterm)) : option (list (nat * ecval)) :=
                     match fs0 with
                     | [] => Some []
                     | (fn0, false, _) :: rest0 =>
                         match go_fields rest0 with Some rv => Some ((fn0, EVErased) :: rv) | None => None end
                     | (fn0, true, fv0) :: rest0 =>
                         match eval_ecterm f1' erho fv0, go_fields rest0 with Some ev0, Some rv => Some ((fn0, ev0) :: rv) | _, _ => None end
                     end) rest) as [rv |] eqn:Hrst; try discriminate.
        inversion Hg; subst. rewrite (IHr rv eq_refl). reflexivity. }
    rewrite (Hmono fields rfs Hfs). reflexivity.
  - destruct (eval_ecterm f1' erho t1) as [[| | | | | | | rfs |] |] eqn:H1; try discriminate.
    erewrite (IH f2' erho t1 _ Hle' H1). eapply IH; [exact Hle' | exact Hev].
  - destruct (eval_ecterm f1' erho t1) as [[n | | | | | | | |] |] eqn:H1; try discriminate.
    erewrite (IH f2' erho t1 _ Hle' H1).
    clear H1. revert v Hev. induction n as [| n' IHn]; intros v Hev; [eapply IH; [exact Hle' | exact Hev] |].
    destruct ((fix eval_efix (k : nat) : option ecval :=
                 match k with
                 | 0 => eval_ecterm f1' erho t2
                 | S k' => match eval_efix k' with Some evr => eval_ecterm f1' (evr :: EVNat k' :: erho) t3 | None => None end
                 end) n') as [evr |] eqn:Hp; [| discriminate].
    rewrite (IHn evr eq_refl). eapply IH; [exact Hle' | exact Hev].
Qed.

(* Structural result-type extractor ignoring ctype_uses so erasure is type_uses-invariant *)
Fixpoint cterm_result_type {D : JoinDomain} (env : cenv D) (t : cterm D) : option (cty D) :=
  match t with
  | CVar x => option_map (fun e => ren_cty (plus (S x)) (cannotation e)) (clookup env x)
  | CNatVal _ => Some CNat
  | CBoolVal _ => Some CBool
  | CTypeVal _ => Some (CUniv 0)
  | CLam x s r dom body =>
      option_map (CPi x s r dom)
        (cterm_result_type ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env) body)
  | CApp fn arg =>
      match cterm_result_type env fn with
      | Some (CPi _ _ _ dom cod) => app_result_ty dom cod arg
      | _ => None
      end
  | CLet x _ _ ann _ body =>
      option_map (unshift_cty 0)
        (cterm_result_type ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env) body)
  | CPair x r fst_ty snd_ty _ _ => Some (CSigma x r fst_ty snd_ty)
  | CLetPair _ _ _ _ mot pr _ => Some (spec_pair_subj_cty pr mot)
  | CPromote q val => option_map (CBox q) (cterm_result_type env val)
  | CLetBox _ _ mot bx _ => Some (spec_box_subj_cty bx mot)
  | CInl rhs_ty val => option_map (fun A => CSum A rhs_ty) (cterm_result_type env val)
  | CInr lhs_ty val => option_map (CSum lhs_ty) (cterm_result_type env val)
  | CMatchSum _ _ _ _ mot scrut _ _ => Some (spec_sum_subj_cty scrut mot)
  | CIf _ th _ => cterm_result_type env th
  | CRecordMk id fields =>
      Some (CRecord id (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields))
  | CMatchRecord _ _ mot _ _ _ => Some mot
  | CSubgrade target _ => Some target
  | CFix _ _ _ mot scrut _ _ => Some (spec_fix_subj_cty scrut mot)
  end.

Definition callee_grade {D : JoinDomain} (env : cenv D) (fn : cterm D) : option (grade D) :=
  match cterm_result_type env fn with
  | Some (CPi _ s _ _ _) => Some s
  | _ => None
  end.

Definition box_grade {D : JoinDomain} (env : cenv D) (bx : cterm D) : option (grade D) :=
  match cterm_result_type env bx with
  | Some (CBox q _) => Some q
  | _ => None
  end.

Fixpoint erase_cterm_extend_go {D : JoinDomain} (n : nat) (env : cenv D)
    (fields : list (nat * grade D * cty D)) : cenv D :=
  match n, fields with
  | 0, _ | _, [] => env
  | S n', (fn, _, ft) :: rest =>
      erase_cterm_extend_go n' ({| cbinder := fn; cannotation := ft; ctype_uses := [] |} :: env)
        (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)
  end.

Definition erase_cterm_extend {D : JoinDomain} (env : cenv D)
    (fields : list (nat * grade D * cty D)) : cenv D :=
  erase_cterm_extend_go (length fields) env fields.

Lemma erase_cterm_extend_nil : forall (D : JoinDomain) (env : cenv D),
  erase_cterm_extend env [] = env.
Proof. reflexivity. Qed.

Lemma erase_cterm_extend_cons : forall (D : JoinDomain) (env : cenv D) fn fg ft rest,
  erase_cterm_extend env ((fn, fg, ft) :: rest) =
  erase_cterm_extend ({| cbinder := fn; cannotation := ft; ctype_uses := [] |} :: env)
    (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest).
Proof.
  intros D env fn fg ft rest.
  unfold erase_cterm_extend. cbn [length erase_cterm_extend_go].
  rewrite length_map. reflexivity.
Qed.

Definition record_fields_ty {D : JoinDomain} (env : cenv D) (scrut : cterm D)
  : option (list (nat * grade D * cty D)) :=
  match cterm_result_type env scrut with
  | Some (CRecord _ fields) => Some fields
  | _ => None
  end.

Fixpoint erase_cterm {D : JoinDomain} (env : cenv D) (t : cterm D) : @ecterm D :=
  match t with
  | CVar x => ECVar x
  | CNatVal i => ECNat i
  | CBoolVal b => ECBool b
  | CTypeVal _ => ECErased
  | CLam x s _ dom body =>
      ECLam (negb (grade_eqb s zero))
        (erase_cterm ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env) body)
  | CApp fn arg =>
      match callee_grade env fn with
      | Some s =>
          if grade_eqb s zero
          then ECApp (erase_cterm env fn) ECErased
          else ECApp (erase_cterm env fn) (erase_cterm env arg)
      | None => ECApp (erase_cterm env fn) (erase_cterm env arg)
      end
  | CLet x s _ ann rhs body =>
      let env' := {| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env in
      if grade_eqb s zero
      then ECLet false ECErased (erase_cterm env' body)
      else ECLet true (erase_cterm env rhs) (erase_cterm env' body)
  | CPair _ _ _ _ fst_val snd_val =>
      ECPair (erase_cterm env fst_val) (erase_cterm env snd_val)
  | CLetPair x y s _ _ pr body =>
      match cterm_result_type env pr with
      | Some (CSigma _ _ A B) =>
          let env' :=
            {| cbinder := y; cannotation := B; ctype_uses := [] |} ::
            {| cbinder := x; cannotation := A; ctype_uses := [] |} :: env in
          if grade_eqb s zero
          then ECLetPair false ECErased (erase_cterm env' body)
          else ECLetPair true (erase_cterm env pr) (erase_cterm env' body)
      | _ =>
          let env' :=
            {| cbinder := y; cannotation := CNat; ctype_uses := [] |} ::
            {| cbinder := x; cannotation := CNat; ctype_uses := [] |} :: env in
          if grade_eqb s zero
          then ECLetPair false ECErased (erase_cterm env' body)
          else ECLetPair true (erase_cterm env pr) (erase_cterm env' body)
      end
  | CPromote q val =>
      if grade_eqb q zero
      then ECBox false ECErased
      else ECBox true (erase_cterm env val)
  | CLetBox x _ _ bx body =>
      match cterm_result_type env bx with
      | Some (CBox q A) =>
          let env' := {| cbinder := x; cannotation := A; ctype_uses := [] |} :: env in
          ECLetBox (negb (grade_eqb q zero)) (erase_cterm env bx) (erase_cterm env' body)
      | _ =>
          let env' := {| cbinder := x; cannotation := CNat; ctype_uses := [] |} :: env in
          ECLetBox true (erase_cterm env bx) (erase_cterm env' body)
      end
  | CInl _ val => ECInl (erase_cterm env val)
  | CInr _ val => ECInr (erase_cterm env val)
  | CMatchSum x y _ _ _ scrut lb rb =>
      match cterm_result_type env scrut with
      | Some (CSum A B) =>
          ECMatchSum (erase_cterm env scrut)
            (erase_cterm ({| cbinder := x; cannotation := A; ctype_uses := [] |} :: env) lb)
            (erase_cterm ({| cbinder := y; cannotation := B; ctype_uses := [] |} :: env) rb)
      | _ =>
          ECMatchSum (erase_cterm env scrut)
            (erase_cterm ({| cbinder := x; cannotation := CNat; ctype_uses := [] |} :: env) lb)
            (erase_cterm ({| cbinder := y; cannotation := CNat; ctype_uses := [] |} :: env) rb)
      end
  | CIf cond th el =>
      ECIf (erase_cterm env cond) (erase_cterm env th) (erase_cterm env el)
  | CRecordMk _ fields =>
      ECRecord (map (fun '(fn, fg, _, fv) =>
        if grade_eqb fg zero
        then (fn, false, ECErased)
        else (fn, true, erase_cterm env fv)) fields)
  | CMatchRecord _ _ _ scrut _ body =>
      match record_fields_ty env scrut with
      | Some fields =>
          ECMatchRecord (erase_cterm env scrut) (erase_cterm (erase_cterm_extend env fields) body)
      | None =>
          ECMatchRecord (erase_cterm env scrut) (erase_cterm env body)
      end
  | CSubgrade _ body => erase_cterm env body
  | CFix xn xr _ mot scrut base step =>
      let env1 := {| cbinder := xn; cannotation := CNat; ctype_uses := [] |} :: env in
      let env2 := {| cbinder := xr; cannotation := mot; ctype_uses := [] |} :: env1 in
      ECFix (erase_cterm env scrut) (erase_cterm env base) (erase_cterm env2 step)
  end.

Lemma cterm_result_type_alpha_env : forall (D : JoinDomain) (t : cterm D) env1 env2,
  cenv_alpha_eq env1 env2 ->
  match cterm_result_type env1 t, cterm_result_type env2 t with
  | Some ty1, Some ty2 => cty_alpha_eq ty1 ty2
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros D t. induction t using cterm_ind_nested; intros env1 env2 Ha; cbn [cterm_result_type].
  - unfold clookup.
    pose proof (cenv_alpha_eq_length _ _ _ Ha) as Hlen.
    destruct (lt_eq_lt_dec x (length env1)) as [[Hlt | Heq] | Hgt].
    + destruct (nth_error env1 x) as [e1 |] eqn:E1;
        [| exfalso; apply nth_error_None in E1; lia].
      destruct (nth_error env2 x) as [e2 |] eqn:E2;
        [| exfalso; apply nth_error_None in E2; lia].
      destruct (cenv_alpha_eq_lookup _ _ _ x e1 Ha ltac:(unfold clookup; exact E1)) as [e2' [E2' Hlk]].
      unfold clookup in E2'; rewrite E2 in E2'; inversion E2'; subst e2'.
      cbn. apply ren_cty_alpha_eq. exact Hlk.
    + rewrite !(proj2 (nth_error_None _ _)) by lia. exact I.
    + rewrite !(proj2 (nth_error_None _ _)) by lia. exact I.
  - apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_refl.
  - specialize (IHt ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env1)
                    ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env2)
                    ltac:(constructor; [cbn; apply cty_alpha_eq_refl | exact Ha])).
    destruct (cterm_result_type _ t), (cterm_result_type _ t); cbn; try contradiction; try exact I.
    unfold cty_alpha_eq in IHt |- *; cbn [erase_hints]; rewrite IHt; reflexivity.
  - specialize (IHt1 env1 env2 Ha).
    destruct (cterm_result_type env1 t1) as [t_fn1 |], (cterm_result_type env2 t1) as [t_fn2 |];
      try contradiction; try exact I.
    destruct t_fn1; unfold cty_alpha_eq in IHt1; cbn in IHt1;
      destruct t_fn2; cbn in IHt1; try discriminate; try exact I.
    inversion IHt1 as [[Hs Hr Hd Hc]].
    unfold cty_alpha_eq in *.
    destruct (app_result_ty t_fn1_1 t_fn1_2 t2) as [r1 |] eqn:Hr1.
    + destruct (app_result_ty_alpha D t_fn2_1 t_fn1_1 t_fn2_2 t_fn1_2 t2 r1
                  (cty_alpha_eq_sym _ _ _ Hd) (cty_alpha_eq_sym _ _ _ Hc) Hr1) as [r2 [Hr2 Heqr]].
      rewrite Hr2. apply cty_alpha_eq_sym; exact Heqr.
    + destruct (app_result_ty t_fn2_1 t_fn2_2 t2) as [r2 |] eqn:Hr2; [| exact I].
      destruct (app_result_ty_alpha D t_fn1_1 t_fn2_1 t_fn1_2 t_fn2_2 t2 r2 Hd Hc Hr2) as [r1' [Hr1' _]].
      congruence.
  - specialize (IHt2 ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env1)
                     ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env2)
                     ltac:(constructor; [cbn; apply cty_alpha_eq_refl | exact Ha])).
    destruct (cterm_result_type _ t2), (cterm_result_type _ t2); cbn; try contradiction; try exact I.
    apply cty_alpha_eq_unshift; exact IHt2.
  - apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_refl.
  - specialize (IHt env1 env2 Ha).
    destruct (cterm_result_type env1 t), (cterm_result_type env2 t); cbn; try contradiction; try exact I.
    unfold cty_alpha_eq in IHt |- *; cbn [erase_hints]; rewrite IHt; reflexivity.
  - apply cty_alpha_eq_refl.
  - specialize (IHt env1 env2 Ha).
    destruct (cterm_result_type env1 t), (cterm_result_type env2 t); cbn; try contradiction; try exact I.
    unfold cty_alpha_eq in IHt |- *; cbn [erase_hints]; rewrite IHt; reflexivity.
  - specialize (IHt env1 env2 Ha).
    destruct (cterm_result_type env1 t), (cterm_result_type env2 t); cbn; try contradiction; try exact I.
    unfold cty_alpha_eq in IHt |- *; cbn [erase_hints]; rewrite IHt; reflexivity.
  - apply cty_alpha_eq_refl.
  - exact (IHt2 env1 env2 Ha).
  - apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_refl.
  - apply cty_alpha_eq_refl.
Qed.

Fixpoint cty_shape_eqb {D : JoinDomain} (a b : cty D) : bool :=
  match a, b with
  | CNat, CNat => true
  | CBool, CBool => true
  | CVec e1 l1, CVec e2 l2 => cty_shape_eqb e1 e2 && cidx_eqb l1 l2
  | CUniv _, CUniv _ => true
  | CTVar x1, CTVar x2 => Nat.eqb x1 x2
  | CTProm q1 i1, CTProm q2 i2 => grade_eqb q1 q2 && cty_shape_eqb i1 i2
  | CTUnbox b1, CTUnbox b2 => Nat.eqb b1 b2
  | CPi _ s1 r1 d1 c1, CPi _ s2 r2 d2 c2 =>
      grade_eqb s1 s2 && grade_eqb r1 r2 && cty_shape_eqb d1 d2 && cty_shape_eqb c1 c2
  | CSigma _ r1 f1 s1, CSigma _ r2 f2 s2 =>
      grade_eqb r1 r2 && cty_shape_eqb f1 f2 && cty_shape_eqb s1 s2
  | CBox q1 i1, CBox q2 i2 => grade_eqb q1 q2 && cty_shape_eqb i1 i2
  | CSum l1 r1, CSum l2 r2 => cty_shape_eqb l1 l2 && cty_shape_eqb r1 r2
  | CRecord id1 fs1, CRecord id2 fs2 =>
      Nat.eqb id1 id2 &&
      (fix go_fs (xs ys : list (nat * grade D * cty D)) : bool :=
         match xs, ys with
         | [], [] => true
         | (n1, g1, t1) :: xs', (n2, g2, t2) :: ys' =>
             Nat.eqb n1 n2 && grade_eqb g1 g2 && cty_shape_eqb t1 t2 && go_fs xs' ys'
         | _, _ => false
         end) fs1 fs2
  | CInd id1 is1, CInd id2 is2 => Nat.eqb id1 id2 && cidx_list_eqb is1 is2
  | _, _ => false
  end.

Lemma cty_alpha_eq_shape : forall (D : JoinDomain) (A B : cty D),
  cty_alpha_eq A B -> cty_shape_eqb A B = true.
Proof.
  intros D A. induction A using cty_ind_nested; intros B Hab;
    destruct B; unfold cty_alpha_eq in Hab; cbn in Hab |- *; try discriminate;
    inversion Hab; subst;
    repeat rewrite Nat.eqb_refl;
    repeat rewrite grade_eqb_refl;
    cbn;
    try reflexivity.
  - erewrite IHA; [rewrite cidx_eqb_refl; reflexivity | unfold cty_alpha_eq; eassumption].
  - erewrite IHA; [reflexivity | unfold cty_alpha_eq; eassumption].
  - erewrite IHA1, IHA2; [reflexivity | unfold cty_alpha_eq; eassumption | unfold cty_alpha_eq; eassumption].
  - erewrite IHA1, IHA2; [reflexivity | unfold cty_alpha_eq; eassumption | unfold cty_alpha_eq; eassumption].
  - erewrite IHA; [reflexivity | unfold cty_alpha_eq; eassumption].
  - erewrite IHA1, IHA2; [reflexivity | unfold cty_alpha_eq; eassumption | unfold cty_alpha_eq; eassumption].
  - clear Hab. revert H fields0 H2.
    induction fields as [| [[fn fg] ft] rest IHf]; intros Hhdall [| [[fn2 fg2] ft2] rest2] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion Hhdall as [| ? ? Hhd Htl]; subst.
    inversion Hfs; subst.
    rewrite Nat.eqb_refl, grade_eqb_refl.
    erewrite Hhd; [cbn; erewrite IHf; [reflexivity | exact Htl | eassumption] | unfold cty_alpha_eq; eassumption].
  - rewrite cidx_list_eqb_refl; reflexivity.
Qed.

Lemma cty_shape_eqb_refl : forall (D : JoinDomain) (A : cty D),
  cty_shape_eqb A A = true.
Proof. intros D A. apply cty_alpha_eq_shape, cty_alpha_eq_refl. Qed.

Lemma cty_shape_eqb_sym : forall (D : JoinDomain) (A B : cty D),
  cty_shape_eqb A B = cty_shape_eqb B A.
Proof.
  intros D A. induction A using cty_ind_nested; intros B; destruct B; cbn; try reflexivity;
    try (rewrite (IHA B); reflexivity);
    try (rewrite cidx_eqb_sym, (IHA B); reflexivity);
    try (rewrite (Nat.eqb_sym x x0); reflexivity);
    try (rewrite (grade_eqb_sym D q q0), (IHA B); reflexivity);
    try (rewrite (Nat.eqb_sym b b0); reflexivity);
    try (rewrite (grade_eqb_sym D s s0), (grade_eqb_sym D r r0), (IHA1 B1), (IHA2 B2); reflexivity);
    try (rewrite (grade_eqb_sym D r r0), (IHA1 B1), (IHA2 B2); reflexivity);
    try (rewrite (IHA1 B1), (IHA2 B2); reflexivity).
  - rewrite (Nat.eqb_sym id id0). f_equal.
    revert fields0. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2]; cbn; try reflexivity.
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    rewrite (Nat.eqb_sym n1 n2), (grade_eqb_sym D g1 g2), (Hhd t2), (IH Htl r2). reflexivity.
  - rewrite (Nat.eqb_sym id id0), cidx_list_eqb_sym. reflexivity.
Qed.

Lemma cty_shape_eqb_trans : forall (D : JoinDomain) (A B C : cty D),
  cty_shape_eqb A B = true -> cty_shape_eqb B C = true -> cty_shape_eqb A C = true.
Proof.
  intros D A. induction A using cty_ind_nested; intros B C H1 H2;
    destruct B, C; cbn in H1, H2 |- *; try discriminate; try reflexivity;
    try exact (nat_eqb_trans _ _ _ H1 H2);
    try exact (IHA _ _ H1 H2).
  - apply andb_true_iff in H1 as [He1 Hl1]; apply andb_true_iff in H2 as [He2 Hl2].
    apply andb_true_iff; split; [exact (IHA _ _ He1 He2) | exact (cidx_eqb_trans _ _ _ _ Hl1 Hl2)].
  - apply andb_true_iff in H1 as [Hq1 Hi1]; apply andb_true_iff in H2 as [Hq2 Hi2].
    apply grade_eqb_sound in Hq1; apply grade_eqb_sound in Hq2; subst.
    apply andb_true_iff; split; [apply grade_eqb_refl | exact (IHA _ _ Hi1 Hi2)].
  - repeat (apply andb_true_iff in H1 as [H1 ?]); repeat (apply andb_true_iff in H2 as [H2 ?]).
    repeat match goal with Hq : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hq end; subst.
    repeat (apply andb_true_iff; split); try apply grade_eqb_refl.
    + eapply IHA1; eassumption.
    + eapply IHA2; eassumption.
  - repeat (apply andb_true_iff in H1 as [H1 ?]); repeat (apply andb_true_iff in H2 as [H2 ?]).
    repeat match goal with Hq : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hq end; subst.
    repeat (apply andb_true_iff; split); try apply grade_eqb_refl.
    + eapply IHA1; eassumption.
    + eapply IHA2; eassumption.
  - apply andb_true_iff in H1 as [Hq1 Hi1]; apply andb_true_iff in H2 as [Hq2 Hi2].
    apply grade_eqb_sound in Hq1; apply grade_eqb_sound in Hq2; subst.
    apply andb_true_iff; split; [apply grade_eqb_refl | exact (IHA _ _ Hi1 Hi2)].
  - apply andb_true_iff in H1 as [Hl1 Hr1]; apply andb_true_iff in H2 as [Hl2 Hr2].
    apply andb_true_iff; split; [exact (IHA1 _ _ Hl1 Hl2) | exact (IHA2 _ _ Hr1 Hr2)].
  - apply andb_true_iff in H1 as [Hid1 Hfs1]; apply andb_true_iff in H2 as [Hid2 Hfs2].
    apply andb_true_iff; split; [exact (nat_eqb_trans _ _ _ Hid1 Hid2) |].
    revert fields0 fields1 Hfs1 Hfs2.
    induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] [| [[n3 g3] t3] r3] Hfs1 Hfs2;
      cbn in *; try discriminate; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    repeat (apply andb_true_iff in Hfs1 as [Hfs1 ?]); repeat (apply andb_true_iff in Hfs2 as [Hfs2 ?]).
    repeat match goal with
    | Hn : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hn
    | Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg
    end; subst.
    repeat (apply andb_true_iff; split); try apply Nat.eqb_refl; try apply grade_eqb_refl.
    + eapply Hhd; eassumption.
    + eapply (IH Htl); eassumption.
  - apply andb_true_iff in H1 as [Hid1 His1]; apply andb_true_iff in H2 as [Hid2 His2].
    apply andb_true_iff; split; [exact (nat_eqb_trans _ _ _ Hid1 Hid2) | exact (cidx_list_eqb_trans _ _ _ _ His1 His2)].
Qed.

Lemma cty_shape_eqb_ren : forall (D : JoinDomain) (r : nat -> nat) (A B : cty D),
  cty_shape_eqb A B = true ->
  cty_shape_eqb (ren_cty r A) (ren_cty r B) = true.
Proof.
  intros D r A. revert r. induction A using cty_ind_nested; intros rr B H1;
    destruct B; cbn in H1 |- *; try discriminate; try reflexivity;
    try (rewrite H1; reflexivity);
    try (apply Nat.eqb_eq in H1; subst; apply Nat.eqb_refl);
    try (apply (IHA rr _ H1)).
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [apply (IHA rr _ H1) |].
    apply cidx_eqb_sound in H2; subst; apply cidx_eqb_refl.
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [exact H1 | apply (IHA rr _ H2)].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    repeat (apply andb_true_iff; split); try assumption; [eapply (IHA1 rr); eassumption | eapply (IHA2 (ren_shift rr)); eassumption].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    repeat (apply andb_true_iff; split); try assumption; [eapply (IHA1 rr); eassumption | eapply (IHA2 (ren_shift rr)); eassumption].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [exact H1 | apply (IHA rr _ H2)].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [apply (IHA1 rr _ H1) | apply (IHA2 rr _ H2)].
  - apply andb_true_iff in H1 as [Hid Hfs]. apply andb_true_iff; split; [exact Hid |].
    revert fields0 Hfs. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    repeat (apply andb_true_iff in Hfs as [Hfs ?]).
    repeat (apply andb_true_iff; split); try assumption.
    + eapply (Hhd rr); eassumption.
    + eapply (IH Htl); eassumption.
  - apply andb_true_iff in H1 as [Hid His]. apply andb_true_iff; split; [exact Hid |].
    apply cidx_list_eqb_sound in His; subst; apply cidx_list_eqb_refl.
Qed.

Lemma cty_shape_eqb_unshift : forall (D : JoinDomain) k (A B : cty D),
  cty_shape_eqb A B = true ->
  cty_shape_eqb (unshift_cty k A) (unshift_cty k B) = true.
Proof. intros D k A B H. apply cty_shape_eqb_ren, H. Qed.

Lemma cty_shape_eqb_subst_cidx : forall (D : JoinDomain) k (v : cidx D) (A B : cty D),
  cty_shape_eqb A B = true ->
  cty_shape_eqb (subst_cidx_in_cty k v A) (subst_cidx_in_cty k v B) = true.
Proof.
  intros D k v A. revert k v. induction A using cty_ind_nested; intros k v B H1;
    destruct B; cbn in H1 |- *; try discriminate; try reflexivity;
    try (rewrite H1; reflexivity);
    try (apply Nat.eqb_eq in H1; subst; apply Nat.eqb_refl);
    try (apply (IHA k v _ H1)).
  - apply andb_true_iff in H1 as [H1 H2]. apply cidx_eqb_sound in H2; subst.
    apply andb_true_iff; split; [apply (IHA k v _ H1) | apply cidx_eqb_refl].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [exact H1 | apply (IHA k v _ H2)].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    repeat (apply andb_true_iff; split); try assumption;
      [eapply (IHA1 k v); eassumption | eapply (IHA2 (S k) (lift_cidx 0 1 v)); eassumption].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    repeat (apply andb_true_iff; split); try assumption;
      [eapply (IHA1 k v); eassumption | eapply (IHA2 (S k) (lift_cidx 0 1 v)); eassumption].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [exact H1 | apply (IHA k v _ H2)].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [apply (IHA1 k v _ H1) | apply (IHA2 k v _ H2)].
  - apply andb_true_iff in H1 as [Hid Hfs]. apply andb_true_iff; split; [exact Hid |].
    revert fields0 Hfs. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    repeat (apply andb_true_iff in Hfs as [Hfs ?]).
    repeat (apply andb_true_iff; split); try assumption;
      [eapply (Hhd k v); eassumption | eapply (IH Htl); eassumption].
  - apply andb_true_iff in H1 as [Hid His]. apply cidx_list_eqb_sound in His; subst.
    apply andb_true_iff; split; [exact Hid | apply cidx_list_eqb_refl].
Qed.

Lemma cty_shape_eqb_subst_tvar : forall (D : JoinDomain) k (U A B : cty D),
  cty_shape_eqb A B = true ->
  cty_shape_eqb (subst_tvar_in_cty k U A) (subst_tvar_in_cty k U B) = true.
Proof.
  intros D k U A. revert k U. induction A using cty_ind_nested; intros k U B H1;
    destruct B; cbn in H1 |- *; try discriminate; try reflexivity;
    try (apply Nat.eqb_eq in H1; subst; first [apply Nat.eqb_refl | apply cty_shape_eqb_refl]);
    try (apply (IHA k U _ H1)).
  - apply andb_true_iff in H1 as [H1 H2]. apply cidx_eqb_sound in H2; subst.
    apply andb_true_iff; split; [apply (IHA k U _ H1) | apply cidx_eqb_refl].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [exact H1 | apply (IHA k U _ H2)].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    repeat (apply andb_true_iff; split); try assumption;
      [eapply (IHA1 k U); eassumption | eapply (IHA2 (S k) (lift_cty 0 1 U)); eassumption].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    repeat (apply andb_true_iff; split); try assumption;
      [eapply (IHA1 k U); eassumption | eapply (IHA2 (S k) (lift_cty 0 1 U)); eassumption].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [exact H1 | apply (IHA k U _ H2)].
  - apply andb_true_iff in H1 as [H1 H2]. apply andb_true_iff; split; [apply (IHA1 k U _ H1) | apply (IHA2 k U _ H2)].
  - apply andb_true_iff in H1 as [Hid Hfs]. apply andb_true_iff; split; [exact Hid |].
    revert fields0 Hfs. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    repeat (apply andb_true_iff in Hfs as [Hfs ?]).
    repeat (apply andb_true_iff; split); try assumption;
      [eapply (Hhd k U); eassumption | eapply (IH Htl); eassumption].
  - apply andb_true_iff in H1 as [Hid His]. apply cidx_list_eqb_sound in His; subst.
    apply andb_true_iff; split; [exact Hid | apply cidx_list_eqb_refl].
Qed.

Lemma cty_shape_eqb_uses_var : forall (D : JoinDomain) k (A B : cty D),
  cty_shape_eqb A B = true -> cty_uses_var k A = cty_uses_var k B.
Proof.
  intros D k A. revert k. induction A using cty_ind_nested; intros k B H1;
    destruct B; cbn in H1 |- *; try discriminate; try reflexivity;
    try (apply Nat.eqb_eq in H1; subst; reflexivity);
    try (apply (IHA k _ H1)).
  - apply andb_true_iff in H1 as [H1 H2]. apply cidx_eqb_sound in H2; subst.
    rewrite (IHA k _ H1). reflexivity.
  - apply andb_true_iff in H1 as [H1 H2]. apply (IHA k _ H2).
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    erewrite (IHA1 k), (IHA2 (S k)); [reflexivity | eassumption | eassumption].
  - repeat (apply andb_true_iff in H1 as [H1 ?]).
    erewrite (IHA1 k), (IHA2 (S k)); [reflexivity | eassumption | eassumption].
  - apply andb_true_iff in H1 as [H1 H2]. apply (IHA k _ H2).
  - apply andb_true_iff in H1 as [H1 H2].
    rewrite (IHA1 k _ H1), (IHA2 k _ H2). reflexivity.
  - apply andb_true_iff in H1 as [Hid Hfs].
    revert fields0 Hfs. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    repeat (apply andb_true_iff in Hfs as [Hfs ?]).
    erewrite (Hhd k), (IH Htl); [reflexivity | eassumption | eassumption].
  - apply andb_true_iff in H1 as [Hid His]. apply cidx_list_eqb_sound in His; subst. reflexivity.
Qed.

Lemma cty_shape_eqb_erase_hints_l : forall (D : JoinDomain) (A B : cty D),
  cty_shape_eqb (erase_hints A) B = cty_shape_eqb A B.
Proof.
  intros D A. induction A using cty_ind_nested; intros B; destruct B; cbn; try reflexivity;
    try (rewrite (IHA B); reflexivity);
    try (rewrite (IHA1 B1), (IHA2 B2); reflexivity).
  f_equal. revert fields0. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2]; cbn; try reflexivity.
  inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
  rewrite (Hhd t2), (IH Htl r2). reflexivity.
Qed.

Lemma cty_shape_eqb_erase_hints : forall (D : JoinDomain) (A B : cty D),
  cty_shape_eqb A B = true ->
  cty_shape_eqb (erase_hints A) (erase_hints B) = true.
Proof.
  intros D A B H.
  rewrite cty_shape_eqb_erase_hints_l, cty_shape_eqb_sym, cty_shape_eqb_erase_hints_l, cty_shape_eqb_sym.
  exact H.
Qed.

Lemma cty_shape_eqb_app_result_ty : forall (D : JoinDomain) (dom1 dom2 cod1 cod2 : cty D) arg res,
  cty_shape_eqb dom1 dom2 = true ->
  cty_shape_eqb cod1 cod2 = true ->
  app_result_ty dom1 cod1 arg = Some res ->
  exists res2,
    app_result_ty dom2 cod2 arg = Some res2 /\
    cty_shape_eqb res res2 = true.
Proof.
  intros D dom1 dom2 cod1 cod2 arg res Hdom Hcod Happ.
  unfold app_result_ty in *.
  rewrite (cty_shape_eqb_uses_var D 0 cod1 cod2 Hcod) in Happ.
  destruct dom1, dom2; cbn in Hdom, Happ |- *; try discriminate;
    try (destruct (cty_uses_var 0 cod2); [discriminate |]; inversion Happ; subst;
         eexists; split; [reflexivity | apply cty_shape_eqb_unshift; exact Hcod]).
  - destruct (term_as_cidx arg) eqn:Eidx;
      [ inversion Happ; subst; eexists; split; [reflexivity | apply cty_shape_eqb_subst_cidx; exact Hcod]
      | destruct (cty_uses_var 0 cod2); [discriminate |]; inversion Happ; subst;
        eexists; split; [reflexivity | apply cty_shape_eqb_unshift; exact Hcod] ].
  - destruct arg;
      first
      [ inversion Happ; subst; eexists; split; [reflexivity | apply cty_shape_eqb_subst_tvar; exact Hcod]
      | destruct (cty_uses_var 0 cod2); [discriminate |]; inversion Happ; subst;
        eexists; split; [reflexivity | apply cty_shape_eqb_unshift; exact Hcod] ].
Qed.

Definition cenv_shape_eq {D : JoinDomain} (env1 env2 : cenv D) : Prop :=
  Forall2 (fun e1 e2 => cty_shape_eqb (cannotation e1) (cannotation e2) = true) env1 env2.

Lemma cenv_shape_eq_refl : forall (D : JoinDomain) (env : cenv D),
  cenv_shape_eq env env.
Proof.
  intros D env. induction env; constructor; [apply cty_shape_eqb_refl | exact IHenv].
Qed.

Lemma clookup_cenv_shape_eq : forall (D : JoinDomain) (env1 env2 : cenv D) x e1,
  cenv_shape_eq env1 env2 ->
  clookup env1 x = Some e1 ->
  exists e2, clookup env2 x = Some e2 /\ cty_shape_eqb (cannotation e1) (cannotation e2) = true.
Proof.
  intros D env1 env2 x e1 Henv. revert x.
  induction Henv; intros [| x'] Hlk; unfold clookup in *; cbn in *; try discriminate.
  - inversion Hlk; subst. exists y; split; [reflexivity | exact H].
  - exact (IHHenv x' Hlk).
Qed.

Lemma cterm_result_type_shape : forall (D : JoinDomain) (env : cenv D) (t : cterm D) (j : cjudgment D),
  CoreDerives env t j ->
  forall env2, cenv_shape_eq env env2 ->
  exists ty2,
    cterm_result_type env2 t = Some ty2 /\
    cty_shape_eqb ty2 (cresult_type j) = true.
Proof.
  intros D env t j H.
  induction H using CoreDerives_ind_mut with
    (P := fun env t j _ => forall env2, cenv_shape_eq env env2 ->
       exists ty2, cterm_result_type env2 t = Some ty2 /\ cty_shape_eqb ty2 (cresult_type j) = true)
    (P0 := fun _ _ _ _ _ => True);
    try exact I; intros env2 Henv; cbn [cterm_result_type cresult_type].
  - lazymatch goal with
    | Hlk : clookup _ _ = Some _ |- _ =>
        destruct (clookup_cenv_shape_eq _ _ _ _ _ Henv Hlk) as [e2 [Hlk2 Hsh2]];
        rewrite Hlk2; cbn; eexists; split; [reflexivity |
          rewrite cty_shape_eqb_sym; apply cty_shape_eqb_ren; exact Hsh2]
    end.
  - eexists; split; reflexivity.
  - eexists; split; reflexivity.
  - eexists; split; reflexivity.
  - destruct (IHCoreDerives ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env2))
      as [ty2 [Hty2 Hsh2]].
    + constructor; [apply cty_shape_eqb_refl | exact Henv].
    + rewrite Hty2. cbn. eexists; split; [reflexivity |].
      repeat (apply andb_true_iff; split); try apply grade_eqb_refl; try apply cty_shape_eqb_refl.
      exact Hsh2.
  - destruct (IHCoreDerives1 _ Henv) as [tfn2 [Hfn2 Hsh_fn]].
    rewrite Hfn2. destruct tfn2; cbn in Hsh_fn; try discriminate.
    repeat (apply andb_true_iff in Hsh_fn as [Hsh_fn ?]).
    repeat match goal with Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg end; subst.
    lazymatch goal with
    | Happ : app_result_ty dom cod arg = Some res_ty |- _ =>
        destruct (cty_shape_eqb_app_result_ty D dom tfn2_1 cod tfn2_2 arg res_ty
                    ltac:(rewrite cty_shape_eqb_sym; assumption)
                    ltac:(rewrite cty_shape_eqb_sym; assumption) Happ) as [res2 [Hres2 Hsh_res]];
        rewrite Hres2; eexists; split; [reflexivity | rewrite cty_shape_eqb_sym; exact Hsh_res]
    end.
  - destruct (IHCoreDerives2 ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env2))
      as [tb2 [Htb2 Hsh_tb]].
    + constructor; [apply cty_shape_eqb_refl | exact Henv].
    + rewrite Htb2. cbn. eexists; split; [reflexivity |].
      apply cty_shape_eqb_unshift; exact Hsh_tb.
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - destruct (IHCoreDerives _ Henv) as [t2 [Ht2 Hsh2]].
    rewrite Ht2. cbn. eexists; split; [reflexivity |].
    apply andb_true_iff; split; [apply grade_eqb_refl | exact Hsh2].
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - destruct (IHCoreDerives _ Henv) as [t2 [Ht2 Hsh2]].
    rewrite Ht2. cbn. eexists; split; [reflexivity |].
    apply andb_true_iff; split; [exact Hsh2 | apply cty_shape_eqb_refl].
  - destruct (IHCoreDerives _ Henv) as [t2 [Ht2 Hsh2]].
    rewrite Ht2. cbn. eexists; split; [reflexivity |].
    apply andb_true_iff; split; [apply cty_shape_eqb_refl | exact Hsh2].
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - exact (IHCoreDerives2 _ Henv).
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
  - subst; eexists; split; [reflexivity | apply cty_shape_eqb_refl].
Qed.

Lemma cenv_shape_eq_extend : forall (D : JoinDomain) (env1 env2 : cenv D) fs1 fs2,
  cenv_shape_eq env1 env2 ->
  Forall2 (fun '(_, g1, t1) '(_, g2, t2) => g1 = g2 /\ cty_shape_eqb t1 t2 = true) fs1 fs2 ->
  cenv_shape_eq (erase_cterm_extend env1 fs1) (erase_cterm_extend env2 fs2).
Proof.
  assert (Hgo : forall (D : JoinDomain) n (env1 env2 : cenv D) fs1 fs2,
    cenv_shape_eq env1 env2 ->
    Forall2 (fun '(_, g1, t1) '(_, g2, t2) => g1 = g2 /\ cty_shape_eqb t1 t2 = true) fs1 fs2 ->
    cenv_shape_eq (erase_cterm_extend_go n env1 fs1) (erase_cterm_extend_go n env2 fs2)).
  { intros D n. induction n as [| n IH]; intros env1 env2 fs1 fs2 Henv Hfs; cbn; [exact Henv |].
    destruct Hfs; [exact Henv |].
    destruct x as [[n1 g1] t1], y as [[n2 g2] t2]. destruct H as [_ Hsh].
    apply IH; [constructor; [exact Hsh | exact Henv] |].
    clear - Hfs. induction Hfs; constructor; [| exact IHHfs].
    destruct x as [[? ?] ?], y as [[? ?] ?]. destruct H as [-> Ht].
    split; [reflexivity | apply cty_shape_eqb_ren; exact Ht]. }
  intros D env1 env2 fs1 fs2 Henv Hfs.
  unfold erase_cterm_extend. rewrite (Forall2_length Hfs).
  exact (Hgo D (length fs2) env1 env2 fs1 fs2 Henv Hfs).
Qed.

Lemma cterm_result_type_shape_env : forall (D : JoinDomain) (t : cterm D) (env1 env2 : cenv D),
  cenv_shape_eq env1 env2 ->
  match cterm_result_type env1 t, cterm_result_type env2 t with
  | Some ty1, Some ty2 => cty_shape_eqb ty1 ty2 = true
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros D t. induction t using cterm_ind_nested; intros env1 env2 Ha; cbn [cterm_result_type];
    try apply cty_shape_eqb_refl.
  - destruct (clookup env1 x) as [e1 |] eqn:E1.
    + destruct (clookup_cenv_shape_eq _ _ _ _ _ Ha E1) as [e2 [E2 Hsh]].
      rewrite E2. cbn. apply cty_shape_eqb_ren; exact Hsh.
    + destruct (clookup env2 x) as [e2 |] eqn:E2; cbn; [| exact I].
      exfalso. unfold clookup in E1, E2.
      apply nth_error_None in E1. assert (Hx : nth_error env2 x <> None) by congruence.
      apply nth_error_Some in Hx. rewrite (Forall2_length Ha) in E1. lia.
  - pose proof (IHt ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env1)
                    ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env2)
                    ltac:(constructor; [apply cty_shape_eqb_refl | exact Ha])) as H1.
    destruct (cterm_result_type _ t), (cterm_result_type _ t); cbn in *; try contradiction; try exact I.
    repeat (apply andb_true_iff; split); try apply grade_eqb_refl; try apply cty_shape_eqb_refl; exact H1.
  - pose proof (IHt1 _ _ Ha) as H1.
    destruct (cterm_result_type env1 t1) as [f1 |], (cterm_result_type env2 t1) as [f2 |];
      cbn in *; try contradiction; try exact I.
    destruct f1, f2; cbn in H1; try discriminate; try exact I.
    repeat (apply andb_true_iff in H1 as [H1 ?]).
    destruct (app_result_ty f1_1 f1_2 t2) as [r1 |] eqn:E1;
      destruct (app_result_ty f2_1 f2_2 t2) as [r2 |] eqn:E2; try exact I.
    + destruct (cty_shape_eqb_app_result_ty D f1_1 f2_1 f1_2 f2_2 t2 r1 ltac:(assumption) ltac:(assumption) E1)
        as [r2' [E2' Hsh]]. rewrite E2' in E2. inversion E2; subst; exact Hsh.
    + destruct (cty_shape_eqb_app_result_ty D f1_1 f2_1 f1_2 f2_2 t2 r1 ltac:(assumption) ltac:(assumption) E1)
        as [r2' [E2' _]]. rewrite E2' in E2; discriminate.
    + destruct (cty_shape_eqb_app_result_ty D f2_1 f1_1 f2_2 f1_2 t2 r2
                  ltac:(rewrite cty_shape_eqb_sym; assumption)
                  ltac:(rewrite cty_shape_eqb_sym; assumption) E2)
        as [r1' [E1' _]]. rewrite E1' in E1; discriminate.
  - pose proof (IHt2 ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env1)
                     ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env2)
                     ltac:(constructor; [apply cty_shape_eqb_refl | exact Ha])) as H1.
    destruct (cterm_result_type _ t2), (cterm_result_type _ t2); cbn in *; try contradiction; try exact I.
    apply cty_shape_eqb_unshift; exact H1.
  - pose proof (IHt _ _ Ha) as H1.
    destruct (cterm_result_type env1 t), (cterm_result_type env2 t); cbn in *; try contradiction; try exact I.
    apply andb_true_iff; split; [apply grade_eqb_refl | exact H1].
  - pose proof (IHt _ _ Ha) as H1.
    destruct (cterm_result_type env1 t), (cterm_result_type env2 t); cbn in *; try contradiction; try exact I.
    apply andb_true_iff; split; [exact H1 | apply cty_shape_eqb_refl].
  - pose proof (IHt _ _ Ha) as H1.
    destruct (cterm_result_type env1 t), (cterm_result_type env2 t); cbn in *; try contradiction; try exact I.
    apply andb_true_iff; split; [apply cty_shape_eqb_refl | exact H1].
  - exact (IHt2 _ _ Ha).
Qed.

Lemma erase_cterm_shape_env : forall (D : JoinDomain) (t : cterm D) env1 env2,
  cenv_shape_eq env1 env2 ->
  erase_cterm env1 t = erase_cterm env2 t.
Proof.
  intros D t. induction t using cterm_ind_nested; intros env1 env2 Ha; cbn; try reflexivity.
  - f_equal. apply IHt. constructor; [apply cty_shape_eqb_refl | exact Ha].
  - unfold callee_grade. pose proof (cterm_result_type_shape_env D t1 env1 env2 Ha) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction; [| rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha); reflexivity].
    destruct ty1; cbn in Hsh; destruct ty2; try discriminate;
      try (rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha); reflexivity).
    repeat (apply andb_true_iff in Hsh as [Hsh ?]).
    repeat match goal with Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg end; subst.
    destruct (grade_eqb _ zero); rewrite (IHt1 _ _ Ha); [reflexivity | rewrite (IHt2 _ _ Ha); reflexivity].
  - destruct (grade_eqb s zero);
      [f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | exact Ha]
      | rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | exact Ha]].
  - rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha); reflexivity.
  - pose proof (cterm_result_type_shape_env D t1 env1 env2 Ha) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction;
      [ destruct ty1; cbn in Hsh; destruct ty2; try discriminate;
        try (destruct (grade_eqb s zero);
             [ f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | exact Ha]]
             | rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | exact Ha]] ]);
        repeat (apply andb_true_iff in Hsh as [Hsh ?]);
        destruct (grade_eqb s zero);
        [ f_equal; apply IHt2; constructor; [assumption | constructor; [assumption | exact Ha]]
        | rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [assumption | constructor; [assumption | exact Ha]] ]
      | destruct (grade_eqb s zero);
        [ f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | exact Ha]]
        | rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | exact Ha]] ] ].
  - destruct (grade_eqb q zero); [reflexivity | f_equal; apply IHt; exact Ha].
  - pose proof (cterm_result_type_shape_env D t1 env1 env2 Ha) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction;
      [ destruct ty1; cbn in Hsh; destruct ty2; try discriminate;
        try (rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | exact Ha]);
        apply andb_true_iff in Hsh as [Hq Hi]; apply grade_eqb_sound in Hq; subst;
        rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [exact Hi | exact Ha]
      | rewrite (IHt1 _ _ Ha); f_equal; apply IHt2; constructor; [apply cty_shape_eqb_refl | exact Ha] ].
  - f_equal; apply IHt; exact Ha.
  - f_equal; apply IHt; exact Ha.
  - pose proof (cterm_result_type_shape_env D t1 env1 env2 Ha) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction;
      [ destruct ty1; cbn in Hsh; destruct ty2; try discriminate;
        try (rewrite (IHt1 _ _ Ha); f_equal;
             [ apply IHt2; constructor; [apply cty_shape_eqb_refl | exact Ha]
             | apply IHt3; constructor; [apply cty_shape_eqb_refl | exact Ha] ]);
        apply andb_true_iff in Hsh as [Hl Hr];
        rewrite (IHt1 _ _ Ha); f_equal;
        [ apply IHt2; constructor; [exact Hl | exact Ha]
        | apply IHt3; constructor; [exact Hr | exact Ha] ]
      | rewrite (IHt1 _ _ Ha); f_equal;
        [ apply IHt2; constructor; [apply cty_shape_eqb_refl | exact Ha]
        | apply IHt3; constructor; [apply cty_shape_eqb_refl | exact Ha] ] ].
  - rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha), (IHt3 _ _ Ha); reflexivity.
  - f_equal. induction fields as [| [[[fn fg] ft] fv] rest IHf]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    destruct (grade_eqb fg zero); [rewrite (IHf Htl); reflexivity | rewrite (Hhd _ _ Ha), (IHf Htl); reflexivity].
  - unfold record_fields_ty. pose proof (cterm_result_type_shape_env D t1 env1 env2 Ha) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction;
      [ destruct ty1; cbn in Hsh; destruct ty2; try discriminate;
        try (rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha); reflexivity);
        apply andb_true_iff in Hsh as [_ Hfs]; rewrite (IHt1 _ _ Ha); f_equal; apply IHt2;
        apply cenv_shape_eq_extend; [exact Ha |];
        clear - Hfs; revert fields0 Hfs; induction fields as [| [[n1 g1] t1'] r1 IH]; intros [| [[n2 g2] t2'] r2] Hfs;
        cbn in *; try discriminate; [constructor |];
        repeat (apply andb_true_iff in Hfs as [Hfs ?]);
        repeat match goal with Hn : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hn | Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg end;
        subst; constructor; [repeat split; assumption | apply IH; assumption]
      | rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha); reflexivity ].
  - exact (IHt _ _ Ha).
  - rewrite (IHt1 _ _ Ha), (IHt2 _ _ Ha); f_equal; apply IHt3;
      constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | exact Ha]].
Qed.

Lemma erase_cterm_head_type_uses : forall (D : JoinDomain) x dom a1 a2 env (t : cterm D),
  erase_cterm ({| cbinder := x; cannotation := dom; ctype_uses := a1 |} :: env) t =
  erase_cterm ({| cbinder := x; cannotation := dom; ctype_uses := a2 |} :: env) t.
Proof.
  intros D x dom a1 a2 env t. apply erase_cterm_shape_env.
  constructor; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl].
Qed.

(* ================================================================= *)
(* Part 2: Semantic Type Shapes, DSubty, ValRel, and Simulation      *)
(* ================================================================= *)

Inductive dcty {D : JoinDomain} : Type :=
| DNat
| DBool
| DVec
| DUniv
| DBound (idx : nat)
| DUnbox (idx : nat)
| DPi (s : grade D) (dom cod : @dcty D)
| DSigma (f s : @dcty D)
| DBox (q : grade D) (inner : @dcty D)
| DSum (l r : @dcty D)
| DRecord (fields : list (grade D * @dcty D))
| DInd.

Definition dcty_ind_nested {D : JoinDomain} (P : @dcty D -> Prop)
  (HNat : P DNat) (HBool : P DBool) (HVec : P DVec) (HUniv : P DUniv)
  (HBound : forall idx, P (DBound idx)) (HUnbox : forall idx, P (DUnbox idx))
  (HPi : forall s dom cod, P dom -> P cod -> P (DPi s dom cod))
  (HSigma : forall f s, P f -> P s -> P (DSigma f s))
  (HBox : forall q inner, P inner -> P (DBox q inner))
  (HSum : forall l r, P l -> P r -> P (DSum l r))
  (HRec : forall fs, Forall (fun '(_, df) => P df) fs -> P (DRecord fs))
  (HInd : P DInd) : forall d, P d :=
  fix F (d : @dcty D) : P d :=
    match d with
    | DNat => HNat | DBool => HBool | DVec => HVec | DUniv => HUniv
    | DBound idx => HBound idx | DUnbox idx => HUnbox idx
    | DPi s dom cod => HPi s dom cod (F dom) (F cod)
    | DSigma f s => HSigma f s (F f) (F s)
    | DBox q inner => HBox q inner (F inner)
    | DSum l r => HSum l r (F l) (F r)
    | DRecord fs =>
        HRec fs ((fix go (xs : list (grade D * @dcty D)) : Forall (fun '(_, df) => P df) xs :=
          match xs with
          | [] => Forall_nil _
          | (fg, df) :: rest => Forall_cons (fg, df) (F df) (go rest)
          end) fs)
    | DInd => HInd
    end.

Fixpoint lift_dcty {D : JoinDomain} (cutoff delta : nat) (d : @dcty D) : @dcty D :=
  match d with
  | DNat | DBool | DVec | DUniv | DInd => d
  | DBound k => if k <? cutoff then DBound k else DBound (k + delta)
  | DUnbox b => if b <? cutoff then DUnbox b else DUnbox (b + delta)
  | DPi s dom cod => DPi s (lift_dcty cutoff delta dom) (lift_dcty (S cutoff) delta cod)
  | DSigma f s => DSigma (lift_dcty cutoff delta f) (lift_dcty (S cutoff) delta s)
  | DBox q inner => DBox q (lift_dcty cutoff delta inner)
  | DSum l r => DSum (lift_dcty cutoff delta l) (lift_dcty cutoff delta r)
  | DRecord fs => DRecord (map (fun '(fg, df) => (fg, lift_dcty cutoff delta df)) fs)
  end.

Fixpoint subst_dcty {D : JoinDomain} (k : nat) (arg d : @dcty D) : @dcty D :=
  match d with
  | DNat | DBool | DVec | DUniv | DInd => d
  | DBound i =>
      if Nat.eqb i k then lift_dcty 0 k arg
      else if Nat.ltb i k then DBound i
      else DBound (i - 1)
  | DUnbox b =>
      if Nat.eqb b k then lift_dcty 0 k arg
      else if Nat.ltb b k then DUnbox b
      else DUnbox (b - 1)
  | DPi s dom cod => DPi s (subst_dcty k arg dom) (subst_dcty (S k) arg cod)
  | DSigma f s => DSigma (subst_dcty k arg f) (subst_dcty (S k) arg s)
  | DBox q inner => DBox q (subst_dcty k arg inner)
  | DSum l r => DSum (subst_dcty k arg l) (subst_dcty k arg r)
  | DRecord fs => DRecord (map (fun '(fg, df) => (fg, subst_dcty k arg df)) fs)
  end.

Fixpoint eval_dcty {D : JoinDomain} (depth : nat) (theta : list (@dcty D)) (T : cty D) : @dcty D :=
  match T with
  | CNat => DNat
  | CBool => DBool
  | CVec _ _ => DVec
  | CUniv _ => DUniv
  | CTVar x =>
      if x <? depth then DBound x
      else lift_dcty 0 depth (nth (x - depth) theta DUniv)
  | CTProm _ inner => eval_dcty depth theta inner
  | CTUnbox b =>
      if b <? depth then DUnbox b
      else match nth (b - depth) theta DUniv with
           | DBox _ inner => lift_dcty 0 depth inner
           | _ => DUniv
           end
  | CPi _ s _ dom cod => DPi s (eval_dcty depth theta dom) (eval_dcty (S depth) theta cod)
  | CSigma _ _ f s => DSigma (eval_dcty depth theta f) (eval_dcty (S depth) theta s)
  | CBox q inner => DBox q (eval_dcty depth theta inner)
  | CSum l r => DSum (eval_dcty depth theta l) (eval_dcty depth theta r)
  | CRecord _ fs => DRecord (map (fun '(_, fg, ft) => (fg, eval_dcty depth theta ft)) fs)
  | CInd _ _ => DInd
  end.

Lemma lift_dcty_0 : forall (D : JoinDomain) c (d : @dcty D), lift_dcty c 0 d = d.
Proof.
  intros D c d. revert c. induction d using dcty_ind_nested; intros c; cbn [lift_dcty]; try reflexivity;
    try (destruct (_ <? c); [reflexivity | f_equal; lia]);
    try (rewrite IHd1, IHd2; reflexivity);
    try (rewrite IHd; reflexivity).
  f_equal. induction fs as [| [fg df] rest IH]; cbn in *; [reflexivity |].
  inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite Hhd, (IH Htl). reflexivity.
Qed.

Lemma lift_dcty_add : forall (D : JoinDomain) c1 c2 n1 n2 (d : @dcty D),
  c1 <= c2 -> c2 <= c1 + n1 ->
  lift_dcty c2 n2 (lift_dcty c1 n1 d) = lift_dcty c1 (n1 + n2) d.
Proof.
  intros D c1 c2 n1 n2 d. revert c1 c2 n1 n2.
  induction d using dcty_ind_nested; intros c1 c2 n1 n2 H1 H2; cbn [lift_dcty]; try reflexivity;
    try (destruct (Nat.ltb_spec idx c1); cbn [lift_dcty];
         [rewrite (proj2 (Nat.ltb_lt idx c2) ltac:(lia)); reflexivity
         | rewrite (proj2 (Nat.ltb_ge (idx + n1) c2) ltac:(lia)); f_equal; lia]);
    try (rewrite (IHd1 _ _ _ _ H1 H2), (IHd2 (S c1) (S c2) n1 n2 ltac:(lia) ltac:(lia)); reflexivity);
    try (rewrite (IHd1 _ _ _ _ H1 H2), (IHd2 _ _ _ _ H1 H2); reflexivity);
    try (rewrite (IHd _ _ _ _ H1 H2); reflexivity).
  f_equal. induction fs as [| [fg df] rest IH]; cbn in *; [reflexivity |].
  inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite (Hhd _ _ _ _ H1 H2), (IH Htl). reflexivity.
Qed.

Lemma subst_dcty_lift_cancel : forall (D : JoinDomain) c k (arg d : @dcty D),
  c <= k ->
  subst_dcty k arg (lift_dcty c (S (k - c)) d) = lift_dcty c (k - c) d.
Proof.
  intros D c k arg d. revert c k arg.
  induction d using dcty_ind_nested; intros c k arg Hle; cbn [subst_dcty lift_dcty]; try reflexivity;
    try (destruct (Nat.ltb_spec idx c); cbn [subst_dcty lift_dcty];
         [ rewrite (proj2 (Nat.eqb_neq idx k) ltac:(lia)), (proj2 (Nat.ltb_lt idx k) ltac:(lia)); reflexivity
         | rewrite (proj2 (Nat.eqb_neq (idx + S (k - c)) k) ltac:(lia)), (proj2 (Nat.ltb_ge (idx + S (k - c)) k) ltac:(lia));
           f_equal; lia ]);
    try (rewrite (IHd1 _ _ _ Hle); pose proof (IHd2 (S c) (S k) arg ltac:(lia)) as H2; cbn [Nat.sub] in H2; rewrite H2; reflexivity);
    try (rewrite (IHd1 _ _ _ Hle), (IHd2 _ _ _ Hle); reflexivity);
    try (rewrite (IHd _ _ _ Hle); reflexivity).
  f_equal. induction fs as [| [fg df] rest IH]; cbn in *; [reflexivity |].
  inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite (Hhd _ _ _ Hle), (IH Htl). reflexivity.
Qed.

Lemma eval_dcty_shape_eq : forall (D : JoinDomain) (A B : cty D) depth theta,
  cty_shape_eqb A B = true ->
  eval_dcty depth theta A = eval_dcty depth theta B.
Proof.
  intros D A. induction A using cty_ind_nested; intros B depth theta H1;
    destruct B; cbn in H1 |- *; try discriminate; try reflexivity;
    try (apply Nat.eqb_eq in H1; subst; reflexivity);
    try (apply andb_true_iff in H1 as [? ?]; apply grade_eqb_sound in H; subst; cbn; first [eapply IHA; eassumption | f_equal; eapply IHA; eassumption]);
    try (repeat (apply andb_true_iff in H1 as [H1 ?]);
         repeat match goal with Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg end; subst;
         cbn; f_equal; [eapply IHA1; eassumption | eapply IHA2; eassumption]).
  - apply andb_true_iff in H1 as [_ Hfs]. f_equal.
    revert fields0 Hfs. induction fields as [| [[n1 g1] t1] r1 IH]; intros [| [[n2 g2] t2] r2] Hfs;
      cbn in *; try discriminate; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    repeat (apply andb_true_iff in Hfs as [Hfs ?]).
    match goal with Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg; subst end.
    f_equal; [f_equal; eapply Hhd; eassumption | eapply (IH Htl); eassumption].
Qed.

Lemma eval_dcty_alpha_eq : forall (D : JoinDomain) (A B : cty D) depth theta,
  cty_alpha_eq A B -> eval_dcty depth theta A = eval_dcty depth theta B.
Proof. intros D A B depth theta H. apply eval_dcty_shape_eq, cty_alpha_eq_shape, H. Qed.

Lemma eval_dcty_ren_shift_lift : forall (D : JoinDomain) (T : cty D) depth m theta,
  eval_dcty (depth + m) theta (lift_cty depth m T) = lift_dcty depth m (eval_dcty depth theta T).
Proof.
  intros D T. induction T using cty_ind_nested; intros depth m theta; cbn [eval_dcty lift_cty lift_dcty ren_cty]; try reflexivity;
    try (rewrite IHT; reflexivity);
    try (rewrite IHT1, IHT2; reflexivity).
  - destruct (Nat.ltb_spec x depth) as [Hlt | Hge]; cbn [eval_dcty lift_dcty]; unfold ren_lift in *.
    + rewrite (proj2 (Nat.ltb_lt x depth) Hlt); cbn iota; rewrite (proj2 (Nat.ltb_lt x (depth + m)) ltac:(lia)); reflexivity.
    + rewrite (proj2 (Nat.ltb_ge x depth) Hge); cbn iota; rewrite (proj2 (Nat.ltb_ge (x + m) (depth + m)) ltac:(lia)).
      replace (x + m - (depth + m)) with (x - depth) by lia.
      rewrite lift_dcty_add by lia. f_equal; lia.
  - destruct (Nat.ltb_spec b depth) as [Hlt | Hge]; cbn [eval_dcty lift_dcty]; unfold ren_lift in *.
    + rewrite (proj2 (Nat.ltb_lt b depth) Hlt); cbn iota; rewrite (proj2 (Nat.ltb_lt b (depth + m)) ltac:(lia)); reflexivity.
    + rewrite (proj2 (Nat.ltb_ge b depth) Hge); cbn iota; rewrite (proj2 (Nat.ltb_ge (b + m) (depth + m)) ltac:(lia)).
      replace (b + m - (depth + m)) with (b - depth) by lia.
      destruct (nth (b - depth) theta DUniv); cbn [lift_dcty]; try reflexivity.
      rewrite lift_dcty_add by lia. reflexivity.
  - rewrite IHT1.
    replace (ren_cty (ren_shift (ren_lift depth m)) T2) with (lift_cty (S depth) m T2)
      by (unfold lift_cty; apply ren_cty_ext; intros [| y]; unfold ren_shift, ren_lift; cbn;
          [reflexivity | destruct (Nat.ltb_spec y depth), (Nat.ltb_spec (S y) (S depth)); cbn; lia]).
    pose proof (IHT2 (S depth) m theta) as H2.
    change (S depth + m) with (S (depth + m)) in H2. rewrite H2. reflexivity.
  - rewrite IHT1.
    replace (ren_cty (ren_shift (ren_lift depth m)) T2) with (lift_cty (S depth) m T2)
      by (unfold lift_cty; apply ren_cty_ext; intros [| y]; unfold ren_shift, ren_lift; cbn;
          [reflexivity | destruct (Nat.ltb_spec y depth), (Nat.ltb_spec (S y) (S depth)); cbn; lia]).
    pose proof (IHT2 (S depth) m theta) as H2.
    change (S depth + m) with (S (depth + m)) in H2. rewrite H2. reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite Hhd, (IH Htl). reflexivity.
Qed.

Lemma eval_dcty_ren_plus : forall (D : JoinDomain) (T : cty D) k theta,
  eval_dcty 0 theta (ren_cty (plus k) T) = eval_dcty 0 (skipn k theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth k theta,
    eval_dcty depth theta (ren_cty (Nat.iter depth ren_shift (plus k)) T0) =
    eval_dcty depth (skipn k theta) T0).
  { induction T0 using cty_ind_nested; intros depth k theta; cbn; try reflexivity;
      try (apply IHT0); try (f_equal; apply IHT0);
      try (rewrite IHT0_1, IHT0_2; reflexivity).
    - destruct (Nat.ltb_spec x depth) as [Hlt | Hge].
      + rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); rewrite (proj2 (Nat.ltb_lt x depth) Hlt); reflexivity.
      + rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); rewrite (proj2 (Nat.ltb_ge (depth + (k + (x - depth))) depth) ltac:(lia)).
        replace (depth + (k + (x - depth)) - depth) with (k + (x - depth)) by lia.
        rewrite nth_skipn; reflexivity.
    - destruct (Nat.ltb_spec b depth) as [Hlt | Hge].
      + rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); rewrite (proj2 (Nat.ltb_lt b depth) Hlt); reflexivity.
      + rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); rewrite (proj2 (Nat.ltb_ge (depth + (k + (b - depth))) depth) ltac:(lia)).
        replace (depth + (k + (b - depth)) - depth) with (k + (b - depth)) by lia.
        rewrite nth_skipn; reflexivity.
    - rewrite IHT0_1.
      pose proof (IHT0_2 (S depth) k theta) as H2.
      change (Nat.iter (S depth) ren_shift (plus k)) with (ren_shift (Nat.iter depth ren_shift (plus k))) in H2.
      rewrite H2. reflexivity.
    - rewrite IHT0_1.
      pose proof (IHT0_2 (S depth) k theta) as H2.
      change (Nat.iter (S depth) ren_shift (plus k)) with (ren_shift (Nat.iter depth ren_shift (plus k))) in H2.
      rewrite H2. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite Hhd, (IH Htl). reflexivity. }
  intros k theta. exact (Hgen T 0 k theta).
Qed.

Lemma eval_dcty_subst_tvar_gen : forall (D : JoinDomain) (T U : cty D) depth theta,
  cty_uses_kinds true true false true true true true depth T = false ->
  eval_dcty depth theta (subst_tvar_in_cty depth (lift_cty 0 depth U) T) =
  subst_dcty depth (eval_dcty 0 theta U) (eval_dcty (S depth) theta T).
Proof.
  intros D T. induction T using cty_ind_nested; intros U depth theta Hsafe; cbn in *; try reflexivity;
    try (apply (IHT U depth theta Hsafe));
    try (f_equal; apply (IHT U depth theta Hsafe)).
  - destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); cbn;
      try (repeat (rw_nat_bool; cbv iota); cbn; reflexivity).
    + rewrite Nat.eqb_refl. pose proof (eval_dcty_ren_shift_lift D U 0 depth theta) as Hl.
      cbn [Nat.add] in Hl. exact Hl.
    + rewrite (proj2 (Nat.ltb_ge (x - 1) depth) ltac:(lia)); cbn iota.
      replace (x - 1 - depth) with (x - S depth) by lia.
      replace (S depth) with (S (depth - 0)) by lia.
      rewrite subst_dcty_lift_cancel by lia.
      replace (depth - 0) with depth by lia. reflexivity.
  - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |]; repeat (rw_nat_bool; cbv iota); cbn;
      try (repeat (rw_nat_bool; cbv iota); cbn; reflexivity).
    + replace (b - 1 - depth) with (b - S depth) by lia.
      destruct (nth (b - S depth) theta DUniv); cbn;
        repeat (rw_nat_bool; cbv iota); cbn;
        try reflexivity;
        replace (S depth) with (S (depth - 0)) by lia;
        rewrite subst_dcty_lift_cancel by lia; replace (depth - 0) with depth by lia; reflexivity.
  - apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (IHT1 U depth theta H1), (lift_cty_add D 1 depth U).
    replace (1 + depth) with (S depth) by lia.
    rewrite (IHT2 U (S depth) theta H2). reflexivity.
  - apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (IHT1 U depth theta H1), (lift_cty_add D 1 depth U).
    replace (1 + depth) with (S depth) by lia.
    rewrite (IHT2 U (S depth) theta H2). reflexivity.
  - apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (IHT1 U depth theta H1), (IHT2 U depth theta H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (Hhd U depth theta H1), (IH Htl H2). reflexivity.
Qed.

Lemma eval_dcty_subst_tvar_0 : forall (D : JoinDomain) (T U : cty D) theta,
  cty_uses_kinds true true false true true true true 0 T = false ->
  eval_dcty 0 theta (subst_tvar_in_cty 0 U T) =
  subst_dcty 0 (eval_dcty 0 theta U) (eval_dcty 1 theta T).
Proof.
  intros D T U theta Hs.
  pose proof (eval_dcty_subst_tvar_gen D T U 0 theta Hs) as H.
  rewrite lift_cty_0_0 in H. exact H.
Qed.

Lemma eval_dcty_subst_var_0 : forall (D : JoinDomain) (T : cty D) y theta,
  eval_dcty 0 theta (subst_var_in_cty 0 y T) =
  eval_dcty 0 (nth y theta DUniv :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth y theta,
    eval_dcty depth theta (ren_cty (Nat.iter depth ren_shift (fun i => match i with 0 => y | S i' => i' end)) T0) =
    eval_dcty depth (nth y theta DUniv :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth y theta; cbn; try reflexivity;
      try (apply IHT0); try (f_equal; apply IHT0);
      try (rewrite IHT0_1, IHT0_2; reflexivity).
    - destruct (Nat.ltb_spec x depth) as [Hlt | Hge].
      + rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); rewrite (proj2 (Nat.ltb_lt x depth) Hlt); reflexivity.
      + rewrite (Nat_iter_ren_shift_ge _ _ _ Hge).
        destruct (x - depth) as [| k'] eqn:Hxk; cbn.
        * rewrite (proj2 (Nat.ltb_ge (depth + y) depth) ltac:(lia)).
          replace (depth + y - depth) with y by lia. reflexivity.
        * rewrite (proj2 (Nat.ltb_ge (depth + k') depth) ltac:(lia)).
          replace (depth + k' - depth) with k' by lia. reflexivity.
    - destruct (Nat.ltb_spec b depth) as [Hlt | Hge].
      + rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); rewrite (proj2 (Nat.ltb_lt b depth) Hlt); reflexivity.
      + rewrite (Nat_iter_ren_shift_ge _ _ _ Hge).
        destruct (b - depth) as [| k'] eqn:Hbk; cbn.
        * rewrite (proj2 (Nat.ltb_ge (depth + y) depth) ltac:(lia)).
          replace (depth + y - depth) with y by lia. reflexivity.
        * rewrite (proj2 (Nat.ltb_ge (depth + k') depth) ltac:(lia)).
          replace (depth + k' - depth) with k' by lia. reflexivity.
    - rewrite IHT0_1. pose proof (IHT0_2 (S depth) y theta) as H2.
      change (Nat.iter (S depth) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end))
        with (ren_shift (Nat.iter depth ren_shift (fun i : nat => match i with 0 => y | S i' => i' end))) in H2.
      rewrite H2. reflexivity.
    - rewrite IHT0_1. pose proof (IHT0_2 (S depth) y theta) as H2.
      change (Nat.iter (S depth) ren_shift (fun i : nat => match i with 0 => y | S i' => i' end))
        with (ren_shift (Nat.iter depth ren_shift (fun i : nat => match i with 0 => y | S i' => i' end))) in H2.
      rewrite H2. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite Hhd, (IH Htl). reflexivity. }
  intros y theta. exact (Hgen T 0 y theta).
Qed.

Lemma eval_dcty_shift_down_gen : forall (D : JoinDomain) (T : cty D) depth (d_any : cidx D) theta,
  cty_uses_kinds true false false true true true true depth T = false ->
  eval_dcty depth theta (subst_cidx_in_cty depth (CIdxLit 0) T) =
  eval_dcty depth theta (unshift_cty depth T).
Proof.
  intros D T. induction T using cty_ind_nested; intros depth d_any theta Hsafe; cbn in *; try reflexivity;
    try (apply (IHT depth d_any theta Hsafe));
    try (f_equal; apply (IHT depth d_any theta Hsafe)).
  - nat_bool_hyps. unfold unshift_cty; cbn.
    change (Nat.iter depth ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end)) with (r_var depth 0).
    destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |].
    + rewrite r_var_lt by lia. rw_nat_bool. reflexivity.
    + rewrite r_var_gt by lia. rw_nat_bool. reflexivity.
  - nat_bool_hyps. unfold unshift_cty; cbn.
    change (Nat.iter depth ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end)) with (r_var depth 0).
    destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |].
    + rewrite r_var_lt by lia. rw_nat_bool. reflexivity.
    + rewrite r_var_gt by lia. rw_nat_bool. reflexivity.
  - apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (IHT1 depth d_any theta H1).
    pose proof (IHT2 (S depth) d_any theta H2) as H2'.
    unfold unshift_cty in H2' |- *; cbn in H2' |- *. rewrite H2'. reflexivity.
  - apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (IHT1 depth d_any theta H1).
    pose proof (IHT2 (S depth) d_any theta H2) as H2'.
    unfold unshift_cty in H2' |- *; cbn in H2' |- *. rewrite H2'. reflexivity.
  - apply orb_false_iff in Hsafe as [H1 H2].
    rewrite (IHT1 depth d_any theta H1), (IHT2 depth d_any theta H2). reflexivity.
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
    pose proof (Hhd depth d_any theta H1) as Hhd'.
    pose proof (IH Htl H2) as Hr. unfold unshift_cty in Hhd', Hr |- *; cbn in Hhd', Hr |- *.
    rewrite Hhd'. inversion Hr; reflexivity.
Qed.

Lemma eval_dcty_unshift_0 : forall (D : JoinDomain) (T : cty D) d_any theta,
  cty_uses_kinds true false false true true true true 0 T = false ->
  eval_dcty 0 theta (unshift_cty 0 T) = eval_dcty 0 (d_any :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth d_any theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth theta (unshift_cty depth T0) = eval_dcty depth (d_any :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth d_any theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth d_any theta Hsafe));
      try (f_equal; apply (IHT0 depth d_any theta Hsafe)).
    - nat_bool_hyps. unfold unshift_cty; cbn.
      change (Nat.iter depth ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end)) with (r_var depth 0).
      destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |].
      + rewrite r_var_lt by lia. cbn. rewrite (proj2 (Nat.ltb_lt x depth) Hlt). reflexivity.
      + rewrite r_var_gt by lia. cbn.
        rewrite (proj2 (Nat.ltb_ge (x - 1) depth) ltac:(lia)), (proj2 (Nat.ltb_ge x depth) ltac:(lia)).
        destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
        replace (x - 1 - depth) with k' by lia. reflexivity.
    - nat_bool_hyps. unfold unshift_cty; cbn.
      change (Nat.iter depth ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end)) with (r_var depth 0).
      destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |].
      + rewrite r_var_lt by lia. cbn. rewrite (proj2 (Nat.ltb_lt b depth) Hlt). reflexivity.
      + rewrite r_var_gt by lia. cbn.
        rewrite (proj2 (Nat.ltb_ge (b - 1) depth) ltac:(lia)), (proj2 (Nat.ltb_ge b depth) ltac:(lia)).
        destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
        replace (b - 1 - depth) with k' by lia. reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d_any theta H1).
      pose proof (IHT0_2 (S depth) d_any theta H2) as H2'.
      unfold unshift_cty in H2' |- *; cbn [ren_cty eval_dcty] in H2' |- *.
      change (Nat.iter (S depth) ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))
        with (ren_shift (Nat.iter depth ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))) in H2'.
      rewrite H2'. reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d_any theta H1).
      pose proof (IHT0_2 (S depth) d_any theta H2) as H2'.
      unfold unshift_cty in H2' |- *; cbn [ren_cty eval_dcty] in H2' |- *.
      change (Nat.iter (S depth) ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))
        with (ren_shift (Nat.iter depth ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))) in H2'.
      rewrite H2'. reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d_any theta H1), (IHT0_2 depth d_any theta H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      pose proof (Hhd depth d_any theta H1) as Hhd'.
      pose proof (IH Htl H2) as Hr. unfold unshift_cty in Hhd', Hr |- *; cbn in Hhd', Hr |- *.
      rewrite Hhd'. inversion Hr; reflexivity. }
  intros d_any theta Hsafe. exact (Hgen T 0 d_any theta Hsafe).
Qed.

Lemma eval_dcty_subst_cidx_0 : forall (D : JoinDomain) (T : cty D) val d_any theta,
  cty_uses_kinds true false false true true true true 0 T = false ->
  eval_dcty 0 theta (subst_cidx_in_cty 0 val T) = eval_dcty 0 (d_any :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth val d_any theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth theta (subst_cidx_in_cty depth val T0) = eval_dcty depth (d_any :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth val d_any theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth val d_any theta Hsafe));
      try (f_equal; apply (IHT0 depth val d_any theta Hsafe));
      try (apply orb_false_iff in Hsafe as [H1 _]; apply (IHT0 depth val d_any theta H1));
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth val d_any theta H1), (IHT0_2 (S depth) (lift_cidx 0 1 val) d_any theta H2); reflexivity);
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth val d_any theta H1), (IHT0_2 depth val d_any theta H2); reflexivity).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
      replace (x - 1 - depth) with k' by lia. reflexivity.
    - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
      replace (b - 1 - depth) with k' by lia. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth val d_any theta H1), (IH Htl H2). reflexivity. }
  intros val d_any theta Hsafe. exact (Hgen T 0 val d_any theta Hsafe).
Qed.

Lemma eval_dcty_subst_pair_0 : forall (D : JoinDomain) (T : cty D) fi si d_any theta,
  cty_uses_kinds true false false true true true true 0 T = false ->
  eval_dcty 0 theta (subst_pair_cty 0 fi si T) = eval_dcty 0 (d_any :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth fi si d_any theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth theta (subst_pair_cty depth fi si T0) = eval_dcty depth (d_any :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth fi si d_any theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth fi si d_any theta Hsafe));
      try (f_equal; apply (IHT0 depth fi si d_any theta Hsafe));
      try (apply orb_false_iff in Hsafe as [H1 _]; apply (IHT0 depth fi si d_any theta H1));
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth fi si d_any theta H1), (IHT0_2 (S depth) (lift_cidx 0 1 fi) (lift_cidx 0 1 si) d_any theta H2); reflexivity);
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth fi si d_any theta H1), (IHT0_2 depth fi si d_any theta H2); reflexivity).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
      replace (x - 1 - depth) with k' by lia. reflexivity.
    - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
      replace (b - 1 - depth) with k' by lia. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth fi si d_any theta H1), (IH Htl H2). reflexivity. }
  intros fi si d_any theta Hsafe. exact (Hgen T 0 fi si d_any theta Hsafe).
Qed.

Lemma eval_dcty_subst_sum_0 : forall (D : JoinDomain) (T : cty D) is_left val d_any theta,
  cty_uses_kinds true false false true true true true 0 T = false ->
  eval_dcty 0 theta (subst_sum_cty is_left 0 val T) = eval_dcty 0 (d_any :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth is_left val d_any theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth theta (subst_sum_cty is_left depth val T0) = eval_dcty depth (d_any :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth is_left val d_any theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth is_left val d_any theta Hsafe));
      try (f_equal; apply (IHT0 depth is_left val d_any theta Hsafe));
      try (apply orb_false_iff in Hsafe as [H1 _]; apply (IHT0 depth is_left val d_any theta H1));
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth is_left val d_any theta H1), (IHT0_2 (S depth) is_left (lift_cidx 0 1 val) d_any theta H2); reflexivity);
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth is_left val d_any theta H1), (IHT0_2 depth is_left val d_any theta H2); reflexivity).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
      replace (x - 1 - depth) with k' by lia. reflexivity.
    - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
      replace (b - 1 - depth) with k' by lia. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth is_left val d_any theta H1), (IH Htl H2). reflexivity. }
  intros is_left val d_any theta Hsafe. exact (Hgen T 0 is_left val d_any theta Hsafe).
Qed.

Lemma eval_dcty_subst_box_nat_0 : forall (D : JoinDomain) (T : cty D) q val d_any theta,
  cty_uses_kinds true false false true true true true 0 T = false ->
  eval_dcty 0 theta (subst_box_nat_cty 0 q val T) = eval_dcty 0 (d_any :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 : cty D) depth q val d_any theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth theta (subst_box_nat_cty depth q val T0) = eval_dcty depth (d_any :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth qb val d_any theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth qb val d_any theta Hsafe));
      try (f_equal; apply (IHT0 depth qb val d_any theta Hsafe));
      try (apply orb_false_iff in Hsafe as [H1 _]; apply (IHT0 depth qb val d_any theta H1));
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth qb val d_any theta H1), (IHT0_2 (S depth) qb (lift_cidx 0 1 val) d_any theta H2); reflexivity);
      try (apply orb_false_iff in Hsafe as [H1 H2];
           rewrite (IHT0_1 depth qb val d_any theta H1), (IHT0_2 depth qb val d_any theta H2); reflexivity).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
      replace (x - 1 - depth) with k' by lia. reflexivity.
    - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
      replace (b - 1 - depth) with k' by lia. reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth qb val d_any theta H1), (IH Htl H2). reflexivity. }
  intros q val d_any theta Hsafe. exact (Hgen T 0 q val d_any theta Hsafe).
Qed.

Lemma eval_dcty_subst_box_ty_0 : forall (D : JoinDomain) (T U : cty D) q theta,
  cty_uses_kinds true false true true true true true 0 T = false ->
  eval_dcty 0 theta (subst_box_ty_cty 0 q U T) = eval_dcty 0 (DBox q (eval_dcty 0 theta U) :: theta) T.
Proof.
  intros D T.
  assert (Hgen : forall (T0 U0 : cty D) depth q theta,
    cty_uses_kinds true false true true true true true depth T0 = false ->
    eval_dcty depth theta (subst_box_ty_cty depth q (lift_cty 0 depth U0) T0) =
    eval_dcty depth (DBox q (eval_dcty 0 theta U0) :: theta) T0).
  { induction T0 using cty_ind_nested; intros U0 depth qb theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 U0 depth qb theta Hsafe));
      try (f_equal; apply (IHT0 U0 depth qb theta Hsafe)).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
      replace (x - 1 - depth) with k' by lia. reflexivity.
    - destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); cbn.
      + rewrite (proj2 (Nat.ltb_lt b depth) Hlt); reflexivity.
      + rewrite Nat.sub_diag; cbn. pose proof (eval_dcty_ren_shift_lift D U0 0 depth theta) as Hl.
        cbn [Nat.add] in Hl. exact Hl.
      + rewrite (proj2 (Nat.ltb_ge (b - 1) depth) ltac:(lia)); cbn iota.
        destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
        replace (b - 1 - depth) with k' by lia. reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 U0 depth qb theta H1), (lift_cty_add D 1 depth U0).
      replace (1 + depth) with (S depth) by lia.
      rewrite (IHT0_2 U0 (S depth) qb theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 U0 depth qb theta H1), (lift_cty_add D 1 depth U0).
      replace (1 + depth) with (S depth) by lia.
      rewrite (IHT0_2 U0 (S depth) qb theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 U0 depth qb theta H1), (IHT0_2 U0 depth qb theta H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd U0 depth qb theta H1), (IH Htl H2). reflexivity. }
  intros U q theta Hsafe.
  pose proof (Hgen T U 0 q theta Hsafe) as H.
  rewrite lift_cty_0_0 in H. exact H.
Qed.

Lemma eval_dcty_spec_pair_body : forall (D : JoinDomain) (mot : cty D) d1 d2 d3 theta,
  cty_uses_kinds true false false true true true true 0 mot = false ->
  eval_dcty 0 (d2 :: d1 :: theta) (spec_pair_body_cty 0 mot) = eval_dcty 0 (d3 :: theta) mot.
Proof.
  intros D mot.
  assert (Hgen : forall (T0 : cty D) depth d1 d2 d3 theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth (d2 :: d1 :: theta) (spec_pair_body_cty depth T0) =
    eval_dcty depth (d3 :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth d1 d2 d3 theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth d1 d2 d3 theta Hsafe));
      try (f_equal; apply (IHT0 depth d1 d2 d3 theta Hsafe));
      try (apply orb_false_iff in Hsafe as [H1 _]; apply (IHT0 depth d1 d2 d3 theta H1)).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
      replace (match depth with 0 => S x | S l => x - l end) with (S (S k')) by (destruct depth; lia). reflexivity.
    - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
      replace (match depth with 0 => S b | S l => b - l end) with (S (S k')) by (destruct depth; lia). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d1 d2 d3 theta H1), (IHT0_2 (S depth) d1 d2 d3 theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d1 d2 d3 theta H1), (IHT0_2 (S depth) d1 d2 d3 theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d1 d2 d3 theta H1), (IHT0_2 depth d1 d2 d3 theta H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth d1 d2 d3 theta H1), (IH Htl H2). reflexivity. }
  intros d1 d2 d3 theta Hsafe. exact (Hgen mot 0 d1 d2 d3 theta Hsafe).
Qed.

Lemma eval_dcty_spec_box_body : forall (D : JoinDomain) (mot : cty D) q d_unbox theta,
  cty_uses_kinds true false true true true true true 0 mot = false ->
  eval_dcty 0 (d_unbox :: theta) (spec_box_body_cty q 0 mot) = eval_dcty 0 (DBox q d_unbox :: theta) mot.
Proof.
  intros D mot.
  assert (Hgen : forall (T0 : cty D) depth q d_unbox theta,
    cty_uses_kinds true false true true true true true depth T0 = false ->
    eval_dcty depth (d_unbox :: theta) (spec_box_body_cty q depth T0) =
    eval_dcty depth (DBox q d_unbox :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth qb d_unbox theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth qb d_unbox theta Hsafe));
      try (f_equal; apply (IHT0 depth qb d_unbox theta Hsafe)).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia | reflexivity].
    - destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; repeat (rw_nat_bool; cbv iota); cbn.
      + try (rewrite (proj2 (Nat.ltb_lt b depth) Hlt)); reflexivity.
      + rewrite Nat.ltb_irrefl, Nat.sub_diag; reflexivity.
      + try (rewrite (proj2 (Nat.ltb_ge b depth) ltac:(lia))).
        destruct (b - depth) as [| k'] eqn:Hbk; [lia | reflexivity].
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth qb d_unbox theta H1), (IHT0_2 (S depth) qb d_unbox theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth qb d_unbox theta H1), (IHT0_2 (S depth) qb d_unbox theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth qb d_unbox theta H1), (IHT0_2 depth qb d_unbox theta H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth qb d_unbox theta H1), (IH Htl H2). reflexivity. }
  intros q d_unbox theta Hsafe. exact (Hgen mot 0 q d_unbox theta Hsafe).
Qed.

Lemma eval_dcty_spec_sum_branch : forall (D : JoinDomain) (mot : cty D) is_left d1 d2 theta,
  cty_uses_kinds true false false true true true true 0 mot = false ->
  eval_dcty 0 (d1 :: theta) (spec_sum_branch_cty is_left 0 mot) = eval_dcty 0 (d2 :: theta) mot.
Proof.
  intros D mot.
  assert (Hgen : forall (T0 : cty D) depth is_left d1 d2 theta,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth (d1 :: theta) (spec_sum_branch_cty is_left depth T0) =
    eval_dcty depth (d2 :: theta) T0).
  { induction T0 using cty_ind_nested; intros depth is_left d1 d2 theta Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth is_left d1 d2 theta Hsafe));
      try (f_equal; apply (IHT0 depth is_left d1 d2 theta Hsafe)).
    - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (x - depth) as [| k'] eqn:Hxk; [lia | reflexivity].
    - nat_bool_hyps. destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt]; [| contradiction |];
        repeat (rw_nat_bool; cbv iota); cbn; [reflexivity |].
      destruct (b - depth) as [| k'] eqn:Hbk; [lia | reflexivity].
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth is_left d1 d2 theta H1), (IHT0_2 (S depth) is_left d1 d2 theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth is_left d1 d2 theta H1), (IHT0_2 (S depth) is_left d1 d2 theta H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth is_left d1 d2 theta H1), (IHT0_2 depth is_left d1 d2 theta H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth is_left d1 d2 theta H1), (IH Htl H2). reflexivity. }
  intros is_left d1 d2 theta Hsafe. exact (Hgen mot 0 is_left d1 d2 theta Hsafe).
Qed.

Lemma eval_dcty_lift_1_drop : forall (D : JoinDomain) (T : cty D) d0 theta,
  eval_dcty 0 (d0 :: theta) (lift_cty 0 1 T) = eval_dcty 0 theta T.
Proof.
  intros D T d0 theta.
  replace (lift_cty 0 1 T) with (ren_cty (plus 1) T)
    by (unfold lift_cty; apply ren_cty_ext; intro x; unfold ren_lift; destruct (Nat.ltb_spec x 0); cbn; lia).
  rewrite eval_dcty_ren_plus. reflexivity.
Qed.

Inductive DSubty {D : JoinDomain} : @dcty D -> @dcty D -> Prop :=
| DSubRefl : forall d, DSubty d d
| DSubBox : forall q q' A B,
    allows q' q -> DSubty A B -> DSubty (DBox q A) (DBox q' B)
| DSubPi : forall s s' A A' B B',
    allows s s' -> DSubty A' A -> DSubty B B' -> DSubty (DPi s A B) (DPi s' A' B')
| DSubSigma : forall A A' B B',
    DSubty A A' -> DSubty B B' -> DSubty (DSigma A B) (DSigma A' B')
| DSubSum : forall A A' B B',
    DSubty A A' -> DSubty B B' -> DSubty (DSum A B) (DSum A' B')
| DSubVec : DSubty DVec DVec.

Lemma DSubty_trans : forall (D : JoinDomain) (d1 d2 d3 : @dcty D),
  DSubty d1 d2 -> DSubty d2 d3 -> DSubty d1 d3.
Proof.
  intros D d1 d2 d3 H12 H23. revert d1 d3 H12 H23.
  induction d2 using dcty_ind_nested; intros d1 d3 H12 H23;
    inversion H12; subst; try exact H23;
    inversion H23; subst; try exact H12.
  - apply DSubPi; [eapply allows_trans; eassumption | eapply IHd2_1; eassumption | eapply IHd2_2; eassumption].
  - apply DSubSigma; [eapply IHd2_1; eassumption | eapply IHd2_2; eassumption].
  - apply DSubBox; [eapply allows_trans; eassumption | eapply IHd2; eassumption].
  - apply DSubSum; [eapply IHd2_1; eassumption | eapply IHd2_2; eassumption].
Qed.

Lemma DSubty_lift : forall (D : JoinDomain) (d1 d2 : @dcty D) c m,
  DSubty d1 d2 -> DSubty (lift_dcty c m d1) (lift_dcty c m d2).
Proof.
  intros D d1 d2 c m H. revert c m.
  induction H; intros c m; cbn; try constructor; try assumption;
    try (apply IHDSubty); try (apply IHDSubty1); try (apply IHDSubty2).
Qed.

Lemma DSubty_subst : forall (D : JoinDomain) (d1 d2 arg : @dcty D) k,
  DSubty d1 d2 -> DSubty (subst_dcty k arg d1) (subst_dcty k arg d2).
Proof.
  intros D d1 d2 arg k H. revert k arg.
  induction H; intros k arg; cbn; try constructor; try assumption;
    try (apply IHDSubty); try (apply IHDSubty1); try (apply IHDSubty2).
Qed.

Fixpoint dcty_uses_unbox {D : JoinDomain} (k : nat) (d : @dcty D) : bool :=
  match d with
  | DNat | DBool | DVec | DUniv | DBound _ | DInd => false
  | DUnbox idx => idx =? k
  | DPi _ dom cod => dcty_uses_unbox k dom || dcty_uses_unbox (S k) cod
  | DSigma f s => dcty_uses_unbox k f || dcty_uses_unbox (S k) s
  | DBox _ inner => dcty_uses_unbox k inner
  | DSum l r => dcty_uses_unbox k l || dcty_uses_unbox k r
  | DRecord fs =>
      (fix go (xs : list (grade D * @dcty D)) : bool :=
         match xs with
         | [] => false
         | (_, df) :: rest => dcty_uses_unbox k df || go rest
         end) fs
  end.

Lemma dcty_uses_unbox_lift_drop : forall (D : JoinDomain) (d : @dcty D) c m k,
  c <= k -> k < c + m ->
  dcty_uses_unbox k (lift_dcty c m d) = false.
Proof.
  intros D d. induction d using dcty_ind_nested; intros c m k Hc Hkm; cbn in *; try reflexivity;
    try (rewrite IHd1, IHd2 by lia; reflexivity);
    try (apply IHd; lia).
  - destruct (Nat.ltb_spec idx c); reflexivity.
  - destruct (Nat.ltb_spec idx c); cbn; apply Nat.eqb_neq; lia.
  - induction fs as [| [fg df] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in *.
    rewrite (Hhd c m k Hc Hkm), (IH Htl). reflexivity.
Qed.

Lemma DSubty_dcty_uses_unbox : forall (D : JoinDomain) (d1 d2 : @dcty D) k,
  DSubty d1 d2 ->
  dcty_uses_unbox k d1 = dcty_uses_unbox k d2.
Proof.
  intros D d1 d2 k H. revert k.
  induction H; intros k; cbn; try reflexivity;
    try match goal with H1 : forall k0, _, H2 : forall k0, _ |- _ =>
      first [rewrite H1, H2; reflexivity | rewrite <- H1, H2; reflexivity]
    end;
    match goal with H1 : forall k0, _ |- _ => apply H1 end.
Qed.

Lemma Subty_eval_dcty : forall (D : JoinDomain) env A B,
  Subty env A B ->
  forall depth (theta : list (@dcty D)),
    DSubty (eval_dcty depth theta A) (eval_dcty depth theta B).
Proof.
  intros D env A B H.
  induction H; intros depth theta; cbn.
  - rewrite (eval_dcty_alpha_eq D A B depth theta H). apply DSubRefl.
  - apply DSubBox; [exact H | apply IHSubty].
  - apply DSubPi; [exact H | apply IHSubty1 | apply IHSubty2].
  - apply DSubSigma; [apply IHSubty1 | apply IHSubty2].
  - apply DSubSum; [apply IHSubty1 | apply IHSubty2].
  - apply DSubVec.
Qed.

Definition cenv_not_tvar_0 {D : JoinDomain} (env : cenv D) (T : cty D) : Prop :=
  match env with
  | [] => True
  | e0 :: _ =>
      (forall lvl, erase_hints (cannotation e0) <> CUniv lvl) ->
      cty_uses_kinds true false true true true true true 0 T = false
  end.

Lemma cdemand_not_tvar_0 : forall (D : JoinDomain) env (e0 : cbinding D) T d,
  (forall lvl, erase_hints (cannotation e0) <> CUniv lvl) ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds true false true true true true true 0 T = false.
Proof.
  intros D env e0 T d Hnu HT.
  eapply ctype_demand_uses_kinds; [exact HT | reflexivity |].
  unfold flags_allow. rewrite erase_hints_ren.
  destruct (erase_hints (cannotation e0)) eqn:Ee; cbn [ren_cty]; try exact I;
    try reflexivity;
    try (exfalso; eapply Hnu; reflexivity);
    repeat match goal with
    | |- context [match ?x with CNat => _ | _ => _ end] => destruct x
    end; try exact I; repeat split; reflexivity.
Qed.

Lemma cdemand_not_tvar_tunbox_0 : forall (D : JoinDomain) env (e0 : cbinding D) T d,
  (forall lvl, erase_hints (cannotation e0) <> CUniv lvl) ->
  (forall q lvl, erase_hints (cannotation e0) <> CBox q (CUniv lvl)) ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds true false false true true true true 0 T = false.
Proof.
  intros D env e0 T d Hnu Hnb HT.
  eapply ctype_demand_uses_kinds; [exact HT | reflexivity |].
  unfold flags_allow. rewrite erase_hints_ren.
  destruct (erase_hints (cannotation e0)) eqn:Ee; cbn [ren_cty]; try exact I;
    try reflexivity;
    try (exfalso; eapply Hnu; reflexivity).
  - repeat match goal with
    | |- context [match ?x with CNat => _ | _ => _ end] => destruct x
    end; try exact I; repeat split; reflexivity.
  - match goal with
    | |- context [match ren_cty _ ?c with CNat => _ | _ => _ end] => destruct c; cbn [ren_cty]
    end; try exact I; try reflexivity.
    exfalso; eapply Hnb; reflexivity.
Qed.

Lemma cdemand_univ_not_tunbox_0 : forall (D : JoinDomain) env (e0 : cbinding D) lvl T d,
  erase_hints (cannotation e0) = CUniv lvl ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds true true false true true true true 0 T = false.
Proof.
  intros D env e0 lvl T d Hu HT.
  eapply ctype_demand_uses_kinds; [exact HT | reflexivity |].
  unfold flags_allow. rewrite erase_hints_ren, Hu. reflexivity.
Qed.

Fixpoint cidx_no_zero_unbox {D : JoinDomain} (env : cenv D) (i : cidx D) : Prop :=
  match i with
  | CIdxVar _ | CIdxLit _ | CIdxFst _ | CIdxSnd _ => True
  | CIdxAdd l r => cidx_no_zero_unbox env l /\ cidx_no_zero_unbox env r
  | CIdxProm _ inner => cidx_no_zero_unbox env inner
  | CIdxUnbox b =>
      match clookup env b with
      | Some e => match erase_hints (cannotation e) with CBox q _ => q <> zero | _ => False end
      | None => False
      end
  | CIdxCase s l r =>
      match clookup env s with
      | Some e =>
          match erase_hints (cannotation e) with
          | CSum CNat CNat =>
              cidx_no_zero_unbox ({| cbinder := 0; cannotation := CNat; ctype_uses := [] |} :: env) l /\
              cidx_no_zero_unbox ({| cbinder := 0; cannotation := CNat; ctype_uses := [] |} :: env) r
          | _ => False
          end
      | None => False
      end
  end.

Definition record_erasure_aligned {D : JoinDomain} (fields : list (nat * grade D * cty D)) : Prop :=
  Forall2 (fun '(_, g1, _) '(_, g2, _) => g1 = zero <-> g2 = zero) fields (rev fields).

Fixpoint erasure_wf_cterm {D : JoinDomain} (env : cenv D) (t : cterm D) : Prop :=
  match t with
  | CVar _ | CBoolVal _ | CTypeVal _ => True
  | CNatVal i => cidx_no_zero_unbox env i
  | CLam x _ _ dom body =>
      erasure_wf_cterm ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env) body
  | CApp fn arg => erasure_wf_cterm env fn /\ erasure_wf_cterm env arg
  | CLet x _ _ ann rhs body =>
      erasure_wf_cterm env rhs /\
      erasure_wf_cterm ({| cbinder := x; cannotation := ann; ctype_uses := [] |} :: env) body
  | CPair _ _ _ _ fv sv => erasure_wf_cterm env fv /\ erasure_wf_cterm env sv
  | CLetPair x y _ _ _ pr body =>
      erasure_wf_cterm env pr /\
      match cterm_result_type env pr with
      | Some (CSigma _ _ A B) =>
          erasure_wf_cterm
            ({| cbinder := y; cannotation := B; ctype_uses := [] |} ::
             {| cbinder := x; cannotation := A; ctype_uses := [] |} :: env) body
      | _ => True
      end
  | CPromote _ val => erasure_wf_cterm env val
  | CLetBox x _ _ bx body =>
      erasure_wf_cterm env bx /\
      match cterm_result_type env bx with
      | Some (CBox _ A) =>
          erasure_wf_cterm ({| cbinder := x; cannotation := A; ctype_uses := [] |} :: env) body
      | _ => True
      end
  | CInl _ val | CInr _ val | CSubgrade _ val => erasure_wf_cterm env val
  | CMatchSum x y _ _ _ scrut lb rb =>
      erasure_wf_cterm env scrut /\
      match cterm_result_type env scrut with
      | Some (CSum A B) =>
          erasure_wf_cterm ({| cbinder := x; cannotation := A; ctype_uses := [] |} :: env) lb /\
          erasure_wf_cterm ({| cbinder := y; cannotation := B; ctype_uses := [] |} :: env) rb
      | _ => True
      end
  | CIf cond th el =>
      erasure_wf_cterm env cond /\ erasure_wf_cterm env th /\ erasure_wf_cterm env el
  | CRecordMk _ fields =>
      record_erasure_aligned (map (fun '(fn, fg, ft, _) => (fn, fg, ft)) fields) /\
      (fix go_wf (fs : list (nat * grade D * cty D * cterm D)) : Prop :=
         match fs with
         | [] => True
         | (_, _, _, fv) :: rest => erasure_wf_cterm env fv /\ go_wf rest
         end) fields
  | CMatchRecord _ _ _ scrut _ body =>
      erasure_wf_cterm env scrut /\
      match record_fields_ty env scrut with
      | Some fields =>
          record_erasure_aligned fields /\
          erasure_wf_cterm (erase_cterm_extend env fields) body
      | None => True
      end
  | CFix xn xr _ mot scrut base step =>
      erasure_wf_cterm env scrut /\
      erasure_wf_cterm env base /\
      erasure_wf_cterm
        ({| cbinder := xr; cannotation := mot; ctype_uses := [] |} ::
         {| cbinder := xn; cannotation := CNat; ctype_uses := [] |} :: env) step
  end.

Inductive Forall3 {A B C : Type} (P : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
| Forall3_nil : Forall3 P [] [] []
| Forall3_cons : forall a b c la lb lc,
    P a b c -> Forall3 P la lb lc -> Forall3 P (a :: la) (b :: lb) (c :: lc).

Scheme All for Forall3.

Inductive ValRel {D : JoinDomain} : @dcty D -> @crval D -> @ecval D -> Prop :=
| VR_Nat : forall n, ValRel DNat (RNat n) (EVNat n)
| VR_Bool : forall b, ValRel DBool (RBool b) (EVBool b)
| VR_Vec : forall v ev, ValRel DVec v ev
| VR_Univ : forall v ev, ValRel DUniv v ev
| VR_Bound : forall k v ev, ValRel (DBound k) v ev
| VR_Unbox : forall k v ev, ValRel (DUnbox k) v ev
| VR_Ind : forall v ev, ValRel DInd v ev
| VR_Box_Zero : forall inner v ev,
    ValRel (DBox zero inner) (RBox v) (EVBox ev)
| VR_Box : forall q inner v ev,
    q <> zero ->
    ValRel inner v ev ->
    ValRel (DBox q inner) (RBox v) (EVBox ev)
| VR_Sum_Inl : forall l r v ev,
    ValRel l v ev ->
    ValRel (DSum l r) (RInl v) (EVInl ev)
| VR_Sum_Inr : forall l r v ev,
    ValRel r v ev ->
    ValRel (DSum l r) (RInr v) (EVInr ev)
| VR_Pair : forall df ds d_fst v1 v2 ev1 ev2,
    dcty_uses_unbox 0 ds = false ->
    ValRel df v1 ev1 ->
    ValRel (subst_dcty 0 d_fst ds) v2 ev2 ->
    ValRel (DSigma df ds) (RPair v1 v2) (EVPair ev1 ev2)
| VR_Record : forall dfs rfs erfs,
    ValRecordRel dfs rfs erfs ->
    ValRel (DRecord dfs) (RRecord rfs) (EVRecord erfs)
| VR_Clos : forall (env0 : cenv D) theta0 x s0 (r0 : grade D) dom0 cod0 a0 u0 v0 body rho0 erho0
    s ddom dcod,
    ErasureDomain D ->
    CoreDerives ({| cbinder := x; cannotation := dom0; ctype_uses := a0 |} :: env0)
      body {| cresult_type := cod0; ccomp_demand := u0; ctype_demand_row := v0 |} ->
    erasure_wf_cterm ({| cbinder := x; cannotation := dom0; ctype_uses := [] |} :: env0) body ->
    allows (nth_grade u0 0) s0 ->
    length rho0 = length env0 ->
    length erho0 = length env0 ->
    length theta0 = length env0 ->
    (forall y e, nth_error env0 y = Some e -> nth_grade (tl u0) y <> zero ->
       exists vy evy, nth_error rho0 y = Some vy /\ nth_error erho0 y = Some evy /\
         ValRel (eval_dcty 0 (skipn (S y) theta0) (cannotation e)) vy evy) ->
    DSubty (DPi s0 (eval_dcty 0 theta0 dom0) (eval_dcty 1 theta0 cod0)) (DPi s ddom dcod) ->
    ValRel (DPi s ddom dcod) (RClos body rho0)
      (EVClos (negb (grade_eqb s0 zero))
        (erase_cterm ({| cbinder := x; cannotation := dom0; ctype_uses := [] |} :: env0) body) erho0)

with ValRecordRel {D : JoinDomain}
  : list (grade D * @dcty D) -> list (nat * @crval D) -> list (nat * @ecval D) -> Prop :=
| VRR_Nil : ValRecordRel [] [] []
| VRR_Cons : forall fg df fn vr efn evr dfs rfs erfs,
    fn = efn ->
    (fg = zero \/ ValRel df vr evr) ->
    ValRecordRel dfs rfs erfs ->
    ValRecordRel ((fg, df) :: dfs) ((fn, vr) :: rfs) ((efn, evr) :: erfs).

Lemma ValRecordRel_Forall3 : forall (D : JoinDomain) dfs rfs erfs,
  @ValRecordRel D dfs rfs erfs <->
  Forall3 (fun '(fg, df) '(fn, vr) '(efn, evr) => fn = efn /\ (fg = zero \/ ValRel df vr evr)) dfs rfs erfs.
Proof.
  intros D dfs rfs erfs; split; intro H.
  - induction H; constructor; [split; assumption | assumption].
  - induction H as [| [fg df] [fn vr] [efn evr] dfs' rfs' erfs' [Hfn Hvr] Hrest IH];
      constructor; assumption.
Qed.

Definition EnvRel {D : JoinDomain} (theta : list (@dcty D)) (env : cenv D)
    (u : list (grade D)) (rho : list (@crval D)) (erho : list (@ecval D)) : Prop :=
  length rho = length env /\
  length erho = length env /\
  length theta = length env /\
  forall y e,
    nth_error env y = Some e ->
    nth_grade u y <> zero ->
    exists vy evy,
      nth_error rho y = Some vy /\
      nth_error erho y = Some evy /\
      ValRel (eval_dcty 0 (skipn (S y) theta) (cannotation e)) vy evy.

Lemma ValRel_subty : forall (D : JoinDomain),
  ErasureDomain D ->
  forall (d1 d2 : @dcty D) v ev,
    DSubty d1 d2 -> ValRel d1 v ev -> ValRel d2 v ev.
Proof.
  intros D ED d1 d2 v ev Hsub Hv. revert d2 Hsub.
  induction Hv; intros d2 Hsub; inversion Hsub; subst;
    try (solve [constructor; assumption]);
    try (solve [eapply VR_Pair; eassumption]);
    try (solve [eapply VR_Clos; eauto]).
  - lazymatch goal with Ha : allows _ zero |- _ => apply (erasure_allows_zero_eq D ED) in Ha; subst; apply VR_Box_Zero end.
  - destruct (grade_eqb_spec D q' zero);
      [subst q'; apply VR_Box_Zero | apply VR_Box; [exact n | apply IHHv; assumption]].
  - apply VR_Sum_Inl, IHHv; assumption.
  - apply VR_Sum_Inr, IHHv; assumption.
  - lazymatch goal with Ha : DSubty ?A ?A', Hb : DSubty ?B ?B', Hun : dcty_uses_unbox 0 ?B = false |- _ =>
      eapply VR_Pair;
      [ rewrite <- (DSubty_dcty_uses_unbox D _ _ 0 Hb); exact Hun
      | apply IHHv1; exact Ha
      | apply IHHv2, DSubty_subst; exact Hb ]
    end.
  - eapply VR_Clos; eauto.
    lazymatch goal with Hs : DSubty (DPi _ (eval_dcty 0 _ _) _) _ |- _ => eapply DSubty_trans; [exact Hs | exact Hsub] end.
Qed.

Lemma nth_grade_vec_add_safe : forall (D : JoinDomain) (u1 u2 : list (grade D)) y,
  length u1 = length u2 ->
  nth_grade (vec_add u1 u2) y = add (nth_grade u1 y) (nth_grade u2 y).
Proof.
  intros D u1. induction u1 as [| a1 r1 IH]; intros [| a2 r2] y Hlen; cbn in *; try lia;
    [destruct y; cbn; rewrite add_zero; reflexivity |].
  unfold nth_grade, nth_default in *.
  destruct y as [| y']; cbn; [reflexivity | apply IH; lia].
Qed.

Lemma env_rel_add_l : forall (D : JoinDomain) (theta : list (@dcty D)) env u1 u2 rho erho,
  ErasureDomain D ->
  length u1 = length u2 ->
  EnvRel theta env (vec_add u1 u2) rho erho ->
  EnvRel theta env u1 rho erho.
Proof.
  intros D theta env u1 u2 rho erho ED Hlen [Hr [He [Ht H]]].
  repeat split; try assumption.
  intros y e Hlk Hy. apply H; [exact Hlk |].
  intro Hsum. rewrite nth_grade_vec_add_safe in Hsum by exact Hlen.
  apply (erasure_add_zero D ED) in Hsum as [H1 _]. contradiction.
Qed.

Lemma env_rel_add_r : forall (D : JoinDomain) (theta : list (@dcty D)) env u1 u2 rho erho,
  ErasureDomain D ->
  length u1 = length u2 ->
  EnvRel theta env (vec_add u1 u2) rho erho ->
  EnvRel theta env u2 rho erho.
Proof.
  intros D theta env u1 u2 rho erho ED Hlen [Hr [He [Ht H]]].
  repeat split; try assumption.
  intros y e Hlk Hy. apply H; [exact Hlk |].
  intro Hsum. rewrite nth_grade_vec_add_safe in Hsum by exact Hlen.
  apply (erasure_add_zero D ED) in Hsum as [_ H2]. contradiction.
Qed.

Lemma env_rel_scale : forall (D : JoinDomain) (theta : list (@dcty D)) env q u rho erho,
  ErasureDomain D ->
  q <> zero ->
  EnvRel theta env (vec_scale q u) rho erho ->
  EnvRel theta env u rho erho.
Proof.
  intros D theta env q u rho erho ED Hq [Hr [He [Ht H]]].
  repeat split; try assumption.
  intros y e Hlk Hy. apply H; [exact Hlk |].
  intro Hmul. rewrite nth_grade_scale in Hmul.
  apply (erasure_mul_zero D ED) in Hmul as [H1 | H2]; contradiction.
Qed.

Lemma BranchVec_allows_l : forall (D : JoinDomain) (u1 u2 u_br : list (grade D)),
  length u1 = length u2 ->
  BranchVec u1 u2 u_br ->
  vec_allows u1 u_br.
Proof.
  intros D u1 u2 u_br Hlen Hbv.
  unfold BranchVec in Hbv.
  destruct (grade_join D) as [j |] eqn:Hj.
  - subst u_br. apply vec_allows_join_left; assumption.
  - destruct Hbv as [-> ->]. apply vec_allows_refl.
Qed.

Lemma BranchVec_allows_r : forall (D : JoinDomain) (u1 u2 u_br : list (grade D)),
  length u1 = length u2 ->
  BranchVec u1 u2 u_br ->
  vec_allows u2 u_br.
Proof.
  intros D u1 u2 u_br Hlen Hbv.
  unfold BranchVec in Hbv.
  destruct (grade_join D) as [j |] eqn:Hj.
  - subst u_br. apply vec_allows_join_right; assumption.
  - destruct Hbv as [-> ->]. apply vec_allows_refl.
Qed.

Lemma env_rel_branch_l : forall (D : JoinDomain) (theta : list (@dcty D)) env u1 u2 u_br rho erho,
  ErasureDomain D ->
  length u1 = length u2 ->
  BranchVec u1 u2 u_br ->
  EnvRel theta env u_br rho erho ->
  EnvRel theta env u1 rho erho.
Proof.
  intros D theta env u1 u2 u_br rho erho ED Hlen Hbv [Hr [He [Ht H]]].
  repeat split; try assumption.
  intros y e Hlk Hy. apply H; [exact Hlk |].
  intro Hz.
  pose proof (BranchVec_allows_l D u1 u2 u_br Hlen Hbv) as Hal.
  pose proof (vec_allows_nth D _ _ y Hal) as Hny.
  rewrite Hz in Hny.
  apply (erasure_allows_zero_eq D ED) in Hny. contradiction.
Qed.

Lemma env_rel_branch_r : forall (D : JoinDomain) (theta : list (@dcty D)) env u1 u2 u_br rho erho,
  ErasureDomain D ->
  length u1 = length u2 ->
  BranchVec u1 u2 u_br ->
  EnvRel theta env u_br rho erho ->
  EnvRel theta env u2 rho erho.
Proof.
  intros D theta env u1 u2 u_br rho erho ED Hlen Hbv [Hr [He [Ht H]]].
  repeat split; try assumption.
  intros y e Hlk Hy. apply H; [exact Hlk |].
  intro Hz.
  pose proof (BranchVec_allows_r D u1 u2 u_br Hlen Hbv) as Hal.
  pose proof (vec_allows_nth D _ _ y Hal) as Hny.
  rewrite Hz in Hny.
  apply (erasure_allows_zero_eq D ED) in Hny. contradiction.
Qed.

Lemma env_rel_upd_zero : forall (D : JoinDomain) (d0 : @dcty D) (theta : list (@dcty D)) e0 env u0 rho0 erho0 v ev,
  nth_grade u0 0 = zero ->
  length rho0 = length env ->
  length erho0 = length env ->
  length theta = length env ->
  (forall y e, nth_error env y = Some e -> nth_grade (tl u0) y <> zero ->
     exists vy evy, nth_error rho0 y = Some vy /\ nth_error erho0 y = Some evy /\
       ValRel (eval_dcty 0 (skipn (S y) theta) (cannotation e)) vy evy) ->
  EnvRel (d0 :: theta) (e0 :: env) u0 (v :: rho0) (ev :: erho0).
Proof.
  intros D d0 theta e0 env u0 rho0 erho0 v ev Hz Hr He Ht H.
  repeat split; cbn; try lia.
  intros [| y'] e Hlk Hy; cbn in *.
  - contradiction.
  - destruct u0 as [| u0h u0t]; cbn in *; [contradiction |].
    exact (H y' e Hlk Hy).
Qed.

Lemma env_rel_upd_val : forall (D : JoinDomain) (d0 : @dcty D) (theta : list (@dcty D)) e0 env u0 rho0 erho0 v ev,
  ValRel (eval_dcty 0 theta (cannotation e0)) v ev ->
  length rho0 = length env ->
  length erho0 = length env ->
  length theta = length env ->
  (forall y e, nth_error env y = Some e -> nth_grade (tl u0) y <> zero ->
     exists vy evy, nth_error rho0 y = Some vy /\ nth_error erho0 y = Some evy /\
       ValRel (eval_dcty 0 (skipn (S y) theta) (cannotation e)) vy evy) ->
  EnvRel (d0 :: theta) (e0 :: env) u0 (v :: rho0) (ev :: erho0).
Proof.
  intros D d0 theta e0 env u0 rho0 erho0 v ev Hv Hr He Ht H.
  repeat split; cbn; try lia.
  intros [| y'] e Hlk Hy; cbn in *.
  - inversion Hlk; subst e. exists v, ev. split; [reflexivity | split; [reflexivity | exact Hv]].
  - destruct u0 as [| u0h u0t]; cbn in *;
      [apply nth_error_In in Hlk; exfalso; apply Hy; destruct y'; reflexivity |].
    exact (H y' e Hlk Hy).
Qed.

Lemma Forall2_nth_error_both : forall {A B : Type} (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys ->
  forall idx a,
    nth_error xs idx = Some a ->
    exists b, nth_error ys idx = Some b /\ R a b.
Proof.
  intros A B R xs ys Hfor.
  induction Hfor; intros [| idx'] a Hlk; cbn in *; try discriminate.
  - inversion Hlk; subst. exists y; split; [reflexivity | exact H].
  - apply IHHfor; exact Hlk.
Qed.

Lemma cidx_no_zero_unbox_shape_env : forall (D : JoinDomain) (i : cidx D) env1 env2,
  cenv_shape_eq env1 env2 ->
  cidx_no_zero_unbox env1 i ->
  cidx_no_zero_unbox env2 i.
Proof.
  intros D i. induction i; intros env1 env2 Hs Hnz; cbn in *; try exact I.
  - destruct Hnz as [H1 H2]; split; [eapply IHi1; eauto | eapply IHi2; eauto].
  - eapply IHi; eauto.
  - unfold clookup in *.
    destruct (nth_error env1 b) as [e1 |] eqn:E1; [| contradiction].
    pose proof (Forall2_nth_error_both _ _ _ Hs b e1 E1) as [e2 [E2 Hsh]].
    rewrite E2. pose proof (cty_shape_eqb_erase_hints _ _ _ Hsh) as Heh.
    destruct (erase_hints (cannotation e1)), (erase_hints (cannotation e2));
      cbn in Heh; try contradiction; try discriminate; try exact Hnz.
    apply andb_true_iff in Heh as [Hq _]; apply grade_eqb_sound in Hq; subst; exact Hnz.
  - unfold clookup in *.
    destruct (nth_error env1 s) as [e1 |] eqn:E1; [| contradiction].
    pose proof (Forall2_nth_error_both _ _ _ Hs s e1 E1) as [e2 [E2 Hsh]].
    rewrite E2. pose proof (cty_shape_eqb_erase_hints _ _ _ Hsh) as Heh.
    destruct (erase_hints (cannotation e1)), (erase_hints (cannotation e2));
      cbn in Heh; try contradiction; try discriminate.
    lazymatch type of Hnz with
    | match ?a1 with CNat => match ?b1 with CNat => _ | _ => _ end | _ => _ end =>
        lazymatch goal with
        | |- match ?a2 with CNat => match ?b2 with CNat => _ | _ => _ end | _ => _ end =>
            destruct a1, b1; try contradiction; destruct a2, b2; cbn in Heh; try discriminate
        end
    end.
    destruct Hnz as [H1 H2].
    split; [eapply IHi1; [| exact H1] | eapply IHi2; [| exact H2]];
      (constructor; [apply cty_shape_eqb_refl | exact Hs]).
Qed.

Lemma cidx_demand_erased_eval : forall (D : JoinDomain) (theta : list (@dcty D)) (env : cenv D) (i : cidx D) d rho (erho : list (@ecval D)) n,
  ErasureDomain D ->
  cidx_no_zero_unbox env i ->
  CIdxDemand env i d ->
  EnvRel theta env d rho erho ->
  eval_cidx rho i = Some n ->
  eval_ecidx erho i = Some n.
Proof.
  intros D theta env i d rho erho n ED Hnz Hd. revert theta rho erho n.
  induction Hd; intros theta rho erho m Henv Heval; cbn [eval_cidx eval_ecidx cidx_no_zero_unbox] in *.
  - unfold clookup in H. destruct Henv as [_ [_ [_ Hrel]]].
    assert (Hy : @nth_grade D (@vec_single D (length env) x one) x <> zero).
    { rewrite nth_grade_single_eq by (apply nth_error_Some; congruence).
      intro Heq; apply (erasure_one_nonzero D ED); rewrite Heq; apply allows_refl. }
    destruct (Hrel x e H Hy) as [vx [evx [Hrx [Hex Hvx]]]].
    rewrite Hrx, Hex in *. inversion Heval.
    pose proof (eval_dcty_alpha_eq D (cannotation e) CNat 0 (skipn (S x) theta) H0) as Hnat.
    rewrite Hnat in Hvx.
    cbn in Hvx. inversion Hvx; subst.
    inversion H2; subst. reflexivity.
  - inversion Heval; reflexivity.
  - destruct (eval_cidx rho l) eqn:Hl; try discriminate.
    destruct (eval_cidx rho r) eqn:Hr; try discriminate.
    inversion Heval; subst. destruct Hnz as [Hnz1 Hnz2].
    pose proof (cidx_demand_length D _ _ _ Hd1) as Hl1.
    pose proof (cidx_demand_length D _ _ _ Hd2) as Hl2.
    rewrite (IHHd1 Hnz1 _ _ _ _ (env_rel_add_l _ _ _ _ _ _ _ ED (eq_trans Hl1 (eq_sym Hl2)) Henv) Hl).
    rewrite (IHHd2 Hnz2 _ _ _ _ (env_rel_add_r _ _ _ _ _ _ _ ED (eq_trans Hl1 (eq_sym Hl2)) Henv) Hr).
    reflexivity.
  - destruct (grade_eqb_spec D q zero) as [_ | Hq_nz]; [discriminate |].
    apply (IHHd Hnz _ _ _ _ (env_rel_scale _ _ _ q _ _ _ ED Hq_nz Henv) Heval).
  - unfold clookup in H. destruct Henv as [_ [_ [_ Hrel]]].
    assert (Hy : @nth_grade D (@vec_single D (length env) b one) b <> zero).
    { rewrite nth_grade_single_eq by (apply nth_error_Some; congruence).
      intro Heq; apply (erasure_one_nonzero D ED); rewrite Heq; apply allows_refl. }
    destruct (Hrel b e H Hy) as [vb [evb [Hrb [Heb Hvb]]]].
    rewrite Hrb, Heb in *.
    unfold clookup in Hnz. rewrite H in Hnz.
    pose proof (eval_dcty_alpha_eq D (cannotation e) (CBox q CNat) 0 (skipn (S b) theta) H0) as Hbx.
    rewrite Hbx in Hvb.
    cbn in Hvb. inversion Hvb; subst;
      [ exfalso; rewrite (erase_hints_alpha_eq _ _ _ H0) in Hnz; cbn in Hnz; contradiction
      | lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end;
        inversion Heval; subst; reflexivity ].
  - unfold clookup in H. destruct Henv as [_ [_ [_ Hrel]]].
    assert (Hy : @nth_grade D (@vec_single D (length env) p one) p <> zero).
    { rewrite nth_grade_single_eq by (apply nth_error_Some; congruence).
      intro Heq; apply (erasure_one_nonzero D ED); rewrite Heq; apply allows_refl. }
    destruct (Hrel p e H Hy) as [vp [evp [Hrp [Hep Hvp]]]].
    rewrite Hrp, Hep in *.
    pose proof (eval_dcty_alpha_eq D (cannotation e) (CSigma z r CNat snd_ty) 0 (skipn (S p) theta) H0) as Hsg.
    rewrite Hsg in Hvp.
    cbn in Hvp. inversion Hvp; subst.
    lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end.
    inversion Heval; subst. reflexivity.
  - unfold clookup in H. destruct Henv as [_ [_ [_ Hrel]]].
    assert (Hy : @nth_grade D (@vec_single D (length env) p one) p <> zero).
    { rewrite nth_grade_single_eq by (apply nth_error_Some; congruence).
      intro Heq; apply (erasure_one_nonzero D ED); rewrite Heq; apply allows_refl. }
    destruct (Hrel p e H Hy) as [vp [evp [Hrp [Hep Hvp]]]].
    rewrite Hrp, Hep in *.
    pose proof (eval_dcty_alpha_eq D (cannotation e) (CSigma z r fst_ty CNat) 0 (skipn (S p) theta) H0) as Hsg.
    rewrite Hsg in Hvp.
    cbn in Hvp. inversion Hvp; subst.
    assert (Hcnat : subst_dcty 0 d_fst DNat = DNat) by reflexivity.
    rewrite Hcnat in *. cbn in *.
    lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end.
    inversion Heval; subst. reflexivity.
  - unfold clookup in H, Hnz. rewrite H in Hnz.
    destruct (erase_hints (cannotation e)) eqn:Hee; try contradiction.
    lazymatch type of Hnz with
    | match ?a0 with CNat => match ?b0 with CNat => _ | _ => _ end | _ => _ end =>
        destruct a0, b0; try contradiction
    end.
    destruct Hnz as [Hnz1 Hnz2].
    assert (HAB : erase_hints A = CNat /\ erase_hints B = CNat).
    { unfold cty_alpha_eq in H0; rewrite erase_hints_ren, Hee in H0; cbn in H0; inversion H0; split; reflexivity. }
    destruct HAB as [HA HB].
    assert (HnzA : cidx_no_zero_unbox ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length env) |} :: env) l).
    { eapply cidx_no_zero_unbox_shape_env; [| exact Hnz1].
      constructor; [cbn [cannotation]; rewrite cty_shape_eqb_sym, <- cty_shape_eqb_erase_hints_l, HA; reflexivity | apply cenv_shape_eq_refl]. }
    assert (HnzB : cidx_no_zero_unbox ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length env) |} :: env) r).
    { eapply cidx_no_zero_unbox_shape_env; [| exact Hnz2].
      constructor; [cbn [cannotation]; rewrite cty_shape_eqb_sym, <- cty_shape_eqb_erase_hints_l, HB; reflexivity | apply cenv_shape_eq_refl]. }
    destruct Henv as [Hlr [Hle [Hlt Hrel]]].
    pose proof (cidx_demand_length D _ _ _ Hd1) as Hl1.
    pose proof (cidx_demand_length D _ _ _ Hd2) as Hl2.
    cbn [length] in Hl1, Hl2.
    assert (Hlen_tl : length (tl dl) = length (tl dr)) by (destruct dl, dr; cbn in *; lia).
    assert (Hbr_len : length d_br = length env).
    { lazymatch goal with Hbv : BranchVec _ _ d_br |- _ =>
        rewrite (BranchVec_length D _ _ _ Hlen_tl Hbv); destruct dl; cbn in *; lia
      end. }
    assert (Hs : nth_grade (vec_add (vec_single (length env) s one) d_br) s <> zero).
    { rewrite nth_grade_vec_add_safe by (rewrite vec_single_length; lia).
      rewrite nth_grade_single_eq by (apply nth_error_Some; congruence).
      intro Hsum. apply (erasure_add_zero D ED) in Hsum as [H1z _].
      apply (erasure_one_nonzero D ED); rewrite H1z; apply allows_refl. }
    destruct (Hrel s e H Hs) as [vs [evs [Hrs [Hes Hvs]]]].
    rewrite Hrs, Hes in *.
    pose proof (eval_dcty_alpha_eq D (ren_cty (plus (S s)) (cannotation e)) (CSum CNat CNat) 0 theta
                  ltac:(unfold cty_alpha_eq; rewrite erase_hints_ren, Hee; reflexivity)) as Hsm.
    rewrite eval_dcty_ren_plus in Hsm. rewrite Hsm in Hvs.
    cbn in Hvs. inversion Hvs; subst;
      lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end;
      [ eapply IHHd1; [exact HnzA | | exact Heval];
        assert (Henv_br : EnvRel theta env d_br rho erho) by
          (eapply env_rel_add_r; [exact ED | | exact (conj Hlr (conj Hle (conj Hlt Hrel)))]; rewrite vec_single_length; lia);
        destruct dl as [| hd_l tl_l], dr as [| hd_r tl_r]; cbn in *; try lia;
        eapply env_rel_upd_val with (d0 := DUniv);
        [ cbn [cannotation]; rewrite (eval_dcty_alpha_eq D A CNat 0 theta HA); apply VR_Nat
        | exact Hlr | exact Hle | exact Hlt
        | assert (Hdl : EnvRel theta env (tl (hd_l :: tl_l)) rho erho) by (eapply env_rel_branch_l; eauto);
          destruct Hdl as [_ [_ [_ Hdl']]]; exact Hdl' ]
      | eapply IHHd2; [exact HnzB | | exact Heval];
        assert (Henv_br : EnvRel theta env d_br rho erho) by
          (eapply env_rel_add_r; [exact ED | | exact (conj Hlr (conj Hle (conj Hlt Hrel)))]; rewrite vec_single_length; lia);
        destruct dl as [| hd_l tl_l], dr as [| hd_r tl_r]; cbn in *; try lia;
        eapply env_rel_upd_val with (d0 := DUniv);
        [ cbn [cannotation]; rewrite (eval_dcty_alpha_eq D B CNat 0 theta HB); apply VR_Nat
        | exact Hlr | exact Hle | exact Hlt
        | assert (Hdr : EnvRel theta env (tl (hd_r :: tl_r)) rho erho) by (eapply env_rel_branch_r; eauto);
          destruct Hdr as [_ [_ [_ Hdr']]]; exact Hdr' ] ].
Qed.

Lemma cty_uses_kinds_ren_plus : forall (D : JoinDomain) idx tv tu ub fs sn sc k m (T : cty D),
  k < m ->
  cty_uses_kinds idx tv tu ub fs sn sc k (ren_cty (plus m) T) = false.
Proof.
  intros D idx tv tu ub fs sn sc k m T Hkm.
  assert (Hci : forall (i : cidx D) d,
    cidx_uses_kinds idx ub fs sn sc (d + k) (ren_cidx (Nat.iter d ren_shift (plus m)) i) = false).
  { induction i; intros d; cbn; try reflexivity;
      try (rewrite (IHi1 d), (IHi2 d); reflexivity);
      try (apply IHi; exact Hkm).
    - destruct (Nat.ltb_spec x d);
        [ rewrite Nat_iter_ren_shift_lt by lia; destruct idx; [reflexivity | apply Nat.eqb_neq; lia]
        | rewrite Nat_iter_ren_shift_ge by lia; destruct idx; [reflexivity | apply Nat.eqb_neq; lia] ].
    - destruct (Nat.ltb_spec b d);
        [ rewrite Nat_iter_ren_shift_lt by lia; destruct ub; [reflexivity | apply Nat.eqb_neq; lia]
        | rewrite Nat_iter_ren_shift_ge by lia; destruct ub; [reflexivity | apply Nat.eqb_neq; lia] ].
    - destruct (Nat.ltb_spec p d);
        [ rewrite Nat_iter_ren_shift_lt by lia; destruct fs; [reflexivity | apply Nat.eqb_neq; lia]
        | rewrite Nat_iter_ren_shift_ge by lia; destruct fs; [reflexivity | apply Nat.eqb_neq; lia] ].
    - destruct (Nat.ltb_spec p d);
        [ rewrite Nat_iter_ren_shift_lt by lia; destruct sn; [reflexivity | apply Nat.eqb_neq; lia]
        | rewrite Nat_iter_ren_shift_ge by lia; destruct sn; [reflexivity | apply Nat.eqb_neq; lia] ].
    - assert (Hs : (if sc then false else Nat.iter d ren_shift (plus m) s =? d + k) = false).
      { destruct (Nat.ltb_spec s d);
          [ rewrite Nat_iter_ren_shift_lt by lia; destruct sc; [reflexivity | apply Nat.eqb_neq; lia]
          | rewrite Nat_iter_ren_shift_ge by lia; destruct sc; [reflexivity | apply Nat.eqb_neq; lia] ]. }
      pose proof (IHi1 (S d)) as H1.
      pose proof (IHi2 (S d)) as H2.
      change (Nat.iter (S d) ren_shift (plus m)) with (ren_shift (Nat.iter d ren_shift (plus m))) in H1, H2.
      cbn [Nat.add] in H1, H2.
      rewrite Hs, H1, H2. reflexivity. }
  assert (Hct : forall (T0 : cty D) d,
    cty_uses_kinds idx tv tu ub fs sn sc (d + k) (ren_cty (Nat.iter d ren_shift (plus m)) T0) = false).
  { induction T0 using cty_ind_nested; intros d; cbn; try reflexivity;
      try (apply IHT0);
      try (rewrite (IHT0_1 d), (IHT0_2 d); reflexivity).
    - rewrite (IHT0 d), (Hci len d); reflexivity.
    - destruct (Nat.ltb_spec x d);
        [ rewrite Nat_iter_ren_shift_lt by lia; destruct tv; [reflexivity | apply Nat.eqb_neq; lia]
        | rewrite Nat_iter_ren_shift_ge by lia; destruct tv; [reflexivity | apply Nat.eqb_neq; lia] ].
    - destruct (Nat.ltb_spec b d);
        [ rewrite Nat_iter_ren_shift_lt by lia; destruct tu; [reflexivity | apply Nat.eqb_neq; lia]
        | rewrite Nat_iter_ren_shift_ge by lia; destruct tu; [reflexivity | apply Nat.eqb_neq; lia] ].
    - rewrite (IHT0_1 d).
      pose proof (IHT0_2 (S d)) as H2.
      change (Nat.iter (S d) ren_shift (plus m)) with (ren_shift (Nat.iter d ren_shift (plus m))) in H2.
      cbn [Nat.add] in H2.
      rewrite H2; reflexivity.
    - rewrite (IHT0_1 d).
      pose proof (IHT0_2 (S d)) as H2.
      change (Nat.iter (S d) ren_shift (plus m)) with (ren_shift (Nat.iter d ren_shift (plus m))) in H2.
      cbn [Nat.add] in H2.
      rewrite H2; reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. rewrite (Hhd d), (IH Htl); reflexivity.
    - induction indices as [| idx0 rest IH]; cbn; [reflexivity |].
      rewrite (Hci idx0 d), IH; reflexivity. }
  exact (Hct T 0).
Qed.

Lemma cidx_uses_kinds_all_true : forall (D : JoinDomain) k (i : cidx D),
  cidx_uses_kinds true true true true true k i = false.
Proof.
  intros D k i. revert k. induction i; intros k; cbn;
    try reflexivity;
    try (rewrite IHi1, IHi2; reflexivity);
    try (apply IHi).
Qed.

Lemma cty_uses_kinds_ren_ne : forall (D : JoinDomain) (V : cty D) (rho : nat -> nat) tv tu d d',
  (forall y, y <> d -> rho y <> d') ->
  cty_uses_kinds true tv tu true true true true d V = false ->
  cty_uses_kinds true tv tu true true true true d' (ren_cty rho V) = false.
Proof.
  intros D V. induction V using cty_ind_nested; intros rho tv tu d d' Hne HV; cbn in *; try reflexivity;
    try (apply (IHV rho tv tu d d' Hne HV));
    try (apply orb_false_iff in HV as [H1 H2]; rewrite (IHV1 rho tv tu d d' Hne H1), (IHV2 rho tv tu d d' Hne H2); reflexivity).
  - apply orb_false_iff in HV as [H1 H2]. rewrite (IHV rho tv tu d d' Hne H1), cidx_uses_kinds_all_true. reflexivity.
  - destruct tv; [reflexivity | apply Nat.eqb_neq, Hne; apply Nat.eqb_neq; exact HV].
  - destruct tu; [reflexivity | apply Nat.eqb_neq, Hne; apply Nat.eqb_neq; exact HV].
  - apply orb_false_iff in HV as [H1 H2].
    assert (Hne_S : forall y, y <> S d -> ren_shift rho y <> S d') by
      (intros [| y'] Hy; cbn; [lia | intro Heq; injection Heq; apply Hne; lia]).
    rewrite (IHV1 rho tv tu d d' Hne H1), (IHV2 (ren_shift rho) tv tu (S d) (S d') Hne_S H2). reflexivity.
  - apply orb_false_iff in HV as [H1 H2].
    assert (Hne_S : forall y, y <> S d -> ren_shift rho y <> S d') by
      (intros [| y'] Hy; cbn; [lia | intro Heq; injection Heq; apply Hne; lia]).
    rewrite (IHV1 rho tv tu d d' Hne H1), (IHV2 (ren_shift rho) tv tu (S d) (S d') Hne_S H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HV as [H1 H2].
    rewrite (Hhd rho tv tu d d' Hne H1), (IH Htl H2). reflexivity.
  - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
    rewrite cidx_uses_kinds_all_true; cbn; apply IH; exact eq_refl || (apply orb_false_iff in HV as [_ HV]; exact HV).
Qed.

Lemma cty_uses_kinds_lift_0_1 : forall (D : JoinDomain) (V : cty D) tv tu d,
  cty_uses_kinds true tv tu true true true true d V = false ->
  cty_uses_kinds true tv tu true true true true (S d) (lift_cty 0 1 V) = false.
Proof.
  intros D V tv tu d HV. unfold lift_cty.
  eapply cty_uses_kinds_ren_ne; [| exact HV].
  intros y Hy. unfold ren_lift. destruct (Nat.ltb_spec y 0); lia.
Qed.

Lemma cty_uses_kinds_subst_tvar_drop : forall (D : JoinDomain) (T U : cty D) c tv tu,
  (tu = true \/ c > 0 \/ cty_uses_kinds true true false true true true true 0 T = false) ->
  cty_uses_kinds true tv tu true true true true c U = false ->
  cty_uses_kinds true tv tu true true true true (S c) T = false ->
  cty_uses_kinds true tv tu true true true true c (subst_tvar_in_cty c U T) = false.
Proof.
  intros D T U c tv tu Htun HU HT.
  assert (Hgen : forall (T0 U0 : cty D) c0,
    (tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 T0 = false) ->
    cty_uses_kinds true tv tu true true true true c0 U0 = false ->
    cty_uses_kinds true tv tu true true true true (S c0) T0 = false ->
    cty_uses_kinds true tv tu true true true true c0 (subst_tvar_in_cty c0 U0 T0) = false).
  { induction T0 using cty_ind_nested; intros U0 c0 Htu0 HU0 HT0; cbn in *; try reflexivity;
      try (apply IHT0; [destruct Htu0 as [? | [? | ?]]; auto | exact HU0 | exact HT0]);
      try (apply orb_false_iff in HT0 as [H1 H2];
           assert (Htu1 : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 T0_1 = false) by
             (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [? _]; exact H]);
           assert (Htu2 : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 T0_2 = false) by
             (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [_ ?]; exact H]);
           rewrite (IHT0_1 U0 c0 Htu1 HU0 H1), (IHT0_2 U0 c0 Htu2 HU0 H2); reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Htu1 : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 T0 = false) by
        (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [? _]; exact H]).
      rewrite (IHT0 U0 c0 Htu1 HU0 H1), cidx_uses_kinds_all_true. reflexivity.
    - destruct (lt_eq_lt_dec x c0) as [[Hlt | ->] | Hgt].
      + rewrite (proj2 (Nat.eqb_neq x c0) ltac:(lia)), (proj2 (Nat.ltb_lt x c0) Hlt).
        cbn. destruct tv; [reflexivity | apply Nat.eqb_neq; lia].
      + rewrite Nat.eqb_refl. exact HU0.
      + rewrite (proj2 (Nat.eqb_neq x c0) ltac:(lia)), (proj2 (Nat.ltb_ge x c0) ltac:(lia)).
        cbn. destruct tv; [reflexivity |].
        destruct (Nat.eq_dec x (S c0)) as [-> | Hne];
          [rewrite Nat.eqb_refl in HT0; discriminate | apply Nat.eqb_neq; lia].
    - destruct (lt_eq_lt_dec b c0) as [[Hlt | Heq] | Hgt].
      + rewrite (proj2 (Nat.eqb_neq b c0) ltac:(lia)), (proj2 (Nat.ltb_lt b c0) Hlt).
        cbn. destruct tu; [reflexivity | apply Nat.eqb_neq; lia].
      + rewrite Heq, Nat.ltb_irrefl, Nat.eqb_refl. cbn. destruct tu; [reflexivity |].
        destruct (Nat.eqb_spec c0 0) as [Hc0 | Hc0]; [| apply Nat.eqb_neq; lia].
        rewrite Heq, Hc0 in *.
        destruct Htu0 as [? | [? | Htu0]]; [discriminate | lia |].
        cbn in Htu0; discriminate.
      + rewrite (proj2 (Nat.eqb_neq b c0) ltac:(lia)), (proj2 (Nat.ltb_ge b c0) ltac:(lia)).
        cbn. destruct tu; [reflexivity |].
        destruct (Nat.eq_dec b (S c0)) as [-> | Hne];
          [rewrite Nat.eqb_refl in HT0; discriminate | apply Nat.eqb_neq; lia].
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Htu1 : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 T0_1 = false) by
        (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [? _]; exact H]).
      rewrite (IHT0_1 U0 c0 Htu1 HU0 H1).
      pose proof (cty_uses_kinds_lift_0_1 D U0 tv tu c0 HU0) as HU1.
      rewrite (IHT0_2 _ (S c0) ltac:(right; left; lia) HU1 H2). reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Htu1 : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 T0_1 = false) by
        (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [? _]; exact H]).
      rewrite (IHT0_1 U0 c0 Htu1 HU0 H1).
      pose proof (cty_uses_kinds_lift_0_1 D U0 tv tu c0 HU0) as HU1.
      rewrite (IHT0_2 _ (S c0) ltac:(right; left; lia) HU1 H2). reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      assert (Htu1 : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 ft = false) by
        (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [Hft _]; exact Hft]).
      assert (Htu_r : tu = true \/ c0 > 0 \/ cty_uses_kinds true true false true true true true 0 (CRecord id rest) = false) by
        (destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [_ Hrest]; exact Hrest]).
      rewrite (Hhd U0 c0 Htu1 HU0 H1), (IH Htl Htu_r H2); reflexivity.
    - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
      rewrite cidx_uses_kinds_all_true; cbn; apply IH;
        [destruct Htu0 as [? | [? | Htu0]]; [left; auto | right; left; auto | right; right; cbn in Htu0; apply orb_false_iff in Htu0 as [_ Hrest]; exact Hrest]
        | apply orb_false_iff in HT0 as [_ Hrest]; exact Hrest]. }
  exact (Hgen T U c Htun HU HT).
Qed.

Lemma cdemand_box_univ_0 : forall (D : JoinDomain) env (e0 : cbinding D) q lvl T d,
  erase_hints (cannotation e0) = CBox q (CUniv lvl) ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds true false true true true true true 0 T = false.
Proof.
  intros D env e0 q lvl T d Hb HT.
  eapply ctype_demand_uses_kinds; [exact HT | reflexivity |].
  unfold flags_allow. rewrite erase_hints_ren, Hb. reflexivity.
Qed.

Lemma cdemand_box_any_0 : forall (D : JoinDomain) env (e0 : cbinding D) q A T d,
  erase_hints (cannotation e0) = CBox q A ->
  CTypeDemand (e0 :: env) T d ->
  cty_uses_kinds true false true true true true true 0 T = false.
Proof.
  intros D env e0 q A T d Hb HT.
  eapply ctype_demand_uses_kinds; [exact HT | reflexivity |].
  unfold flags_allow. rewrite erase_hints_ren, Hb.
  cbn [ren_cty]. destruct (ren_cty (plus 1) A); try exact I; reflexivity.
Qed.

Lemma cty_uses_kinds_subst_tvar_at0_drop : forall (D : JoinDomain) (T U : cty D) tv tu k,
  (tu = true \/ k > 0 \/ cty_uses_kinds true true false true true true true 0 T = false) ->
  cty_uses_kinds true tv tu true true true true k U = false ->
  cty_uses_kinds true tv tu true true true true (S k) T = false ->
  cty_uses_kinds true tv tu true true true true k (subst_tvar_in_cty 0 (lift_cty 0 0 U) T) = false.
Proof.
  intros D T U tv tu [| k'] Htu HU HT.
  - rewrite lift_cty_0_0 in *. exact (cty_uses_kinds_subst_tvar_drop D T U 0 tv tu Htu HU HT).
  - rewrite lift_cty_0_0 in *.
    assert (Hgen : forall (T0 U0 : cty D) c k0,
      c < k0 ->
      cty_uses_kinds true tv tu true true true true k0 U0 = false ->
      cty_uses_kinds true tv tu true true true true (S k0) T0 = false ->
      cty_uses_kinds true tv tu true true true true k0 (subst_tvar_in_cty c U0 T0) = false).
    { induction T0 using cty_ind_nested; intros U0 c k0 Hck HU0 HT0; cbn in *; try reflexivity;
        try (apply IHT0; assumption);
        try (apply orb_false_iff in HT0 as [H1 H2]; rewrite (IHT0_1 U0 c k0 Hck HU0 H1), (IHT0_2 U0 c k0 Hck HU0 H2); reflexivity).
      - apply orb_false_iff in HT0 as [H1 H2]. rewrite (IHT0 U0 c k0 Hck HU0 H1), cidx_uses_kinds_all_true. reflexivity.
      - destruct (lt_eq_lt_dec x c) as [[Hlt | Heq] | Hgt].
        + rewrite (proj2 (Nat.eqb_neq x c) ltac:(lia)), (proj2 (Nat.ltb_lt x c) Hlt).
          cbn. destruct tv; [reflexivity | apply Nat.eqb_neq; lia].
        + subst x. rewrite Nat.eqb_refl. exact HU0.
        + rewrite (proj2 (Nat.eqb_neq x c) ltac:(lia)), (proj2 (Nat.ltb_ge x c) ltac:(lia)).
          cbn. destruct tv; [reflexivity |].
          destruct (Nat.eq_dec x (S k0)) as [-> | Hne];
            [rewrite Nat.eqb_refl in HT0; discriminate | apply Nat.eqb_neq; lia].
      - destruct (lt_eq_lt_dec b c) as [[Hlt | Heq] | Hgt].
        + rewrite (proj2 (Nat.ltb_lt b c) Hlt). cbn. destruct tu; [reflexivity | apply Nat.eqb_neq; lia].
        + subst b. rewrite Nat.ltb_irrefl, Nat.eqb_refl. cbn. destruct tu; [reflexivity | apply Nat.eqb_neq; lia].
        + rewrite (proj2 (Nat.ltb_ge b c) ltac:(lia)), (proj2 (Nat.eqb_neq b c) ltac:(lia)).
          cbn. destruct tu; [reflexivity |].
          destruct (Nat.eq_dec b (S k0)) as [-> | Hne];
            [rewrite Nat.eqb_refl in HT0; discriminate | apply Nat.eqb_neq; lia].
      - apply orb_false_iff in HT0 as [H1 H2]. rewrite (IHT0_1 U0 c k0 Hck HU0 H1).
        pose proof (cty_uses_kinds_lift_0_1 D U0 tv tu k0 HU0) as HU1.
        rewrite (IHT0_2 (lift_cty 0 1 U0) (S c) (S k0) ltac:(lia) HU1 H2). reflexivity.
      - apply orb_false_iff in HT0 as [H1 H2]. rewrite (IHT0_1 U0 c k0 Hck HU0 H1).
        pose proof (cty_uses_kinds_lift_0_1 D U0 tv tu k0 HU0) as HU1.
        rewrite (IHT0_2 (lift_cty 0 1 U0) (S c) (S k0) ltac:(lia) HU1 H2). reflexivity.
      - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
        inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
        rewrite (Hhd U0 c k0 Hck HU0 H1), (IH Htl H2); reflexivity.
      - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
        rewrite cidx_uses_kinds_all_true; cbn; apply IH; apply orb_false_iff in HT0 as [_ Hrest]; exact Hrest. }
    exact (Hgen T U 0 (S k') ltac:(lia) HU HT).
Qed.

Lemma cty_uses_var_0_uses_kinds : forall (D : JoinDomain) (T : cty D) k,
  cty_uses_var k T = false ->
  cty_uses_kinds true false false true true true true k T = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros k HT; cbn in *; try reflexivity;
    try (apply IHT; exact HT);
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 k H1), (IHT2 k H2); reflexivity);
    try (apply orb_false_iff in HT as [H1 H2]; rewrite (IHT1 k H1), (IHT2 (S k) H2); reflexivity).
  - apply orb_false_iff in HT as [H1 H2]. rewrite (IHT k H1), cidx_uses_kinds_all_true. reflexivity.
  - exact HT.
  - exact HT.
  - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd.
    apply orb_false_iff in HT as [H1 H2].
    rewrite (Hhd k H1), (IH Htl H2). reflexivity.
  - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in HT as [_ H2].
    rewrite cidx_uses_kinds_all_true. exact (IH H2).
Qed.

Lemma cty_uses_kinds_subst_cidx_at0_drop : forall (D : JoinDomain) (T : cty D) val tv tu k,
  (k > 0 \/ cty_uses_kinds true false false true true true true 0 T = false) ->
  cty_uses_kinds true tv tu true true true true (S k) T = false ->
  cty_uses_kinds true tv tu true true true true k (subst_cidx_in_cty 0 val T) = false.
Proof.
  intros D T val tv tu k Hk HT.
  assert (Hgen : forall (T0 : cty D) c k0 val0,
    c <= k0 ->
    (k0 > 0 \/ cty_uses_kinds true false false true true true true 0 T0 = false) ->
    cty_uses_kinds true tv tu true true true true (S k0) T0 = false ->
    cty_uses_kinds true tv tu true true true true k0 (subst_cidx_in_cty c val0 T0) = false).
  { induction T0 using cty_ind_nested; intros c k0 val0 Hck Hk0 HT0; cbn in *; try reflexivity;
      try (apply (IHT0 c k0 val0 Hck Hk0 HT0));
      try (apply orb_false_iff in HT0 as [H1 H2];
           assert (Hk1 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 T0_1 = false) by
             (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]);
           assert (Hk2 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 T0_2 = false) by
             (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]);
           rewrite (IHT0_1 c k0 val0 Hck Hk1 H1), (IHT0_2 c k0 val0 Hck Hk2 H2); reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 T0 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0 c k0 val0 Hck Hk1 H1), cidx_uses_kinds_all_true. reflexivity.
    - destruct tv; [reflexivity |].
      destruct (lt_eq_lt_dec x c) as [[Hlt | ->] | Hgt];
        [ rewrite (proj2 (Nat.ltb_lt x c) Hlt); cbn; apply Nat.eqb_neq; lia
        | rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn;
          destruct (Nat.eq_dec k0 0) as [-> | Hk0_nz];
          [ assert (c = 0) by lia; subst; destruct Hk0 as [? | H0]; [lia | cbn in H0; exact H0]
          | apply Nat.eqb_neq; lia ]
        | rewrite (proj2 (Nat.ltb_ge x c) ltac:(lia)), (proj2 (Nat.eqb_neq x c) ltac:(lia)); cbn;
          nat_bool_hyps; apply Nat.eqb_neq; lia ].
    - destruct tu; [reflexivity |].
      destruct (lt_eq_lt_dec b c) as [[Hlt | ->] | Hgt];
        [ rewrite (proj2 (Nat.ltb_lt b c) Hlt); cbn; apply Nat.eqb_neq; lia
        | rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn;
          destruct (Nat.eq_dec k0 0) as [-> | Hk0_nz];
          [ assert (c = 0) by lia; subst; destruct Hk0 as [? | H0]; [lia | cbn in H0; exact H0]
          | apply Nat.eqb_neq; lia ]
        | rewrite (proj2 (Nat.ltb_ge b c) ltac:(lia)), (proj2 (Nat.eqb_neq b c) ltac:(lia)); cbn;
          nat_bool_hyps; apply Nat.eqb_neq; lia ].
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 T0_1 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0_1 c k0 val0 Hck Hk1 H1), (IHT0_2 (S c) (S k0) (lift_cidx 0 1 val0) ltac:(lia) ltac:(left; lia) H2); reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 T0_1 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0_1 c k0 val0 Hck Hk1 H1), (IHT0_2 (S c) (S k0) (lift_cidx 0 1 val0) ltac:(lia) ltac:(left; lia) H2); reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 ft = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hk2 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 (CRecord id rest) = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (Hhd c k0 val0 Hck Hk1 H1), (IH Htl Hk2 H2); reflexivity.
    - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [_ HT0].
      assert (Hk2 : k0 > 0 \/ cty_uses_kinds true false false true true true true 0 (CInd id rest) = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (IH Hk2 HT0), cidx_uses_kinds_all_true. reflexivity. }
  exact (Hgen T 0 k val ltac:(lia) Hk HT).
Qed.

Lemma cty_uses_kinds_unshift_at0_drop : forall (D : JoinDomain) (T : cty D) tv tu k,
  (k > 0 \/ cty_uses_kinds true false false true true true true 0 T = false) ->
  cty_uses_kinds true tv tu true true true true (S k) T = false ->
  cty_uses_kinds true tv tu true true true true k (unshift_cty 0 T) = false.
Proof.
  intros D T tv tu k Hk HT.
  assert (Hgen : forall (T0 : cty D) c k0,
    c <= k0 ->
    (c < k0 \/ cty_uses_kinds true false false true true true true c T0 = false) ->
    cty_uses_kinds true tv tu true true true true (S k0) T0 = false ->
    cty_uses_kinds true tv tu true true true true k0 (unshift_cty c T0) = false).
  { induction T0 using cty_ind_nested; intros c k0 Hck Hk0 HT0; unfold unshift_cty; cbn in *; try reflexivity;
      try (apply (IHT0 c k0 Hck Hk0 HT0));
      try (apply orb_false_iff in HT0 as [H1 H2];
           assert (Hk1 : c < k0 \/ cty_uses_kinds true false false true true true true c T0_1 = false) by
             (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]);
           assert (Hk2 : c < k0 \/ cty_uses_kinds true false false true true true true c T0_2 = false) by
             (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]);
           pose proof (IHT0_1 c k0 Hck Hk1 H1) as Hr1;
           pose proof (IHT0_2 c k0 Hck Hk2 H2) as Hr2;
           unfold unshift_cty in Hr1, Hr2;
           rewrite Hr1, Hr2; reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c < k0 \/ cty_uses_kinds true false false true true true true c T0 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      pose proof (IHT0 c k0 Hck Hk1 H1) as H1'. unfold unshift_cty in H1'.
      rewrite H1', cidx_uses_kinds_all_true. reflexivity.
    - change (Nat.iter c ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      destruct tv; [reflexivity |].
      destruct (lt_eq_lt_dec x c) as [[? | ->] | ?];
        [ rewrite r_var_lt by lia; cbn; apply Nat.eqb_neq; lia
        | rewrite r_var_eq by lia; cbn;
          destruct Hk0 as [Hk0 | H0]; [apply Nat.eqb_neq; lia | cbn in H0; rewrite Nat.eqb_refl in H0; discriminate]
        | rewrite r_var_gt by lia; cbn; nat_bool_hyps; apply Nat.eqb_neq; lia ].
    - change (Nat.iter c ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end)) with (r_var c 0).
      destruct tu; [reflexivity |].
      destruct (lt_eq_lt_dec b c) as [[? | ->] | ?];
        [ rewrite r_var_lt by lia; cbn; apply Nat.eqb_neq; lia
        | rewrite r_var_eq by lia; cbn;
          destruct Hk0 as [Hk0 | H0]; [apply Nat.eqb_neq; lia | cbn in H0; rewrite Nat.eqb_refl in H0; discriminate]
        | rewrite r_var_gt by lia; cbn; nat_bool_hyps; apply Nat.eqb_neq; lia ].
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c < k0 \/ cty_uses_kinds true false false true true true true c T0_1 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hk2 : S c < S k0 \/ cty_uses_kinds true false false true true true true (S c) T0_2 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      pose proof (IHT0_1 c k0 Hck Hk1 H1) as H1'. pose proof (IHT0_2 (S c) (S k0) ltac:(lia) Hk2 H2) as H2'.
      unfold unshift_cty in H1', H2'.
      change (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))) in H2'.
      rewrite H1', H2'; reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c < k0 \/ cty_uses_kinds true false false true true true true c T0_1 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hk2 : S c < S k0 \/ cty_uses_kinds true false false true true true true (S c) T0_2 = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      pose proof (IHT0_1 c k0 Hck Hk1 H1) as H1'. pose proof (IHT0_2 (S c) (S k0) ltac:(lia) Hk2 H2) as H2'.
      unfold unshift_cty in H1', H2'.
      change (Nat.iter (S c) ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i : nat => match i with 0 => 0 | S i' => i' end))) in H2'.
      rewrite H1', H2'; reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c < k0 \/ cty_uses_kinds true false false true true true true c ft = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hk2 : c < k0 \/ cty_uses_kinds true false false true true true true c (CRecord id rest) = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      pose proof (Hhd c k0 Hck Hk1 H1) as Hhd'. pose proof (IH Htl Hk2 H2) as Hr.
      unfold unshift_cty in Hhd', Hr. rewrite Hhd'. cbn in Hr. exact Hr.
    - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [_ HT0].
      assert (Hk2 : c < k0 \/ cty_uses_kinds true false false true true true true c (CInd id rest) = false) by
        (destruct Hk0 as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      pose proof (IH Hk2 HT0) as Hr. unfold unshift_cty in Hr; cbn in Hr; rewrite Hr, cidx_uses_kinds_all_true. reflexivity. }
  exact (Hgen T 0 k ltac:(lia) Hk HT).
Qed.

Lemma cty_uses_kinds_subst_var_at0_drop : forall (D : JoinDomain) (T : cty D) y tv tu k,
  (y <> k \/ cty_uses_kinds true tv tu true true true true 0 T = false) ->
  cty_uses_kinds true tv tu true true true true (S k) T = false ->
  cty_uses_kinds true tv tu true true true true k (subst_var_in_cty 0 y T) = false.
Proof.
  intros D T y tv tu k Hy HT.
  assert (Hgen : forall (T0 : cty D) c k0 y0,
    c <= k0 ->
    (y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c T0 = false) ->
    cty_uses_kinds true tv tu true true true true (S k0) T0 = false ->
    cty_uses_kinds true tv tu true true true true k0
      (ren_cty (Nat.iter c ren_shift (fun i => match i with 0 => y0 | S i' => i' end)) T0) = false).
  { induction T0 using cty_ind_nested; intros c k0 y0 Hck Hne HT0; cbn in *; try reflexivity;
      try (apply (IHT0 c k0 y0 Hck Hne HT0));
      try (apply orb_false_iff in HT0 as [H1 H2];
           assert (Hne1 : y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c T0_1 = false) by
             (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [? _]; right; assumption]);
           assert (Hne2 : y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c T0_2 = false) by
             (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [_ ?]; right; assumption]);
           rewrite (IHT0_1 c k0 y0 Hck Hne1 H1), (IHT0_2 c k0 y0 Hck Hne2 H2); reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hne1 : y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c T0 = false) by
        (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0 c k0 y0 Hck Hne1 H1), cidx_uses_kinds_all_true. reflexivity.
    - destruct (Nat.ltb_spec x c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); destruct tv; cbn in *; try reflexivity; apply Nat.eqb_neq; lia
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (x - c) eqn:Hx;
          [ destruct tv; cbn in *; try reflexivity; destruct Hne as [Hne | H0];
            [apply Nat.eqb_neq; lia | nat_bool_hyps; lia]
          | destruct tv; cbn in *; try reflexivity; nat_bool_hyps; apply Nat.eqb_neq; lia ] ].
    - destruct (Nat.ltb_spec b c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); destruct tu; cbn in *; try reflexivity; apply Nat.eqb_neq; lia
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (b - c) eqn:Hb;
          [ destruct tu; cbn in *; try reflexivity; destruct Hne as [Hne | H0];
            [apply Nat.eqb_neq; lia | nat_bool_hyps; lia]
          | destruct tu; cbn in *; try reflexivity; nat_bool_hyps; apply Nat.eqb_neq; lia ] ].
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hne1 : y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c T0_1 = false) by
        (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hne2 : y0 <> S k0 - S c \/ cty_uses_kinds true tv tu true true true true (S c) T0_2 = false) by
        (destruct Hne as [H0 | H0]; [left; cbn; exact H0 | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (IHT0_1 c k0 y0 Hck Hne1 H1).
      pose proof (IHT0_2 (S c) (S k0) y0 ltac:(lia) Hne2 H2) as H2'.
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => y0 | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i => match i with 0 => y0 | S i' => i' end))) in H2'.
      rewrite H2'. reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hne1 : y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c T0_1 = false) by
        (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hne2 : y0 <> S k0 - S c \/ cty_uses_kinds true tv tu true true true true (S c) T0_2 = false) by
        (destruct Hne as [H0 | H0]; [left; cbn; exact H0 | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (IHT0_1 c k0 y0 Hck Hne1 H1).
      pose proof (IHT0_2 (S c) (S k0) y0 ltac:(lia) Hne2 H2) as H2'.
      change (Nat.iter (S c) ren_shift (fun i => match i with 0 => y0 | S i' => i' end))
        with (ren_shift (Nat.iter c ren_shift (fun i => match i with 0 => y0 | S i' => i' end))) in H2'.
      rewrite H2'. reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      assert (Hne1 : y0 <> k0 - c \/ cty_uses_kinds true tv tu true true true true c ft = false) by
        (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hne2 : y0 <> k0 - c \/ (fix go_fs (fs : list (nat * grade D * cty D)) : bool :=
        match fs with [] => false | (_, _, ft0) :: r0 => cty_uses_kinds true tv tu true true true true c ft0 || go_fs r0 end) rest = false) by
        (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (Hhd c k0 y0 Hck Hne1 H1), (IH Htl Hne2 H2); reflexivity.
    - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [_ HT0].
      assert (Hne2 : y0 <> k0 - c \/ (fix go_is (ls : list (cidx D)) : bool :=
        match ls with [] => false | hd :: r0 => cidx_uses_kinds true true true true true c hd || go_is r0 end) rest = false) by
        (destruct Hne as [H0 | H0]; [left; exact H0 | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (IH Hne2 HT0), cidx_uses_kinds_all_true. reflexivity. }
  replace k with (k - 0) in Hy by lia.
  exact (Hgen T 0 k y ltac:(lia) Hy HT).
Qed.

Lemma cty_uses_kinds_subst_box_ty_at0_drop : forall (D : JoinDomain) (T U : cty D) q tv tu k,
  (k > 0 \/ cty_uses_kinds true false true true true true true 0 T = false) ->
  cty_uses_kinds true tv tu true true true true k U = false ->
  cty_uses_kinds true tv tu true true true true (S k) T = false ->
  cty_uses_kinds true tv tu true true true true k (subst_box_ty_cty 0 q U T) = false.
Proof.
  intros D T U q tv tu k Hk HU HT.
  assert (Hgen : forall (T0 U0 : cty D) c ku,
    (c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 T0 = false) ->
    cty_uses_kinds true tv tu true true true true ku U0 = false ->
    cty_uses_kinds true tv tu true true true true (S (c + ku)) T0 = false ->
    cty_uses_kinds true tv tu true true true true (c + ku) (subst_box_ty_cty c q (lift_cty 0 c U0) T0) = false).
  { induction T0 using cty_ind_nested; intros U0 c ku Hck HU0 HT0; cbn in *; try reflexivity;
      try (apply (IHT0 U0 c ku Hck HU0 HT0));
      try (apply orb_false_iff in HT0 as [H1 H2];
           assert (Hk1 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 T0_1 = false) by
             (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]);
           assert (Hk2 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 T0_2 = false) by
             (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]);
           rewrite (IHT0_1 U0 c ku Hk1 HU0 H1), (IHT0_2 U0 c ku Hk2 HU0 H2); reflexivity).
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 T0 = false) by
        (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0 U0 c ku Hk1 HU0 H1), cidx_uses_kinds_all_true; reflexivity.
    - destruct tv; [reflexivity |].
      destruct (lt_eq_lt_dec x c) as [[Hlt | ->] | Hgt];
        [ rewrite (proj2 (Nat.ltb_lt x c) Hlt); cbn; apply Nat.eqb_neq; lia
        | rewrite Nat.ltb_irrefl, Nat.eqb_refl; cbn;
          destruct (Nat.eq_dec (c + ku) 0) as [Hcz | Hcnz];
          [ assert (c = 0) by lia; subst; destruct Hck as [? | H0]; [lia | cbn in H0; discriminate]
          | apply Nat.eqb_neq; lia ]
        | rewrite (proj2 (Nat.ltb_ge x c) ltac:(lia)), (proj2 (Nat.eqb_neq x c) ltac:(lia)); cbn;
          nat_bool_hyps; apply Nat.eqb_neq; lia ].
    - destruct (lt_eq_lt_dec b c) as [[Hlt | ->] | Hgt].
      + rewrite (proj2 (Nat.eqb_neq b c) ltac:(lia)), (proj2 (Nat.ltb_lt b c) Hlt); cbn.
        destruct tu; cbn in *; [reflexivity | apply Nat.eqb_neq; lia].
      + rewrite Nat.eqb_refl; cbn.
        unfold lift_cty. eapply cty_uses_kinds_ren_ne; [| exact HU0].
        intros y Hy. unfold ren_lift. destruct (Nat.ltb_spec y 0); lia.
      + rewrite (proj2 (Nat.eqb_neq b c) ltac:(lia)), (proj2 (Nat.ltb_ge b c) ltac:(lia)); cbn.
        destruct tu; cbn in *; try reflexivity; nat_bool_hyps; apply Nat.eqb_neq; lia.
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 T0_1 = false) by
        (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0_1 U0 c ku Hk1 HU0 H1).
      rewrite (lift_cty_add D 1 c U0).
      replace (1 + c) with (S c) by lia.
      pose proof (IHT0_2 U0 (S c) ku ltac:(left; lia) HU0 H2) as H2'.
      cbn [Nat.add] in H2'. rewrite H2'; reflexivity.
    - apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 T0_1 = false) by
        (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      rewrite (IHT0_1 U0 c ku Hk1 HU0 H1).
      rewrite (lift_cty_add D 1 c U0).
      replace (1 + c) with (S c) by lia.
      pose proof (IHT0_2 U0 (S c) ku ltac:(left; lia) HU0 H2) as H2'.
      cbn [Nat.add] in H2'. rewrite H2'; reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in HT0 as [H1 H2].
      assert (Hk1 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 ft = false) by
        (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [? _]; right; assumption]).
      assert (Hk2 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 (CRecord id rest) = false) by
        (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (Hhd U0 c ku Hk1 HU0 H1), (IH Htl Hk2 H2); reflexivity.
    - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in HT0 as [_ HT0].
      assert (Hk2 : c + ku > 0 \/ cty_uses_kinds true false true true true true true 0 (CInd id rest) = false) by
        (destruct Hck as [? | H0]; [left; lia | apply orb_false_iff in H0 as [_ ?]; right; assumption]).
      rewrite (IH Hk2 HT0), cidx_uses_kinds_all_true; reflexivity. }
  pose proof (Hgen T U 0 k Hk HU HT) as H.
  rewrite lift_cty_0_0 in H. exact H.
Qed.

Lemma cty_uses_kinds_tv_false_to_true : forall (D : JoinDomain) (T : cty D) idx tu ub fs sn sc k,
  cty_uses_kinds idx false tu ub fs sn sc k T = false ->
  cty_uses_kinds idx true tu ub fs sn sc k T = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros idx tu ub fs sn sc k Hs; cbn in *; try reflexivity;
    try exact Hs;
    try (apply (IHT idx tu ub fs sn sc k Hs));
    try (apply orb_false_iff in Hs as [H1 H2]; rewrite (IHT1 idx tu ub fs sn sc k H1), (IHT2 idx tu ub fs sn sc k H2); reflexivity).
  - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT idx tu ub fs sn sc k H1), H2. reflexivity.
  - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT1 idx tu ub fs sn sc k H1), (IHT2 idx tu ub fs sn sc (S k) H2). reflexivity.
  - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT1 idx tu ub fs sn sc k H1), (IHT2 idx tu ub fs sn sc (S k) H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hs as [H1 H2].
    rewrite (Hhd idx tu ub fs sn sc k H1), (IH Htl H2). reflexivity.
Qed.

Lemma flags_allow_ren_0 : forall (D : JoinDomain) (T : cty D) m idx tvar tunbox unbox fst snd scase,
  flags_allow T idx tvar tunbox unbox fst snd scase ->
  flags_allow (ren_cty (plus m) T) idx tvar tunbox unbox fst snd scase.
Proof.
  intros D T m idx tvar tunbox unbox fst snd scase H.
  unfold flags_allow in *. rewrite erase_hints_ren.
  destruct (erase_hints T); cbn in *; try exact H;
    match goal with
    | x : cty D, y : cty D |- _ => destruct x, y; cbn in *; exact H
    | x : cty D |- _ => destruct x; cbn in *; exact H
    end.
Qed.

(* Note: core_derives_uses_kinds_prefix and simulation below *)
Lemma core_derives_uses_kinds_prefix : forall (D : JoinDomain) (env1 : cenv D) (t : cterm D) (j : cjudgment D),
  CoreDerives env1 t j ->
  forall env_p e0 env_b tv tu,
    env1 = env_p ++ e0 :: env_b ->
    ((forall lvl, erase_hints (cannotation e0) <> CUniv lvl) -> tv = false) ->
    ((forall q lvl, erase_hints (cannotation e0) <> CBox q (CUniv lvl)) -> tu = false) ->
    flags_allow (cannotation e0) true tv tu true true true true ->
    cty_uses_kinds true tv tu true true true true (length env_p) (cresult_type j) = false.
Proof.
  intros D env1 t j H.
  induction H using CoreDerives_ind_mut with
    (P := fun env1 t j _ =>
      forall env_p e_tgt env_b tv tu,
        env1 = env_p ++ e_tgt :: env_b ->
        ((forall lvl, erase_hints (cannotation e_tgt) <> CUniv lvl) -> tv = false) ->
        ((forall q lvl, erase_hints (cannotation e_tgt) <> CBox q (CUniv lvl)) -> tu = false) ->
        flags_allow (cannotation e_tgt) true tv tu true true true true ->
        cty_uses_kinds true tv tu true true true true (length env_p) (cresult_type j) = false)
    (P0 := fun _ _ _ _ _ => True);
    try exact I;
    intros env_p e_tgt env_b tv tu Henv Htv Htu Hfl;
    try (lazymatch type of Henv with ?v = _ => is_var v; subst v end);
    cbn [cresult_type]; try reflexivity.
  - (* CoreVar *)
    lazymatch goal with
    | Hlk : clookup _ x = Some ?ee, Htd : CTypeDemand (skipn (S x) _) (cannotation ?ee) _ |- _ =>
      destruct (lt_eq_lt_dec x (length env_p)) as [[Hlt | ->] | Hgt];
      [ unfold clookup in Hlk; rewrite nth_error_app1 in Hlk by exact Hlt;
        rewrite skipn_app in Htd;
        replace (S x - length env_p) with 0 in Htd by lia; cbn [skipn] in Htd;
        assert (Hlen_sk : length (match env_p with [] => [] | _ :: l => skipn x l end) = length env_p - S x) by
          (destruct env_p; cbn; [lia | rewrite length_skipn; lia]);
        eapply cty_uses_kinds_ren_ne with (d := length env_p - S x);
        [ intros y Hy; lia
        | eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Hlen_sk, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl] ]
      | apply cty_uses_kinds_ren_plus; lia
      | apply cty_uses_kinds_ren_plus; lia ]
    end.
  - (* CoreLam *)
    lazymatch goal with
    | Htd : CTypeDemand _ dom _,
      IHb : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type _) = false |- _ =>
      assert (Hdom : cty_uses_kinds true tv tu true true true true (length env_p) dom = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
      cbn [cty_uses_kinds]; rewrite Hdom; apply (IHb (_ :: env_p) e_tgt env_b tv tu eq_refl Htv Htu Hfl)
    end.
  - (* CoreApp *)
    lazymatch goal with
    | IHfn : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type {| cresult_type := CPi _ _ _ _ _ |}) = false,
      IHarg : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type {| cresult_type := kind |}) = false |- _ =>
      pose proof (IHfn env_p e_tgt env_b tv tu eq_refl Htv Htu Hfl) as Hfn;
      cbn [cty_uses_kinds] in Hfn; apply orb_false_iff in Hfn as [Hdom Hcod];
      pose proof (IHarg env_p e_tgt env_b tv tu eq_refl Htv Htu Hfl) as Harg_res;
      cbn [cresult_type] in Harg_res
    end.
    lazymatch goal with
    | Hty : app_result_ty dom cod arg = Some res_ty,
      Hca : cty_alpha_eq kind dom,
      Htd_cod : CTypeDemand (_ :: _) cod _ |- _ =>
        unfold app_result_ty in Hty;
        destruct dom;
        try (destruct (cty_uses_var 0 cod) eqn:Euv;
             [ discriminate
             | inversion Hty; subst res_ty;
               apply cty_uses_kinds_unshift_at0_drop;
               [ right; apply cty_uses_var_0_uses_kinds; exact Euv | exact Hcod ] ])
    end.
    + lazymatch goal with
      | Hty : _ = Some res_ty, Htd_cod : CTypeDemand (_ :: _) cod _ |- _ =>
          destruct (term_as_cidx arg) eqn:Earg;
          [ inversion Hty; subst res_ty;
            apply cty_uses_kinds_subst_cidx_at0_drop;
            [ right; eapply ctype_demand_uses_kinds; [exact Htd_cod | reflexivity | unfold flags_allow; reflexivity]
            | exact Hcod ]
          | destruct (cty_uses_var 0 cod) eqn:Euv;
            [ discriminate
            | inversion Hty; subst res_ty;
              apply cty_uses_kinds_unshift_at0_drop;
              [ right; apply cty_uses_var_0_uses_kinds; exact Euv | exact Hcod ] ] ]
      end.
    + lazymatch goal with
      | Hty : _ = Some res_ty, Hca : cty_alpha_eq kind (CUniv _), Htd_cod : CTypeDemand (_ :: _) cod _ |- _ =>
          destruct arg;
          try (destruct (cty_uses_var 0 cod) eqn:Euv;
               [ discriminate
               | inversion Hty; subst res_ty;
                 apply cty_uses_kinds_unshift_at0_drop;
                 [ right; apply cty_uses_var_0_uses_kinds; exact Euv | exact Hcod ] ]);
          [ inversion Hty; subst res_ty;
            lazymatch goal with Hdv : CoreDerives _ (CVar ?xv) _ |- _ =>
              destruct (Nat.eq_dec xv (length env_p)) as [-> | Hne];
              [ inversion Hdv; subst;
                lazymatch goal with Hlk : clookup _ (length env_p) = Some ?ee |- _ =>
                  unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
                  pose proof (erase_hints_alpha_eq _ _ _ Hca) as Hca1;
                  rewrite erase_hints_ren in Hca1; cbn in Hca1;
                  destruct (erase_hints (cannotation e_tgt)) eqn:Ee0; cbn in Hca1; try discriminate;
                  unfold flags_allow in Hfl; rewrite Ee0 in Hfl; subst tv;
                  rewrite <- (lift_cty_0_0 (CTVar (length env_p)));
                  apply cty_uses_kinds_subst_tvar_at0_drop;
                  [ right; destruct (length env_p);
                    [ right; eapply cdemand_univ_not_tunbox_0; [| exact Htd_cod]; reflexivity
                    | left; lia ]
                  | cbn; reflexivity | exact Hcod ]
                end
              | rewrite <- (lift_cty_0_0 (CTVar xv));
                apply cty_uses_kinds_subst_tvar_at0_drop;
                [ right; destruct (length env_p);
                  [ right; eapply cdemand_univ_not_tunbox_0; [| exact Htd_cod]; reflexivity
                  | left; lia ]
                | cbn; destruct tv; [reflexivity | apply Nat.eqb_neq; exact Hne]
                | exact Hcod ] ]
            end
          | inversion Hty; subst res_ty;
            lazymatch goal with Hdv : CoreDerives _ (CTypeVal ?T0) _ |- _ =>
              inversion Hdv; subst;
              lazymatch goal with Htd : CTypeDemand _ T0 _ |- _ =>
                assert (HT : cty_uses_kinds true tv tu true true true true (length env_p) T0 = false) by
                  (eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
                rewrite <- (lift_cty_0_0 T0);
                apply cty_uses_kinds_subst_tvar_at0_drop;
                  [ right; destruct (length env_p);
                    [ right; eapply cdemand_univ_not_tunbox_0; [| exact Htd_cod]; reflexivity
                    | left; lia ]
                  | exact HT | exact Hcod ]
              end
            end ]
      end.
  - (* CoreLet *)
    lazymatch goal with
    | Huv : cty_uses_var 0 bod_ty = false,
      IHb : forall env_p0 e_tgt0 env_b0 tv0 tu0, (_ :: _) = _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type {| cresult_type := bod_ty |}) = false |- _ =>
      apply cty_uses_kinds_unshift_at0_drop;
        [ right; apply cty_uses_var_0_uses_kinds; exact Huv
        | exact (IHb (_ :: env_p) e_tgt env_b tv tu eq_refl Htv Htu Hfl) ]
    end.
  - (* CorePair *)
    lazymatch goal with
    | Htd1 : CTypeDemand _ fst_ty _,
      Htd2 : CTypeDemand (_ :: _) snd_ty _ |- _ =>
      assert (HA : cty_uses_kinds true tv tu true true true true (length env_p) fst_ty = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd1 | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
      assert (HB : cty_uses_kinds true tv tu true true true true (S (length env_p)) snd_ty = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd2 | unfold clookup; cbn [nth_error]; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
      cbn [cty_uses_kinds]; rewrite HA, HB; reflexivity
    end.
  - (* CoreLetPair *)
    lazymatch goal with Htd_mot : CTypeDemand (_ :: _) mot _ |- _ =>
      assert (Hm : cty_uses_kinds true tv tu true true true true (S (length env_p)) mot = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd_mot | unfold clookup; cbn [nth_error]; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
      assert (Hm0 : cty_uses_kinds true false false true true true true 0 mot = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; destruct (erase_hints A), (erase_hints B); repeat split; reflexivity])
    end.
    assert (Hsp : forall fi si,
      cty_uses_kinds true tv tu true true true true (length env_p) (subst_pair_cty 0 fi si mot) = false).
    { clear - Hm Hm0. intros fi si.
      assert (H0 : forall (T0 : cty D) c k fi0 si0, c <= k ->
        cty_uses_kinds true false false true true true true c T0 = false ->
        cty_uses_kinds true tv tu true true true true (S k) T0 = false ->
        cty_uses_kinds true tv tu true true true true k (subst_pair_cty c fi0 si0 T0) = false).
      { induction T0 using cty_ind_nested; intros c k fi0 si0 Hck HT0 HT; cbn in *; try reflexivity;
          try (apply IHT0; assumption);
          try (apply orb_false_iff in HT0 as [? ?]; apply orb_false_iff in HT as [? ?];
               rewrite (IHT0_1 c k fi0 si0 Hck ltac:(assumption) ltac:(assumption)), (IHT0_2 c k fi0 si0 Hck ltac:(assumption) ltac:(assumption)); reflexivity).
        - apply orb_false_iff in HT0 as [? ?]; apply orb_false_iff in HT as [? ?];
            rewrite (IHT0 c k fi0 si0 Hck ltac:(assumption) ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
        - destruct (lt_eq_lt_dec x c) as [[? | ->] | ?]; repeat (rw_nat_bool; cbv iota); cbn;
            destruct tv; cbn in *; try reflexivity; nat_bool_hyps; try (exfalso; lia); apply Nat.eqb_neq; lia.
        - destruct (lt_eq_lt_dec b c) as [[? | ->] | ?]; repeat (rw_nat_bool; cbv iota); cbn;
            destruct tu; cbn in *; try reflexivity; nat_bool_hyps; try (exfalso; lia); apply Nat.eqb_neq; lia.
        - apply orb_false_iff in HT0 as [? ?]; apply orb_false_iff in HT as [? ?];
            rewrite (IHT0_1 c k fi0 si0 Hck ltac:(assumption) ltac:(assumption)), (IHT0_2 (S c) (S k) _ _ ltac:(lia) ltac:(assumption) ltac:(assumption)); reflexivity.
        - apply orb_false_iff in HT0 as [? ?]; apply orb_false_iff in HT as [? ?];
            rewrite (IHT0_1 c k fi0 si0 Hck ltac:(assumption) ltac:(assumption)), (IHT0_2 (S c) (S k) _ _ ltac:(lia) ltac:(assumption) ltac:(assumption)); reflexivity.
        - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H; subst; cbn in *; apply orb_false_iff in HT0 as [? ?]; apply orb_false_iff in HT as [? ?];
            pose proof (IH H3 ltac:(assumption) ltac:(assumption)) as Hr; cbn in Hr;
            rewrite (H2 c k fi0 si0 Hck ltac:(assumption) ltac:(assumption)), Hr; reflexivity].
        - induction indices; cbn in *; try reflexivity; apply orb_false_iff in HT0 as [? ?]; apply orb_false_iff in HT as [? ?];
            pose proof (IHindices ltac:(assumption) ltac:(assumption)) as Hr; cbn in Hr;
            rewrite Hr, cidx_uses_kinds_all_true; reflexivity. }
      exact (H0 mot 0 (length env_p) fi si ltac:(lia) Hm0 Hm). }
    assert (Hmono_0 : forall (T0 : cty D) c0,
      cty_uses_kinds true false false true true true true c0 T0 = false ->
      cty_uses_kinds true tv tu true true true true c0 T0 = false).
    { clear. intros T0. induction T0 using cty_ind_nested; intros c0 H0; cbn in *; try reflexivity;
        try (apply IHT0; exact H0);
        try (apply orb_false_iff in H0 as [? ?]; rewrite (IHT0_1 c0 ltac:(assumption)), (IHT0_2 c0 ltac:(assumption)); reflexivity);
        try (apply orb_false_iff in H0 as [? ?]; rewrite (IHT0_1 c0 ltac:(assumption)), (IHT0_2 (S c0) ltac:(assumption)); reflexivity).
      - apply orb_false_iff in H0 as [H1' H2']; rewrite (IHT0 c0 ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
      - destruct tv; [reflexivity | exact H0].
      - destruct tu; [reflexivity | exact H0].
      - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H as [| ? ? Hhd Htl]; subst; cbn in *; apply orb_false_iff in H0 as [? ?]; rewrite (Hhd c0 ltac:(assumption)), (IH Htl ltac:(assumption)); reflexivity].
      - clear; induction indices; cbn; [reflexivity | rewrite cidx_uses_kinds_all_true, IHindices; reflexivity]. }
    subst res_ty; destruct pr; unfold spec_pair_subj_cty;
      try (apply cty_uses_kinds_unshift_at0_drop; [right; exact Hm0 | exact Hm]).
    + apply cty_uses_kinds_subst_var_at0_drop; [right; apply Hmono_0; exact Hm0 | exact Hm].
    + destruct (term_as_cidx pr1), (term_as_cidx pr2); [apply Hsp | apply cty_uses_kinds_unshift_at0_drop; [right; exact Hm0 | exact Hm] ..].
  - (* CorePromote *)
    lazymatch goal with
    | IHv : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type _) = false |- _ =>
      cbn [cty_uses_kinds]; apply (IHv env_p e_tgt env_b tv tu eq_refl Htv Htu Hfl)
    end.
  - (* CoreLetBox *)
    lazymatch goal with Hbx0 : CoreDerives _ box_term _, Htd0 : CTypeDemand (_ :: _) mot _ |- _ =>
      rename Hbx0 into Hbx; rename Htd0 into Htd_mot
    end.
    assert (Hm : cty_uses_kinds true tv tu true true true true (S (length env_p)) mot = false) by
      (eapply ctype_demand_uses_kinds; [exact Htd_mot | unfold clookup; cbn [nth_error]; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]).
    assert (Hbn : forall (T0 : cty D) qb val0,
      cty_uses_kinds true false false true true true true 0 T0 = false ->
      cty_uses_kinds true tv tu true true true true (S (length env_p)) T0 = false ->
      cty_uses_kinds true tv tu true true true true (length env_p) (subst_box_nat_cty 0 qb val0 T0) = false).
    { clear. intros T0 qb val0 HT0 HT.
      assert (H0 : forall (V : cty D) c k v0, c <= k ->
        cty_uses_kinds true false false true true true true c V = false ->
        cty_uses_kinds true tv tu true true true true (S k) V = false ->
        cty_uses_kinds true tv tu true true true true k (subst_box_nat_cty c qb v0 V) = false).
      { induction V using cty_ind_nested; intros c k v0 Hck HV0 HV; cbn in *; try reflexivity;
          try (apply IHV; assumption);
          try (apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
               rewrite (IHV1 c k v0 Hck ltac:(assumption) ltac:(assumption)), (IHV2 c k v0 Hck ltac:(assumption) ltac:(assumption)); reflexivity).
        - apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            rewrite (IHV c k v0 Hck ltac:(assumption) ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
        - destruct (lt_eq_lt_dec x c) as [[? | ->] | ?]; repeat (rw_nat_bool; cbv iota); cbn;
            destruct tv; cbn in *; try reflexivity; nat_bool_hyps; try (exfalso; lia); apply Nat.eqb_neq; lia.
        - destruct (lt_eq_lt_dec b c) as [[? | ->] | ?]; repeat (rw_nat_bool; cbv iota); cbn;
            destruct tu; cbn in *; try reflexivity; nat_bool_hyps; try (exfalso; lia); apply Nat.eqb_neq; lia.
        - apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            rewrite (IHV1 c k v0 Hck ltac:(assumption) ltac:(assumption)), (IHV2 (S c) (S k) _ ltac:(lia) ltac:(assumption) ltac:(assumption)); reflexivity.
        - apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            rewrite (IHV1 c k v0 Hck ltac:(assumption) ltac:(assumption)), (IHV2 (S c) (S k) _ ltac:(lia) ltac:(assumption) ltac:(assumption)); reflexivity.
        - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H; subst; cbn in *; apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            pose proof (IH H3 ltac:(assumption) ltac:(assumption)) as Hr; cbn in Hr;
            rewrite (H2 c k v0 Hck ltac:(assumption) ltac:(assumption)), Hr; reflexivity].
        - induction indices; cbn in *; try reflexivity; apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            pose proof (IHindices ltac:(assumption) ltac:(assumption)) as Hr; cbn in Hr;
            rewrite Hr, cidx_uses_kinds_all_true; reflexivity. }
      exact (H0 T0 0 (length env_p) val0 ltac:(lia) HT0 HT). }
    assert (Hmono_0 : forall (T0 : cty D) c0,
      cty_uses_kinds true false false true true true true c0 T0 = false ->
      cty_uses_kinds true tv tu true true true true c0 T0 = false).
    { clear. intros T0. induction T0 using cty_ind_nested; intros c0 H0; cbn in *; try reflexivity;
        try (apply IHT0; exact H0);
        try (apply orb_false_iff in H0 as [? ?]; rewrite (IHT0_1 c0 ltac:(assumption)), (IHT0_2 c0 ltac:(assumption)); reflexivity);
        try (apply orb_false_iff in H0 as [? ?]; rewrite (IHT0_1 c0 ltac:(assumption)), (IHT0_2 (S c0) ltac:(assumption)); reflexivity).
      - apply orb_false_iff in H0 as [H1' H2']; rewrite (IHT0 c0 ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
      - destruct tv; [reflexivity | exact H0].
      - destruct tu; [reflexivity | exact H0].
      - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H as [| ? ? Hhd Htl]; subst; cbn in *; apply orb_false_iff in H0 as [? ?]; rewrite (Hhd c0 ltac:(assumption)), (IH Htl ltac:(assumption)); reflexivity].
      - clear; induction indices; cbn; [reflexivity | rewrite cidx_uses_kinds_all_true, IHindices; reflexivity]. }
    assert (Hsb : forall qb (T0 : cty D),
      cty_uses_kinds true tv tu true true true true (S (length env_p)) T0 = false ->
      cty_uses_kinds true tv tu true true true true (S (length env_p)) (spec_box_body_cty qb 0 T0) = false).
    { clear. intros qb T0 HT.
      assert (H0 : forall (V : cty D) c k, c <= k ->
        cty_uses_kinds true tv tu true true true true (S k) V = false ->
        cty_uses_kinds true tv tu true true true true (S k) (spec_box_body_cty qb c V) = false).
      { induction V using cty_ind_nested; intros c k Hck HV; cbn in *; try reflexivity; try exact HV;
          try (apply IHV; assumption);
          try (apply orb_false_iff in HV as [? ?]; rewrite (IHV1 c k Hck ltac:(assumption)), (IHV2 c k Hck ltac:(assumption)); reflexivity);
          try (apply orb_false_iff in HV as [? ?]; rewrite (IHV1 c k Hck ltac:(assumption)), (IHV2 (S c) (S k) ltac:(lia) ltac:(assumption)); reflexivity).
        - apply orb_false_iff in HV as [? ?]; rewrite (IHV c k Hck ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
        - destruct (Nat.eqb_spec b c); [cbn; destruct tv; [reflexivity | apply Nat.eqb_neq; lia] | cbn; exact HV].
        - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H; subst; cbn in *; apply orb_false_iff in HV as [? ?];
            pose proof (IH H3 ltac:(assumption)) as Hr; cbn in Hr;
            rewrite (H2 c k Hck ltac:(assumption)), Hr; reflexivity].
        - clear; induction indices; cbn; [reflexivity | rewrite cidx_uses_kinds_all_true, IHindices; reflexivity]. }
      exact (H0 T0 0 (length env_p) ltac:(lia) HT). }
    subst res_ty; destruct box_term; unfold spec_box_subj_cty;
      try (apply cty_uses_kinds_unshift_at0_drop; [right; apply cty_uses_var_0_uses_kinds; assumption | exact Hm]).
    + apply cty_uses_kinds_subst_var_at0_drop; [| exact Hm].
      destruct (Nat.eq_dec x0 (length env_p)) as [-> | Hne]; [| left; exact Hne].
      right. inversion Hbx; subst; lazymatch goal with Hlk : clookup _ _ = Some ?ee, Heq : ren_cty _ (cannotation ?ee) = CBox _ _ |- _ =>
        unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
        apply (f_equal erase_hints) in Heq; rewrite erase_hints_ren in Heq; cbn in Heq;
        unfold flags_allow in Hfl;
        destruct (erase_hints A) eqn:EA;
        try (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; rewrite EA; try exact I; reflexivity]);
        destruct (erase_hints (cannotation e_tgt)) eqn:Ee_tgt; cbn in Heq, Hfl; try discriminate;
        inversion Heq; subst;
        match goal with Hc : ren_cty _ ?inner = CUniv _ |- _ => destruct inner; cbn in Hc; try discriminate end;
        eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; rewrite EA, Hfl; reflexivity]
      end.
    + destruct box_term; try (apply cty_uses_kinds_unshift_at0_drop; [right; apply cty_uses_var_0_uses_kinds; assumption | exact Hm]).
      * apply cty_uses_kinds_subst_var_at0_drop; [| exact (Hsb q0 mot Hm)].
        destruct (Nat.eq_dec x0 (length env_p)) as [-> | Hne]; [| left; exact Hne].
        right. inversion Hbx; subst; lazymatch goal with Hdv : CoreDerives _ (CVar _) _ |- _ =>
          inversion Hdv; subst; lazymatch goal with Hlk : clookup _ _ = Some ?ee |- _ =>
            unfold clookup in Hlk; rewrite nth_error_app2, Nat.sub_diag in Hlk by lia; inversion Hlk; subst ee;
            unfold flags_allow in Hfl;
            destruct (erase_hints (cannotation e_tgt)) eqn:Ee0;
            try (
              assert (Hm0 : cty_uses_kinds true false false true true true true 0 mot = false) by
                (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; rewrite erase_hints_ren; cbn; rewrite Ee0; cbn; try match goal with |- context [match ren_cty _ (ren_cty _ ?c) with _ => _ end] => destruct c; cbn end; try exact I; reflexivity]);
              clear - Hm0;
              assert (Hg : forall qb (V : cty D) c, cty_uses_kinds true false false true true true true c V = false ->
                cty_uses_kinds true tv tu true true true true c (spec_box_body_cty qb c V) = false);
              [ intros qb V; induction V using cty_ind_nested; intros c HV; cbn in *; try reflexivity;
                  try (apply IHV; exact HV);
                  try (apply orb_false_iff in HV as [? ?]; rewrite (IHV1 c ltac:(assumption)), (IHV2 c ltac:(assumption)); reflexivity);
                  try (apply orb_false_iff in HV as [? ?]; rewrite (IHV1 c ltac:(assumption)), (IHV2 (S c) ltac:(assumption)); reflexivity);
                  [ apply orb_false_iff in HV as [? ?]; rewrite (IHV c ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity
                  | destruct tv; [reflexivity | exact HV]
                  | destruct (Nat.eqb_spec b c) as [-> | Hne_b];
                    [ cbn in HV; discriminate
                    | cbn; destruct tu; [reflexivity | apply Nat.eqb_neq; exact Hne_b] ]
                  | induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H as [| ? ? Hhd Htl]; subst; cbn in *; apply orb_false_iff in HV as [? ?]; pose proof (IH Htl ltac:(assumption)) as Hr; cbn in Hr; rewrite (Hhd c ltac:(assumption)), Hr; reflexivity]
                  | clear; induction indices; cbn; [reflexivity | rewrite cidx_uses_kinds_all_true, IHindices; reflexivity] ]
              | exact (Hg _ mot 0 Hm0) ]);
            cbn in Hfl; subst tv;
            assert (Hm_bx : cty_uses_kinds true false true true true true true 0 mot = false) by
              (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; rewrite erase_hints_ren; cbn; rewrite Ee0; reflexivity]);
            clear - Hm_bx;
            assert (Hg : forall qb (V : cty D) c, cty_uses_kinds true false true true true true true c V = false ->
              cty_uses_kinds true true tu true true true true c (spec_box_body_cty qb c V) = false);
            [ intros qb V; induction V using cty_ind_nested; intros c HV; cbn in *; try reflexivity;
                try (apply IHV; exact HV);
                try (apply orb_false_iff in HV as [? ?]; rewrite (IHV1 c ltac:(assumption)), (IHV2 c ltac:(assumption)); reflexivity);
                try (apply orb_false_iff in HV as [? ?]; rewrite (IHV1 c ltac:(assumption)), (IHV2 (S c) ltac:(assumption)); reflexivity);
                [ apply orb_false_iff in HV as [? ?]; rewrite (IHV c ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity
                | destruct (Nat.eqb_spec b c); cbn; [reflexivity | destruct tu; [reflexivity | apply Nat.eqb_neq; assumption]]
                | induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H as [| ? ? Hhd Htl]; subst; cbn in *; apply orb_false_iff in HV as [? ?]; pose proof (IH Htl ltac:(assumption)) as Hr; cbn in Hr; rewrite (Hhd c ltac:(assumption)), Hr; reflexivity]
                | clear; induction indices; cbn; [reflexivity | rewrite cidx_uses_kinds_all_true, IHindices; reflexivity] ]
            | exact (Hg _ mot 0 Hm_bx) ]
          end end.
      * assert (Hm0 : cty_uses_kinds true false false true true true true 0 mot = false) by
          (inversion Hbx; subst; lazymatch goal with Hdv : CoreDerives _ (CNatVal _) _ |- _ =>
            inversion Hdv; subst;
            eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]
          end).
        apply (Hbn mot q0 i Hm0 Hm).
      * inversion Hbx; subst; lazymatch goal with Hdv : CoreDerives _ (CTypeVal ?T0) _ |- _ =>
          inversion Hdv; subst; lazymatch goal with Htd : CTypeDemand _ T0 _ |- _ =>
            assert (HT : cty_uses_kinds true tv tu true true true true (length env_p) T0 = false) by
              (eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
            assert (Hm_bx0 : cty_uses_kinds true false true true true true true 0 mot = false) by
              (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity]);
            apply cty_uses_kinds_subst_box_ty_at0_drop; [right; exact Hm_bx0 | exact HT | exact Hm]
          end end.
  - (* CoreInl *)
    lazymatch goal with
    | Htd : CTypeDemand _ rhs_ty _,
      IHv : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type _) = false |- _ =>
      pose proof (IHv env_p e_tgt env_b tv tu eq_refl Htv Htu Hfl) as HI; cbn [cresult_type] in HI;
      cbn [cty_uses_kinds]; rewrite HI;
      eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]
    end.
  - (* CoreInr *)
    lazymatch goal with
    | Htd : CTypeDemand _ lhs_ty _,
      IHv : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type _) = false |- _ =>
      pose proof (IHv env_p e_tgt env_b tv tu eq_refl Htv Htu Hfl) as HI; cbn [cresult_type] in HI;
      cbn [cty_uses_kinds]; rewrite HI, orb_false_r;
      eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]
    end.
  - (* CoreMatchSum *)
    lazymatch goal with Htd_mot : CTypeDemand (_ :: _) mot _ |- _ =>
    assert (Hm : cty_uses_kinds true tv tu true true true true (S (length env_p)) mot = false) by
      (eapply ctype_demand_uses_kinds; [exact Htd_mot | unfold clookup; cbn [nth_error]; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
    assert (Hm0 : cty_uses_kinds true false false true true true true 0 mot = false) by
      (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; rewrite erase_hints_ren; cbn; reflexivity])
    end.
    assert (Hss : forall is_left val0,
      cty_uses_kinds true tv tu true true true true (length env_p) (subst_sum_cty is_left 0 val0 mot) = false).
    { clear - Hm Hm0. intros is_left val0.
      assert (H0 : forall (V : cty D) c k v0, c <= k ->
        cty_uses_kinds true false false true true true true c V = false ->
        cty_uses_kinds true tv tu true true true true (S k) V = false ->
        cty_uses_kinds true tv tu true true true true k (subst_sum_cty is_left c v0 V) = false).
      { induction V using cty_ind_nested; intros c k v0 Hck HV0 HV; cbn in *; try reflexivity;
          try (apply IHV; assumption);
          try (apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
               rewrite (IHV1 c k v0 Hck ltac:(assumption) ltac:(assumption)), (IHV2 c k v0 Hck ltac:(assumption) ltac:(assumption)); reflexivity).
        - apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            rewrite (IHV c k v0 Hck ltac:(assumption) ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
        - destruct (lt_eq_lt_dec x c) as [[? | ->] | ?]; repeat (rw_nat_bool; cbv iota); cbn;
            destruct tv; cbn in *; try reflexivity; nat_bool_hyps; try (exfalso; lia); apply Nat.eqb_neq; lia.
        - destruct (lt_eq_lt_dec b c) as [[? | ->] | ?]; repeat (rw_nat_bool; cbv iota); cbn;
            destruct tu; cbn in *; try reflexivity; nat_bool_hyps; try (exfalso; lia); apply Nat.eqb_neq; lia.
        - apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            rewrite (IHV1 c k v0 Hck ltac:(assumption) ltac:(assumption)), (IHV2 (S c) (S k) _ ltac:(lia) ltac:(assumption) ltac:(assumption)); reflexivity.
        - apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            rewrite (IHV1 c k v0 Hck ltac:(assumption) ltac:(assumption)), (IHV2 (S c) (S k) _ ltac:(lia) ltac:(assumption) ltac:(assumption)); reflexivity.
        - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H; subst; cbn in *; apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            pose proof (IH H3 ltac:(assumption) ltac:(assumption)) as Hr; cbn in Hr;
            rewrite (H2 c k v0 Hck ltac:(assumption) ltac:(assumption)), Hr; reflexivity].
        - induction indices; cbn in *; try reflexivity; apply orb_false_iff in HV0 as [? ?]; apply orb_false_iff in HV as [? ?];
            pose proof (IHindices ltac:(assumption) ltac:(assumption)) as Hr; cbn in Hr;
            rewrite Hr, cidx_uses_kinds_all_true; reflexivity. }
      exact (H0 mot 0 (length env_p) val0 ltac:(lia) Hm0 Hm). }
    assert (Hmono_0 : forall (T0 : cty D) c0,
      cty_uses_kinds true false false true true true true c0 T0 = false ->
      cty_uses_kinds true tv tu true true true true c0 T0 = false).
    { clear. intros T0. induction T0 using cty_ind_nested; intros c0 H0; cbn in *; try reflexivity;
        try (apply IHT0; exact H0);
        try (apply orb_false_iff in H0 as [? ?]; rewrite (IHT0_1 c0 ltac:(assumption)), (IHT0_2 c0 ltac:(assumption)); reflexivity);
        try (apply orb_false_iff in H0 as [? ?]; rewrite (IHT0_1 c0 ltac:(assumption)), (IHT0_2 (S c0) ltac:(assumption)); reflexivity).
      - apply orb_false_iff in H0 as [H1' H2']; rewrite (IHT0 c0 ltac:(assumption)), cidx_uses_kinds_all_true; reflexivity.
      - destruct tv; [reflexivity | exact H0].
      - destruct tu; [reflexivity | exact H0].
      - induction fields as [| [[? ?] ?] ? IH]; cbn in *; [reflexivity | inversion H as [| ? ? Hhd Htl]; subst; cbn in *; apply orb_false_iff in H0 as [? ?]; rewrite (Hhd c0 ltac:(assumption)), (IH Htl ltac:(assumption)); reflexivity].
      - clear; induction indices; cbn; [reflexivity | rewrite cidx_uses_kinds_all_true, IHindices; reflexivity]. }
    subst res_ty; destruct scrut; unfold spec_sum_subj_cty;
      try (apply cty_uses_kinds_unshift_at0_drop; [right; exact Hm0 | exact Hm]).
    + apply cty_uses_kinds_subst_var_at0_drop; [right; apply Hmono_0; exact Hm0 | exact Hm].
    + destruct (term_as_cidx scrut); [apply Hss | apply cty_uses_kinds_unshift_at0_drop; [right; exact Hm0 | exact Hm]].
    + destruct (term_as_cidx scrut); [apply Hss | apply cty_uses_kinds_unshift_at0_drop; [right; exact Hm0 | exact Hm]].
  - (* CoreIf *)
    lazymatch goal with
    | IHth : forall env_p0 e_tgt0 env_b0 tv0 tu0, _ -> _ -> _ -> _ -> cty_uses_kinds _ _ _ _ _ _ _ _ (cresult_type {| cresult_type := t1 |}) = false |- _ =>
      exact (IHth env_p e_tgt env_b tv tu eq_refl Htv Htu Hfl)
    end.
  - (* CoreRecordMk *)
    lazymatch goal with Hrec : CRecordElemDerives _ fields _ _ |- _ =>
      clear - Hrec Hfl;
      remember (env_p ++ e_tgt :: env_b) as env_r eqn:Henv_r in Hrec;
      induction Hrec; cbn; [reflexivity |];
      lazymatch goal with Henv : ?v = env_p ++ _ :: _, IH : ?v = env_p ++ _ :: _ -> _ |- _ =>
        pose proof (IH Henv) as IH'; subst v;
        lazymatch goal with Htd : CTypeDemand _ ?ft0 _ |- _ =>
          assert (Hft : cty_uses_kinds true tv tu true true true true (length env_p) ft0 = false) by
            (eapply ctype_demand_uses_kinds; [exact Htd | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
          cbn [cty_uses_kinds map] in *; rewrite Hft; exact IH'
        end
      end
    end.
  - (* CoreMatchRecord *)
    lazymatch goal with Htd_mot : CTypeDemand _ mot _ |- _ =>
      eapply ctype_demand_uses_kinds; [exact Htd_mot | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]
    end.
  - (* CoreSubgrade *)
    lazymatch goal with Htd_tgt : CTypeDemand _ target _ |- _ =>
      eapply ctype_demand_uses_kinds; [exact Htd_tgt | unfold clookup; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]
    end.
  - (* CoreFix *)
    lazymatch goal with Htd_mot : CTypeDemand (_ :: _) mot _ |- _ =>
      assert (Hm : cty_uses_kinds true tv tu true true true true (S (length env_p)) mot = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd_mot | unfold clookup; cbn [nth_error]; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity | apply flags_allow_ren_0; exact Hfl]);
      assert (Hm0 : cty_uses_kinds true false false true true true true 0 mot = false) by
        (eapply ctype_demand_uses_kinds; [exact Htd_mot | reflexivity | unfold flags_allow; reflexivity])
    end.
    subst res_ty; unfold spec_fix_subj_cty.
    destruct (term_as_cidx scrut);
      [apply cty_uses_kinds_subst_cidx_at0_drop; [right; exact Hm0 | exact Hm]
      | apply cty_uses_kinds_unshift_at0_drop; [right; exact Hm0 | exact Hm]].
Qed.

Lemma eval_cfields_erasure : forall (D : JoinDomain) fuel (theta : list (@dcty D)) env fields u v rho erho rfs,
  ErasureDomain D ->
  (forall t' j' rho' erho' v',
     length rho' = length env ->
     CoreDerives env t' j' ->
     erasure_wf_cterm env t' ->
     EnvRel theta env (ccomp_demand j') rho' erho' ->
     eval_cterm fuel rho' t' = Some v' ->
     exists ev', eval_ecterm fuel erho' (erase_cterm env t') = Some ev' /\
       ValRel (eval_dcty 0 theta (cresult_type j')) v' ev') ->
  CRecordElemDerives env fields u v ->
  (fix go_wf (fs : list (nat * grade D * cty D * cterm D)) : Prop :=
     match fs with [] => True | (_, _, _, fv) :: rest => erasure_wf_cterm env fv /\ go_wf rest end) fields ->
  EnvRel theta env u rho erho ->
  (fix go_fields (fs : list (nat * grade D * cty D * cterm D)) : option (list (nat * @crval D)) :=
     match fs with
     | [] => Some []
     | (fn, _, _, fv) :: rest =>
         match eval_cterm fuel rho fv, go_fields rest with
         | Some v0, Some rv => Some ((fn, v0) :: rv)
         | _, _ => None
         end
     end) fields = Some rfs ->
  exists erfs,
    (fix go_efields (fs : list (nat * bool * @ecterm D)) : option (list (nat * @ecval D)) :=
       match fs with
       | [] => Some []
       | (fn, false, _) :: rest =>
           match go_efields rest with
           | Some rv => Some ((fn, EVErased) :: rv)
           | None => None
           end
       | (fn, true, fv) :: rest =>
           match eval_ecterm fuel erho fv, go_efields rest with
           | Some ev, Some rv => Some ((fn, ev) :: rv)
           | _, _ => None
           end
       end) (map (fun '(fn, fg, _, fv) =>
                   if grade_eqb fg zero then (fn, false, ECErased) else (fn, true, erase_cterm env fv)) fields) = Some erfs /\
    Forall3 (fun '(fg, df) '(fn, vr) '(efn, evr) => fn = efn /\ (fg = zero \/ ValRel df vr evr))
      (map (fun '(_, fg, ft, _) => (fg, eval_dcty 0 theta ft)) fields) rfs erfs.
Proof.
  intros D fuel theta env fields u v rho erho rfs ED IH Hrec.
  revert rfs. induction Hrec; intros rfs Hwf Henv Hev; cbn in *.
  - inversion Hev; subst. exists []; split; [reflexivity | constructor].
  - destruct (eval_cterm fuel rho fv) as [v_fv |] eqn:Hfv; [| discriminate].
    destruct ((fix go_fields (fs : list (nat * grade D * cty D * cterm D)) : option (list (nat * @crval D)) :=
      match fs with [] => Some [] | (fn0, _, _, fv0) :: rest0 =>
        match eval_cterm fuel rho fv0, go_fields rest0 with Some v1, Some rv => Some ((fn0, v1) :: rv) | _, _ => None end
      end) rest) as [rfs_rest |] eqn:Hrest; [| discriminate].
    inversion Hev; subst rfs. destruct Hwf as [Hwf_fv Hwf_rest].
    lazymatch goal with
    | Hdv : CoreDerives _ fv _, Hca : cty_alpha_eq _ ft, Hrd : CRecordElemDerives _ rest _ _ |- _ =>
      pose proof (core_derives_lengths D _ _ _ Hdv) as [Hlen_uv _];
      pose proof (record_elem_derives_lengths D _ _ _ _ Hrd) as [Hlen_ur _];
      cbn [ccomp_demand] in Hlen_uv, Hlen_ur;
      assert (Hlen_eq : length (vec_scale fg u_v) = length u_rest) by
        (rewrite vec_scale_length; lia);
      assert (Henv_fv : EnvRel theta env (vec_scale fg u_v) rho erho) by
        (eapply env_rel_add_l; [exact ED | exact Hlen_eq | exact Henv]);
      assert (Henv_rest : EnvRel theta env u_rest rho erho) by
        (eapply env_rel_add_r; [exact ED | exact Hlen_eq | exact Henv]);
      destruct (IHHrec IH rfs_rest Hwf_rest Henv_rest eq_refl) as [erfs [Herfs Hfa]];
      destruct (grade_eqb_spec D fg zero) as [-> | Hnz];
      [ rewrite Herfs; exists ((fn, EVErased) :: erfs); split; [reflexivity |];
        constructor; [split; [reflexivity | left; reflexivity] | exact Hfa]
      | assert (Hlr : length rho = length env) by (destruct Henv as [? _]; assumption);
        destruct (IH fv _ rho erho v_fv Hlr Hdv Hwf_fv (env_rel_scale _ _ _ fg _ _ _ ED Hnz Henv_fv) Hfv) as [ev [Hev_fv Hrel_fv]];
        rewrite Hev_fv, Herfs; exists ((fn, ev) :: erfs); split; [reflexivity |];
        constructor; [split; [reflexivity | right; rewrite <- (eval_dcty_alpha_eq D t_v ft 0 theta Hca); exact Hrel_fv] | exact Hfa]
      ]
    end.
Qed.

Lemma nth_grade_firstn : forall (D : JoinDomain) k (u : list (grade D)) idx,
  idx < k ->
  nth_grade (firstn k u) idx = nth_grade u idx.
Proof.
  intros D k. induction k as [| k IH]; intros [| a u'] idx Hlt; cbn in *; try lia;
    [destruct idx; reflexivity |].
  destruct idx; [reflexivity | unfold nth_grade, nth_default in *; cbn; apply IH; lia].
Qed.

Lemma nth_grade_skipn : forall (D : JoinDomain) k (u : list (grade D)) idx,
  nth_grade (skipn k u) idx = nth_grade u (k + idx).
Proof.
  intros D k. induction k as [| k IH]; intros [| a u'] idx; cbn in *; try reflexivity.
  - destruct idx; reflexivity.
  - unfold nth_grade, nth_default in *; cbn. apply IH.
Qed.

Lemma env_rel_vec_zero : forall (D : JoinDomain) (theta : list (@dcty D)) env u rho erho,
  vec_is_zero u = true ->
  length rho = length env ->
  length erho = length env ->
  length theta = length env ->
  EnvRel theta env u rho erho.
Proof.
  intros D theta env u rho erho Hz Hr He Ht.
  repeat split; try assumption.
  intros y e Hlk Hnz. exfalso. apply Hnz.
  clear - Hz. revert y. induction u as [| a u' IH]; intros [| y']; cbn in *; try reflexivity;
    apply andb_true_iff in Hz as [Ha Hu]; [apply grade_eqb_sound; exact Ha | apply (IH Hu)].
Qed.

Lemma cty_uses_kinds_eval_dcty_no_unbox : forall (D : JoinDomain) (T : cty D) theta k,
  cty_uses_kinds true true false true true true true k T = false ->
  dcty_uses_unbox k (eval_dcty (S k) theta T) = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros theta k Hs; cbn in *; try reflexivity;
    try (apply IHT; exact Hs).
  - destruct (Nat.ltb_spec x (S k)); [reflexivity | apply dcty_uses_unbox_lift_drop; lia].
  - destruct (Nat.ltb_spec b (S k));
      [ cbn; nat_bool_hyps; apply Nat.eqb_neq; lia
      | destruct (nth (b - S k) theta DUniv); try reflexivity; apply dcty_uses_unbox_lift_drop; lia ].
  - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT1 theta k H1), (IHT2 theta (S k) H2). reflexivity.
  - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT1 theta k H1), (IHT2 theta (S k) H2). reflexivity.
  - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT1 theta k H1), (IHT2 theta k H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in *.
    apply orb_false_iff in Hs as [H1 H2].
    rewrite (Hhd theta k H1), (IH Htl H2). reflexivity.
Qed.

Lemma eval_dcty_subst_dcty_no_unbox_0 : forall (D : JoinDomain) (T : cty D) d theta,
  dcty_uses_unbox 0 (eval_dcty 1 theta T) = false ->
  eval_dcty 0 (d :: theta) T = subst_dcty 0 d (eval_dcty 1 theta T).
Proof.
  intros D T d theta Hs.
  assert (Hgen : forall (T0 : cty D) depth d0 th,
    dcty_uses_unbox depth (eval_dcty (S depth) th T0) = false ->
    eval_dcty depth (d0 :: th) T0 = subst_dcty depth d0 (eval_dcty (S depth) th T0)).
  { induction T0 using cty_ind_nested; intros depth d0 th Hsafe; cbn in *; try reflexivity;
      try (apply (IHT0 depth d0 th Hsafe)).
    - destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; cbn.
      + rewrite (proj2 (Nat.ltb_lt x depth) Hlt), (proj2 (Nat.ltb_lt x (S depth)) ltac:(lia)); cbn.
        rewrite (proj2 (Nat.eqb_neq x depth) ltac:(lia)), (proj2 (Nat.ltb_lt x depth) Hlt). reflexivity.
      + rewrite (proj2 (Nat.ltb_ge depth depth) ltac:(lia)), (proj2 (Nat.ltb_lt depth (S depth)) ltac:(lia)); cbn.
        rewrite Nat.sub_diag, Nat.eqb_refl; cbn. reflexivity.
      + rewrite (proj2 (Nat.ltb_ge x depth) ltac:(lia)), (proj2 (Nat.ltb_ge x (S depth)) ltac:(lia)); cbn.
        destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
        replace (x - S depth) with k' by lia. cbn.
        replace (S depth) with (S (depth - 0)) by lia.
        rewrite subst_dcty_lift_cancel by lia.
        replace (depth - 0) with depth by lia. reflexivity.
    - destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt].
      + cbn. rewrite (proj2 (Nat.ltb_lt b depth) Hlt), (proj2 (Nat.ltb_lt b (S depth)) ltac:(lia)); cbn.
        rewrite (proj2 (Nat.eqb_neq b depth) ltac:(lia)), (proj2 (Nat.ltb_lt b depth) Hlt). reflexivity.
      + rewrite (proj2 (Nat.ltb_lt depth (S depth)) ltac:(lia)) in Hsafe; cbn in Hsafe; rewrite Nat.eqb_refl in Hsafe; discriminate.
      + cbn. rewrite (proj2 (Nat.ltb_ge b depth) ltac:(lia)), (proj2 (Nat.ltb_ge b (S depth)) ltac:(lia)); cbn.
        destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
        replace (b - S depth) with k' by lia. cbn.
        destruct (nth k' th DUniv); cbn; try reflexivity;
          replace (S depth) with (S (depth - 0)) by lia;
          rewrite subst_dcty_lift_cancel by lia; replace (depth - 0) with depth by lia; reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d0 th H1), (IHT0_2 (S depth) d0 th H2). reflexivity.
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d0 th H1), (IHT0_2 (S depth) d0 th H2). reflexivity.
    - f_equal; apply (IHT0 depth d0 th Hsafe).
    - apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (IHT0_1 depth d0 th H1), (IHT0_2 depth d0 th H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hsafe as [H1 H2].
      rewrite (Hhd depth d0 th H1), (IH Htl H2). reflexivity. }
  apply Hgen; exact Hs.
Qed.

Lemma eval_dcty_subst_dcty_0 : forall (D : JoinDomain) (T : cty D) d theta,
  cty_uses_kinds true true false true true true true 0 T = false ->
  eval_dcty 0 (d :: theta) T = subst_dcty 0 d (eval_dcty 1 theta T).
Proof.
  intros D T d theta Hs.
  apply eval_dcty_subst_dcty_no_unbox_0, cty_uses_kinds_eval_dcty_no_unbox; exact Hs.
Qed.

Lemma cty_uses_kinds_ren_lift_1_2_0 : forall (D : JoinDomain) (T : cty D) idx tv tu ub fs sn sc,
  cty_uses_kinds idx tv tu ub fs sn sc 0 T = false ->
  cty_uses_kinds idx tv tu ub fs sn sc 0 (ren_cty (ren_lift 1 2) T) = false.
Proof.
  intros D T idx tv tu ub fs sn sc Hs.
  assert (Hci : forall (i : cidx D) c,
    cidx_uses_kinds idx ub fs sn sc c i = false ->
    cidx_uses_kinds idx ub fs sn sc c (ren_cidx (Nat.iter c ren_shift (ren_lift 1 2)) i) = false).
  { induction i; intros c H; cbn in *; try reflexivity;
      try (apply orb_false_iff in H as [H1 H2]; rewrite (IHi1 c H1), (IHi2 c H2); reflexivity);
      try (apply IHi; exact H).
    - destruct (Nat.ltb_spec x c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); exact H
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (x - c) as [| k'] eqn:Hx; unfold ren_lift; cbn;
          [ replace (c + 0) with x by lia; exact H
          | destruct idx; [reflexivity | apply Nat.eqb_neq; lia] ] ].
    - destruct (Nat.ltb_spec b c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); exact H
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (b - c) as [| k'] eqn:Hb; unfold ren_lift; cbn;
          [ replace (c + 0) with b by lia; exact H
          | destruct ub; [reflexivity | apply Nat.eqb_neq; lia] ] ].
    - destruct (Nat.ltb_spec p c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); exact H
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (p - c) as [| k'] eqn:Hp; unfold ren_lift; cbn;
          [ replace (c + 0) with p by lia; exact H
          | destruct fs; [reflexivity | apply Nat.eqb_neq; lia] ] ].
    - destruct (Nat.ltb_spec p c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); exact H
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (p - c) as [| k'] eqn:Hp; unfold ren_lift; cbn;
          [ replace (c + 0) with p by lia; exact H
          | destruct sn; [reflexivity | apply Nat.eqb_neq; lia] ] ].
    - apply orb_false_iff in H as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
      pose proof (IHi1 (S c) H2) as H1'. pose proof (IHi2 (S c) H3) as H2'.
      change (Nat.iter (S c) ren_shift (ren_lift 1 2)) with (ren_shift (Nat.iter c ren_shift (ren_lift 1 2))) in H1', H2'.
      rewrite H1', H2'. destruct (Nat.ltb_spec s c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt), H1; reflexivity
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (s - c) as [| k'] eqn:Hsc; unfold ren_lift; cbn;
          [ replace (c + 0) with s by lia; rewrite H1; reflexivity
          | destruct sc; cbn; [reflexivity | destruct (c + S (k' + 2) =? c) eqn:Heq; [apply Nat.eqb_eq in Heq; lia | reflexivity]] ] ]. }
  assert (Hct : forall (T0 : cty D) c,
    cty_uses_kinds idx tv tu ub fs sn sc c T0 = false ->
    cty_uses_kinds idx tv tu ub fs sn sc c (ren_cty (Nat.iter c ren_shift (ren_lift 1 2)) T0) = false).
  { induction T0 using cty_ind_nested; intros c Huse; cbn in *; try reflexivity;
      try (apply (IHT0 c Huse));
      try (apply orb_false_iff in Huse as [H1 H2]; rewrite (IHT0_1 c H1), (IHT0_2 c H2); reflexivity).
    - apply orb_false_iff in Huse as [H1 H2]; rewrite (IHT0 c H1), (Hci len c H2); reflexivity.
    - destruct (Nat.ltb_spec x c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); exact Huse
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (x - c) as [| k'] eqn:Hx; unfold ren_lift; cbn;
          [ replace (c + 0) with x by lia; exact Huse
          | destruct tv; [reflexivity | apply Nat.eqb_neq; lia] ] ].
    - destruct (Nat.ltb_spec b c) as [Hlt | Hge];
        [ rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt); exact Huse
        | rewrite (Nat_iter_ren_shift_ge _ _ _ Hge); destruct (b - c) as [| k'] eqn:Hb; unfold ren_lift; cbn;
          [ replace (c + 0) with b by lia; exact Huse
          | destruct tu; [reflexivity | apply Nat.eqb_neq; lia] ] ].
    - apply orb_false_iff in Huse as [H1 H2].
      pose proof (IHT0_2 (S c) H2) as H2'.
      change (Nat.iter (S c) ren_shift (ren_lift 1 2)) with (ren_shift (Nat.iter c ren_shift (ren_lift 1 2))) in H2'.
      rewrite (IHT0_1 c H1), H2'. reflexivity.
    - apply orb_false_iff in Huse as [H1 H2].
      pose proof (IHT0_2 (S c) H2) as H2'.
      change (Nat.iter (S c) ren_shift (ren_lift 1 2)) with (ren_shift (Nat.iter c ren_shift (ren_lift 1 2))) in H2'.
      rewrite (IHT0_1 c H1), H2'. reflexivity.
    - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Huse as [H1 H2].
      rewrite (Hhd c H1), (IH Htl H2). reflexivity.
    - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
      apply orb_false_iff in Huse as [H1 H2]. rewrite (Hci idx0 c H1), (IH H2). reflexivity. }
  exact (Hct T 0 Hs).
Qed.

Lemma eval_dcty_spec_fix_step : forall (D : JoinDomain) (mot : cty D) d1 d2 d3 theta,
  cty_uses_kinds true false false true true true true 0 mot = false ->
  eval_dcty 0 (d1 :: d2 :: theta) (spec_fix_step_cty mot) = eval_dcty 0 (d3 :: theta) mot.
Proof.
  intros D mot d1 d2 d3 theta Hsafe.
  unfold spec_fix_step_cty.
  rewrite (eval_dcty_subst_cidx_0 D (ren_cty (ren_lift 1 2) mot) _ d1 (d1 :: d2 :: theta))
    by (apply cty_uses_kinds_ren_lift_1_2_0; exact Hsafe).
  assert (Hgen : forall (T0 : cty D) depth a1 a2 a3 a4 th,
    cty_uses_kinds true false false true true true true depth T0 = false ->
    eval_dcty depth (a1 :: a2 :: a3 :: th) (ren_cty (Nat.iter depth ren_shift (ren_lift 1 2)) T0) =
    eval_dcty depth (a4 :: th) T0).
  { induction T0 using cty_ind_nested; intros depth a1 a2 a3 a4 th Hs; cbn in *; try reflexivity;
      try (apply (IHT0 depth a1 a2 a3 a4 th Hs));
      try (apply orb_false_iff in Hs as [H1 _]; apply (IHT0 depth a1 a2 a3 a4 th H1)).
    - nat_bool_hyps. destruct (Nat.ltb_spec x depth) as [Hlt | Hge].
      + rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt), (proj2 (Nat.ltb_lt x depth) Hlt). reflexivity.
      + rewrite (Nat_iter_ren_shift_ge _ _ _ Hge).
        destruct (x - depth) as [| k'] eqn:Hxk; [lia |].
        unfold ren_lift; cbn.
        rewrite (proj2 (Nat.ltb_ge (depth + S (k' + 2)) depth) ltac:(lia)).
        replace (depth + S (k' + 2) - depth) with (S (S (S k'))) by lia.
        reflexivity.
    - nat_bool_hyps. destruct (Nat.ltb_spec b depth) as [Hlt | Hge].
      + rewrite (Nat_iter_ren_shift_lt _ _ _ Hlt), (proj2 (Nat.ltb_lt b depth) Hlt). reflexivity.
      + rewrite (Nat_iter_ren_shift_ge _ _ _ Hge).
        destruct (b - depth) as [| k'] eqn:Hbk; [lia |].
        unfold ren_lift; cbn.
        rewrite (proj2 (Nat.ltb_ge (depth + S (k' + 2)) depth) ltac:(lia)).
        replace (depth + S (k' + 2) - depth) with (S (S (S k'))) by lia.
        reflexivity.
    - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT0_1 depth a1 a2 a3 a4 th H1).
      pose proof (IHT0_2 (S depth) a1 a2 a3 a4 th H2) as H2'.
      change (Nat.iter (S depth) ren_shift (ren_lift 1 2))
        with (ren_shift (Nat.iter depth ren_shift (ren_lift 1 2))) in H2'.
      rewrite H2'. reflexivity.
    - apply orb_false_iff in Hs as [H1 H2]. rewrite (IHT0_1 depth a1 a2 a3 a4 th H1).
      pose proof (IHT0_2 (S depth) a1 a2 a3 a4 th H2) as H2'.
      change (Nat.iter (S depth) ren_shift (ren_lift 1 2))
        with (ren_shift (Nat.iter depth ren_shift (ren_lift 1 2))) in H2'.
      rewrite H2'. reflexivity.
    - f_equal. apply (IHT0 depth a1 a2 a3 a4 th Hs).
    - apply orb_false_iff in Hs as [H1 H2].
      rewrite (IHT0_1 depth a1 a2 a3 a4 th H1), (IHT0_2 depth a1 a2 a3 a4 th H2). reflexivity.
    - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
      inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hs as [H1 H2].
      rewrite (Hhd depth a1 a2 a3 a4 th H1), (IH Htl H2). reflexivity. }
  exact (Hgen mot 0 d1 d1 d2 d3 theta Hsafe).
Qed.

Lemma cenv_shape_eq_trans : forall (D : JoinDomain) (env1 env2 env3 : cenv D),
  cenv_shape_eq env1 env2 ->
  cenv_shape_eq env2 env3 ->
  cenv_shape_eq env1 env3.
Proof.
  intros D env1 env2 env3 H12. revert env3.
  induction H12; intros env3 H23; inversion H23; subst.
  - apply Forall2_nil.
  - apply Forall2_cons; [eapply cty_shape_eqb_trans; eassumption | lazymatch goal with IH : forall _, cenv_shape_eq _ _ -> _ |- _ => apply IH; assumption end].
Qed.

Lemma cenv_shape_eq_CRecordExtendEnv : forall (D : JoinDomain) (env : cenv D) bs fields (body_env : cenv D),
  CRecordExtendEnv env bs fields body_env ->
  @cenv_shape_eq D (erase_cterm_extend env fields) body_env.
Proof.
  intros D env bs fields body_env Hext.
  induction Hext; [rewrite erase_cterm_extend_nil; apply cenv_shape_eq_refl |].
  rewrite erase_cterm_extend_cons.
  assert (Hsh_rest : Forall2 (fun '(_, g1, t1) '(_, g2, t2) => g1 = g2 /\ cty_shape_eqb t1 t2 = true)
    (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)
    (map (fun '(n0, g0, t0) => (n0, g0, lift_cty 0 1 t0)) rest)).
  { clear. induction rest as [| [[n0 g0] t0] r IH]; constructor; [split; [reflexivity | apply cty_shape_eqb_refl] | exact IH]. }
  eapply cenv_shape_eq_trans; [| exact IHHext].
  apply cenv_shape_eq_extend; [| exact Hsh_rest].
  apply Forall2_cons; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl].
Qed.

Lemma cty_uses_var_0_no_kinds : forall (D : JoinDomain) (T : cty D) k,
  cty_uses_var k T = false ->
  cty_uses_kinds true false false true true true true k T = false.
Proof.
  intros D T. induction T using cty_ind_nested; intros k Huv; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huv as [H1 H2]); try (apply (IHT k Huv));
    try (rewrite (IHT1 k H1), (IHT2 k H2); reflexivity).
  - rewrite (IHT k H1), cidx_uses_kinds_all_true. reflexivity.
  - exact Huv.
  - exact Huv.
  - rewrite (IHT1 k H1), (IHT2 (S k) H2). reflexivity.
  - rewrite (IHT1 k H1), (IHT2 (S k) H2). reflexivity.
  - induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Huv as [H1 H2].
    rewrite (Hhd k H1), (IH Htl H2). reflexivity.
  - induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huv as [H1 H2].
    rewrite cidx_uses_kinds_all_true, (IH H2). reflexivity.
Qed.

Lemma app_result_ty_no_unbox_0 : forall (D : JoinDomain) env x (dom : cty D) a cod b arg res,
  CTypeDemand ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) cod b ->
  app_result_ty dom cod arg = Some res ->
  cty_uses_kinds true true false true true true true 0 cod = false.
Proof.
  intros D env x dom a cod b arg res Hd Happ.
  destruct dom; cbn [app_result_ty] in Happ;
    [ eapply cty_uses_kinds_tv_false_to_true; eapply cdemand_not_tvar_tunbox_0;
        [| | exact Hd]; [intros ? C; cbn in C; discriminate | intros ? ? C; cbn in C; discriminate]
    | destruct (cty_uses_var 0 cod) eqn:Huv;
        [discriminate | apply cty_uses_kinds_tv_false_to_true; apply cty_uses_var_0_no_kinds; exact Huv]
    | destruct (cty_uses_var 0 cod) eqn:Huv;
        [discriminate | apply cty_uses_kinds_tv_false_to_true; apply cty_uses_var_0_no_kinds; exact Huv]
    | eapply cdemand_univ_not_tunbox_0; [| exact Hd]; cbn; reflexivity
    | destruct (cty_uses_var 0 cod) eqn:Huv;
        [discriminate | apply cty_uses_kinds_tv_false_to_true; apply cty_uses_var_0_no_kinds; exact Huv] .. ].
Qed.

Lemma eval_dcty_app_result_ty : forall (D : JoinDomain) env x dom a cod b arg res (theta : list (@dcty D)),
  CTypeDemand ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) cod b ->
  app_result_ty dom cod arg = Some res ->
  let d_arg := match dom, arg with
               | CUniv _, CTypeVal T => eval_dcty 0 theta T
               | CUniv _, CVar y => nth y theta DUniv
               | _, _ => DUniv
               end in
  eval_dcty 0 theta res = subst_dcty 0 d_arg (eval_dcty 1 theta cod).
Proof.
  intros D env x dom a cod b arg res theta Hd Happ d_arg.
  pose proof (app_result_ty_no_unbox_0 D env x dom a cod b arg res Hd Happ) as Hcod_safe.
  subst d_arg.
  destruct dom; cbn [app_result_ty] in *;
    [ destruct (term_as_cidx arg) eqn:Ea;
      [ inversion Happ; subst;
        rewrite eval_dcty_subst_cidx_0 with (d_any := DUniv)
          by (eapply cdemand_not_tvar_tunbox_0; [| | exact Hd];
              [intros ? C; cbn in C; discriminate | intros ? ? C; cbn in C; discriminate]);
        apply eval_dcty_subst_dcty_0; exact Hcod_safe
      | destruct (cty_uses_var 0 cod) eqn:Huv; [discriminate |];
        inversion Happ; subst;
        rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_uses_kinds; exact Huv);
        apply eval_dcty_subst_dcty_0; exact Hcod_safe ]
    | destruct (cty_uses_var 0 cod) eqn:Huv; [discriminate |];
      inversion Happ; subst;
      rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_uses_kinds; exact Huv);
      apply eval_dcty_subst_dcty_0; exact Hcod_safe
    | destruct (cty_uses_var 0 cod) eqn:Huv; [discriminate |];
      inversion Happ; subst;
      rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_uses_kinds; exact Huv);
      apply eval_dcty_subst_dcty_0; exact Hcod_safe
    | destruct arg;
      try (destruct (cty_uses_var 0 cod) eqn:Huv; [discriminate |];
           inversion Happ; subst;
           rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_uses_kinds; exact Huv);
           apply eval_dcty_subst_dcty_0; exact Hcod_safe);
      [ inversion Happ; subst;
        rewrite (eval_dcty_subst_tvar_0 D cod (CTVar x0) theta Hcod_safe);
        cbn [eval_dcty]; rewrite lift_dcty_0, Nat.sub_0_r; reflexivity
      | inversion Happ; subst; apply eval_dcty_subst_tvar_0; exact Hcod_safe ]
    | destruct (cty_uses_var 0 cod) eqn:Huv; [discriminate |];
      inversion Happ; subst;
      rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_uses_kinds; exact Huv);
      apply eval_dcty_subst_dcty_0; exact Hcod_safe .. ].
Qed.

Lemma erasure_wf_cterm_shape_env : forall (D : JoinDomain) (t : cterm D) env1 env2,
  cenv_shape_eq env1 env2 ->
  erasure_wf_cterm env1 t ->
  erasure_wf_cterm env2 t.
Proof.
  intros D t. induction t using cterm_ind_nested; intros env1 env2 Hs Hwf; cbn in *; try exact I.
  - eapply cidx_no_zero_unbox_shape_env; eauto.
  - apply (IHt ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env1));
      [constructor; [apply cty_shape_eqb_refl | exact Hs] | exact Hwf].
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto | eapply IHt2; eauto].
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto |].
    eapply IHt2; [constructor; [apply cty_shape_eqb_refl | exact Hs] | exact H2].
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto | eapply IHt2; eauto].
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto |].
    pose proof (cterm_result_type_shape_env D t1 env1 env2 Hs) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction; try exact I.
    destruct ty1; cbn in Hsh; destruct ty2; try discriminate; try exact I.
    apply andb_true_iff in Hsh as [Hsh Hsnd]; apply andb_true_iff in Hsh as [_ Hfst].
    eapply IHt2; [| exact H2]; constructor; [exact Hsnd | constructor; [exact Hfst | exact Hs]].
  - eapply IHt; eauto.
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto |].
    pose proof (cterm_result_type_shape_env D t1 env1 env2 Hs) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction; try exact I.
    destruct ty1; cbn in Hsh; destruct ty2; try discriminate; try exact I.
    apply andb_true_iff in Hsh as [_ Hsh].
    eapply IHt2; [| exact H2]; constructor; [exact Hsh | exact Hs].
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto |].
    pose proof (cterm_result_type_shape_env D t1 env1 env2 Hs) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction; try exact I.
    destruct ty1; cbn in Hsh; destruct ty2; try discriminate; try exact I.
    apply andb_true_iff in Hsh as [Hl Hr]. destruct H2 as [Hlb Hrb].
    split; [eapply IHt2; [| exact Hlb]; constructor; [exact Hl | exact Hs]
           | eapply IHt3; [| exact Hrb]; constructor; [exact Hr | exact Hs]].
  - destruct Hwf as [H1 [H2 H3]]; repeat split; [eapply IHt1; eauto | eapply IHt2; eauto | eapply IHt3; eauto].
  - destruct Hwf as [Halgn Hfs]; split; [exact Halgn |].
    clear Halgn. induction fields as [| [[[fn fg] ft] fv] rest IHf]; cbn in *; [exact I |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. destruct Hfs as [Hwf1 Hwfs].
    split; [eapply Hhd; eauto | exact (IHf Htl Hwfs)].
  - destruct Hwf as [H1 H2]; split; [eapply IHt1; eauto |].
    unfold record_fields_ty in *.
    pose proof (cterm_result_type_shape_env D t1 env1 env2 Hs) as Hsh.
    destruct (cterm_result_type env1 t1) as [ty1 |], (cterm_result_type env2 t1) as [ty2 |];
      try contradiction; try exact I.
    destruct ty1; cbn in Hsh; destruct ty2; try discriminate; try exact I.
    apply andb_true_iff in Hsh as [_ Hfs].
    assert (Hfl : Forall2 (fun '(_, g1, t1') '(_, g2, t2') => g1 = g2 /\ cty_shape_eqb t1' t2' = true) fields fields0).
    { clear - Hfs. revert fields0 Hfs.
      induction fields as [| [[n1 g1] t1'] r1 IH]; intros [| [[n2 g2] t2'] r2] Hfs;
        cbn in *; try discriminate; [constructor |].
      repeat (apply andb_true_iff in Hfs as [Hfs ?]).
      repeat match goal with Hn : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hn | Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg end;
      subst; constructor; [repeat split; assumption | apply IH; assumption]. }
    destruct H2 as [Halgn Hbody]. split.
    + clear - Halgn Hfl. unfold record_erasure_aligned in *.
      assert (Hgrades_eq : map (fun '(_, g, _) => g) fields = map (fun '(_, g, _) => g) fields0).
      { clear - Hfl. induction Hfl; cbn; [reflexivity |].
        destruct x as [[? ?] ?], y as [[? ?] ?], H as [-> _]. f_equal; exact IHHfl. }
      assert (Hto_grades : forall (A B : list (nat * grade D * cty D)),
        Forall2 (fun '(_, g1, _) '(_, g2, _) => g1 = zero <-> g2 = zero) A B <->
        Forall2 (fun g1 g2 => g1 = zero <-> g2 = zero)
          (map (fun '(_, g, _) => g) A) (map (fun '(_, g, _) => g) B)).
      { clear. intros A; induction A as [| [[? g1] ?] A' IH]; intros [| [[? g2] ?] B']; cbn;
          split; intro H; inversion H; subst; try apply Forall2_nil;
          (apply Forall2_cons; [assumption | apply IH; assumption]). }
      apply Hto_grades. rewrite !map_rev, <- Hgrades_eq, <- !map_rev. apply Hto_grades; exact Halgn.
    + eapply IHt2; [| exact Hbody]. apply cenv_shape_eq_extend; assumption.
  - eapply IHt; eauto.
  - destruct Hwf as [H1 [H2 H3]]; repeat split; [eapply IHt1; eauto | eapply IHt2; eauto |].
    eapply IHt3; [constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | exact Hs]] | exact H3].
Qed.

Lemma nth_error_rev_lt : forall (A : Type) (n : nat) (l : list A),
  n < length l ->
  nth_error (rev l) n = nth_error l (length l - S n).
Proof.
  intros A n l Hlt. rewrite nth_error_rev, (proj2 (Nat.ltb_lt n (length l)) Hlt). reflexivity.
Qed.

Lemma skipn_repeat : forall (A : Type) (x : A) n m,
  skipn n (repeat x m) = repeat x (m - n).
Proof.
  intros A x n. induction n; intros [| m]; cbn; try reflexivity. apply IHn.
Qed.

Lemma length_repeat : forall (A : Type) (x : A) n,
  length (repeat x n) = n.
Proof.
  intros A x n. apply repeat_length.
Qed.

Lemma env_rel_record_extend : forall (D : JoinDomain) (theta : list (@dcty D)) env bs fields body_env
    s u_b rho erho dfs (rfs : list (nat * @crval D)) (erfs : list (nat * @ecval D)),
  ErasureDomain D ->
  s <> zero ->
  CRecordExtendEnv env bs fields body_env ->
  CRecordFieldAllows s fields (firstn (length fields) u_b) ->
  record_erasure_aligned fields ->
  Forall3 (fun '(fg, df) '(fn, vr) '(efn, evr) => fn = efn /\ (fg = zero \/ ValRel df vr evr)) dfs rfs erfs ->
  dfs = map (fun '(_, fg, ft) => (fg, eval_dcty 0 theta ft)) fields ->
  length rfs = length fields ->
  length erfs = length fields ->
  EnvRel theta env (skipn (length fields) u_b) rho erho ->
  exists theta_ext,
    length theta_ext = length body_env /\
    EnvRel theta_ext body_env u_b (rev (map snd rfs) ++ rho) (rev (map snd erfs) ++ erho) /\
    (forall T, eval_dcty 0 theta_ext (lift_cty 0 (length fields) T) = eval_dcty 0 theta T).
Proof.
  intros D theta env bs fields body_env s u_b rho erho dfs rfs erfs ED Hs Hext Hfa Halgn H3 -> Hlr Hle Henv.
  assert (Hlen_ext : length body_env = length fields + length env).
  { clear - Hext. induction Hext; cbn; [reflexivity | rewrite IHHext, length_map; cbn [length]; lia]. }
  assert (Hfields_lookup : forall idx b_e,
    idx < length fields ->
    nth_error body_env idx = Some b_e ->
    exists n_f g_f t_f,
      nth_error (rev fields) idx = Some (n_f, g_f, t_f) /\
      eval_dcty 0 (skipn (S idx) (repeat DUniv (length fields) ++ theta)) (cannotation b_e) =
      eval_dcty 0 theta t_f).
  { clear - Hext.
    assert (Hrep : forall (A : Type) (x : A) n, repeat x n ++ [x] = x :: repeat x n).
    { intros A x n. induction n; cbn; [reflexivity | f_equal; exact IHn]. }
    assert (Hwalk : forall (env0 : cenv D) bs0 fs0 ext0,
      CRecordExtendEnv env0 bs0 fs0 ext0 ->
      forall idx b_e (th_suf : list (@dcty D)),
        idx < length fs0 ->
        nth_error ext0 idx = Some b_e ->
        exists n_f g_f t_f,
          nth_error (rev fs0) idx = Some (n_f, g_f, t_f) /\
          eval_dcty 0 (skipn (S idx) (repeat DUniv (length fs0) ++ th_suf)) (cannotation b_e) =
          eval_dcty 0 th_suf t_f).
    { clear - Hrep. intros env0 bs0 fs0 ext0 Hext.
      induction Hext as [env_b | env_b b bs fn fg ft rest row ext Htd Hext_sub IHHext];
        intros idx b_e th_suf Hlt Hlk; cbn in *; [lia |].
      destruct (lt_eq_lt_dec idx (length rest)) as [[Hlt_r | ->] | Hgt].
      - destruct (IHHext idx b_e (DUniv :: th_suf) ltac:(rewrite length_map; exact Hlt_r) Hlk) as [nf [gf [tf [Hnth Hev]]]].
        rewrite nth_error_rev_lt in Hnth by (rewrite length_map; exact Hlt_r).
        rewrite nth_error_map, length_map in Hnth.
        destruct (nth_error rest (length rest - S idx)) as [[[n0 g0] t0] |] eqn:Er;
          [| cbn in Hnth; discriminate].
        cbn in Hnth. inversion Hnth.
        match goal with Ht : lift_cty 0 1 t0 = tf |- _ => rewrite <- Ht in Hev end.
        rewrite nth_error_app1 by (rewrite length_rev; lia).
        rewrite nth_error_rev_lt by lia. rewrite Er.
        exists n0, g0, t0; split; [reflexivity |].
        rewrite eval_dcty_lift_1_drop in Hev.
        rewrite length_map in Hev.
        replace (repeat (DUniv (D := D)) (length rest) ++ (DUniv (D := D)) :: th_suf)
          with ((DUniv (D := D)) :: (repeat (DUniv (D := D)) (length rest) ++ th_suf)) in Hev
          by (change ((DUniv (D := D)) :: th_suf) with ([DUniv (D := D)] ++ th_suf); rewrite app_assoc, Hrep; reflexivity).
        exact Hev.
      - assert (Hext_split : exists pre, length pre = length rest /\ ext = pre ++ {| cbinder := b; cannotation := ft; ctype_uses := row |} :: env_b).
        { clear - Hext_sub.
          assert (Hg : forall (e_base : cenv D) bs0 fs0 ext0,
            CRecordExtendEnv e_base bs0 fs0 ext0 ->
            exists pre, length pre = length fs0 /\ ext0 = pre ++ e_base).
          { intros e_base bs0 fs0 ext0 He.
            induction He as [env0 | env0 b0 bs1 fn0 fg0 ft0 rest0 row0 ext1 Htd0 He0 IHHe];
              [exists []; split; reflexivity |].
            destruct IHHe as [pre [Hlp ->]].
            exists (pre ++ [{| cbinder := b0; cannotation := ft0; ctype_uses := row0 |}]).
            split; [rewrite length_app, Hlp, length_map; cbn; lia | rewrite <- app_assoc; reflexivity]. }
          destruct (Hg _ _ _ _ Hext_sub) as [pre [Hlp Hp]].
          rewrite length_map in Hlp. exists pre; split; assumption. }
        destruct Hext_split as [pre [Hlp Hext_eq]].
        rewrite Hext_eq, nth_error_app2, Hlp, Nat.sub_diag in Hlk by lia.
        cbn in Hlk; inversion Hlk; subst b_e.
        rewrite nth_error_app2 by (rewrite length_rev; lia); rewrite length_rev, Nat.sub_diag; cbn.
        exists fn, fg, ft; split; [reflexivity |].
        rewrite skipn_app, skipn_repeat, length_repeat, Nat.sub_diag; cbn [repeat app skipn]; reflexivity.
      - lia. }
    intros idx b_e Hlt Hlk. exact (Hwalk env bs fields body_env Hext idx b_e theta Hlt Hlk). }
  assert (Hbody_split : exists pre, length pre = length fields /\ body_env = pre ++ env).
  { clear - Hext.
    induction Hext as [env0 | env0 b0 bs0 fn0 fg0 ft0 rest0 row0 ext0 Htd0 He0 IHHext];
      [exists []; split; reflexivity |].
    destruct IHHext as [pre [Hlp ->]]. rewrite length_map in Hlp.
    exists (pre ++ [{| cbinder := b0; cannotation := ft0; ctype_uses := row0 |}]).
    split; [rewrite length_app, Hlp; cbn; lia | rewrite <- app_assoc; reflexivity]. }
  destruct Hbody_split as [pre [Hlp Hbe]].
  destruct Henv as [Hlr_env [Hle_env [Hlt_env Henv_rel]]].
  exists (repeat DUniv (length fields) ++ theta).
  repeat split.
  - rewrite length_app, length_repeat, Hlt_env, Hlen_ext. reflexivity.
  - rewrite length_app, length_rev, length_map, Hlr, Hlr_env, Hlen_ext. reflexivity.
  - rewrite length_app, length_rev, length_map, Hle, Hle_env, Hlen_ext. reflexivity.
  - rewrite length_app, length_repeat, Hlt_env, Hlen_ext. reflexivity.
  - intros y e Hlk Hy.
    destruct (lt_dec y (length fields)) as [Hlt | Hge].
    + destruct (Hfields_lookup y e Hlt Hlk) as [nf [gf [tf [Hrev Hev]]]].
      rewrite nth_error_rev_lt in Hrev by exact Hlt.
      destruct (nth_error fields (length fields - S y)) as [[[n0 g0] t0] |] eqn:Ef; [| discriminate].
      inversion Hrev; subst nf gf tf.
      assert (Hg0_nz : g0 <> zero).
      { assert (Hy_f : exists nf_y gf_y tf_y, nth_error fields y = Some (nf_y, gf_y, tf_y) /\
          allows (nth_grade u_b y) (mul s gf_y) /\ (gf_y = zero <-> g0 = zero)).
        { clear - Hfa Halgn Hlt Ef.
          assert (Hfa_at : forall (s0 : grade D) (fs0 : list (nat * grade D * cty D)) (us0 : list (grade D)) k,
            CRecordFieldAllows s0 fs0 us0 -> k < length fs0 ->
            exists nk gk tk, nth_error fs0 k = Some (nk, gk, tk) /\ allows (nth_grade us0 k) (mul s0 gk)).
          { clear. intros s0 fs0 us0 k Hfa. revert k.
            induction Hfa; intros k Hlt; cbn in *; [lia |].
            destruct k; [exists fn, fg, ft; split; [reflexivity | assumption] | apply IHHfa; lia]. }
          destruct (Hfa_at s fields (firstn (length fields) u_b) y Hfa Hlt) as [nky [gky [tky [Hfy Haly]]]].
          rewrite nth_grade_firstn in Haly by exact Hlt.
          unfold record_erasure_aligned in Halgn.
          pose proof (Forall2_nth_error_both _ _ _ Halgn y _ Hfy) as [[[? ?] ?] [Hr_y Hiff]].
          rewrite nth_error_rev_lt, Ef in Hr_y by exact Hlt. inversion Hr_y; subst. cbn in Hiff.
          exists nky, gky, tky; split; [exact Hfy | split; [exact Haly | exact Hiff]]. }
        destruct Hy_f as [? [gf_y [? [_ [Haly Hiff]]]]].
        intro Hg0. apply Hiff in Hg0. subst gf_y.
        rewrite mul_zero_r in Haly. apply (erasure_allows_zero_eq D ED) in Haly. contradiction. }
      assert (Hval_at : exists fn0 vr evr,
        nth_error rfs (length fields - S y) = Some (fn0, vr) /\
        nth_error erfs (length fields - S y) = Some (fn0, evr) /\
        ValRel (eval_dcty 0 theta t0) vr evr).
      { clear - H3 Ef Hg0_nz.
        assert (Hg : forall (fs0 : list (nat * grade D * cty D)) (rfs0 : list (nat * @crval D)) (erfs0 : list (nat * @ecval D)) k nf0 gf0 tf0,
          Forall3 (fun '(fg, df) '(fn, vr) '(efn, evr) => fn = efn /\ (fg = zero \/ ValRel df vr evr))
            (map (fun '(_, fg, ft) => (fg, eval_dcty 0 theta ft)) fs0) rfs0 erfs0 ->
          nth_error fs0 k = Some (nf0, gf0, tf0) -> gf0 <> zero ->
          exists fn0 vr evr,
            nth_error rfs0 k = Some (fn0, vr) /\
            nth_error erfs0 k = Some (fn0, evr) /\
            ValRel (eval_dcty 0 theta tf0) vr evr).
        { intros fs0; induction fs0 as [| [[n1 g1] t1] fs' IH];
            intros [| [fn1 vr1] rfs'] [| [efn1 evr1] erfs'] k nf0 gf0 tf0 Hfor Hlk Hnz;
            cbn in *; try (inversion Hfor; fail); [destruct k; discriminate |].
          inversion Hfor; subst.
          lazymatch goal with
          | Hhd : fn1 = efn1 /\ _, Htl : Forall3 _ _ rfs' erfs' |- _ =>
              destruct Hhd as [Heq_fn Hdisj]; subst;
              destruct k;
              [ inversion Hlk; subst; destruct Hdisj as [Hz | Hv];
                [contradiction | exists efn1, vr1, evr1; repeat split; reflexivity || exact Hv]
              | exact (IH _ _ k nf0 gf0 tf0 Htl Hlk Hnz) ]
          end. }
        exact (Hg fields rfs erfs _ _ _ _ H3 Ef Hg0_nz). }
      destruct Hval_at as [fn0 [vr [evr [Hrfs [Herfs Hvr]]]]].
      exists vr, evr. repeat split.
      * rewrite nth_error_app1 by (rewrite length_rev, length_map, Hlr; exact Hlt).
        rewrite nth_error_rev_lt by (rewrite length_map, Hlr; exact Hlt).
        rewrite length_map, Hlr, nth_error_map, Hrfs. reflexivity.
      * rewrite nth_error_app1 by (rewrite length_rev, length_map, Hle; exact Hlt).
        rewrite nth_error_rev_lt by (rewrite length_map, Hle; exact Hlt).
        rewrite length_map, Hle, nth_error_map, Herfs. reflexivity.
      * rewrite Hev. exact Hvr.
    + assert (Hge' : length fields <= y) by lia.
      rewrite Hbe, nth_error_app2, Hlp in Hlk by (rewrite Hlp; lia).
      assert (Hsk_nz : nth_grade (skipn (length fields) u_b) (y - length fields) <> zero).
      { rewrite nth_grade_skipn.
        replace (length fields + (y - length fields)) with y by lia. exact Hy. }
      destruct (Henv_rel (y - length fields) e Hlk Hsk_nz) as [vy [evy [Hry [Hey Hvy]]]].
      exists vy, evy. repeat split.
      * rewrite nth_error_app2 by (rewrite length_rev, length_map, Hlr; exact Hge').
        rewrite length_rev, length_map, Hlr. exact Hry.
      * rewrite nth_error_app2 by (rewrite length_rev, length_map, Hle; exact Hge').
        rewrite length_rev, length_map, Hle. exact Hey.
      * rewrite skipn_app, skipn_repeat, length_repeat, (proj2 (Nat.sub_0_le (length fields) (S y)) ltac:(lia)); cbn [repeat app].
        replace (S y - length fields) with (S (y - length fields)) by lia.
        exact Hvy.
  - intro T. replace (lift_cty 0 (length fields) T) with (ren_cty (plus (length fields)) T)
      by (unfold lift_cty; apply ren_cty_ext; intro z; unfold ren_lift; destruct (Nat.ltb_spec z 0); lia).
    rewrite eval_dcty_ren_plus, skipn_app, skipn_repeat, length_repeat, Nat.sub_diag; cbn [repeat app skipn]; reflexivity.
Qed.

Lemma eval_dcty_head_equiv : forall (D : JoinDomain) (T : cty D) depth d1 d2 th,
  cty_uses_kinds true false true true true true true depth T = false ->
  (match d1 with DBox _ inner => inner | _ => DUniv end =
   match d2 with DBox _ inner => inner | _ => DUniv end) ->
  eval_dcty depth (d1 :: th) T = eval_dcty depth (d2 :: th) T.
Proof.
  intros D T. induction T using cty_ind_nested; intros depth d1 d2 th Hs Heq; cbn in *; try reflexivity;
    try (apply (IHT depth d1 d2 th Hs Heq));
    try (apply orb_false_iff in Hs as [H1 _]; apply (IHT depth d1 d2 th H1 Heq));
    try (apply orb_false_iff in Hs as [H1 H2];
         rewrite (IHT1 depth d1 d2 th H1 Heq), (IHT2 depth d1 d2 th H2 Heq); reflexivity).
  - nat_bool_hyps. destruct (lt_eq_lt_dec x depth) as [[Hlt | ->] | Hgt]; [| contradiction |].
    + rewrite (proj2 (Nat.ltb_lt x depth) Hlt); reflexivity.
    + rewrite (proj2 (Nat.ltb_ge x depth) ltac:(lia)); destruct (x - depth) eqn:Hx; [lia | reflexivity].
  - destruct (lt_eq_lt_dec b depth) as [[Hlt | ->] | Hgt].
    + rewrite (proj2 (Nat.ltb_lt b depth) Hlt); reflexivity.
    + rewrite (proj2 (Nat.ltb_ge depth depth) ltac:(lia)), Nat.sub_diag; cbn.
      destruct d1, d2; cbn in Heq; subst; reflexivity.
    + rewrite (proj2 (Nat.ltb_ge b depth) ltac:(lia)); destruct (b - depth) eqn:Hb; [lia | reflexivity].
  - apply orb_false_iff in Hs as [H1 H2].
    rewrite (IHT1 depth d1 d2 th H1 Heq), (IHT2 (S depth) d1 d2 th H2 Heq); reflexivity.
  - apply orb_false_iff in Hs as [H1 H2].
    rewrite (IHT1 depth d1 d2 th H1 Heq), (IHT2 (S depth) d1 d2 th H2 Heq); reflexivity.
  - f_equal; apply (IHT depth d1 d2 th Hs Heq).
  - f_equal. induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Hs as [H1 H2].
    rewrite (Hhd depth d1 d2 th H1 Heq), (IH Htl H2). reflexivity.
Qed.

Lemma Forall3_lengths : forall (A B C : Type) (P : A -> B -> C -> Prop) xs ys zs,
  Forall3 P xs ys zs -> length xs = length ys /\ length ys = length zs.
Proof.
  intros A B C P xs ys zs H. induction H; cbn in *; lia.
Qed.

Theorem core_erasure_simulation : forall (D : JoinDomain) fuel (theta : list (@dcty D)) env t j rho erho v,
  ErasureDomain D ->
  CoreDerives env t j ->
  erasure_wf_cterm env t ->
  EnvRel theta env (ccomp_demand j) rho erho ->
  eval_cterm fuel rho t = Some v ->
  exists ev,
    eval_ecterm fuel erho (erase_cterm env t) = Some ev /\
    ValRel (eval_dcty 0 theta (cresult_type j)) v ev.
Proof.
  intros D fuel. induction fuel as [| fuel' IH]; intros theta env t j rho erho v ED Hd Hwf Henv Hev;
    [discriminate |].
  cbn [eval_cterm] in Hev.
  destruct Hd; cbn [cresult_type ccomp_demand] in *; cbn [erase_cterm erasure_wf_cterm] in *.
  - (* CoreVar *)
    destruct Henv as [_ [_ [_ Hrel]]].
    assert (Hy : @nth_grade D (@vec_single D (length env) x one) x <> zero).
    { unfold clookup in H. rewrite nth_grade_single_eq by (apply nth_error_Some; congruence).
      intro Hz. apply (erasure_one_nonzero D ED); rewrite Hz; apply allows_refl. }
    destruct (Hrel x e H Hy) as [vx [evx [Hrx [Hex Hvx]]]].
    rewrite Hrx in Hev. inversion Hev; subst v.
    cbn [eval_ecterm]. rewrite Hex. exists evx; split; [reflexivity |].
    rewrite eval_dcty_ren_plus. exact Hvx.
  - (* CoreNat *)
    destruct (eval_cidx rho i) eqn:Hi; [| discriminate].
    inversion Hev; subst v.
    cbn [eval_ecterm]. rewrite (cidx_demand_erased_eval D theta env i d rho erho n ED Hwf H Henv Hi).
    exists (EVNat n); split; [reflexivity | apply VR_Nat].
  - (* CoreBool *)
    inversion Hev; subst v. cbn [eval_ecterm]. exists (EVBool b); split; [reflexivity | apply VR_Bool].
  - (* CoreTypeVal *)
    inversion Hev; subst v. cbn [eval_ecterm]. exists EVErased; split; [reflexivity | apply VR_Univ].
  - (* CoreLam *)
    inversion Hev; subst v. cbn [eval_ecterm].
    exists (EVClos (negb (grade_eqb s zero)) (erase_cterm ({| cbinder := x; cannotation := dom; ctype_uses := [] |} :: env) body) erho).
    split; [reflexivity |].
    destruct Henv as [Hlr [Hle [Hlt Hrel]]].
    eapply VR_Clos with (env0 := env) (theta0 := theta) (s0 := s) (r0 := r) (dom0 := dom) (cod0 := cod) (a0 := a) (u0 := u) (v0 := v0);
      try assumption; apply DSubRefl.
  - (* CoreApp *)
    destruct (eval_cterm fuel' rho fn) as [vfn |] eqn:Hfn; [| discriminate].
    destruct vfn as [| | body_fn rho_fn | | | | | |]; try discriminate.
    destruct (eval_cterm fuel' rho arg) as [varg |] eqn:Harg; [| discriminate].
    destruct Hwf as [Hwf_fn Hwf_arg].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hlen_w _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hlen_ua _].
    cbn [ccomp_demand] in Hlen_w, Hlen_ua.
    assert (Henv_fn : EnvRel theta env w rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite vec_scale_length; lia).
    assert (Henv_arg : EnvRel theta env (vec_scale s u_arg) rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite vec_scale_length; lia).
    destruct (IH _ _ _ _ _ _ _ ED Hd1 Hwf_fn Henv_fn Hfn) as [evfn [Hev_fn Hrel_fn]].
    inversion Hrel_fn; subst.
    lazymatch goal with
    | Hsub : DSubty (DPi ?s0 (eval_dcty 0 ?theta0 ?dom0) (eval_dcty 1 ?theta0 ?cod0))
                    (DPi s (eval_dcty 0 theta dom) (eval_dcty 1 theta cod)),
      Hd_b : CoreDerives ({| cbinder := ?x0; cannotation := ?dom0; ctype_uses := ?a0 |} :: ?env0) ?b0
                         {| cresult_type := ?cod0; ccomp_demand := ?u0; ctype_demand_row := _ |},
      Hwf_b : erasure_wf_cterm ({| cbinder := ?x0; cannotation := ?dom0; ctype_uses := [] |} :: ?env0) ?b0,
      Hal_s0 : allows (nth_grade ?u0 0) ?s0,
      Hrel_c : forall y e, nth_error ?env0 y = Some e -> _ ->
                 exists vy evy, nth_error ?rho0 y = Some vy /\ nth_error ?erho0 y = Some evy /\ _ |- _ =>
        assert (Hpi_sub : allows s0 s /\
                          DSubty (eval_dcty 0 theta dom) (eval_dcty 0 theta0 dom0) /\
                          DSubty (eval_dcty 1 theta0 cod0) (eval_dcty 1 theta cod)) by
          (inversion Hsub; subst; [repeat split; first [apply allows_refl | apply DSubRefl] | repeat split; assumption]);
        destruct Hpi_sub as [Hal_ss [Hsub_dom Hsub_cod]];
        pose proof (app_result_ty_no_unbox_0 D env x dom a_dom cod b arg res_ty H1 H4) as Hcod_safe;
        assert (Hcod0_nou : dcty_uses_unbox 0 (eval_dcty 1 theta0 cod0) = false) by
          (erewrite DSubty_dcty_uses_unbox; [apply cty_uses_kinds_eval_dcty_no_unbox; exact Hcod_safe | exact Hsub_cod]);
        pose proof (cterm_result_type_shape D env fn _ Hd1 env (cenv_shape_eq_refl D env)) as [tfn2 [Htfn2 Hsh_fn]];
        cbn [cresult_type] in Hsh_fn;
        destruct tfn2; cbn in Hsh_fn; try discriminate;
        repeat (apply andb_true_iff in Hsh_fn as [Hsh_fn ?]);
        repeat match goal with Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg; try rewrite Hg in Htfn2 end;
        unfold callee_grade; rewrite Htfn2;
        set (d_arg := match dom, arg with
                      | CUniv _, CTypeVal T => eval_dcty 0 theta T
                      | CUniv _, CVar y => nth y theta DUniv
                      | _, _ => DUniv
                      end);
        assert (Hcod_eq : subst_dcty 0 d_arg (eval_dcty 1 theta cod) = eval_dcty 0 theta res_ty) by
          (symmetry; exact (eval_dcty_app_result_ty D env x dom a_dom cod b arg res_ty theta H1 H4));
        assert (Hd_sub : DSubty (eval_dcty 0 (d_arg :: theta0) cod0) (eval_dcty 0 theta res_ty)) by
          (rewrite <- Hcod_eq; rewrite (eval_dcty_subst_dcty_no_unbox_0 D cod0 d_arg theta0 Hcod0_nou);
           apply DSubty_subst; exact Hsub_cod);
        assert (Hwf_b' : erasure_wf_cterm ({| cbinder := x0; cannotation := dom0; ctype_uses := a0 |} :: env0) b0) by
          (eapply erasure_wf_cterm_shape_env; [| exact Hwf_b]; constructor; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl]);
        destruct (grade_eqb_spec D s zero) as [-> | Hs_nz];
        [ assert (Hs0_z : s0 = zero) by (apply (erasure_allows_zero_eq D ED); exact Hal_ss);
          rewrite Hs0_z in Hev_fn, Hal_s0; rewrite grade_eqb_refl in Hev_fn;
          assert (Hu0_z : nth_grade u0 0 = zero) by (apply (erasure_allows_zero_eq D ED); exact Hal_s0);
          assert (Henv_b : EnvRel (d_arg :: theta0) ({| cbinder := x0; cannotation := dom0; ctype_uses := a0 |} :: env0) u0 (varg :: rho0) (EVErased :: erho0)) by
            (apply env_rel_upd_zero; assumption);
          destruct (IH (d_arg :: theta0) _ b0 _ (varg :: rho0) (EVErased :: erho0) v ED Hd_b Hwf_b' Henv_b Hev) as [evb [Hevb Hrel_b]];
          cbn [eval_ecterm]; rewrite Hev_fn;
          destruct fuel' as [| fuel'']; [discriminate |]; cbn [eval_ecterm];
          rewrite (erase_cterm_head_type_uses D x0 dom0 a0 [] env0 b0) in Hevb;
          exists evb; split; [exact Hevb | eapply ValRel_subty; [exact ED | exact Hd_sub | exact Hrel_b]]
        | destruct (IH theta env arg _ rho erho varg ED Hd2 Hwf_arg (env_rel_scale _ _ _ s _ _ _ ED Hs_nz Henv_arg) Harg) as [evarg [Hev_arg Hrel_arg]];
          cbn [eval_ecterm]; rewrite Hev_fn, Hev_arg;
          destruct (grade_eqb_spec D s0 zero) as [Hs0_z | Hs0_nz];
          [ rewrite Hs0_z in Hal_s0;
            assert (Hu0_z : nth_grade u0 0 = zero) by (apply (erasure_allows_zero_eq D ED); exact Hal_s0);
            assert (Henv_b : EnvRel (d_arg :: theta0) ({| cbinder := x0; cannotation := dom0; ctype_uses := a0 |} :: env0) u0 (varg :: rho0) (EVErased :: erho0)) by
              (apply env_rel_upd_zero; assumption);
            destruct (IH (d_arg :: theta0) _ b0 _ (varg :: rho0) (EVErased :: erho0) v ED Hd_b Hwf_b' Henv_b Hev) as [evb [Hevb Hrel_b]];
            rewrite (erase_cterm_head_type_uses D x0 dom0 a0 [] env0 b0) in Hevb;
            exists evb; split; [exact Hevb | eapply ValRel_subty; [exact ED | exact Hd_sub | exact Hrel_b]]
          | assert (Hrel_arg0 : ValRel (eval_dcty 0 theta0 dom0) varg evarg) by
              (eapply ValRel_subty; [exact ED | exact Hsub_dom | rewrite <- (eval_dcty_alpha_eq D kind dom 0 theta H); exact Hrel_arg]);
            assert (Henv_b : EnvRel (d_arg :: theta0) ({| cbinder := x0; cannotation := dom0; ctype_uses := a0 |} :: env0) u0 (varg :: rho0) (evarg :: erho0)) by
              (apply env_rel_upd_val; assumption);
            destruct (IH (d_arg :: theta0) _ b0 _ (varg :: rho0) (evarg :: erho0) v ED Hd_b Hwf_b' Henv_b Hev) as [evb [Hevb Hrel_b]];
            rewrite (erase_cterm_head_type_uses D x0 dom0 a0 [] env0 b0) in Hevb;
            exists evb; split; [exact Hevb | eapply ValRel_subty; [exact ED | exact Hd_sub | exact Hrel_b]] ] ]
    end.
  - (* CoreLet *)
    destruct (eval_cterm fuel' rho rhs) as [vr |] eqn:Hrhs; [| discriminate].
    destruct Hwf as [Hwf_rhs Hwf_body].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hlen_ur _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hlen_ub _].
    cbn [ccomp_demand] in Hlen_ur, Hlen_ub.
    assert (Henv_rhs : EnvRel theta env (vec_scale s u_rhs) rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite vec_scale_length; destruct u_bod; cbn in *; lia).
    assert (Henv_bod : EnvRel theta env (tl u_bod) rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite vec_scale_length; destruct u_bod; cbn in *; lia).
    destruct Henv_bod as [Hlr [Hle [Hlt Hrel_bod]]].
    assert (Hbod_no_u : cty_uses_kinds true false false true true true true 0 bod_ty = false) by
      (apply cty_uses_var_0_no_kinds; exact H3).
    assert (Hres_eq : eval_dcty 0 (DUniv :: theta) bod_ty = eval_dcty 0 theta (unshift_cty 0 bod_ty)) by
      (symmetry; apply eval_dcty_unshift_0; exact Hbod_no_u).
    assert (Hwf_b' : erasure_wf_cterm ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env) body) by
      (eapply erasure_wf_cterm_shape_env; [| exact Hwf_body]; constructor; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl]).
    destruct (grade_eqb_spec D s zero) as [-> | Hs_nz].
    + assert (Hub_z : nth_grade u_bod 0 = zero) by (apply (erasure_allows_zero_eq D ED); exact H1).
      assert (Henv_b : EnvRel (DUniv :: theta) ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env) u_bod (vr :: rho) (EVErased :: erho)) by
        (apply env_rel_upd_zero; assumption).
      destruct (IH (DUniv :: theta) _ body _ (vr :: rho) (EVErased :: erho) v ED Hd2 Hwf_b' Henv_b Hev) as [evb [Hevb Hrel_b]].
      cbn [eval_ecterm].
      rewrite (erase_cterm_head_type_uses D x ann a_ann [] env body) in Hevb.
      exists evb; split; [exact Hevb | rewrite <- Hres_eq; exact Hrel_b].
    + destruct (IH theta env rhs _ rho erho vr ED Hd1 Hwf_rhs (env_rel_scale _ _ _ s _ _ _ ED Hs_nz Henv_rhs) Hrhs) as [evr [Hevr Hrel_r]].
      assert (Hrel_ann : ValRel (eval_dcty 0 theta ann) vr evr) by
        (rewrite <- (eval_dcty_alpha_eq D rhs_ty ann 0 theta H0); exact Hrel_r).
      assert (Henv_b : EnvRel (DUniv :: theta) ({| cbinder := x; cannotation := ann; ctype_uses := a_ann |} :: env) u_bod (vr :: rho) (evr :: erho)) by
        (apply env_rel_upd_val; assumption).
      destruct (IH (DUniv :: theta) _ body _ (vr :: rho) (evr :: erho) v ED Hd2 Hwf_b' Henv_b Hev) as [evb [Hevb Hrel_b]].
      cbn [eval_ecterm]. rewrite Hevr.
      rewrite (erase_cterm_head_type_uses D x ann a_ann [] env body) in Hevb.
      exists evb; split; [exact Hevb | rewrite <- Hres_eq; exact Hrel_b].
  - (* CorePair *)
    destruct (eval_cterm fuel' rho fst_val) as [v1 |] eqn:H1', (eval_cterm fuel' rho snd_val) as [v2 |] eqn:H2';
      try discriminate.
    inversion Hev; subst v. destruct Hwf as [Hwf1 Hwf2].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hl1 _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hl2 _].
    cbn [ccomp_demand] in Hl1, Hl2.
    destruct (IH theta env fst_val _ rho erho v1 ED Hd1 Hwf1 (env_rel_add_l _ _ _ _ _ _ _ ED (eq_trans Hl1 (eq_sym Hl2)) Henv) H1') as [ev1 [Hev1 Hrel1]].
    destruct (IH theta env snd_val _ rho erho v2 ED Hd2 Hwf2 (env_rel_add_r _ _ _ _ _ _ _ ED (eq_trans Hl1 (eq_sym Hl2)) Henv) H2') as [ev2 [Hev2 Hrel2]].
    cbn [eval_ecterm]. rewrite Hev1, Hev2. exists (EVPair ev1 ev2); split; [reflexivity |].
    set (d_fst := match fst_ty, fst_val with
                  | CUniv _, CTypeVal T => eval_dcty 0 theta T
                  | CUniv _, CVar y => nth y theta DUniv
                  | _, _ => DUniv
                  end).
    cbn [cresult_type eval_dcty].
    cbn [cresult_type] in Hrel1, Hrel2.
    eapply VR_Pair with (d_fst := d_fst).
    + apply cty_uses_kinds_eval_dcty_no_unbox.
      eapply app_result_ty_no_unbox_0; [exact H0 | exact H3].
    + rewrite (eval_dcty_alpha_eq D fst_act fst_ty 0 theta H2) in Hrel1; exact Hrel1.
    + rewrite (eval_dcty_alpha_eq D snd_act exp_snd 0 theta H4) in Hrel2.
      rewrite (eval_dcty_app_result_ty D env x fst_ty a snd_ty b fst_val exp_snd theta H0 H3) in Hrel2.
      exact Hrel2.
  - (* CoreLetPair *)
    destruct (eval_cterm fuel' rho pr) as [vpr |] eqn:Hpr; [| discriminate].
    destruct vpr; try discriminate.
    destruct Hwf as [Hwf_pr Hwf_body].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hlen_w _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hlen_ub _].
    cbn [ccomp_demand] in Hlen_w, Hlen_ub.
    assert (Henv_pr : EnvRel theta env (vec_scale s w) rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite vec_scale_length; destruct u_b as [| ? [| ? ?]]; cbn in *; lia).
    assert (Henv_bod : EnvRel theta env (tl (tl u_b)) rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite vec_scale_length; destruct u_b as [| ? [| ? ?]]; cbn in *; lia).
    pose proof (cterm_result_type_shape D env pr _ Hd1 env (cenv_shape_eq_refl D env)) as [tpr2 [Htpr2 Hsh_pr]].
    cbn [cresult_type] in Hsh_pr.
    destruct tpr2; cbn in Hsh_pr; try discriminate.
    repeat (apply andb_true_iff in Hsh_pr as [Hsh_pr ?]).
    rewrite Htpr2. rewrite Htpr2 in Hwf_body.
    assert (Hwf_b_env : erasure_wf_cterm
      ({| cbinder := y; cannotation := B; ctype_uses := b |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env) body) by
      (eapply erasure_wf_cterm_shape_env; [| exact Hwf_body];
       constructor; [exact H9 | constructor; [exact H10 | apply cenv_shape_eq_refl]]).
    assert (Hmot_safe : cty_uses_kinds true false false true true true true 0 mot = false) by
      (eapply cdemand_not_tvar_tunbox_0; [| | exact H1];
       [intros ? C; cbn in C; discriminate | intros ? ? C; cbn in C; discriminate]).
    assert (Hmot_eq : eval_dcty 0 theta res_ty = eval_dcty 0 (DUniv :: theta) mot).
    { subst res_ty. unfold spec_pair_subj_cty.
      destruct pr; try (rewrite eval_dcty_unshift_0 with (d_any := DUniv); [reflexivity | apply cty_uses_var_0_no_kinds; exact H7]).
      - rewrite eval_dcty_subst_var_0.
        rewrite <- (eval_dcty_unshift_0 D mot _ theta Hmot_safe).
        rewrite (eval_dcty_unshift_0 D mot DUniv theta Hmot_safe). reflexivity.
      - destruct (term_as_cidx pr1) eqn:E1, (term_as_cidx pr2) eqn:E2;
          try (rewrite eval_dcty_unshift_0 with (d_any := DUniv); [reflexivity | apply cty_uses_var_0_no_kinds; exact H7]).
        apply eval_dcty_subst_pair_0; exact Hmot_safe. }
    assert (Hact_eq : eval_dcty 0 (DUniv :: DUniv :: theta) act_mot = eval_dcty 0 theta res_ty).
    { rewrite Hmot_eq, (eval_dcty_alpha_eq D act_mot exp_mot 0 (DUniv :: DUniv :: theta) H4), H3.
      apply (eval_dcty_spec_pair_body D mot DUniv DUniv DUniv theta Hmot_safe). }
    destruct Henv_bod as [Hlr [Hle [Hlt Hrel_bod]]].
    destruct (grade_eqb_spec D s zero) as [-> | Hs_nz].
    + assert (Hy_z : nth_grade u_b 0 = zero) by (apply (erasure_allows_zero_eq D ED); exact H6).
      assert (Hx_z : nth_grade (tl u_b) 0 = zero) by
        (destruct u_b as [| u0 [| u1 ur]]; cbn in *; [lia | lia | apply (erasure_allows_zero_eq D ED); exact H5]).
      assert (Henv_b : EnvRel (DUniv :: DUniv :: theta)
        ({| cbinder := y; cannotation := B; ctype_uses := b |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
        u_b (vpr2 :: vpr1 :: rho) (EVErased :: EVErased :: erho)).
      { apply env_rel_upd_zero; [exact Hy_z | cbn; lia | cbn; lia | cbn; lia |].
        destruct (env_rel_upd_zero D DUniv theta {| cbinder := x; cannotation := A; ctype_uses := a |} env (tl u_b) rho erho vpr1 EVErased
                    Hx_z Hlr Hle Hlt Hrel_bod) as [_ [_ [_ Hxy]]].
        exact Hxy. }
      destruct (IH (DUniv :: DUniv :: theta) _ body _ (vpr2 :: vpr1 :: rho) (EVErased :: EVErased :: erho) v ED Hd2 Hwf_b_env Henv_b Hev) as [evb [Hevb Hrel_b]].
      cbn [eval_ecterm].
      rewrite (erase_cterm_shape_env D body
        ({| cbinder := y; cannotation := B; ctype_uses := b |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
        ({| cbinder := y; cannotation := tpr2_2; ctype_uses := [] |} :: {| cbinder := x; cannotation := tpr2_1; ctype_uses := [] |} :: env))
        in Hevb
        by (constructor; [rewrite cty_shape_eqb_sym; exact H9 | constructor; [rewrite cty_shape_eqb_sym; exact H10 | apply cenv_shape_eq_refl]]).
      exists evb; split; [exact Hevb | rewrite <- Hact_eq; exact Hrel_b].
    + destruct (IH theta env pr _ rho erho (RPair vpr1 vpr2) ED Hd1 Hwf_pr (env_rel_scale _ _ _ s _ _ _ ED Hs_nz Henv_pr) Hpr) as [evpr [Hevpr Hrel_pr]].
      cbn [cresult_type eval_dcty] in Hrel_pr.
      inversion Hrel_pr; subst.
      lazymatch goal with
      | Hunbox : dcty_uses_unbox 0 (eval_dcty 1 theta B) = false,
        Hv1 : ValRel (eval_dcty 0 theta A) vpr1 ?ev1,
        Hv2 : ValRel (subst_dcty 0 ?d_fst_p (eval_dcty 1 theta B)) vpr2 ?ev2 |- _ =>
          rewrite <- (eval_dcty_subst_dcty_no_unbox_0 D B d_fst_p theta Hunbox) in Hv2;
          assert (Henv_b : EnvRel (DUniv :: d_fst_p :: theta)
            ({| cbinder := y; cannotation := B; ctype_uses := b |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
            u_b (vpr2 :: vpr1 :: rho) (ev2 :: ev1 :: erho)) by
            (apply env_rel_upd_val; [exact Hv2 | cbn; lia | cbn; lia | cbn; lia |];
             destruct (env_rel_upd_val D d_fst_p theta {| cbinder := x; cannotation := A; ctype_uses := a |} env (tl u_b) rho erho vpr1 ev1
                         Hv1 Hlr Hle Hlt Hrel_bod) as [_ [_ [_ Hxy]]]; exact Hxy);
          assert (Hact_eq2 : eval_dcty 0 (DUniv :: d_fst_p :: theta) act_mot = eval_dcty 0 theta (spec_pair_subj_cty pr mot)) by
            (rewrite Hmot_eq, (eval_dcty_alpha_eq D act_mot (spec_pair_body_cty 0 mot) 0 (DUniv :: d_fst_p :: theta) H4);
             apply (eval_dcty_spec_pair_body D mot d_fst_p DUniv DUniv theta Hmot_safe));
          destruct (IH (DUniv :: d_fst_p :: theta) _ body _ (vpr2 :: vpr1 :: rho) (ev2 :: ev1 :: erho) v ED Hd2 Hwf_b_env Henv_b Hev) as [evb [Hevb Hrel_b]];
          cbn [eval_ecterm]; rewrite Hevpr;
          rewrite (erase_cterm_shape_env D body
            ({| cbinder := y; cannotation := B; ctype_uses := b |} :: {| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
            ({| cbinder := y; cannotation := tpr2_2; ctype_uses := [] |} :: {| cbinder := x; cannotation := tpr2_1; ctype_uses := [] |} :: env))
            in Hevb
            by (constructor; [rewrite cty_shape_eqb_sym; exact H9 | constructor; [rewrite cty_shape_eqb_sym; exact H10 | apply cenv_shape_eq_refl]]);
          exists evb; split; [exact Hevb | rewrite <- Hact_eq2; exact Hrel_b]
      end.
  - (* CorePromote *)
    destruct (eval_cterm fuel' rho val) as [vv |] eqn:Hval; [| discriminate].
    inversion Hev; subst v.
    destruct (grade_eqb_spec D q zero) as [-> | Hq_nz].
    + cbn [eval_ecterm]. exists (EVBox EVErased); split; [reflexivity | apply VR_Box_Zero].
    + destruct (IH theta env val _ rho erho vv ED Hd Hwf (env_rel_scale _ _ _ q _ _ _ ED Hq_nz Henv) Hval) as [evv [Hevv Hrel_v]].
      cbn [eval_ecterm]. rewrite Hevv. exists (EVBox evv); split; [reflexivity | apply VR_Box; assumption].
  - (* CoreLetBox *)
    destruct (eval_cterm fuel' rho box_term) as [vbx |] eqn:Hbx; [| discriminate].
    destruct vbx; try discriminate.
    destruct Hwf as [Hwf_bx Hwf_body].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hlen_w _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hlen_ub _].
    cbn [ccomp_demand] in Hlen_w, Hlen_ub.
    assert (Henv_bx : EnvRel theta env z_b rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; destruct w; cbn in *; lia).
    assert (Henv_bod : EnvRel theta env (tl w) rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; destruct w; cbn in *; lia).
    destruct (IH theta env box_term _ rho erho (RBox vbx) ED Hd1 Hwf_bx Henv_bx Hbx) as [evbx [Hevbx Hrel_bx]].
    cbn [cresult_type eval_dcty] in Hrel_bx.
    assert (Hevbx_box : exists ev0, evbx = EVBox ev0) by (inversion Hrel_bx; eauto).
    destruct Hevbx_box as [ev0 ->].
    pose proof (cterm_result_type_shape D env box_term _ Hd1 env (cenv_shape_eq_refl D env)) as [tbx2 [Htbx2 Hsh_bx]].
    cbn [cresult_type] in Hsh_bx.
    destruct tbx2; cbn in Hsh_bx; try discriminate.
    apply andb_true_iff in Hsh_bx as [Hq_eq HA_sh].
    apply grade_eqb_sound in Hq_eq; try rewrite Hq_eq in Htbx2.
    rewrite Htbx2. rewrite Htbx2 in Hwf_body.
    assert (Hwf_b_env : erasure_wf_cterm ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) body) by
      (eapply erasure_wf_cterm_shape_env; [| exact Hwf_body];
       constructor; [exact HA_sh | apply cenv_shape_eq_refl]).
    assert (Hmot_safe : cty_uses_kinds true false true true true true true 0 mot = false) by
      (eapply cdemand_box_any_0; [| exact H0]; cbn; reflexivity).
    assert (Hres_eq : let d_unbox :=
              match box_term with
              | CPromote _ (CNatVal _) => DNat
              | CPromote _ (CTypeVal T) => eval_dcty 0 theta T
              | CPromote _ (CVar y0) => nth y0 theta DUniv
              | CVar y0 => match nth y0 theta DUniv with DBox _ inner => inner | _ => DUniv end
              | _ => DUniv
              end in
            eval_dcty 0 (d_unbox :: theta) (spec_box_body_cty q 0 mot) = eval_dcty 0 theta res_ty).
    { intro d_unbox.
      rewrite (eval_dcty_spec_box_body D mot q d_unbox theta Hmot_safe).
      subst res_ty d_unbox. unfold spec_box_subj_cty.
      destruct box_term as [y0 | | | | | | | | | q_p bx_in | | | | | | | | |];
        try (rewrite eval_dcty_unshift_0 with (d_any := DBox q DUniv) by (apply cty_uses_var_0_no_kinds; exact H6); reflexivity).
      - rewrite eval_dcty_subst_var_0.
        apply eval_dcty_head_equiv; [exact Hmot_safe |].
        destruct (nth y0 theta DUniv); reflexivity.
      - destruct bx_in as [y0 | | | | | | | | | | | | | | | | | |];
          try (rewrite eval_dcty_unshift_0 with (d_any := DBox q DUniv) by (apply cty_uses_var_0_no_kinds; exact H6); reflexivity).
        + rewrite eval_dcty_subst_var_0.
          rewrite (eval_dcty_spec_box_body D mot q_p (nth y0 theta DUniv) theta Hmot_safe).
          inversion Hd1; subst; reflexivity.
        + inversion Hd1; subst.
          lazymatch goal with Hdv : CoreDerives _ (CNatVal _) _ |- _ => inversion Hdv; subst end.
          symmetry; apply eval_dcty_subst_box_nat_0.
          eapply cdemand_not_tvar_tunbox_0; [| | exact H0];
            [intros ? C; cbn in C; discriminate | intros ? ? C; cbn in C; discriminate].
        + inversion Hd1; subst.
          symmetry; apply eval_dcty_subst_box_ty_0; exact Hmot_safe. }
    cbn zeta in Hres_eq.
    set (d_unbox :=
           match box_term with
           | CPromote _ (CNatVal _) => DNat
           | CPromote _ (CTypeVal T) => eval_dcty 0 theta T
           | CPromote _ (CVar y0) => nth y0 theta DUniv
           | CVar y0 => match nth y0 theta DUniv with DBox _ inner => inner | _ => DUniv end
           | _ => DUniv
           end) in *.
    assert (Hact_eq : eval_dcty 0 (d_unbox :: theta) act_mot = eval_dcty 0 theta res_ty).
    { rewrite (eval_dcty_alpha_eq D act_mot exp_mot 0 (d_unbox :: theta) H3), H2.
      exact Hres_eq. }
    destruct Henv_bod as [Hlr [Hle [Hlt Hrel_bod]]].
    cbn [eval_ecterm]. rewrite Hevbx.
    destruct (grade_eqb_spec D q zero) as [-> | Hq_nz].
    + assert (Hw0 : nth_grade w 0 = zero) by (apply (erasure_allows_zero_eq D ED); exact H4).
      assert (Henv_b : EnvRel (d_unbox :: theta) ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) w (vbx :: rho) (EVErased :: erho)) by
        (apply env_rel_upd_zero; assumption).
      destruct (IH (d_unbox :: theta) _ body _ (vbx :: rho) (EVErased :: erho) v ED Hd2 Hwf_b_env Henv_b Hev) as [evb [Hevb Hrel_b]].
      rewrite (erase_cterm_shape_env D body ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
                 ({| cbinder := x; cannotation := tbx2; ctype_uses := [] |} :: env)) in Hevb
        by (constructor; [rewrite cty_shape_eqb_sym; exact HA_sh | apply cenv_shape_eq_refl]).
      exists evb; split; [exact Hevb | rewrite <- Hact_eq; exact Hrel_b].
    + inversion Hrel_bx; subst; try contradiction.
      lazymatch goal with Hvi : ValRel (eval_dcty 0 theta A) vbx ?evi |- _ =>
        assert (Henv_b : EnvRel (d_unbox :: theta) ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) w (vbx :: rho) (evi :: erho)) by
          (apply env_rel_upd_val; assumption);
        destruct (IH (d_unbox :: theta) _ body _ (vbx :: rho) (evi :: erho) v ED Hd2 Hwf_b_env Henv_b Hev) as [evb [Hevb Hrel_b]];
        rewrite (erase_cterm_shape_env D body ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
                   ({| cbinder := x; cannotation := tbx2; ctype_uses := [] |} :: env)) in Hevb
          by (constructor; [rewrite cty_shape_eqb_sym; exact HA_sh | apply cenv_shape_eq_refl]);
        exists evb; split; [exact Hevb | rewrite <- Hact_eq; exact Hrel_b]
      end.
  - (* CoreInl *)
    destruct (eval_cterm fuel' rho val) as [vv |] eqn:Hval; [| discriminate].
    inversion Hev; subst v.
    destruct (IH theta env val _ rho erho vv ED Hd Hwf Henv Hval) as [evv [Hevv Hrel_v]].
    cbn [eval_ecterm]. rewrite Hevv. exists (EVInl evv); split; [reflexivity | apply VR_Sum_Inl; exact Hrel_v].
  - (* CoreInr *)
    destruct (eval_cterm fuel' rho val) as [vv |] eqn:Hval; [| discriminate].
    inversion Hev; subst v.
    destruct (IH theta env val _ rho erho vv ED Hd Hwf Henv Hval) as [evv [Hevv Hrel_v]].
    cbn [eval_ecterm]. rewrite Hevv. exists (EVInr evv); split; [reflexivity | apply VR_Sum_Inr; exact Hrel_v].
  - (* CoreMatchSum *)
    destruct (eval_cterm fuel' rho scrut) as [vsc |] eqn:Hsc; [| discriminate].
    destruct vsc; try discriminate.
    all: destruct Hwf as [Hwf_sc Hwf_brs];
         pose proof (core_derives_lengths D _ _ _ Hd1) as [Hlen_ws _];
         pose proof (core_derives_lengths D _ _ _ Hd2) as [Hlen_ul _];
         pose proof (core_derives_lengths D _ _ _ Hd3) as [Hlen_ur _];
         cbn [ccomp_demand] in Hlen_ws, Hlen_ul, Hlen_ur;
         assert (Hlen_br : length (tl u1) = length (tl u2)) by (destruct u1, u2; cbn in *; lia);
         assert (Henv_sc : EnvRel theta env (vec_scale s w) rho erho) by
           (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite vec_scale_length, (BranchVec_length _ _ _ _ Hlen_br H8); destruct u1; cbn in *; lia);
         assert (Henv_br : EnvRel theta env u_br rho erho) by
           (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite vec_scale_length, (BranchVec_length _ _ _ _ Hlen_br H8); destruct u1; cbn in *; lia);
         pose proof (cterm_result_type_shape D env scrut _ Hd1 env (cenv_shape_eq_refl D env)) as [tsc2 [Htsc2 Hsh_sc]];
         cbn [cresult_type] in Hsh_sc; destruct tsc2; cbn in Hsh_sc; try discriminate;
         apply andb_true_iff in Hsh_sc as [HA_sh HB_sh];
         rewrite Htsc2; rewrite Htsc2 in Hwf_brs; destruct Hwf_brs as [Hwf_lb Hwf_rb];
         assert (Hmot_safe : cty_uses_kinds true false false true true true true 0 mot = false) by
           (eapply cdemand_not_tvar_tunbox_0; [| | exact H2];
            [intros ? C; cbn in C; discriminate | intros ? ? C; cbn in C; discriminate]);
         set (d_sc := match scrut with CVar y0 => nth y0 theta DUniv | _ => DUniv end);
         assert (Hres_eq : eval_dcty 0 theta res_ty = eval_dcty 0 (d_sc :: theta) mot) by
           (subst res_ty d_sc; unfold spec_sum_subj_cty;
            destruct scrut as [y0 | | | | | | | | | | | ? v_in | ? v_in | | | | | |];
            try (rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_no_kinds; exact H9); reflexivity);
            [ rewrite eval_dcty_subst_var_0; reflexivity
            | destruct (term_as_cidx v_in) eqn:Ei, A;
              try (rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_no_kinds; exact H9); reflexivity);
              apply eval_dcty_subst_sum_0; exact Hmot_safe
            | destruct (term_as_cidx v_in) eqn:Ei, B;
              try (rewrite eval_dcty_unshift_0 with (d_any := DUniv) by (apply cty_uses_var_0_no_kinds; exact H9); reflexivity);
              apply eval_dcty_subst_sum_0; exact Hmot_safe ]);
         destruct (IH theta env scrut _ rho erho _ ED Hd1 Hwf_sc (env_rel_scale _ _ _ s _ _ _ ED H Henv_sc) Hsc) as [evsc [Hevsc Hrel_sc]];
         cbn [cresult_type eval_dcty] in Hrel_sc;
         inversion Hrel_sc; subst;
         cbn [eval_ecterm]; rewrite Hevsc.
    + destruct (env_rel_branch_l D theta env (tl u1) (tl u2) u_br rho erho ED Hlen_br H8 Henv_br) as [Hlr [Hle [Hlt Hrel_l]]].
      assert (Hwf_lb' : erasure_wf_cterm ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) lb) by
        (eapply erasure_wf_cterm_shape_env; [| exact Hwf_lb]; constructor; [exact HA_sh | apply cenv_shape_eq_refl]).
      lazymatch goal with Hvi : ValRel (eval_dcty 0 theta A) vsc ?evi |- _ =>
        assert (Henv_l : EnvRel (DUniv :: theta) ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env) u1 (vsc :: rho) (evi :: erho)) by
          (apply env_rel_upd_val; assumption);
        destruct (IH (DUniv :: theta) _ lb _ (vsc :: rho) (evi :: erho) v ED Hd2 Hwf_lb' Henv_l Hev) as [evb [Hevb Hrel_b]];
        rewrite (erase_cterm_shape_env D lb ({| cbinder := x; cannotation := A; ctype_uses := a |} :: env)
                   ({| cbinder := x; cannotation := tsc2_1; ctype_uses := [] |} :: env)) in Hevb
          by (constructor; [rewrite cty_shape_eqb_sym; exact HA_sh | apply cenv_shape_eq_refl]);
        exists evb; split; [exact Hevb |];
        cbn [cresult_type] in Hrel_b;
        rewrite Hres_eq, <- (eval_dcty_spec_sum_branch D mot true DUniv d_sc theta Hmot_safe),
                <- (eval_dcty_alpha_eq D t1 (spec_sum_branch_cty true 0 mot) 0 (DUniv :: theta) H4);
        exact Hrel_b
      end.
    + destruct (env_rel_branch_r D theta env (tl u1) (tl u2) u_br rho erho ED Hlen_br H8 Henv_br) as [Hlr [Hle [Hlt Hrel_r]]].
      assert (Hwf_rb' : erasure_wf_cterm ({| cbinder := y; cannotation := B; ctype_uses := b |} :: env) rb) by
        (eapply erasure_wf_cterm_shape_env; [| exact Hwf_rb]; constructor; [exact HB_sh | apply cenv_shape_eq_refl]).
      lazymatch goal with Hvi : ValRel (eval_dcty 0 theta B) vsc ?evi |- _ =>
        assert (Henv_r : EnvRel (DUniv :: theta) ({| cbinder := y; cannotation := B; ctype_uses := b |} :: env) u2 (vsc :: rho) (evi :: erho)) by
          (apply env_rel_upd_val; assumption);
        destruct (IH (DUniv :: theta) _ rb _ (vsc :: rho) (evi :: erho) v ED Hd3 Hwf_rb' Henv_r Hev) as [evb [Hevb Hrel_b]];
        rewrite (erase_cterm_shape_env D rb ({| cbinder := y; cannotation := B; ctype_uses := b |} :: env)
                   ({| cbinder := y; cannotation := tsc2_2; ctype_uses := [] |} :: env)) in Hevb
          by (constructor; [rewrite cty_shape_eqb_sym; exact HB_sh | apply cenv_shape_eq_refl]);
        exists evb; split; [exact Hevb |];
        cbn [cresult_type] in Hrel_b;
        rewrite Hres_eq, <- (eval_dcty_spec_sum_branch D mot false DUniv d_sc theta Hmot_safe),
                <- (eval_dcty_alpha_eq D t2 (spec_sum_branch_cty false 0 mot) 0 (DUniv :: theta) H5);
        exact Hrel_b
      end.
  - (* CoreIf *)
    destruct (eval_cterm fuel' rho cond) as [vc |] eqn:Hc; [| discriminate].
    destruct vc; try discriminate.
    destruct Hwf as [Hwf_c [Hwf_th Hwf_el]].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hl_c _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hl_th _].
    pose proof (core_derives_lengths D _ _ _ Hd3) as [Hl_el _].
    cbn [ccomp_demand] in Hl_c, Hl_th, Hl_el.
    assert (Henv_c : EnvRel theta env u_c rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite (BranchVec_length _ _ _ _ (eq_trans Hl_th (eq_sym Hl_el)) H0); lia).
    assert (Henv_br : EnvRel theta env u_br rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite (BranchVec_length _ _ _ _ (eq_trans Hl_th (eq_sym Hl_el)) H0); lia).
    destruct (IH theta env cond _ rho erho (RBool b) ED Hd1 Hwf_c Henv_c Hc) as [evc [Hevc Hrel_c]].
    inversion Hrel_c; subst.
    cbn [eval_ecterm]. rewrite Hevc.
    destruct b.
    + exact (IH theta env th _ rho erho v ED Hd2 Hwf_th (env_rel_branch_l D theta env u1 u2 u_br rho erho ED (eq_trans Hl_th (eq_sym Hl_el)) H0 Henv_br) Hev).
    + destruct (IH theta env el _ rho erho v ED Hd3 Hwf_el (env_rel_branch_r D theta env u1 u2 u_br rho erho ED (eq_trans Hl_th (eq_sym Hl_el)) H0 Henv_br) Hev) as [evel [Hevel Hrel_el]].
      exists evel; split; [exact Hevel |].
      cbn [cresult_type] in Hrel_el.
      rewrite (eval_dcty_alpha_eq D t2 t1 0 theta (cty_alpha_eq_sym _ _ _ H)) in Hrel_el; exact Hrel_el.
  - (* CoreRecordMk *)
    match type of Hev with option_map RRecord (?gf fields) = Some v =>
      destruct (gf fields) as [rfs |] eqn:Hrfs; [| discriminate]
    end.
    inversion Hev; subst v. destruct Hwf as [_ Hwf_fs].
    destruct (eval_cfields_erasure D fuel' theta env fields u v0 rho erho rfs ED
                (fun t' j' rho' erho' v' _ Hd' Hwf' Henv' Hev' => IH theta env t' j' rho' erho' v' ED Hd' Hwf' Henv' Hev')
                H Hwf_fs Henv Hrfs) as [erfs [Herfs Hfa]].
    cbn [eval_ecterm]. rewrite Herfs. cbn.
    eexists; split; [reflexivity | apply VR_Record; apply ValRecordRel_Forall3; rewrite map_map;
      replace (map _ fields) with (map (fun '(_, fg, ft, _) => (fg, eval_dcty 0 theta ft)) fields)
        by (apply map_ext; intros [[[fn fg] ft] fv]; reflexivity); exact Hfa].
  - (* CoreMatchRecord *)
    destruct (eval_cterm fuel' rho scrut) as [vsc |] eqn:Hsc; [| discriminate].
    destruct vsc as [| | | | | | | rfs |]; try discriminate.
    destruct Hwf as [Hwf_sc Hwf_bd].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hlen_w _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hlen_ub _].
    cbn [ccomp_demand] in Hlen_w, Hlen_ub.
    assert (Hbe_len : length body_env = length fields + length env) by
      (clear - H2; induction H2; cbn; [reflexivity | rewrite IHCRecordExtendEnv, length_map; cbn [length]; lia]).
    assert (Henv_sc : EnvRel theta env (vec_scale s w) rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite vec_scale_length, length_skipn; lia).
    assert (Henv_sk : EnvRel theta env (skipn (length fields) u_b) rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite vec_scale_length, length_skipn; lia).
    destruct (IH theta env scrut _ rho erho (RRecord rfs) ED Hd1 Hwf_sc (env_rel_scale _ _ _ s _ _ _ ED H Henv_sc) Hsc) as [evsc [Hevsc Hrel_sc]].
    cbn [cresult_type eval_dcty] in Hrel_sc.
    inversion Hrel_sc; subst.
    lazymatch goal with Hvrr : ValRecordRel _ rfs ?erfs |- _ =>
      apply ValRecordRel_Forall3 in Hvrr;
      pose proof (Forall3_lengths _ _ _ _ _ _ _ Hvrr) as [Hlen1 Hlen2];
      rewrite length_map in Hlen1;
      pose proof (cterm_result_type_shape D env scrut _ Hd1 env (cenv_shape_eq_refl D env)) as [tsc2 [Htsc2 Hsh_sc]];
      cbn [cresult_type] in Hsh_sc; destruct tsc2; cbn in Hsh_sc; try discriminate;
      apply andb_true_iff in Hsh_sc as [_ Hfs_sh];
      unfold record_fields_ty in *; rewrite Htsc2 in Hwf_bd |- *;
      destruct Hwf_bd as [Halgn2 Hwf_body];
      assert (Hfl : Forall2 (fun '(_, g1, t1') '(_, g2, t2') => g1 = g2 /\ cty_shape_eqb t1' t2' = true) fields0 fields) by
        (clear - Hfs_sh; revert fields Hfs_sh;
         induction fields0 as [| [[n1 g1] t1'] r1 IHr]; intros [| [[n2 g2] t2'] r2] Hfs_sh;
         cbn in *; try discriminate; [constructor |];
         repeat (apply andb_true_iff in Hfs_sh as [Hfs_sh ?]);
         repeat match goal with Hn : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in Hn | Hg : grade_eqb _ _ = true |- _ => apply grade_eqb_sound in Hg end;
         subst; constructor; [repeat split; assumption | apply IHr; assumption]);
      assert (Halgn : record_erasure_aligned fields) by
        (clear - Halgn2 Hfl; unfold record_erasure_aligned in *;
         assert (Hgrades_eq : map (fun '(_, g, _) => g) fields0 = map (fun '(_, g, _) => g) fields) by
           (clear - Hfl; induction Hfl; cbn; [reflexivity |];
            destruct x as [[? ?] ?], y as [[? ?] ?], H as [-> _]; f_equal; exact IHHfl);
         assert (Hto_grades : forall (A B : list (nat * grade D * cty D)),
           Forall2 (fun '(_, g1, _) '(_, g2, _) => g1 = zero <-> g2 = zero) A B <->
           Forall2 (fun g1 g2 => g1 = zero <-> g2 = zero)
             (map (fun '(_, g, _) => g) A) (map (fun '(_, g, _) => g) B)) by
           (clear; intros A; induction A as [| [[? g1] ?] A' IHA]; intros [| [[? g2] ?] B']; cbn;
            split; intro H; inversion H; subst; try apply Forall2_nil;
            (apply Forall2_cons; [assumption | apply IHA; assumption]));
         apply Hto_grades; rewrite !map_rev, <- Hgrades_eq, <- !map_rev; apply Hto_grades; exact Halgn2);
      assert (Hsh_ext : cenv_shape_eq (erase_cterm_extend env fields0) body_env) by
        (eapply cenv_shape_eq_trans;
         [ apply cenv_shape_eq_extend; [apply cenv_shape_eq_refl | exact Hfl]
         | exact (cenv_shape_eq_CRecordExtendEnv D env bs fields body_env H2) ]);
      assert (Hwf_b_env : erasure_wf_cterm body_env body) by
        (eapply erasure_wf_cterm_shape_env; [exact Hsh_ext | exact Hwf_body]);
      destruct (env_rel_record_extend D theta env bs fields body_env s u_b rho erho
                  (map (fun '(_, fg, ft) => (fg, eval_dcty 0 theta ft)) fields) rfs erfs
                  ED H H2 H4 Halgn Hvrr eq_refl ltac:(symmetry; exact Hlen1) ltac:(lia) Henv_sk)
        as [theta_ext [Hlt_ext [Henv_ext Hlift_ext]]];
      destruct (IH theta_ext body_env body _ (rev (map snd rfs) ++ rho) (rev (map snd erfs) ++ erho) v
                  ED Hd2 Hwf_b_env Henv_ext Hev) as [evb [Hevb Hrel_b]];
      cbn [eval_ecterm]; rewrite Hevsc;
      rewrite (erase_cterm_shape_env D body body_env (erase_cterm_extend env fields0)) in Hevb by
        (clear - Hsh_ext; induction Hsh_ext; constructor; [rewrite cty_shape_eqb_sym; exact H | exact IHHsh_ext]);
      exists evb; split; [exact Hevb |];
      cbn [cresult_type] in Hrel_b;
      rewrite <- Hlift_ext, <- (eval_dcty_alpha_eq D t_b (lift_cty 0 (length fields) mot) 0 theta_ext H3);
      exact Hrel_b
    end.
  - (* CoreSubgrade *)
    destruct (IH theta env body _ rho erho v ED Hd Hwf Henv Hev) as [evb [Hevb Hrel_b]].
    cbn [cresult_type] in *.
    exists evb; split;
      [ exact (eval_ecterm_fuel_mono D fuel' (S fuel') erho (erase_cterm env body) evb ltac:(lia) Hevb)
      | eapply ValRel_subty; [exact ED | apply (Subty_eval_dcty D env _ _ H) | exact Hrel_b] ].
  - (* CoreFix *)
    destruct (eval_cterm fuel' rho scrut) as [vsc |] eqn:Hsc; [| discriminate].
    destruct vsc as [n | | | | | | | |]; try discriminate.
    destruct Hwf as [Hwf_sc [Hwf_bs Hwf_st]].
    pose proof (core_derives_lengths D _ _ _ Hd1) as [Hl_us _].
    pose proof (core_derives_lengths D _ _ _ Hd2) as [Hl_ub _].
    pose proof (core_derives_lengths D _ _ _ Hd3) as [Hl_st _].
    cbn [ccomp_demand] in Hl_us, Hl_ub, Hl_st.
    assert (Henv_sc : EnvRel theta env u_s rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv]; rewrite vec_add_length; try rewrite vec_scale_length; destruct u_st as [| ? [| ? ?]]; cbn in *; lia).
    assert (Henv_rest : EnvRel theta env (vec_add u_b (vec_scale s_rec (tl (tl u_st)))) rho erho) by
      (eapply env_rel_add_r; [exact ED | | exact Henv]; rewrite vec_add_length; try rewrite vec_scale_length; destruct u_st as [| ? [| ? ?]]; cbn in *; lia).
    assert (Henv_bs : EnvRel theta env u_b rho erho) by
      (eapply env_rel_add_l; [exact ED | | exact Henv_rest]; rewrite vec_scale_length; destruct u_st as [| ? [| ? ?]]; cbn in *; lia).
    assert (Henv_st_tl : EnvRel theta env (tl (tl u_st)) rho erho).
    { pose proof (env_rel_add_r D theta env u_b (vec_scale s_rec (tl (tl u_st))) rho erho ED
                    ltac:(rewrite vec_scale_length; destruct u_st as [| ? [| ? ?]]; cbn in *; lia) Henv_rest) as Hsc_rel.
      unfold fix_recurrence_ok in H4.
      destruct (vec_is_zero (tl (tl u_st))) eqn:Hz.
      - destruct Hsc_rel as [Hlr [Hle [Hlt _]]]. apply env_rel_vec_zero; assumption.
      - destruct H4 as [Hal1 _].
        destruct (grade_eqb_spec D s_rec zero) as [-> | Hs_nz];
          [ exfalso; apply (erasure_allows_zero_eq D ED) in Hal1; apply (erasure_one_nonzero D ED); rewrite Hal1; apply allows_refl
          | exact (env_rel_scale _ _ _ s_rec _ _ _ ED Hs_nz Hsc_rel) ]. }
    destruct (IH theta env scrut _ rho erho (RNat n) ED Hd1 Hwf_sc Henv_sc Hsc) as [evsc [Hevsc Hrel_sc]].
    assert (Hevsc_eq : evsc = EVNat n) by (inversion Hrel_sc; reflexivity).
    subst evsc.
    assert (Hmot_safe : cty_uses_kinds true false false true true true true 0 mot = false) by
      (eapply cdemand_not_tvar_tunbox_0; [| | exact H];
       [intros ? C; cbn in C; discriminate | intros ? ? C; cbn in C; discriminate]).
    assert (Hres_eq : eval_dcty 0 theta res_ty = eval_dcty 0 (DUniv :: theta) mot).
    { subst res_ty. unfold spec_fix_subj_cty.
      destruct (term_as_cidx scrut) eqn:Esc;
        [ apply eval_dcty_subst_cidx_0; exact Hmot_safe
        | try rewrite Esc in H5; apply eval_dcty_unshift_0; apply cty_uses_var_0_no_kinds; exact H5 ]. }
    assert (Hbase_eq : eval_dcty 0 theta t_b = eval_dcty 0 (DUniv :: theta) mot).
    { rewrite (eval_dcty_alpha_eq D t_b (subst_cidx_in_cty 0 (CIdxLit 0) mot) 0 theta H0).
      apply eval_dcty_subst_cidx_0; exact Hmot_safe. }
    assert (Hstep_eq : eval_dcty 0 (DUniv :: DUniv :: theta) t_st = eval_dcty 0 (DUniv :: theta) mot).
    { rewrite (eval_dcty_alpha_eq D t_st (spec_fix_step_cty mot) 0 (DUniv :: DUniv :: theta) H1).
      apply eval_dcty_spec_fix_step; exact Hmot_safe. }
    assert (Hwf_st' : erasure_wf_cterm
      ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
       {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env) step) by
      (eapply erasure_wf_cterm_shape_env;
       [ | exact Hwf_st ];
       constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl]]).
    assert (Hfix : forall k vr,
      (fix eval_fix (k0 : nat) : option (@crval D) :=
         match k0 with
         | 0 => eval_cterm fuel' rho base
         | S k' => match eval_fix k' with Some vr0 => eval_cterm fuel' (vr0 :: RNat k' :: rho) step | None => None end
         end) k = Some vr ->
      exists evr,
        (fix eval_efix (k0 : nat) : option (@ecval D) :=
           match k0 with
           | 0 => eval_ecterm fuel' erho (erase_cterm env base)
           | S k' =>
               match eval_efix k' with
               | Some evr0 =>
                   eval_ecterm fuel' (evr0 :: EVNat k' :: erho)
                     (erase_cterm
                        ({| cbinder := xr; cannotation := mot; ctype_uses := [] |} ::
                         {| cbinder := xn; cannotation := CNat; ctype_uses := [] |} :: env) step)
               | None => None
               end
           end) k = Some evr /\
        ValRel (eval_dcty 0 (DUniv :: theta) mot) vr evr).
    { induction k as [| k' IHk]; intros vr Hkf.
      - destruct (IH theta env base _ rho erho vr ED Hd2 Hwf_bs Henv_bs Hkf) as [evr [Hevr Hrelr]].
        cbn [cresult_type] in Hrelr; rewrite Hbase_eq in Hrelr.
        exists evr; split; [exact Hevr | exact Hrelr].
      - destruct ((fix eval_fix (k0 : nat) : option (@crval D) :=
           match k0 with
           | 0 => eval_cterm fuel' rho base
           | S k'0 => match eval_fix k'0 with Some vr0 => eval_cterm fuel' (vr0 :: RNat k'0 :: rho) step | None => None end
           end) k') as [vr0 |] eqn:Hpk; [| discriminate].
        destruct (IHk vr0 eq_refl) as [evr0 [Hevp Hrel0]].
        destruct Henv_st_tl as [Hlr [Hle [Hlt Hrel_st]]].
        assert (Henv_step : EnvRel (DUniv :: DUniv :: theta)
          ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
           {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env)
          u_st (vr0 :: RNat k' :: rho) (evr0 :: EVNat k' :: erho)).
        { apply env_rel_upd_val; [exact Hrel0 | cbn; lia | cbn; lia | cbn; lia |].
          destruct (env_rel_upd_val D DUniv theta
            {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |}
            env (tl u_st) rho erho (RNat k') (EVNat k') (VR_Nat k') Hlr Hle Hlt
            ltac:(destruct u_st as [| ? [| ? ?]]; cbn in *; [lia | lia | exact Hrel_st])) as [_ [_ [_ Hres]]].
          exact Hres. }
        destruct (IH (DUniv :: DUniv :: theta) _ step _ (vr0 :: RNat k' :: rho) (evr0 :: EVNat k' :: erho) vr
                    ED Hd3 Hwf_st' Henv_step Hkf) as [evr [Hevr Hrelr]].
        rewrite Hevp.
        rewrite (erase_cterm_shape_env D step
          ({| cbinder := xr; cannotation := mot; ctype_uses := v_mot |} ::
           {| cbinder := xn; cannotation := CNat; ctype_uses := vec_zero (length env) |} :: env)
          ({| cbinder := xr; cannotation := mot; ctype_uses := [] |} ::
           {| cbinder := xn; cannotation := CNat; ctype_uses := [] |} :: env)) in Hevr
          by (constructor; [apply cty_shape_eqb_refl | constructor; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl]]).
        cbn [cresult_type] in Hrelr; rewrite Hstep_eq in Hrelr.
        exists evr; split; [exact Hevr | exact Hrelr]. }
    destruct (Hfix n v Hev) as [ev [Hevf Hrelf]].
    cbn [eval_ecterm cresult_type]. rewrite Hevsc. exists ev; split; [exact Hevf | rewrite Hres_eq; exact Hrelf].
Qed.

Theorem core_closed_erasure_sound : forall (D : JoinDomain) fuel (t : cterm D) j v,
  ErasureDomain D ->
  CoreDerives [] t j ->
  erasure_wf_cterm [] t ->
  eval_cterm fuel [] t = Some v ->
  exists ev,
    eval_ecterm fuel [] (erase_cterm [] t) = Some ev /\
    ValRel (eval_dcty 0 [] (cresult_type j)) v ev.
Proof.
  intros D fuel t j v ED Hd Hwf Hev.
  eapply core_erasure_simulation; [exact ED | exact Hd | exact Hwf | | exact Hev].
  repeat split; intros y e Hlk; destruct y; discriminate.
Qed.

Corollary core_zero_computation_irrelevance : forall (D : JoinDomain) fuel (theta : list (@dcty D)) env t j rho erho v,
  ErasureDomain D ->
  CoreDerives env t j ->
  erasure_wf_cterm env t ->
  EnvRel theta env (ccomp_demand j) rho erho ->
  eval_cterm fuel rho t = Some v ->
  exists ev,
    eval_ecterm fuel erho (erase_cterm env t) = Some ev /\
    ValRel (eval_dcty 0 theta (cresult_type j)) v ev.
Proof. exact core_erasure_simulation. Qed.

Theorem core_zero_var_non_interference : forall (D : JoinDomain) fuel (theta : list (@dcty D)) env t j rho1 rho2 erho v1 v2,
  ErasureDomain D ->
  CoreDerives env t j ->
  erasure_wf_cterm env t ->
  EnvRel theta env (ccomp_demand j) rho1 erho ->
  EnvRel theta env (ccomp_demand j) rho2 erho ->
  eval_cterm fuel rho1 t = Some v1 ->
  eval_cterm fuel rho2 t = Some v2 ->
  exists ev,
    eval_ecterm fuel erho (erase_cterm env t) = Some ev /\
    ValRel (eval_dcty 0 theta (cresult_type j)) v1 ev /\
    ValRel (eval_dcty 0 theta (cresult_type j)) v2 ev.
Proof.
  intros D fuel theta env t j rho1 rho2 erho v1 v2 ED Hd Hwf Henv1 Henv2 Hev1 Hev2.
  destruct (core_erasure_simulation D fuel theta env t j rho1 erho v1 ED Hd Hwf Henv1 Hev1) as [ev1 [He1 Hr1]].
  destruct (core_erasure_simulation D fuel theta env t j rho2 erho v2 ED Hd Hwf Henv2 Hev2) as [ev2 [He2 Hr2]].
  rewrite He1 in He2; inversion He2; subst ev2.
  exists ev1; repeat split; assumption.
Qed.

(* ================================================================= *)
(* Part 3: CBV Erasure Preservation of Effectful Zero-Graded Args    *)
(* ================================================================= *)

Inductive core_outcome (Value : Type) : Type :=
| CoreReturned (v : Value)
| CoreFailed (reason : nat).

Arguments CoreReturned {Value} _.
Arguments CoreFailed {Value} _.

Record core_execution (State Event : Type) : Type := {
  core_final_state : State;
  core_trace : list Event;
  core_result : core_outcome nat;
}.

Arguments core_final_state {State Event} _.
Arguments core_trace {State Event} _.
Arguments core_result {State Event} _.

Inductive core_observation (Event : Type) : Type :=
| CoreArgEvent (event : Event)
| CoreArgReturned (value : nat).

Arguments CoreArgEvent {Event} _.
Arguments CoreArgReturned {Event} _.

Record core_cbv_argument (D : JoinDomain) (State Event : Type) : Type := {
  cbv_param : nat * grade D;
  cbv_run : State -> core_execution State Event;
}.

Arguments cbv_param {D State Event} _.
Arguments cbv_run {D State Event} _ _.

Record erased_core_cbv_arg (State Event : Type) : Type := {
  erased_retain : bool;
  erased_run : State -> core_execution State Event;
}.

Arguments erased_retain {State Event} _.
Arguments erased_run {State Event} _ _.

Definition erase_core_cbv_arg {D : JoinDomain} {State Event : Type}
    (arg : core_cbv_argument D State Event) : erased_core_cbv_arg State Event :=
  {| erased_retain := negb (grade_eqb (snd (cbv_param arg)) zero);
     erased_run := cbv_run arg |}.

Fixpoint core_nat_telescope {D : JoinDomain} (params : list (nat * grade D)) (body : cidx D) : cterm D :=
  match params with
  | [] => CNatVal body
  | (x, s) :: rest => CLam x s zero CNat (core_nat_telescope rest body)
  end.

Fixpoint evaluate_core_cbv {D : JoinDomain} {State Event : Type}
    (arguments : list (core_cbv_argument D State Event))
    (rho : list (@crval D)) (body : cidx D) (initial : State)
  : core_execution State (core_observation Event) :=
  match arguments with
  | [] =>
      let res := match eval_cidx rho body with Some n => CoreReturned n | None => CoreFailed 0 end in
      {| core_final_state := initial; core_trace := []; core_result := res |}
  | arg :: rest =>
      let evaluated := cbv_run arg initial in
      let effects := map CoreArgEvent (core_trace evaluated) in
      match core_result evaluated with
      | CoreFailed reason =>
          {| core_final_state := core_final_state evaluated;
             core_trace := effects;
             core_result := CoreFailed reason |}
      | CoreReturned value =>
          let next := evaluate_core_cbv rest (RNat value :: rho) body (core_final_state evaluated) in
          {| core_final_state := core_final_state next;
             core_trace := effects ++ CoreArgReturned value :: core_trace next;
             core_result := core_result next |}
      end
  end.

Fixpoint evaluate_erased_core_cbv {D : JoinDomain} {State Event : Type}
    (arguments : list (erased_core_cbv_arg State Event))
    (erho : list (@ecval D)) (body : cidx D) (initial : State)
  : core_execution State (core_observation Event) :=
  match arguments with
  | [] =>
      let res := match eval_ecidx erho body with Some n => CoreReturned n | None => CoreFailed 0 end in
      {| core_final_state := initial; core_trace := []; core_result := res |}
  | arg :: rest =>
      let evaluated := erased_run arg initial in
      let effects := map CoreArgEvent (core_trace evaluated) in
      match core_result evaluated with
      | CoreFailed reason =>
          {| core_final_state := core_final_state evaluated;
             core_trace := effects;
             core_result := CoreFailed reason |}
      | CoreReturned value =>
          let erho' := (if erased_retain arg then EVNat value else EVErased) :: erho in
          let next := evaluate_erased_core_cbv rest erho' body (core_final_state evaluated) in
          {| core_final_state := core_final_state next;
             core_trace := effects ++ CoreArgReturned value :: core_trace next;
             core_result := core_result next |}
      end
  end.

Definition erased_core_cbv_eval {D : JoinDomain} {State Event : Type}
    (arguments : list (core_cbv_argument D State Event))
    (erho : list (@ecval D)) (body : cidx D) (initial : State)
  : core_execution State (core_observation Event) :=
  evaluate_erased_core_cbv (map erase_core_cbv_arg arguments) erho body initial.

Theorem core_cbv_erasure_sound : forall (D : JoinDomain) State Event
    (arguments : list (core_cbv_argument D State Event)) theta env body j rho erho initial,
  ErasureDomain D ->
  CoreDerives env (core_nat_telescope (map cbv_param arguments) body) j ->
  cidx_no_zero_unbox (fold_left (fun acc p => {| cbinder := fst p; cannotation := CNat; ctype_uses := [] |} :: acc)
                        (map cbv_param arguments) env) body ->
  EnvRel theta env (ccomp_demand j) rho erho ->
  erased_core_cbv_eval arguments erho body initial =
    evaluate_core_cbv arguments rho body initial.
Proof.
  intros D State Event arguments.
  induction arguments as [| arg rest IH]; intros theta env body j rho erho initial ED Hd Hnz Henv;
    cbn in *.
  - inversion Hd; subst. cbn [ccomp_demand] in Henv.
    lazymatch goal with Hcd : CIdxDemand env body ?d |- _ => rename Hcd into Hcd_body end.
    destruct (eval_cidx rho body) eqn:Hev.
    + rewrite (cidx_demand_erased_eval D theta env body _ rho erho n ED Hnz Hcd_body Henv Hev).
      reflexivity.
    + assert (Hrev_eval : forall m, eval_ecidx erho body = Some m -> eval_cidx rho body = Some m).
      { clear - ED Hnz Hcd_body Henv.
        assert (Hg : forall (env0 : cenv D) (body0 : cidx D) d0,
          CIdxDemand env0 body0 d0 ->
          forall (theta0 : list (@dcty D)) (rho0 : list (@crval D)) (erho0 : list (@ecval D)) m,
            cidx_no_zero_unbox env0 body0 ->
            EnvRel theta0 env0 d0 rho0 erho0 ->
            eval_ecidx erho0 body0 = Some m -> eval_cidx rho0 body0 = Some m).
        { clear - ED.
          intros env body d Hd.
          induction Hd; intros theta rho erho m Hnz Henv He_ec; cbn in *;
          [ unfold clookup in H; destruct Henv as [_ [_ [_ Hrel]]];
            assert (Hy : @nth_grade D (@vec_single D (length env) x one) x <> zero) by
              (rewrite nth_grade_single_eq by (apply nth_error_Some; congruence);
               intro Hz; apply (erasure_one_nonzero D ED); rewrite Hz; apply allows_refl);
            destruct (Hrel x e H Hy) as [vx [evx [Hrx [Hex Hvx]]]];
            rewrite Hrx, Hex in *;
            pose proof (eval_dcty_alpha_eq D (cannotation e) CNat 0 (skipn (S x) theta) H0) as Hnat;
            rewrite Hnat in Hvx;
            cbn in Hvx; inversion Hvx; subst; exact He_ec
          | exact He_ec
          | destruct (eval_ecidx erho l) eqn:El, (eval_ecidx erho r) eqn:Er; try discriminate;
            inversion He_ec; subst; destruct Hnz as [Hnz1 Hnz2];
            pose proof (cidx_demand_length D _ _ _ Hd1) as Hl1;
            pose proof (cidx_demand_length D _ _ _ Hd2) as Hl2;
            rewrite (IHHd1 _ _ _ _ Hnz1 (env_rel_add_l _ _ _ _ _ _ _ ED (eq_trans Hl1 (eq_sym Hl2)) Henv) El),
                    (IHHd2 _ _ _ _ Hnz2 (env_rel_add_r _ _ _ _ _ _ _ ED (eq_trans Hl1 (eq_sym Hl2)) Henv) Er);
            reflexivity
          | destruct (grade_eqb_spec D q zero) as [_ | Hq_nz]; [discriminate |];
            exact (IHHd _ _ _ _ Hnz (env_rel_scale _ _ _ q _ _ _ ED Hq_nz Henv) He_ec)
          | unfold clookup in H, Hnz; rewrite H in Hnz; destruct Henv as [_ [_ [_ Hrel]]];
            assert (Hy : @nth_grade D (@vec_single D (length env) b one) b <> zero) by
              (rewrite nth_grade_single_eq by (apply nth_error_Some; congruence);
               intro Hz; apply (erasure_one_nonzero D ED); rewrite Hz; apply allows_refl);
            destruct (Hrel b e H Hy) as [vb [evb [Hrb [Heb Hvb]]]];
            rewrite Hrb, Heb in *;
            pose proof (eval_dcty_alpha_eq D (cannotation e) (CBox q CNat) 0 (skipn (S b) theta) H0) as Hbx;
            rewrite Hbx in Hvb;
            cbn in Hvb; inversion Hvb; subst;
            [ exfalso; rewrite (erase_hints_alpha_eq _ _ _ H0) in Hnz; cbn in Hnz; contradiction
            | lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end; exact He_ec ]
          | unfold clookup in H; destruct Henv as [_ [_ [_ Hrel]]];
            assert (Hy : @nth_grade D (@vec_single D (length env) p one) p <> zero) by
              (rewrite nth_grade_single_eq by (apply nth_error_Some; congruence);
               intro Hz; apply (erasure_one_nonzero D ED); rewrite Hz; apply allows_refl);
            destruct (Hrel p e H Hy) as [vp [evp [Hrp [Hep Hvp]]]];
            rewrite Hrp, Hep in *;
            pose proof (eval_dcty_alpha_eq D (cannotation e) (CSigma z r CNat snd_ty) 0 (skipn (S p) theta) H0) as Hsg;
            rewrite Hsg in Hvp;
            cbn in Hvp; inversion Hvp; subst;
            lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end; exact He_ec
          | unfold clookup in H; destruct Henv as [_ [_ [_ Hrel]]];
            assert (Hy : @nth_grade D (@vec_single D (length env) p one) p <> zero) by
              (rewrite nth_grade_single_eq by (apply nth_error_Some; congruence);
               intro Hz; apply (erasure_one_nonzero D ED); rewrite Hz; apply allows_refl);
            destruct (Hrel p e H Hy) as [vp [evp [Hrp [Hep Hvp]]]];
            rewrite Hrp, Hep in *;
            pose proof (eval_dcty_alpha_eq D (cannotation e) (CSigma z r fst_ty CNat) 0 (skipn (S p) theta) H0) as Hsg;
            rewrite Hsg in Hvp;
            cbn in Hvp; inversion Hvp; subst;
            lazymatch goal with Hvr : ValRel (subst_dcty 0 ?df DNat) _ _ |- _ => cbn in Hvr; inversion Hvr; subst end; exact He_ec
          | unfold clookup in H, Hnz; rewrite H in Hnz;
            destruct (erase_hints (cannotation e)) eqn:Hee; try contradiction;
            lazymatch type of Hnz with
            | match ?a0 with CNat => match ?b0 with CNat => _ | _ => _ end | _ => _ end =>
                destruct a0, b0; try contradiction
            end;
            destruct Hnz as [Hnz1 Hnz2];
            assert (HAB : erase_hints A = CNat /\ erase_hints B = CNat) by
              (unfold cty_alpha_eq in H0; rewrite erase_hints_ren, Hee in H0; cbn in H0; inversion H0; split; reflexivity);
            destruct HAB as [HA HB];
            assert (HnzA : cidx_no_zero_unbox ({| cbinder := 0; cannotation := A; ctype_uses := vec_zero (length env) |} :: env) l) by
              (eapply cidx_no_zero_unbox_shape_env; [| exact Hnz1];
               constructor; [cbn [cannotation]; rewrite cty_shape_eqb_sym, <- cty_shape_eqb_erase_hints_l, HA; reflexivity | apply cenv_shape_eq_refl]);
            assert (HnzB : cidx_no_zero_unbox ({| cbinder := 0; cannotation := B; ctype_uses := vec_zero (length env) |} :: env) r) by
              (eapply cidx_no_zero_unbox_shape_env; [| exact Hnz2];
               constructor; [cbn [cannotation]; rewrite cty_shape_eqb_sym, <- cty_shape_eqb_erase_hints_l, HB; reflexivity | apply cenv_shape_eq_refl]);
            destruct Henv as [Hlr [Hle [Hlt Hrel]]];
            pose proof (cidx_demand_length D _ _ _ Hd1) as Hl1;
            pose proof (cidx_demand_length D _ _ _ Hd2) as Hl2;
            cbn [length] in Hl1, Hl2;
            assert (Hlen_tl : length (tl dl) = length (tl dr)) by (destruct dl, dr; cbn in *; lia);
            lazymatch goal with Hbv : BranchVec _ _ ?dbr |- _ =>
            assert (Hbr_len : length dbr = length env) by
              (rewrite (BranchVec_length D _ _ _ Hlen_tl Hbv); destruct dl; cbn in *; lia);
            assert (Hs : nth_grade (vec_add (vec_single (length env) s one) dbr) s <> zero) by
              (rewrite nth_grade_vec_add_safe by (rewrite vec_single_length; lia);
               rewrite nth_grade_single_eq by (apply nth_error_Some; congruence);
               intro Hsum; apply (erasure_add_zero D ED) in Hsum as [H1z _];
               apply (erasure_one_nonzero D ED); rewrite H1z; apply allows_refl);
            destruct (Hrel s e H Hs) as [vs [evs [Hrs [Hes Hvs]]]];
            rewrite Hrs, Hes in *;
            pose proof (eval_dcty_alpha_eq D (ren_cty (plus (S s)) (cannotation e)) (CSum CNat CNat) 0 theta
                          ltac:(unfold cty_alpha_eq; rewrite erase_hints_ren, Hee; reflexivity)) as Hsm;
            rewrite eval_dcty_ren_plus in Hsm; rewrite Hsm in Hvs;
            cbn in Hvs; inversion Hvs; subst;
            lazymatch goal with Hvr : ValRel DNat _ _ |- _ => inversion Hvr; subst end;
            [ eapply IHHd1; [exact HnzA | | exact He_ec];
              assert (Henv_br : EnvRel theta env dbr rho erho) by
                (eapply env_rel_add_r; [exact ED | | exact (conj Hlr (conj Hle (conj Hlt Hrel)))]; rewrite vec_single_length; lia);
              destruct dl as [| hd_l tl_l], dr as [| hd_r tl_r]; cbn in *; try lia;
              eapply env_rel_upd_val with (d0 := DUniv);
              [ cbn [cannotation]; rewrite (eval_dcty_alpha_eq D A CNat 0 theta HA); apply VR_Nat
              | exact Hlr | exact Hle | exact Hlt
              | assert (Hdl : EnvRel theta env (tl (hd_l :: tl_l)) rho erho) by
                  (eapply env_rel_branch_l; [exact ED | exact Hlen_tl | eassumption | exact Henv_br]);
                destruct Hdl as [_ [_ [_ Hdl']]]; exact Hdl' ]
            | eapply IHHd2; [exact HnzB | | exact He_ec];
              assert (Henv_br : EnvRel theta env dbr rho erho) by
                (eapply env_rel_add_r; [exact ED | | exact (conj Hlr (conj Hle (conj Hlt Hrel)))]; rewrite vec_single_length; lia);
              destruct dl as [| hd_l tl_l], dr as [| hd_r tl_r]; cbn in *; try lia;
              eapply env_rel_upd_val with (d0 := DUniv);
              [ cbn [cannotation]; rewrite (eval_dcty_alpha_eq D B CNat 0 theta HB); apply VR_Nat
              | exact Hlr | exact Hle | exact Hlt
              | assert (Hdr : EnvRel theta env (tl (hd_r :: tl_r)) rho erho) by
                  (eapply env_rel_branch_r; [exact ED | exact Hlen_tl | eassumption | exact Henv_br]);
                destruct Hdr as [_ [_ [_ Hdr']]]; exact Hdr' ] ]
            end ]. }
        intros m Hm. exact (Hg _ _ _ Hcd_body theta rho erho m Hnz Henv Hm). }
      destruct (eval_ecidx erho body) as [m |] eqn:He_ec; [rewrite (Hrev_eval m eq_refl) in Hev; discriminate | reflexivity].
  - destruct arg as [[x s] run]; cbn in *.
    inversion Hd; subst. cbn [ccomp_demand] in Henv.
    lazymatch goal with
    | Hdb : CoreDerives ({| cbinder := x; cannotation := CNat; ctype_uses := ?a |} :: env)
                        (core_nat_telescope (map cbv_param rest) body)
                        {| cresult_type := _; ccomp_demand := ?u; ctype_demand_row := _ |},
      Hal : allows (nth_grade ?u 0) s |- _ =>
        unfold erased_core_cbv_eval, erase_core_cbv_arg; cbn;
        destruct (run initial) as [after trace [val | reason]] eqn:Hrun; cbn [core_final_state core_trace core_result]; [| reflexivity];
        destruct Henv as [Hlr [Hle [Hlt Hrel]]];
        assert (Henv' : EnvRel (DUniv :: theta)
          ({| cbinder := x; cannotation := CNat; ctype_uses := a |} :: env)
          u (RNat val :: rho)
          ((if negb (grade_eqb s zero) then EVNat val else EVErased) :: erho)) by
          (destruct (grade_eqb_spec D s zero) as [-> | Hs_nz]; cbn;
           [ apply env_rel_upd_zero; try assumption;
             apply (erasure_allows_zero_eq D ED); exact Hal
           | apply env_rel_upd_val; try assumption; apply VR_Nat ]);
        assert (Hnz' : cidx_no_zero_unbox
          (fold_left (fun acc p => {| cbinder := fst p; cannotation := CNat; ctype_uses := [] |} :: acc)
             (map cbv_param rest) ({| cbinder := x; cannotation := CNat; ctype_uses := a |} :: env)) body) by
          (clear - Hnz;
           assert (Hg : forall (ps : list (nat * grade D)) e1 e2,
             cenv_shape_eq e1 e2 ->
             cidx_no_zero_unbox (fold_left (fun acc p => {| cbinder := fst p; cannotation := CNat; ctype_uses := [] |} :: acc) ps e1) body ->
             cidx_no_zero_unbox (fold_left (fun acc p => {| cbinder := fst p; cannotation := CNat; ctype_uses := [] |} :: acc) ps e2) body) by
             (induction ps as [| [p1 p2] pr IHps]; intros e1 e2 Hsh Hnb; cbn in *;
               [eapply cidx_no_zero_unbox_shape_env; eauto |
                apply IHps with (e1 := {| cbinder := p1; cannotation := CNat; ctype_uses := [] |} :: e1);
                  [constructor; [apply cty_shape_eqb_refl | exact Hsh] | exact Hnb]]);
           eapply Hg; [| exact Hnz];
           constructor; [apply cty_shape_eqb_refl | apply cenv_shape_eq_refl]);
        pose proof (IH (DUniv :: theta) ({| cbinder := x; cannotation := CNat; ctype_uses := a |} :: env)
                       body _ (RNat val :: rho) ((if negb (grade_eqb s zero) then EVNat val else EVErased) :: erho)
                       after ED Hdb Hnz' Henv') as Hrec;
        unfold erased_core_cbv_eval in Hrec;
        destruct (grade_eqb s zero);
        cbn;
        unfold erase_core_cbv_arg in Hrec;
        cbn in Hrec;
        rewrite Hrec;
        reflexivity
    end.
Qed.

(* ================================================================= *)
(* Part 4: Q25cb Substitution Skipping Soundness for Unified Core    *)
(* ================================================================= *)

Lemma iter_ren_shift_unshift_eq : forall k x,
  x <> k ->
  Nat.iter k ren_shift (fun i => match i with 0 => 0 | S i' => i' end) x =
  if x <? k then x else x - 1.
Proof.
  induction k as [| k IH]; intros x Hne.
  - change (Nat.iter 0 ren_shift (fun i => match i with 0 => 0 | S i' => i' end))
      with (fun i => match i with 0 => 0 | S i' => i' end).
    destruct x as [| x']; [contradiction | destruct (Nat.ltb_spec (S x') 0); lia].
  - change (Nat.iter (S k) ren_shift (fun i => match i with 0 => 0 | S i' => i' end))
      with (ren_shift (Nat.iter k ren_shift (fun i => match i with 0 => 0 | S i' => i' end))).
    destruct x as [| x'].
    + reflexivity.
    + unfold ren_shift at 1. rewrite IH by lia.
      destruct (Nat.ltb_spec x' k), (Nat.ltb_spec (S x') (S k)); lia.
Qed.

Lemma subst_cidx_skip : forall (D : JoinDomain) (i val : cidx D) k,
  cidx_uses_var k i = false ->
  subst_cidx k val i = unshift_cidx k i.
Proof.
  intros D i. induction i; intros val k Huv; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huv as [H1 H2]; rewrite (IHi1 val k H1), (IHi2 val k H2); reflexivity);
    try (rewrite (IHi val k Huv); reflexivity).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq x k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. rewrite iter_ren_shift_unshift_eq by exact Hne.
    destruct (Nat.ltb_spec x k); reflexivity.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq b k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq p k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq p k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - apply orb_false_iff in Huv as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
    destruct (Nat.eq_dec s k) as [-> | Hne]; [rewrite Nat.eqb_refl in H1; discriminate |].
    rewrite (proj2 (Nat.eqb_neq s k) Hne).
    rewrite (IHi1 (lift_cidx 0 1 val) (S k) H2), (IHi2 (lift_cidx 0 1 val) (S k) H3).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
Qed.

Lemma subst_tvar_in_cidx_skip : forall (D : JoinDomain) (i : cidx D) k,
  cidx_uses_var k i = false ->
  subst_tvar_in_cidx k i = unshift_cidx k i.
Proof.
  intros D i. induction i; intros k Huv; cbn in *; try reflexivity;
    try (apply orb_false_iff in Huv as [H1 H2]; rewrite (IHi1 k H1), (IHi2 k H2); reflexivity);
    try (rewrite (IHi k Huv); reflexivity).
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq x k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq b k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq p k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - destruct (Nat.eq_dec p k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq p k) Hne).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - apply orb_false_iff in Huv as [H12 H3]; apply orb_false_iff in H12 as [H1 H2].
    destruct (Nat.eq_dec s k) as [-> | Hne]; [rewrite Nat.eqb_refl in H1; discriminate |].
    rewrite (proj2 (Nat.eqb_neq s k) Hne).
    rewrite (IHi1 (S k) H2), (IHi2 (S k) H3).
    unfold unshift_cidx; cbn [ren_cidx]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
Qed.

Lemma subst_cidx_in_cty_skip : forall (D : JoinDomain) (T : cty D) (val : cidx D) k,
  cty_uses_var k T = false ->
  subst_cidx_in_cty k val T = unshift_cty k T.
Proof.
  intros D T. induction T using cty_ind_nested; intros val k Huv; cbn in *; try reflexivity;
    try (rewrite (IHT val k Huv); reflexivity);
    try (apply orb_false_iff in Huv as [H1 H2]; rewrite (IHT1 val k H1), (IHT2 val k H2); reflexivity).
  - apply orb_false_iff in Huv as [H1 H2].
    rewrite (IHT val k H1), (subst_cidx_skip D len val k H2). reflexivity.
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq x k) Hne).
    unfold unshift_cty; cbn [ren_cty]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq b k) Hne).
    unfold unshift_cty; cbn [ren_cty]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - apply orb_false_iff in Huv as [H1 H2].
    rewrite (IHT1 val k H1), (IHT2 (lift_cidx 0 1 val) (S k) H2). reflexivity.
  - apply orb_false_iff in Huv as [H1 H2].
    rewrite (IHT1 val k H1), (IHT2 (lift_cidx 0 1 val) (S k) H2). reflexivity.
  - unfold unshift_cty; cbn [ren_cty]; f_equal.
    induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Huv as [H1 H2].
    f_equal; [f_equal; apply (Hhd val k H1) | apply (IH Htl H2)].
  - unfold unshift_cty; cbn [ren_cty]; f_equal.
    induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huv as [H1 H2].
    f_equal; [apply (subst_cidx_skip D idx0 val k H1) | apply (IH H2)].
Qed.

Lemma subst_tvar_in_cty_skip : forall (D : JoinDomain) (T U : cty D) k,
  cty_uses_var k T = false ->
  subst_tvar_in_cty k U T = unshift_cty k T.
Proof.
  intros D T. induction T using cty_ind_nested; intros U k Huv; cbn in *; try reflexivity;
    try (rewrite (IHT U k Huv); reflexivity);
    try (apply orb_false_iff in Huv as [H1 H2]; rewrite (IHT1 U k H1), (IHT2 U k H2); reflexivity).
  - apply orb_false_iff in Huv as [H1 H2].
    rewrite (IHT U k H1), (subst_tvar_in_cidx_skip D len k H2). reflexivity.
  - destruct (Nat.eq_dec x k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq x k) Hne).
    unfold unshift_cty; cbn [ren_cty]. rewrite iter_ren_shift_unshift_eq by exact Hne.
    destruct (Nat.ltb_spec x k); reflexivity.
  - destruct (Nat.eq_dec b k) as [-> | Hne]; [rewrite Nat.eqb_refl in Huv; discriminate |].
    rewrite (proj2 (Nat.eqb_neq b k) Hne).
    unfold unshift_cty; cbn [ren_cty]. f_equal. symmetry. apply iter_ren_shift_unshift_eq; exact Hne.
  - apply orb_false_iff in Huv as [H1 H2].
    rewrite (IHT1 U k H1), (IHT2 (lift_cty 0 1 U) (S k) H2). reflexivity.
  - apply orb_false_iff in Huv as [H1 H2].
    rewrite (IHT1 U k H1), (IHT2 (lift_cty 0 1 U) (S k) H2). reflexivity.
  - unfold unshift_cty; cbn [ren_cty]; f_equal.
    induction fields as [| [[fn fg] ft] rest IH]; cbn in *; [reflexivity |].
    inversion H as [| ? ? Hhd Htl]; subst; cbn in Hhd. apply orb_false_iff in Huv as [H1 H2].
    f_equal; [f_equal; apply (Hhd U k H1) | apply (IH Htl H2)].
  - unfold unshift_cty; cbn [ren_cty]; f_equal.
    induction indices as [| idx0 rest IH]; cbn in *; [reflexivity |].
    apply orb_false_iff in Huv as [H1 H2].
    f_equal; [apply (subst_tvar_in_cidx_skip D idx0 k H1) | apply (IH H2)].
Qed.

Definition core_apply_nat_spec {D : JoinDomain} (cod : cty D) (idx : cidx D) : cty D :=
  subst_cidx_in_cty 0 idx cod.

Definition core_apply_nat_skip {D : JoinDomain} (cod : cty D) : cty D :=
  unshift_cty 0 cod.

Definition core_apply_tvar_spec {D : JoinDomain} (cod arg : cty D) : cty D :=
  subst_tvar_in_cty 0 arg cod.

Definition core_apply_tvar_skip {D : JoinDomain} (cod : cty D) : cty D :=
  unshift_cty 0 cod.

Definition core_let_nat_spec {D : JoinDomain} (bod_ty : cty D) (idx : cidx D) : cty D :=
  subst_cidx_in_cty 0 idx bod_ty.

Definition core_let_nat_skip {D : JoinDomain} (bod_ty : cty D) : cty D :=
  unshift_cty 0 bod_ty.

Lemma ctype_demand_zero_unused_0 : forall (D : JoinDomain) (env : cenv D) x (dom : cty D) a (cod : cty D) b,
  ErasureDomain D ->
  CTypeDemand ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) cod b ->
  allows (nth_grade b 0) zero ->
  no_zero_prom_cty cod ->
  cty_uses_var 0 cod = false.
Proof.
  intros D env x dom a cod b ED Hd Hal Hnz.
  exact (proj1 (core_zero_type_use_irrelevance D ED _ cod b 0 Hd ltac:(cbn; lia) Hal Hnz)).
Qed.

Theorem core_skip_subst_agrees : forall (D : JoinDomain) (env : cenv D) x (dom : cty D) a (cod : cty D) b (idx : cidx D) (U : cty D),
  ErasureDomain D ->
  CTypeDemand ({| cbinder := x; cannotation := dom; ctype_uses := a |} :: env) cod b ->
  allows (nth_grade b 0) zero ->
  no_zero_prom_cty cod ->
  core_apply_nat_spec cod idx = core_apply_nat_skip cod /\
  core_apply_tvar_spec cod U = core_apply_tvar_skip cod /\
  core_let_nat_spec cod idx = core_let_nat_skip cod.
Proof.
  intros D env x dom a cod b idx U ED Hd Hal Hnz.
  pose proof (ctype_demand_zero_unused_0 D env x dom a cod b ED Hd Hal Hnz) as Huv.
  repeat split; unfold core_apply_nat_spec, core_apply_nat_skip,
    core_apply_tvar_spec, core_apply_tvar_skip, core_let_nat_spec, core_let_nat_skip.
  - apply subst_cidx_in_cty_skip; exact Huv.
  - apply subst_tvar_in_cty_skip; exact Huv.
  - apply subst_cidx_in_cty_skip; exact Huv.
Qed.

End GradedCoreErasure.
