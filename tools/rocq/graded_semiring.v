(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.
Require Import graded_pure graded_domains.
Import ListNotations.

Module GradedSemiring.
Import GradedPure.

(* ================================================================= *)
(* Part 1: Symbolic Grade Expressions and Canonical Polynomials      *)
(* ================================================================= *)

Inductive grade_expr : Type :=
| GLit (n : nat)
| GVar (x : nat)
| GAdd (e1 e2 : grade_expr)
| GMul (e1 e2 : grade_expr).

Fixpoint eval_grade (rho : nat -> nat) (e : grade_expr) : nat :=
  match e with
  | GLit n => n
  | GVar x => rho x
  | GAdd e1 e2 => eval_grade rho e1 + eval_grade rho e2
  | GMul e1 e2 => eval_grade rho e1 * eval_grade rho e2
  end.

Definition vars := list nat.

Fixpoint eval_vars (rho : nat -> nat) (vs : vars) : nat :=
  match vs with
  | [] => 1
  | x :: rest => rho x * eval_vars rho rest
  end.

Fixpoint insert_var (x : nat) (xs : vars) : vars :=
  match xs with
  | [] => [x]
  | y :: rest => if Nat.leb x y then x :: xs else y :: insert_var x rest
  end.

Lemma eval_vars_insert : forall rho x xs,
  eval_vars rho (insert_var x xs) = rho x * eval_vars rho xs.
Proof.
  intros rho x xs. induction xs as [| y rest IH]; cbn.
  - reflexivity.
  - destruct (Nat.leb x y); cbn; [reflexivity |].
    rewrite IH. lia || nia.
Qed.

Fixpoint mul_vars (xs ys : vars) : vars :=
  match xs with
  | [] => ys
  | x :: rest => insert_var x (mul_vars rest ys)
  end.

Lemma eval_vars_mul : forall rho xs ys,
  eval_vars rho (mul_vars xs ys) = eval_vars rho xs * eval_vars rho ys.
Proof.
  intros rho xs ys. induction xs as [| x rest IH]; cbn.
  - lia.
  - rewrite eval_vars_insert, IH. nia.
Qed.

Fixpoint vars_cmp (xs ys : vars) : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: xs', y :: ys' =>
      match Nat.compare x y with
      | Lt => Lt
      | Gt => Gt
      | Eq => vars_cmp xs' ys'
      end
  end.

Lemma vars_cmp_eq : forall xs ys,
  vars_cmp xs ys = Eq -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; destruct ys as [| y ys']; cbn; intro H; try discriminate.
  - reflexivity.
  - destruct (Nat.compare x y) eqn:Ec; try discriminate.
    apply Nat.compare_eq in Ec. subst y. f_equal. apply IH; exact H.
Qed.

Definition poly := list (nat * vars).

Fixpoint eval_poly (rho : nat -> nat) (p : poly) : nat :=
  match p with
  | [] => 0
  | (c, vs) :: rest => c * eval_vars rho vs + eval_poly rho rest
  end.

Fixpoint insert_term (c : nat) (vs : vars) (p : poly) : poly :=
  if Nat.eqb c 0 then p else
  match p with
  | [] => [(c, vs)]
  | (c', vs') :: rest =>
      match vars_cmp vs vs' with
      | Lt => (c, vs) :: p
      | Eq =>
          let s := c + c' in
          if Nat.eqb s 0 then rest else (s, vs') :: rest
      | Gt => (c', vs') :: insert_term c vs rest
      end
  end.

Lemma eval_poly_insert_term : forall rho c vs p,
  eval_poly rho (insert_term c vs p) = c * eval_vars rho vs + eval_poly rho p.
Proof.
  intros rho c vs p.
  destruct (Nat.eqb c 0) eqn:Ec0.
  - apply Nat.eqb_eq in Ec0. subst c. cbn.
    unfold insert_term. destruct p; reflexivity.
  - induction p as [| [c' vs'] rest IH]; cbn.
    + rewrite Ec0. cbn. reflexivity.
    + rewrite Ec0.
      destruct (vars_cmp vs vs') eqn:Hcmp; cbn.
      * apply vars_cmp_eq in Hcmp. subst vs'.
        destruct (Nat.eqb (c + c') 0) eqn:Es0.
        -- apply Nat.eqb_eq in Es0. assert (Hc0 : c = 0) by lia.
           apply Nat.eqb_neq in Ec0. congruence.
        -- cbn. nia.
      * reflexivity.
      * cbn in IH. rewrite IH. lia.
Qed.

Fixpoint add_poly (p1 p2 : poly) : poly :=
  match p1 with
  | [] => p2
  | (c, vs) :: rest => insert_term c vs (add_poly rest p2)
  end.

Lemma eval_poly_add : forall rho p1 p2,
  eval_poly rho (add_poly p1 p2) = eval_poly rho p1 + eval_poly rho p2.
Proof.
  intros rho p1 p2. induction p1 as [| [c vs] rest IH]; cbn.
  - reflexivity.
  - rewrite eval_poly_insert_term, IH. lia.
Qed.

Fixpoint scale_term (c : nat) (vs : vars) (p : poly) : poly :=
  match p with
  | [] => []
  | (c', vs') :: rest =>
      insert_term (c * c') (mul_vars vs vs') (scale_term c vs rest)
  end.

Lemma eval_poly_scale_term : forall rho c vs p,
  eval_poly rho (scale_term c vs p) = c * eval_vars rho vs * eval_poly rho p.
Proof.
  intros rho c vs p. induction p as [| [c' vs'] rest IH]; cbn.
  - lia.
  - rewrite eval_poly_insert_term, eval_vars_mul, IH. nia.
Qed.

Fixpoint mul_poly (p1 p2 : poly) : poly :=
  match p1 with
  | [] => []
  | (c, vs) :: rest => add_poly (scale_term c vs p2) (mul_poly rest p2)
  end.

Lemma eval_poly_mul : forall rho p1 p2,
  eval_poly rho (mul_poly p1 p2) = eval_poly rho p1 * eval_poly rho p2.
Proof.
  intros rho p1 p2. induction p1 as [| [c vs] rest IH]; cbn.
  - reflexivity.
  - rewrite eval_poly_add, eval_poly_scale_term, IH. nia.
Qed.

Fixpoint normalize_grade (e : grade_expr) : poly :=
  match e with
  | GLit n => if Nat.eqb n 0 then [] else [(n, [])]
  | GVar x => [(1, [x])]
  | GAdd e1 e2 => add_poly (normalize_grade e1) (normalize_grade e2)
  | GMul e1 e2 => mul_poly (normalize_grade e1) (normalize_grade e2)
  end.

Theorem normalize_grade_sound : forall rho e,
  eval_poly rho (normalize_grade e) = eval_grade rho e.
Proof.
  intros rho e. induction e; cbn.
  - destruct (Nat.eqb n 0) eqn:En.
    + apply Nat.eqb_eq in En. subst n. reflexivity.
    + cbn. lia.
  - cbn. lia.
  - rewrite eval_poly_add, IHe1, IHe2. reflexivity.
  - rewrite eval_poly_mul, IHe1, IHe2. reflexivity.
Qed.

Fixpoint vars_eqb (xs ys : vars) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && vars_eqb xs' ys'
  | _, _ => false
  end.

Lemma vars_eqb_sound : forall xs ys, vars_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs' IH]; destruct ys as [| y ys']; cbn; intro H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [Hxy Hrest]. apply Nat.eqb_eq in Hxy. subst y.
    f_equal. apply IH; exact Hrest.
Qed.

Fixpoint poly_eqb (p1 p2 : poly) : bool :=
  match p1, p2 with
  | [], [] => true
  | (c1, vs1) :: r1, (c2, vs2) :: r2 =>
      Nat.eqb c1 c2 && vars_eqb vs1 vs2 && poly_eqb r1 r2
  | _, _ => false
  end.

Lemma poly_eqb_sound : forall p1 p2, poly_eqb p1 p2 = true -> p1 = p2.
Proof.
  induction p1 as [| [c1 vs1] r1 IH]; destruct p2 as [| [c2 vs2] r2]; cbn; intro H; try discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [Hhead Hrest].
    apply andb_true_iff in Hhead as [Hc Hvs].
    apply Nat.eqb_eq in Hc. apply vars_eqb_sound in Hvs. subst.
    f_equal. apply IH; exact Hrest.
Qed.

Definition grade_eqb (e1 e2 : grade_expr) : bool :=
  poly_eqb (normalize_grade e1) (normalize_grade e2).

Definition grade_eq (e1 e2 : grade_expr) : Prop :=
  forall rho, eval_grade rho e1 = eval_grade rho e2.

Theorem grade_eqb_sound : forall e1 e2,
  grade_eqb e1 e2 = true -> forall rho, eval_grade rho e1 = eval_grade rho e2.
Proof.
  intros e1 e2 Heq rho. unfold grade_eqb in Heq.
  apply poly_eqb_sound in Heq.
  rewrite <- !normalize_grade_sound, Heq. reflexivity.
Qed.

Fixpoint poly_leb (p1 p2 : poly) : bool :=
  match p1 with
  | [] => true
  | (c1, vs1) :: r1 =>
      match p2 with
      | [] => false
      | (c2, vs2) :: r2 =>
          match vars_cmp vs1 vs2 with
          | Lt => false
          | Eq => Nat.leb c1 c2 && poly_leb r1 r2
          | Gt => poly_leb p1 r2
          end
      end
  end.

Lemma poly_leb_sound : forall p1 p2,
  poly_leb p1 p2 = true -> forall rho, eval_poly rho p1 <= eval_poly rho p2.
Proof.
  intros p1 p2. revert p1.
  induction p2 as [| [c2 vs2] r2 IH]; intros [| [c1 vs1] r1] Hle rho; cbn in *.
  - lia.
  - discriminate.
  - lia.
  - destruct (vars_cmp vs1 vs2) eqn:Hcmp.
    + apply vars_cmp_eq in Hcmp. subst vs1.
      apply andb_true_iff in Hle as [Hc Hr]. apply Nat.leb_le in Hc.
      specialize (IH r1 Hr rho). nia.
    + discriminate.
    + specialize (IH ((c1, vs1) :: r1) Hle rho). cbn in IH. lia.
Qed.

Definition grade_leb (e1 e2 : grade_expr) : bool :=
  poly_leb (normalize_grade e1) (normalize_grade e2).

Definition grade_le (e1 e2 : grade_expr) : Prop :=
  forall rho, eval_grade rho e1 <= eval_grade rho e2.

Theorem grade_leb_sound : forall e1 e2,
  grade_leb e1 e2 = true -> forall rho, eval_grade rho e1 <= eval_grade rho e2.
Proof.
  intros e1 e2 Hle rho. unfold grade_leb in Hle.
  rewrite <- !normalize_grade_sound. apply poly_leb_sound; exact Hle.
Qed.

Lemma semiring_laws_universal :
  forall q r s : grade_expr,
    grade_eq (GAdd q r) (GAdd r q) /\
    grade_eq (GAdd (GAdd q r) s) (GAdd q (GAdd r s)) /\
    grade_eq (GMul (GAdd q r) s) (GMul s (GAdd q r)) /\
    grade_eq (GMul (GMul q r) s) (GMul q (GMul r s)) /\
    grade_eq (GMul q (GAdd r s)) (GAdd (GMul q r) (GMul q s)) /\
    grade_eq (GMul (GLit 0) q) (GLit 0) /\
    grade_eq (GMul (GLit 1) q) q /\
    grade_eq (GAdd (GLit 0) q) q.
Proof.
  intros q r s. repeat split; intro rho; cbn; nia.
Qed.

Example semiring_axioms_concrete :
  let q := GVar 0 in
  let r := GVar 1 in
  let s := GVar 2 in
  grade_eqb (GAdd q r) (GAdd r q) = true /\
  grade_eqb (GAdd (GAdd q r) s) (GAdd q (GAdd r s)) = true /\
  grade_eqb (GMul (GAdd q r) s) (GMul s (GAdd q r)) = true /\
  grade_eqb (GMul (GMul q r) s) (GMul q (GMul r s)) = true /\
  grade_eqb (GMul q (GAdd r s)) (GAdd (GMul q r) (GMul q s)) = true /\
  grade_eqb (GMul (GLit 0) q) (GLit 0) = true /\
  grade_eqb (GMul (GLit 1) q) q = true /\
  grade_eqb (GAdd (GLit 0) q) q = true /\
  grade_leb q (GAdd q r) = true /\
  grade_leb (GLit 0) q = true.
Proof.
  repeat split; reflexivity.
Qed.

(* ================================================================= *)
(* Part 2: Grade-Polymorphic Linear / Semiring Type System           *)
(* ================================================================= *)

Inductive pty : Type :=
| PUnitTy
| PBase (id : nat)
| PBox (q : grade_expr) (payload : pty)
| PArr (q : grade_expr) (domain codomain : pty)
| PProd (left right : pty).

Fixpoint pty_eqb (A B : pty) : bool :=
  match A, B with
  | PUnitTy, PUnitTy => true
  | PBase a, PBase b => Nat.eqb a b
  | PBox q1 A1, PBox q2 A2 => grade_eqb q1 q2 && pty_eqb A1 A2
  | PArr q1 A1 B1, PArr q2 A2 B2 => grade_eqb q1 q2 && pty_eqb A1 A2 && pty_eqb B1 B2
  | PProd A1 B1, PProd A2 B2 => pty_eqb A1 A2 && pty_eqb B1 B2
  | _, _ => false
  end.

Fixpoint eval_pty (rho : nat -> nat) (t : pty) : pty :=
  match t with
  | PUnitTy => PUnitTy
  | PBase n => PBase n
  | PBox q X => PBox (GLit (eval_grade rho q)) (eval_pty rho X)
  | PArr q X Y => PArr (GLit (eval_grade rho q)) (eval_pty rho X) (eval_pty rho Y)
  | PProd X Y => PProd (eval_pty rho X) (eval_pty rho Y)
  end.

Definition pty_eq (A B : pty) : Prop :=
  forall rho, eval_pty rho A = eval_pty rho B.

Lemma pty_eqb_sound : forall A B,
  pty_eqb A B = true -> pty_eq A B.
Proof.
  induction A; destruct B; cbn; intro H; try discriminate.
  - intro rho; reflexivity.
  - apply Nat.eqb_eq in H. subst. intro rho; reflexivity.
  - apply andb_true_iff in H as [Hq HA].
    pose proof (grade_eqb_sound _ _ Hq) as Hq'. apply IHA in HA.
    intro rho. cbn. rewrite (Hq' rho), (HA rho). reflexivity.
  - apply andb_true_iff in H as [H1 HB].
    apply andb_true_iff in H1 as [Hq HA].
    pose proof (grade_eqb_sound _ _ Hq) as Hq'. apply IHA1 in HA. apply IHA2 in HB.
    intro rho. cbn. rewrite (Hq' rho), (HA rho), (HB rho). reflexivity.
  - apply andb_true_iff in H as [HA HB].
    apply IHA1 in HA. apply IHA2 in HB.
    intro rho. cbn. rewrite (HA rho), (HB rho). reflexivity.
Qed.

Inductive pterm : Type :=
| PVar (x : nat)
| PUnit
| PLam (x : nat) (q : grade_expr) (domain : pty) (body : pterm)
| PApp (callee arg : pterm)
| PPair (lhs rhs : pterm)
| PLetPair (x y : nat) (s : grade_expr) (pr body : pterm)
| PPromote (q : grade_expr) (body : pterm)
| PLetBox (x : nat) (box_term body : pterm).

Definition pdemand := list (nat * grade_expr).

Fixpoint puses (d : pdemand) (x : nat) : grade_expr :=
  match d with
  | [] => GLit 0
  | (y, g) :: rest => if Nat.eqb x y then GAdd g (puses rest x) else puses rest x
  end.

Definition pwithout (x : nat) (d : pdemand) : pdemand :=
  filter (fun '(y, _) => negb (Nat.eqb x y)) d.

Definition pscale (q : grade_expr) (d : pdemand) : pdemand :=
  map (fun '(y, g) => (y, GMul q g)) d.

Record pbinding := {
  pbinder : nat;
  pannotation : pty;
}.

Definition pcontext := list pbinding.

Definition plookup (env : pcontext) (x : nat) : option pty :=
  match find (fun entry => Nat.eqb x (pbinder entry)) env with
  | Some entry => Some (pannotation entry)
  | None => None
  end.

Definition pfresh (env : pcontext) (x : nat) : bool :=
  match plookup env x with None => true | Some _ => false end.

Record pjudgment := {
  presult_type : pty;
  pdemand_row : pdemand;
}.

Inductive PolyDerives (allows : grade_expr -> grade_expr -> Prop) (env : pcontext)
  : pterm -> pjudgment -> Prop :=
| PGradeVar : forall x A,
    plookup env x = Some A ->
    PolyDerives allows env (PVar x) {| presult_type := A; pdemand_row := [(x, GLit 1)] |}
| PGradeUnit :
    PolyDerives allows env PUnit {| presult_type := PUnitTy; pdemand_row := [] |}
| PGradeLam : forall x q dom body cod u,
    pfresh env x = true ->
    PolyDerives allows ({| pbinder := x; pannotation := dom |} :: env) body
      {| presult_type := cod; pdemand_row := u |} ->
    allows (puses u x) q ->
    PolyDerives allows env (PLam x q dom body)
      {| presult_type := PArr q dom cod; pdemand_row := pwithout x u |}
| PGradeApp : forall callee arg q dom cod kind w z,
    PolyDerives allows env callee {| presult_type := PArr q dom cod; pdemand_row := w |} ->
    PolyDerives allows env arg {| presult_type := kind; pdemand_row := z |} ->
    pty_eq kind dom ->
    PolyDerives allows env (PApp callee arg)
      {| presult_type := cod; pdemand_row := w ++ pscale q z |}
| PGradePair : forall lhs rhs A B ul ur,
    PolyDerives allows env lhs {| presult_type := A; pdemand_row := ul |} ->
    PolyDerives allows env rhs {| presult_type := B; pdemand_row := ur |} ->
    PolyDerives allows env (PPair lhs rhs)
      {| presult_type := PProd A B; pdemand_row := ul ++ ur |}
| PGradeLetPair : forall x y s pr body A B mot w u,
    pfresh env x = true ->
    pfresh ({| pbinder := x; pannotation := A |} :: env) y = true ->
    PolyDerives allows env pr {| presult_type := PProd A B; pdemand_row := w |} ->
    PolyDerives allows ({| pbinder := y; pannotation := B |} :: {| pbinder := x; pannotation := A |} :: env)
      body {| presult_type := mot; pdemand_row := u |} ->
    allows (puses u x) s ->
    allows (puses u y) s ->
    PolyDerives allows env (PLetPair x y s pr body)
      {| presult_type := mot; pdemand_row := pwithout x (pwithout y u) ++ pscale s w |}
| PGradePromote : forall q body A u,
    PolyDerives allows env body {| presult_type := A; pdemand_row := u |} ->
    PolyDerives allows env (PPromote q body)
      {| presult_type := PBox q A; pdemand_row := pscale q u |}
| PGradeLetBox : forall x box_term body q A mot z w,
    pfresh env x = true ->
    PolyDerives allows env box_term {| presult_type := PBox q A; pdemand_row := z |} ->
    PolyDerives allows ({| pbinder := x; pannotation := A |} :: env)
      body {| presult_type := mot; pdemand_row := w |} ->
    allows (puses w x) q ->
    PolyDerives allows env (PLetBox x box_term body)
      {| presult_type := mot; pdemand_row := pwithout x w ++ z |}.

Fixpoint poly_infer (allowsb : grade_expr -> grade_expr -> bool) (env : pcontext) (t : pterm)
  : option pjudgment :=
  match t with
  | PVar x =>
      match plookup env x with
      | Some A => Some {| presult_type := A; pdemand_row := [(x, GLit 1)] |}
      | None => None
      end
  | PUnit => Some {| presult_type := PUnitTy; pdemand_row := [] |}
  | PLam x q dom body =>
      if pfresh env x then
        match poly_infer allowsb ({| pbinder := x; pannotation := dom |} :: env) body with
        | Some {| presult_type := cod; pdemand_row := u |} =>
            if allowsb (puses u x) q then
              Some {| presult_type := PArr q dom cod; pdemand_row := pwithout x u |}
            else None
        | None => None
        end
      else None
  | PApp callee arg =>
      match poly_infer allowsb env callee, poly_infer allowsb env arg with
      | Some {| presult_type := PArr q dom cod; pdemand_row := w |},
        Some {| presult_type := kind; pdemand_row := z |} =>
          if pty_eqb kind dom then
            Some {| presult_type := cod; pdemand_row := w ++ pscale q z |}
          else None
      | _, _ => None
      end
  | PPair lhs rhs =>
      match poly_infer allowsb env lhs, poly_infer allowsb env rhs with
      | Some {| presult_type := A; pdemand_row := ul |},
        Some {| presult_type := B; pdemand_row := ur |} =>
          Some {| presult_type := PProd A B; pdemand_row := ul ++ ur |}
      | _, _ => None
      end
  | PLetPair x y s pr body =>
      if pfresh env x then
        match poly_infer allowsb env pr with
        | Some {| presult_type := PProd A B; pdemand_row := w |} =>
            let env1 := {| pbinder := x; pannotation := A |} :: env in
            if pfresh env1 y then
              match poly_infer allowsb ({| pbinder := y; pannotation := B |} :: env1) body with
              | Some {| presult_type := mot; pdemand_row := u |} =>
                  if allowsb (puses u x) s && allowsb (puses u y) s then
                    Some {| presult_type := mot; pdemand_row := pwithout x (pwithout y u) ++ pscale s w |}
                  else None
              | None => None
              end
            else None
        | _ => None
        end
      else None
  | PPromote q body =>
      match poly_infer allowsb env body with
      | Some {| presult_type := A; pdemand_row := u |} =>
          Some {| presult_type := PBox q A; pdemand_row := pscale q u |}
      | None => None
      end
  | PLetBox x box_term body =>
      if pfresh env x then
        match poly_infer allowsb env box_term with
        | Some {| presult_type := PBox q A; pdemand_row := z |} =>
            match poly_infer allowsb ({| pbinder := x; pannotation := A |} :: env) body with
            | Some {| presult_type := mot; pdemand_row := w |} =>
                if allowsb (puses w x) q then
                  Some {| presult_type := mot; pdemand_row := pwithout x w ++ z |}
                else None
            | None => None
            end
        | _ => None
        end
      else None
  end.

Theorem poly_infer_sound : forall allows allowsb,
  (forall a b, allowsb a b = true -> allows a b) ->
  forall t env res,
    poly_infer allowsb env t = Some res ->
    PolyDerives allows env t res.
Proof.
  intros allows allowsb Hsound t.
  induction t; intros env res Hchk; cbn in Hchk.
  - destruct (plookup env x) as [A |] eqn:Hlkp; inversion Hchk; subst.
    constructor; exact Hlkp.
  - inversion Hchk; subst; constructor.
  - destruct (pfresh env x) eqn:Hfr; try discriminate.
    destruct (poly_infer allowsb ({| pbinder := x; pannotation := domain |} :: env) t)
      as [[cod u] |] eqn:Hb; try discriminate.
    destruct (allowsb (puses u x) q) eqn:Hq; inversion Hchk; subst.
    eapply PGradeLam; eauto.
  - destruct (poly_infer allowsb env t1) as [[rt1 w] |] eqn:Hc; try discriminate.
    destruct rt1 as [| | | q dom cod |]; try discriminate.
    destruct (poly_infer allowsb env t2) as [[kind z] |] eqn:Ha; try discriminate.
    destruct (pty_eqb kind dom) eqn:Heq; inversion Hchk; subst.
    eapply PGradeApp; eauto using pty_eqb_sound.
  - destruct (poly_infer allowsb env t1) as [[A ul] |] eqn:Hl; try discriminate.
    destruct (poly_infer allowsb env t2) as [[B ur] |] eqn:Hr; inversion Hchk; subst.
    constructor; auto.
  - destruct (pfresh env x) eqn:Hfrx; try discriminate.
    destruct (poly_infer allowsb env t1) as [[prt w] |] eqn:Hp; try discriminate.
    destruct prt as [| | | | A B]; try discriminate.
    destruct (pfresh ({| pbinder := x; pannotation := A |} :: env) y) eqn:Hfry; try discriminate.
    destruct (poly_infer allowsb
                ({| pbinder := y; pannotation := B |} :: {| pbinder := x; pannotation := A |} :: env) t2)
      as [[mot u] |] eqn:Hb; try discriminate.
    destruct (allowsb (puses u x) s && allowsb (puses u y) s) eqn:Hs; inversion Hchk; subst.
    apply andb_true_iff in Hs as [Hsx Hsy].
    eapply PGradeLetPair; eauto.
  - destruct (poly_infer allowsb env t) as [[A u] |] eqn:Hb; inversion Hchk; subst.
    constructor; auto.
  - destruct (pfresh env x) eqn:Hfr; try discriminate.
    destruct (poly_infer allowsb env t1) as [[brt z] |] eqn:Hbx; try discriminate.
    destruct brt as [| | q A | |]; try discriminate.
    destruct (poly_infer allowsb ({| pbinder := x; pannotation := A |} :: env) t2)
      as [[mot w] |] eqn:Hb; try discriminate.
    destruct (allowsb (puses w x) q) eqn:Hq; inversion Hchk; subst.
    eapply PGradeLetBox; eauto.
Qed.

(* Evaluate symbolic demand and verify concrete NatBounded specialization for ALL rho *)
Definition eval_pdemand (rho : nat -> nat) (d : pdemand) : demand :=
  map (fun '(x, g) => (x, eval_grade rho g)) d.

Lemma eval_puses : forall rho d x,
  uses (eval_pdemand rho d) x = eval_grade rho (puses d x).
Proof.
  intros rho d x. unfold eval_pdemand.
  induction d as [| [y g] rest IH]; cbn; [reflexivity |].
  destruct (Nat.eqb x y); cbn; [rewrite IH; reflexivity | exact IH].
Qed.

Lemma eval_pwithout : forall rho x d,
  eval_pdemand rho (pwithout x d) = without x (eval_pdemand rho d).
Proof.
  intros rho x d. unfold eval_pdemand, pwithout, without.
  induction d as [| [y g] rest IH]; cbn; [reflexivity |].
  destruct (Nat.eqb x y); cbn; [exact IH | f_equal; exact IH].
Qed.

Lemma eval_pscale : forall rho q d,
  eval_pdemand rho (pscale q d) = scale (eval_grade rho q) (eval_pdemand rho d).
Proof.
  intros rho q d. unfold eval_pdemand, pscale, scale.
  induction d as [| [y g] rest IH]; cbn; [reflexivity |].
  f_equal; exact IH.
Qed.

Lemma eval_pdemand_app : forall rho d1 d2,
  eval_pdemand rho (d1 ++ d2) = eval_pdemand rho d1 ++ eval_pdemand rho d2.
Proof.
  intros rho d1 d2. apply map_app.
Qed.

(* For all valuations rho : nat -> nat, every grade_le-valid PolyDerives checks concrete Nat.le bounds *)
Inductive ConcretePolyOk (env : pcontext) (rho : nat -> nat) : pterm -> pjudgment -> Prop :=
| CPolyVar : forall x A,
    plookup env x = Some A ->
    ConcretePolyOk env rho (PVar x) {| presult_type := A; pdemand_row := [(x, GLit 1)] |}
| CPolyUnit :
    ConcretePolyOk env rho PUnit {| presult_type := PUnitTy; pdemand_row := [] |}
| CPolyLam : forall x q dom body cod u,
    pfresh env x = true ->
    ConcretePolyOk ({| pbinder := x; pannotation := dom |} :: env) rho body
      {| presult_type := cod; pdemand_row := u |} ->
    uses (eval_pdemand rho u) x <= eval_grade rho q ->
    ConcretePolyOk env rho (PLam x q dom body)
      {| presult_type := PArr q dom cod; pdemand_row := pwithout x u |}
| CPolyApp : forall callee arg q dom cod kind w z,
    ConcretePolyOk env rho callee {| presult_type := PArr q dom cod; pdemand_row := w |} ->
    ConcretePolyOk env rho arg {| presult_type := kind; pdemand_row := z |} ->
    pty_eq kind dom ->
    ConcretePolyOk env rho (PApp callee arg)
      {| presult_type := cod; pdemand_row := w ++ pscale q z |}
| CPolyPair : forall lhs rhs A B ul ur,
    ConcretePolyOk env rho lhs {| presult_type := A; pdemand_row := ul |} ->
    ConcretePolyOk env rho rhs {| presult_type := B; pdemand_row := ur |} ->
    ConcretePolyOk env rho (PPair lhs rhs)
      {| presult_type := PProd A B; pdemand_row := ul ++ ur |}
| CPolyLetPair : forall x y s pr body A B mot w u,
    pfresh env x = true ->
    pfresh ({| pbinder := x; pannotation := A |} :: env) y = true ->
    ConcretePolyOk env rho pr {| presult_type := PProd A B; pdemand_row := w |} ->
    ConcretePolyOk ({| pbinder := y; pannotation := B |} :: {| pbinder := x; pannotation := A |} :: env) rho
      body {| presult_type := mot; pdemand_row := u |} ->
    uses (eval_pdemand rho u) x <= eval_grade rho s ->
    uses (eval_pdemand rho u) y <= eval_grade rho s ->
    ConcretePolyOk env rho (PLetPair x y s pr body)
      {| presult_type := mot; pdemand_row := pwithout x (pwithout y u) ++ pscale s w |}
| CPolyPromote : forall q body A u,
    ConcretePolyOk env rho body {| presult_type := A; pdemand_row := u |} ->
    ConcretePolyOk env rho (PPromote q body)
      {| presult_type := PBox q A; pdemand_row := pscale q u |}
| CPolyLetBox : forall x box_term body q A mot z w,
    pfresh env x = true ->
    ConcretePolyOk env rho box_term {| presult_type := PBox q A; pdemand_row := z |} ->
    ConcretePolyOk ({| pbinder := x; pannotation := A |} :: env) rho
      body {| presult_type := mot; pdemand_row := w |} ->
    uses (eval_pdemand rho w) x <= eval_grade rho q ->
    ConcretePolyOk env rho (PLetBox x box_term body)
      {| presult_type := mot; pdemand_row := pwithout x w ++ z |}.

Theorem poly_derives_all_valuations : forall env t res,
  PolyDerives grade_le env t res ->
  forall rho, ConcretePolyOk env rho t res.
Proof.
  intros env t res Hd rho. induction Hd; try (econstructor; eauto; fail).
  - eapply CPolyLam; eauto. rewrite eval_puses. apply H0.
  - eapply CPolyLetPair; eauto; rewrite eval_puses; [apply H1 | apply H2].
  - eapply CPolyLetBox; eauto. rewrite eval_puses. apply H0.
Qed.

Corollary poly_exact_infer_all_valuations : forall env t res,
  poly_infer grade_eqb env t = Some res ->
  forall rho, ConcretePolyOk env rho t res.
Proof.
  intros env t res Hchk rho.
  apply poly_derives_all_valuations.
  eapply poly_infer_sound; [| exact Hchk].
  intros a b Heq r. rewrite (grade_eqb_sound a b Heq r). lia.
Qed.

Corollary poly_bounded_infer_all_valuations : forall env t res,
  poly_infer grade_leb env t = Some res ->
  forall rho, ConcretePolyOk env rho t res.
Proof.
  intros env t res Hchk rho.
  apply poly_derives_all_valuations.
  eapply poly_infer_sound; [| exact Hchk].
  exact grade_leb_sound.
Qed.

(* ================================================================= *)
(* Part 3: Verified Grade-Polymorphic Combinators & Negative Controls*)
(* ================================================================= *)

Definition g_q : grade_expr := GVar 0.
Definition g_r : grade_expr := GVar 1.
Definition p_A : pty := PBase 42.

(* poly_duplicate : Box (q * r) A -> Box q (Box r A) *)
Definition poly_duplicate_term : pterm :=
  PLam 1 (GLit 1) (PBox (GMul g_q g_r) p_A)
    (PLetBox 2 (PVar 1)
      (PPromote g_q (PPromote g_r (PVar 2)))).

Theorem poly_duplicate_verified :
  (match poly_infer grade_eqb [] poly_duplicate_term with
   | Some res =>
       presult_type res = PArr (GLit 1) (PBox (GMul g_q g_r) p_A) (PBox g_q (PBox g_r p_A))
   | None => False
   end) /\
  (forall rho,
    match poly_infer grade_eqb [] poly_duplicate_term with
    | Some res => ConcretePolyOk [] rho poly_duplicate_term res
    | None => False
    end).
Proof.
  split; [reflexivity |].
  intro rho.
  destruct (poly_infer grade_eqb [] poly_duplicate_term) eqn:Hchk; [| vm_compute in Hchk; discriminate].
  eapply poly_exact_infer_all_valuations; exact Hchk.
Qed.

(* poly_split : Box (q + r) A -> Box q A * Box r A *)
Definition poly_split_term : pterm :=
  PLam 1 (GLit 1) (PBox (GAdd g_q g_r) p_A)
    (PLetBox 2 (PVar 1)
      (PPair (PPromote g_q (PVar 2)) (PPromote g_r (PVar 2)))).

Theorem poly_split_verified :
  (match poly_infer grade_eqb [] poly_split_term with
   | Some res =>
       presult_type res = PArr (GLit 1) (PBox (GAdd g_q g_r) p_A) (PProd (PBox g_q p_A) (PBox g_r p_A))
   | None => False
   end) /\
  (forall rho,
    match poly_infer grade_eqb [] poly_split_term with
    | Some res => ConcretePolyOk [] rho poly_split_term res
    | None => False
    end).
Proof.
  split; [reflexivity |].
  intro rho.
  destruct (poly_infer grade_eqb [] poly_split_term) eqn:Hchk; [| vm_compute in Hchk; discriminate].
  eapply poly_exact_infer_all_valuations; exact Hchk.
Qed.

(* poly_extract : Box 1 A -> A *)
Definition poly_extract_term : pterm :=
  PLam 1 (GLit 1) (PBox (GLit 1) p_A)
    (PLetBox 2 (PVar 1) (PVar 2)).

Theorem poly_extract_verified :
  (match poly_infer grade_eqb [] poly_extract_term with
   | Some res => presult_type res = PArr (GLit 1) (PBox (GLit 1) p_A) p_A
   | None => False
   end) /\
  (forall rho,
    match poly_infer grade_eqb [] poly_extract_term with
    | Some res => ConcretePolyOk [] rho poly_extract_term res
    | None => False
    end).
Proof.
  split; [reflexivity |].
  intro rho.
  destruct (poly_infer grade_eqb [] poly_extract_term) eqn:Hchk; [| vm_compute in Hchk; discriminate].
  eapply poly_exact_infer_all_valuations; exact Hchk.
Qed.

(* poly_discard : Box 0 A -> Unit *)
Definition poly_discard_term : pterm :=
  PLam 1 (GLit 1) (PBox (GLit 0) p_A)
    (PLetBox 2 (PVar 1) PUnit).

Theorem poly_discard_verified :
  (match poly_infer grade_eqb [] poly_discard_term with
   | Some res => presult_type res = PArr (GLit 1) (PBox (GLit 0) p_A) PUnitTy
   | None => False
   end) /\
  (forall rho,
    match poly_infer grade_eqb [] poly_discard_term with
    | Some res => ConcretePolyOk [] rho poly_discard_term res
    | None => False
    end).
Proof.
  split; [reflexivity |].
  intro rho.
  destruct (poly_infer grade_eqb [] poly_discard_term) eqn:Hchk; [| vm_compute in Hchk; discriminate].
  eapply poly_exact_infer_all_valuations; exact Hchk.
Qed.

(* Negative controls *)
(* 1. Reject Box (q + r) A -> Box (q * r) A *)
Definition poly_bad_add_to_mul : pterm :=
  PLam 1 (GLit 1) (PBox (GAdd g_q g_r) p_A)
    (PLetBox 2 (PVar 1)
      (PPromote g_q (PPromote g_r (PVar 2)))).

(* 2. Reject Box q A -> Box (q + 1) A *)
Definition poly_bad_inc : pterm :=
  PLam 1 (GLit 1) (PBox g_q p_A)
    (PLetBox 2 (PVar 1)
      (PPromote (GAdd g_q (GLit 1)) (PVar 2))).

Example poly_negative_controls :
  poly_infer grade_eqb [] poly_bad_add_to_mul = None /\
  poly_infer grade_leb [] poly_bad_add_to_mul = None /\
  poly_infer grade_eqb [] poly_bad_inc = None /\
  poly_infer grade_leb [] poly_bad_inc = None.
Proof.
  repeat split; reflexivity.
Qed.

End GradedSemiring.

(* ================================================================= *)
(* Part 3: Combinator and Synthesis Modal Kernel                     *)
(* ================================================================= *)

Module CombinatorKernel.
Import GradedDomains GradedSemiring.

Inductive cty : Type :=
| CUnitTy
| CBase (id : nat)
| CBox (q : grade_expr) (payload : cty)
| CArr (q : grade_expr) (domain codomain : cty)
| CProd (left right : cty)
| CSum (left right : cty).

Fixpoint cty_eqb (A B : cty) : bool :=
  match A, B with
  | CUnitTy, CUnitTy => true
  | CBase a, CBase b => Nat.eqb a b
  | CBox q1 A1, CBox q2 A2 => grade_eqb q1 q2 && cty_eqb A1 A2
  | CArr q1 A1 B1, CArr q2 A2 B2 => grade_eqb q1 q2 && cty_eqb A1 A2 && cty_eqb B1 B2
  | CProd A1 B1, CProd A2 B2 => cty_eqb A1 A2 && cty_eqb B1 B2
  | CSum A1 B1, CSum A2 B2 => cty_eqb A1 A2 && cty_eqb B1 B2
  | _, _ => false
  end.

Fixpoint eval_cty (rho : nat -> nat) (t : cty) : cty :=
  match t with
  | CUnitTy => CUnitTy
  | CBase n => CBase n
  | CBox q X => CBox (GLit (eval_grade rho q)) (eval_cty rho X)
  | CArr q X Y => CArr (GLit (eval_grade rho q)) (eval_cty rho X) (eval_cty rho Y)
  | CProd X Y => CProd (eval_cty rho X) (eval_cty rho Y)
  | CSum X Y => CSum (eval_cty rho X) (eval_cty rho Y)
  end.

Definition cty_eq (A B : cty) : Prop :=
  forall rho, eval_cty rho A = eval_cty rho B.

Lemma cty_eqb_sound : forall A B, cty_eqb A B = true -> cty_eq A B.
Proof.
  induction A; destruct B; cbn; intro H; try discriminate.
  - intro rho; reflexivity.
  - apply Nat.eqb_eq in H. subst. intro rho; reflexivity.
  - apply andb_true_iff in H as [Hq HA].
    pose proof (grade_eqb_sound _ _ Hq) as Hq'. apply IHA in HA.
    intro rho. cbn. rewrite (Hq' rho), (HA rho). reflexivity.
  - apply andb_true_iff in H as [H1 HB].
    apply andb_true_iff in H1 as [Hq HA].
    pose proof (grade_eqb_sound _ _ Hq) as Hq'. apply IHA1 in HA. apply IHA2 in HB.
    intro rho. cbn. rewrite (Hq' rho), (HA rho), (HB rho). reflexivity.
  - apply andb_true_iff in H as [HA HB].
    apply IHA1 in HA. apply IHA2 in HB.
    intro rho. cbn. rewrite (HA rho), (HB rho). reflexivity.
  - apply andb_true_iff in H as [HA HB].
    apply IHA1 in HA. apply IHA2 in HB.
    intro rho. cbn. rewrite (HA rho), (HB rho). reflexivity.
Qed.

Inductive cterm : Type :=
| CVar (x : nat)
| CUnit
| CLam (x : nat) (q : grade_expr) (domain : cty) (body : cterm)
| CApp (callee arg : cterm)
| CPair (lhs rhs : cterm)
| CLetPair (x y : nat) (s : grade_expr) (pr body : cterm)
| CPromote (q : grade_expr) (body : cterm)
| CLetBox (x : nat) (scale_q : grade_expr) (box_term body : cterm)
| CInl (right_ty : cty) (body : cterm)
| CInr (left_ty : cty) (body : cterm)
| CMatchSum (lx rx : nat) (s : grade_expr) (scrut lbody rbody : cterm).

Record cbinding := {
  cbinder : nat;
  cannotation : cty;
}.

Definition ccontext := list cbinding.

Definition clookup (env : ccontext) (x : nat) : option cty :=
  match find (fun entry => Nat.eqb x (cbinder entry)) env with
  | Some entry => Some (cannotation entry)
  | None => None
  end.

Definition cfresh (env : ccontext) (x : nat) : bool :=
  match clookup env x with None => true | Some _ => false end.

Record cjudgment := {
  cresult_type : cty;
  cdemand_row : pdemand;
}.

Definition cbranch_ok (allows : grade_expr -> grade_expr -> Prop)
    (d1 d2 d : pdemand) : Prop :=
  forall x, allows (puses d1 x) (puses d x) /\ allows (puses d2 x) (puses d x).

Definition cbranch_join (allowsb : grade_expr -> grade_expr -> bool)
    (d1 d2 : pdemand) : option pdemand :=
  let keys := map fst (d1 ++ d2) in
  if forallb (fun x => allowsb (puses d1 x) (puses d2 x) && allowsb (puses d2 x) (puses d2 x)) keys
  then Some d2
  else if forallb (fun x => allowsb (puses d1 x) (puses d1 x) && allowsb (puses d2 x) (puses d1 x)) keys
  then Some d1
  else None.

Lemma cbranch_join_sound : forall (allows : grade_expr -> grade_expr -> Prop) allowsb,
  (forall a b, allowsb a b = true -> allows a b) ->
  allows (GLit 0) (GLit 0) ->
  forall d1 d2 d, cbranch_join allowsb d1 d2 = Some d -> cbranch_ok allows d1 d2 d.
Proof.
  intros allows allowsb Hsound Hzero d1 d2 d Hj. unfold cbranch_join in Hj.
  destruct (forallb (fun x => allowsb (puses d1 x) (puses d2 x) && allowsb (puses d2 x) (puses d2 x))
              (map fst (d1 ++ d2))) eqn:H2.
  - inversion Hj as [Heq]; subst d. intro x.
    destruct (in_dec Nat.eq_dec x (map fst (d1 ++ d2))) as [Hin | Hout].
    + rewrite forallb_forall in H2. specialize (H2 x Hin).
      apply andb_true_iff in H2 as [H12 H22]. split; auto.
    + assert (Habs : forall row, ~ In x (map fst row) -> puses row x = GLit 0).
      { induction row as [| [y g] rest IH]; intro Hnot; [reflexivity |].
        cbn in *. destruct (Nat.eqb x y) eqn:Exy.
        - apply Nat.eqb_eq in Exy. subst y. exfalso. apply Hnot. now left.
        - apply IH. intro Hp. apply Hnot. now right. }
      rewrite !Habs; [split; exact Hzero | |];
        intro Hp; apply Hout; rewrite map_app; apply in_or_app; [right | left]; exact Hp.
  - destruct (forallb (fun x => allowsb (puses d1 x) (puses d1 x) && allowsb (puses d2 x) (puses d1 x))
              (map fst (d1 ++ d2))) eqn:H1; [| discriminate].
    inversion Hj as [Heq]; subst d.
    intro x. destruct (in_dec Nat.eq_dec x (map fst (d1 ++ d2))) as [Hin | Hout].
    + rewrite forallb_forall in H1. specialize (H1 x Hin).
      apply andb_true_iff in H1 as [H11 H21]. split; auto.
    + assert (Habs : forall row, ~ In x (map fst row) -> puses row x = GLit 0).
      { induction row as [| [y g] rest IH]; intro Hnot; [reflexivity |].
        cbn in *. destruct (Nat.eqb x y) eqn:Exy.
        - apply Nat.eqb_eq in Exy. subst y. exfalso. apply Hnot. now left.
        - apply IH. intro Hp. apply Hnot. now right. }
      rewrite !Habs; [split; exact Hzero | |];
        intro Hp; apply Hout; rewrite map_app; apply in_or_app; [right | left]; exact Hp.
Qed.

Inductive CDerives (allows : grade_expr -> grade_expr -> Prop) (env : ccontext)
  : cterm -> cjudgment -> Prop :=
| CGradeVar : forall x A,
    clookup env x = Some A ->
    CDerives allows env (CVar x) {| cresult_type := A; cdemand_row := [(x, GLit 1)] |}
| CGradeUnit :
    CDerives allows env CUnit {| cresult_type := CUnitTy; cdemand_row := [] |}
| CGradeLam : forall x q dom body cod u,
    cfresh env x = true ->
    CDerives allows ({| cbinder := x; cannotation := dom |} :: env) body
      {| cresult_type := cod; cdemand_row := u |} ->
    allows (puses u x) q ->
    CDerives allows env (CLam x q dom body)
      {| cresult_type := CArr q dom cod; cdemand_row := pwithout x u |}
| CGradeApp : forall callee arg q dom cod kind w z,
    CDerives allows env callee {| cresult_type := CArr q dom cod; cdemand_row := w |} ->
    CDerives allows env arg {| cresult_type := kind; cdemand_row := z |} ->
    cty_eq kind dom ->
    CDerives allows env (CApp callee arg)
      {| cresult_type := cod; cdemand_row := w ++ pscale q z |}
| CGradePair : forall lhs rhs A B ul ur,
    CDerives allows env lhs {| cresult_type := A; cdemand_row := ul |} ->
    CDerives allows env rhs {| cresult_type := B; cdemand_row := ur |} ->
    CDerives allows env (CPair lhs rhs)
      {| cresult_type := CProd A B; cdemand_row := ul ++ ur |}
| CGradeLetPair : forall x y s pr body A B mot w u,
    cfresh env x = true ->
    cfresh ({| cbinder := x; cannotation := A |} :: env) y = true ->
    CDerives allows env pr {| cresult_type := CProd A B; cdemand_row := w |} ->
    CDerives allows ({| cbinder := y; cannotation := B |} :: {| cbinder := x; cannotation := A |} :: env)
      body {| cresult_type := mot; cdemand_row := u |} ->
    allows (puses u x) s ->
    allows (puses u y) s ->
    CDerives allows env (CLetPair x y s pr body)
      {| cresult_type := mot; cdemand_row := pwithout x (pwithout y u) ++ pscale s w |}
| CGradePromote : forall q body A u,
    CDerives allows env body {| cresult_type := A; cdemand_row := u |} ->
    CDerives allows env (CPromote q body)
      {| cresult_type := CBox q A; cdemand_row := pscale q u |}
| CGradeLetBox : forall x s box_term body q A mot z w,
    cfresh env x = true ->
    CDerives allows env box_term {| cresult_type := CBox q A; cdemand_row := z |} ->
    CDerives allows ({| cbinder := x; cannotation := A |} :: env)
      body {| cresult_type := mot; cdemand_row := w |} ->
    allows (puses w x) (GMul s q) ->
    CDerives allows env (CLetBox x s box_term body)
      {| cresult_type := mot; cdemand_row := pwithout x w ++ pscale s z |}
| CGradeInl : forall right_ty body left_ty u,
    CDerives allows env body {| cresult_type := left_ty; cdemand_row := u |} ->
    CDerives allows env (CInl right_ty body)
      {| cresult_type := CSum left_ty right_ty; cdemand_row := u |}
| CGradeInr : forall left_ty body right_ty u,
    CDerives allows env body {| cresult_type := right_ty; cdemand_row := u |} ->
    CDerives allows env (CInr left_ty body)
      {| cresult_type := CSum left_ty right_ty; cdemand_row := u |}
| CGradeMatchSum : forall lx rx s scrut lbody rbody left_ty right_ty mot1 mot2 z u1 u2 ub,
    cfresh env lx = true ->
    cfresh env rx = true ->
    CDerives allows env scrut {| cresult_type := CSum left_ty right_ty; cdemand_row := z |} ->
    CDerives allows ({| cbinder := lx; cannotation := left_ty |} :: env)
      lbody {| cresult_type := mot1; cdemand_row := u1 |} ->
    CDerives allows ({| cbinder := rx; cannotation := right_ty |} :: env)
      rbody {| cresult_type := mot2; cdemand_row := u2 |} ->
    cty_eq mot1 mot2 ->
    grade_le (GLit 1) s ->
    allows (puses u1 lx) s ->
    allows (puses u2 rx) s ->
    cbranch_ok allows (pwithout lx u1) (pwithout rx u2) ub ->
    CDerives allows env (CMatchSum lx rx s scrut lbody rbody)
      {| cresult_type := mot1; cdemand_row := pscale s z ++ ub |}.

Fixpoint cinfer (allowsb : grade_expr -> grade_expr -> bool) (env : ccontext) (t : cterm)
  : option cjudgment :=
  match t with
  | CVar x =>
      match clookup env x with
      | Some A => Some {| cresult_type := A; cdemand_row := [(x, GLit 1)] |}
      | None => None
      end
  | CUnit => Some {| cresult_type := CUnitTy; cdemand_row := [] |}
  | CLam x q dom body =>
      if cfresh env x then
        match cinfer allowsb ({| cbinder := x; cannotation := dom |} :: env) body with
        | Some {| cresult_type := cod; cdemand_row := u |} =>
            if allowsb (puses u x) q then
              Some {| cresult_type := CArr q dom cod; cdemand_row := pwithout x u |}
            else None
        | None => None
        end
      else None
  | CApp callee arg =>
      match cinfer allowsb env callee, cinfer allowsb env arg with
      | Some {| cresult_type := CArr q dom cod; cdemand_row := w |},
        Some {| cresult_type := kind; cdemand_row := z |} =>
          if cty_eqb kind dom then
            Some {| cresult_type := cod; cdemand_row := w ++ pscale q z |}
          else None
      | _, _ => None
      end
  | CPair lhs rhs =>
      match cinfer allowsb env lhs, cinfer allowsb env rhs with
      | Some {| cresult_type := A; cdemand_row := ul |},
        Some {| cresult_type := B; cdemand_row := ur |} =>
          Some {| cresult_type := CProd A B; cdemand_row := ul ++ ur |}
      | _, _ => None
      end
  | CLetPair x y s pr body =>
      if cfresh env x then
        match cinfer allowsb env pr with
        | Some {| cresult_type := CProd A B; cdemand_row := w |} =>
            let env1 := {| cbinder := x; cannotation := A |} :: env in
            if cfresh env1 y then
              match cinfer allowsb ({| cbinder := y; cannotation := B |} :: env1) body with
              | Some {| cresult_type := mot; cdemand_row := u |} =>
                  if allowsb (puses u x) s && allowsb (puses u y) s then
                    Some {| cresult_type := mot; cdemand_row := pwithout x (pwithout y u) ++ pscale s w |}
                  else None
              | None => None
              end
            else None
        | _ => None
        end
      else None
  | CPromote q body =>
      match cinfer allowsb env body with
      | Some {| cresult_type := A; cdemand_row := u |} =>
          Some {| cresult_type := CBox q A; cdemand_row := pscale q u |}
      | None => None
      end
  | CLetBox x s box_term body =>
      if cfresh env x then
        match cinfer allowsb env box_term with
        | Some {| cresult_type := CBox q A; cdemand_row := z |} =>
            match cinfer allowsb ({| cbinder := x; cannotation := A |} :: env) body with
            | Some {| cresult_type := mot; cdemand_row := w |} =>
                if allowsb (puses w x) (GMul s q) then
                  Some {| cresult_type := mot; cdemand_row := pwithout x w ++ pscale s z |}
                else None
            | None => None
            end
        | _ => None
        end
      else None
  | CInl right_ty body =>
      match cinfer allowsb env body with
      | Some {| cresult_type := left_ty; cdemand_row := u |} =>
          Some {| cresult_type := CSum left_ty right_ty; cdemand_row := u |}
      | None => None
      end
  | CInr left_ty body =>
      match cinfer allowsb env body with
      | Some {| cresult_type := right_ty; cdemand_row := u |} =>
          Some {| cresult_type := CSum left_ty right_ty; cdemand_row := u |}
      | None => None
      end
  | CMatchSum lx rx s scrut lbody rbody =>
      if cfresh env lx && cfresh env rx then
        match cinfer allowsb env scrut with
        | Some {| cresult_type := CSum left_ty right_ty; cdemand_row := z |} =>
            match cinfer allowsb ({| cbinder := lx; cannotation := left_ty |} :: env) lbody,
                  cinfer allowsb ({| cbinder := rx; cannotation := right_ty |} :: env) rbody with
            | Some {| cresult_type := mot1; cdemand_row := u1 |},
              Some {| cresult_type := mot2; cdemand_row := u2 |} =>
                if cty_eqb mot1 mot2 && grade_leb (GLit 1) s
                   && allowsb (puses u1 lx) s && allowsb (puses u2 rx) s then
                  match cbranch_join allowsb (pwithout lx u1) (pwithout rx u2) with
                  | Some ub => Some {| cresult_type := mot1; cdemand_row := pscale s z ++ ub |}
                  | None => None
                  end
                else None
            | _, _ => None
            end
        | _ => None
        end
      else None
  end.

Theorem cinfer_sound : forall allows allowsb,
  (forall a b, allowsb a b = true -> allows a b) ->
  allows (GLit 0) (GLit 0) ->
  forall t env res,
    cinfer allowsb env t = Some res ->
    CDerives allows env t res.
Proof.
  intros allows allowsb Hsound Hzero t.
  induction t; intros env res Hchk; cbn in Hchk.
  - destruct (clookup env x) as [A |] eqn:Hlkp; inversion Hchk; subst.
    constructor; exact Hlkp.
  - inversion Hchk; subst; constructor.
  - destruct (cfresh env x) eqn:Hfr; try discriminate.
    destruct (cinfer allowsb ({| cbinder := x; cannotation := domain |} :: env) t)
      as [[cod u] |] eqn:Hb; try discriminate.
    destruct (allowsb (puses u x) q) eqn:Hq; inversion Hchk; subst.
    eapply CGradeLam; eauto.
  - destruct (cinfer allowsb env t1) as [[rt1 w] |] eqn:Hc; try discriminate.
    destruct rt1 as [| | | q dom cod | |]; try discriminate.
    destruct (cinfer allowsb env t2) as [[kind z] |] eqn:Ha; try discriminate.
    destruct (cty_eqb kind dom) eqn:Heq; inversion Hchk; subst.
    eapply CGradeApp; eauto using cty_eqb_sound.
  - destruct (cinfer allowsb env t1) as [[A ul] |] eqn:Hl; try discriminate.
    destruct (cinfer allowsb env t2) as [[B ur] |] eqn:Hr; inversion Hchk; subst.
    constructor; auto.
  - destruct (cfresh env x) eqn:Hfrx; try discriminate.
    destruct (cinfer allowsb env t1) as [[prt w] |] eqn:Hp; try discriminate.
    destruct prt as [| | | | A B |]; try discriminate.
    destruct (cfresh ({| cbinder := x; cannotation := A |} :: env) y) eqn:Hfry; try discriminate.
    destruct (cinfer allowsb
                ({| cbinder := y; cannotation := B |} :: {| cbinder := x; cannotation := A |} :: env) t2)
      as [[mot u] |] eqn:Hb; try discriminate.
    destruct (allowsb (puses u x) s && allowsb (puses u y) s) eqn:Hs; inversion Hchk; subst.
    apply andb_true_iff in Hs as [Hsx Hsy].
    eapply CGradeLetPair; eauto.
  - destruct (cinfer allowsb env t) as [[A u] |] eqn:Hb; inversion Hchk; subst.
    constructor; auto.
  - destruct (cfresh env x) eqn:Hfr; try discriminate.
    destruct (cinfer allowsb env t1) as [[brt z] |] eqn:Hbx; try discriminate.
    destruct brt as [| | q A | | |]; try discriminate.
    destruct (cinfer allowsb ({| cbinder := x; cannotation := A |} :: env) t2)
      as [[mot w] |] eqn:Hb; try discriminate.
    destruct (allowsb (puses w x) (GMul scale_q q)) eqn:Hq; inversion Hchk; subst.
    eapply CGradeLetBox; eauto.
  - destruct (cinfer allowsb env t) as [[lt u] |] eqn:Hb; inversion Hchk; subst.
    constructor; auto.
  - destruct (cinfer allowsb env t) as [[rt u] |] eqn:Hb; inversion Hchk; subst.
    constructor; auto.
  - destruct (cfresh env lx && cfresh env rx) eqn:Hfr; try discriminate.
    apply andb_true_iff in Hfr as [Hfl Hfr].
    destruct (cinfer allowsb env t1) as [[srt z] |] eqn:Hs; try discriminate.
    destruct srt as [| | | | | lt rt]; try discriminate.
    destruct (cinfer allowsb ({| cbinder := lx; cannotation := lt |} :: env) t2)
      as [[m1 u1] |] eqn:Hl; try discriminate.
    destruct (cinfer allowsb ({| cbinder := rx; cannotation := rt |} :: env) t3)
      as [[m2 u2] |] eqn:Hr; try discriminate.
    destruct (cty_eqb m1 m2 && grade_leb (GLit 1) s && allowsb (puses u1 lx) s && allowsb (puses u2 rx) s)
      eqn:Hcond; try discriminate.
    destruct (cbranch_join allowsb (pwithout lx u1) (pwithout rx u2)) as [ub |] eqn:Hjb;
      inversion Hchk; subst.
    apply andb_true_iff in Hcond as [Hcond Hur].
    apply andb_true_iff in Hcond as [Hcond Hul].
    apply andb_true_iff in Hcond as [Hm H1s].
    eapply CGradeMatchSum; eauto using cty_eqb_sound, cbranch_join_sound.
    exact (grade_leb_sound _ _ H1s).
Qed.

Definition affine_le (a b : grade_expr) : Prop :=
  forall rho, eval_grade rho a <= eval_grade rho b /\ eval_grade rho b <= 1.

Definition affine_leb (a b : grade_expr) : bool :=
  grade_leb a b && grade_leb b (GLit 1).

Lemma affine_leb_sound : forall a b, affine_leb a b = true -> affine_le a b.
Proof.
  intros a b H rho. unfold affine_leb in H.
  apply andb_true_iff in H as [Hab Hb1].
  split; [apply grade_leb_sound; exact Hab | apply (grade_leb_sound _ _ Hb1 rho)].
Qed.

Lemma affine_zero : affine_le (GLit 0) (GLit 0).
Proof. intro rho. cbn. lia. Qed.

Definition presence_grade_le (a b : grade_expr) : Prop :=
  forall rho, eval_grade rho a > 0 -> eval_grade rho b > 0.

Definition poly_support_leb (p1 p2 : poly) : bool :=
  forallb (fun '(c1, vs1) =>
    Nat.eqb c1 0 ||
    existsb (fun '(c2, vs2) => negb (Nat.eqb c2 0) && vars_eqb vs1 vs2) p2)
    p1.

Lemma eval_poly_pos_exists : forall rho p,
  eval_poly rho p > 0 ->
  exists c vs, In (c, vs) p /\ c <> 0 /\ eval_vars rho vs > 0.
Proof.
  intros rho p. induction p as [| [c vs] rest IH]; cbn; intro H; [lia |].
  destruct (Nat.eqb c 0) eqn:Hc0.
  - apply Nat.eqb_eq in Hc0. subst c. cbn in H.
    destruct (IH H) as [c' [vs' [Hin Hpos]]]. exists c', vs'. split; [right; exact Hin | exact Hpos].
  - destruct (Nat.eqb (eval_vars rho vs) 0) eqn:Hv0.
    + apply Nat.eqb_eq in Hv0. rewrite Hv0, Nat.mul_0_r in H. cbn in H.
      destruct (IH H) as [c' [vs' [Hin Hpos]]]. exists c', vs'. split; [right; exact Hin | exact Hpos].
    + exists c, vs. split; [left; reflexivity | split].
      * intro Hc. apply Nat.eqb_neq in Hc0. congruence.
      * apply Nat.eqb_neq in Hv0. lia.
Qed.

Lemma eval_poly_in_pos : forall rho c vs p,
  In (c, vs) p -> c <> 0 -> eval_vars rho vs > 0 -> eval_poly rho p > 0.
Proof.
  intros rho c vs p. induction p as [| [c' vs'] rest IH]; cbn; [contradiction |].
  intros [Heq | Hin] Hc Hv.
  - inversion Heq; subst. nia.
  - specialize (IH Hin Hc Hv). lia.
Qed.

Lemma poly_support_leb_pos : forall p1 p2 rho,
  poly_support_leb p1 p2 = true ->
  eval_poly rho p1 > 0 -> eval_poly rho p2 > 0.
Proof.
  intros p1 p2 rho Hsup Hpos.
  destruct (eval_poly_pos_exists rho p1 Hpos) as [c1 [vs1 [Hin [Hc1 Hv1]]]].
  unfold poly_support_leb in Hsup.
  rewrite forallb_forall in Hsup. specialize (Hsup (c1, vs1) Hin). cbn in Hsup.
  apply orb_true_iff in Hsup as [Hz | Hex].
  - apply Nat.eqb_eq in Hz. congruence.
  - rewrite existsb_exists in Hex. destruct Hex as [[c2 vs2] [Hin2 Hcond]].
    apply andb_true_iff in Hcond as [Hc2 Hvs].
    apply negb_true_iff in Hc2. apply Nat.eqb_neq in Hc2.
    apply vars_eqb_sound in Hvs. subst vs2.
    eapply eval_poly_in_pos; eauto.
Qed.

Definition presence_grade_leb (a b : grade_expr) : bool :=
  grade_leb a b || poly_support_leb (normalize_grade a) (normalize_grade b).

Lemma presence_grade_leb_sound : forall a b,
  presence_grade_leb a b = true -> presence_grade_le a b.
Proof.
  intros a b H rho Hpos. unfold presence_grade_leb in H.
  apply orb_true_iff in H as [Hle | Hsup].
  - pose proof (grade_leb_sound a b Hle rho) as Hle'. lia.
  - rewrite <- !normalize_grade_sound in *. eapply poly_support_leb_pos; eauto.
Qed.

Example presence_contraction_sound :
  presence_grade_leb (GLit 2) (GLit 1) = true /\
  presence_grade_leb (GAdd (GVar 0) (GVar 0)) (GVar 0) = true.
Proof.
  split; reflexivity.
Qed.

Lemma presence_zero : presence_grade_le (GLit 0) (GLit 0).
Proof. intros rho H. cbn in H. lia. Qed.

Lemma exact_zero : grade_eq (GLit 0) (GLit 0).
Proof. intro rho. reflexivity. Qed.

Lemma bound_zero : grade_le (GLit 0) (GLit 0).
Proof. intro rho. cbn. lia. Qed.

(* ================================================================= *)
(* Mode Crossing for Deeply Immutable, Authority-Free Types          *)
(* ================================================================= *)

Fixpoint mode_crosses (pure_base : nat -> bool) (t : cty) : bool :=
  match t with
  | CUnitTy => true
  | CBase id => pure_base id
  | CProd A B => mode_crosses pure_base A && mode_crosses pure_base B
  | CSum A B => mode_crosses pure_base A && mode_crosses pure_base B
  | CBox _ A => mode_crosses pure_base A
  | CArr _ _ _ => false
  end.

Lemma mode_crosses_eval_cty : forall pure_base rho t,
  mode_crosses pure_base (eval_cty rho t) = mode_crosses pure_base t.
Proof.
  intros pure_base rho t.
  induction t; cbn; try reflexivity; rewrite ?IHt, ?IHt1, ?IHt2; reflexivity.
Qed.

Lemma mode_crosses_cty_eq : forall pure_base A B,
  cty_eq A B -> mode_crosses pure_base A = mode_crosses pure_base B.
Proof.
  intros pure_base A B Heq.
  rewrite <- (mode_crosses_eval_cty pure_base (fun _ => 0) A).
  rewrite <- (mode_crosses_eval_cty pure_base (fun _ => 0) B).
  rewrite (Heq (fun _ => 0)). reflexivity.
Qed.

Inductive ModeCrossAdmits (pure_base : nat -> bool) (t : cty) : grade_expr -> Prop :=
| ModeCrossPure :
    mode_crosses pure_base t = true ->
    forall q, ModeCrossAdmits pure_base t q.

Definition mode_cross_check (pure_base : nat -> bool) (t : cty) (_q : grade_expr) : bool :=
  mode_crosses pure_base t.

Lemma mode_cross_check_sound : forall pure_base t q,
  mode_cross_check pure_base t q = true -> ModeCrossAdmits pure_base t q.
Proof.
  intros pure_base t q H. constructor. exact H.
Qed.

Lemma mode_cross_prod_elim : forall pure_base A B,
  mode_crosses pure_base (CProd A B) = true ->
  mode_crosses pure_base A = true /\ mode_crosses pure_base B = true.
Proof.
  intros pure_base A B H. cbn in H. apply andb_true_iff in H. exact H.
Qed.

Lemma mode_cross_sum_elim : forall pure_base A B,
  mode_crosses pure_base (CSum A B) = true ->
  mode_crosses pure_base A = true /\ mode_crosses pure_base B = true.
Proof.
  intros pure_base A B H. cbn in H. apply andb_true_iff in H. exact H.
Qed.

Lemma mode_cross_arr_false : forall pure_base q A B,
  mode_crosses pure_base (CArr q A B) = false.
Proof.
  intros; reflexivity.
Qed.

Example mode_cross_authority_refused :
  let pure_base := fun id => Nat.eqb id 0 in
  mode_crosses pure_base (CProd (CBase 0) (CBase 1)) = false /\
  mode_crosses pure_base (CProd (CBase 0) CUnitTy) = true.
Proof.
  split; reflexivity.
Qed.

End CombinatorKernel.
