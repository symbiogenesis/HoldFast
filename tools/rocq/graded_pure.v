(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool.
Import ListNotations.

Module GradedPure.

(* Each pair records a binder identifier and a contribution to its demand.
   Multiple entries for the same binder are summed by uses. *)
Definition demand := list (nat * nat).

Fixpoint uses (d : demand) (x : nat) : nat :=
  match d with
  | [] => 0
  | (y, n) :: rest => (if Nat.eqb x y then n else 0) + uses rest x
  end.

Definition without (x : nat) (d : demand) : demand :=
  filter (fun entry => negb (Nat.eqb x (fst entry))) d.

Definition scale (n : nat) (d : demand) : demand :=
  map (fun '(x, m) => (x, n * m)) d.

Definition substitute_demand (x : nat) (argument d : demand) : demand :=
  without x d ++ scale (uses d x) argument.

Definition same_demand (left right : demand) : Prop :=
  forall x, uses left x = uses right x.

Definition demand_eqb (left right : demand) : bool :=
  forallb (fun entry => Nat.eqb (uses left (fst entry)) (uses right (fst entry)))
    (left ++ right).

Lemma uses_append : forall left right x,
  uses (left ++ right) x = uses left x + uses right x.
Proof.
  induction left as [| [key n] rest IH]; intros right x; cbn.
  - reflexivity.
  - now rewrite IH, Nat.add_assoc.
Qed.

Lemma uses_without : forall d x y,
  uses (without x d) y = if Nat.eqb y x then 0 else uses d y.
Proof.
  induction d as [| [key n] rest IH]; intros x y.
  - cbn. now destruct (Nat.eqb y x).
  - unfold without in *. cbn.
    destruct (Nat.eqb x key) eqn:removed; cbn.
    + apply Nat.eqb_eq in removed. subst key.
      rewrite IH. now destruct (Nat.eqb y x).
    + rewrite IH. destruct (Nat.eqb y x) eqn:equal; try reflexivity.
      apply Nat.eqb_eq in equal. subst y. now rewrite removed.
Qed.

Lemma absent_use : forall d x, ~ In x (map fst d) -> uses d x = 0.
Proof.
  induction d as [| [y n] rest IH]; intros x absent; cbn in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:equal.
    + apply Nat.eqb_eq in equal. subst. exfalso. apply absent. now left.
    + apply IH. intro present. apply absent. now right.
Qed.

Lemma demand_eqb_sound : forall left right,
  demand_eqb left right = true -> same_demand left right.
Proof.
  intros left right equal x.
  destruct (in_dec Nat.eq_dec x (map fst (left ++ right))) as [present | absent].
  - apply in_map_iff in present as [entry [<- present]].
    unfold demand_eqb in equal. rewrite forallb_forall in equal.
    apply Nat.eqb_eq. now apply equal.
  - rewrite map_app in absent. rewrite !absent_use; auto using in_or_app.
Qed.

Inductive index : Type :=
| IndexVar (x : nat)
| IndexLit (n : nat)
| IndexAdd (left right : index).

Inductive ty : Type :=
| Natural
| Vector (length : index)
| Pi (x allowance : nat) (domain codomain : ty).

Definition canonical_index (names : list (nat * nat)) (x : nat) : nat :=
  match find (fun binding => Nat.eqb x (fst binding)) names with
  | Some binding => 2 * snd binding
  | None => 2 * x + 1
  end.

Fixpoint canonical_value (names : list (nat * nat)) (value : index) : index :=
  match value with
  | IndexVar x => IndexVar (canonical_index names x)
  | IndexLit _ => value
  | IndexAdd lhs rhs => IndexAdd (canonical_value names lhs) (canonical_value names rhs)
  end.

Fixpoint canonical_type (names : list (nat * nat)) (kind : ty) : ty :=
  match kind with
  | Natural => Natural
  | Vector size => Vector (canonical_value names size)
  | Pi x allowance domain codomain =>
      let depth := length names in
      Pi (2 * depth) allowance (canonical_type names domain)
        (canonical_type ((x, depth) :: names) codomain)
  end.

Scheme Equality for index.
Scheme Equality for ty.

Record binding := {
  binder : nat;
  annotation : ty;
  type_uses : demand;
}.

Definition context := list binding.

Definition lookup (env : context) (x : nat) : option binding :=
  find (fun entry => Nat.eqb x (binder entry)) env.

Definition fresh (env : context) (x : nat) : bool :=
  match lookup env x with None => true | Some _ => false end.

Fixpoint substitute_index (x : nat) (value i : index) : index :=
  match i with
  | IndexVar y => if Nat.eqb x y then value else i
  | IndexLit _ => i
  | IndexAdd lhs rhs =>
      IndexAdd (substitute_index x value lhs) (substitute_index x value rhs)
  end.

Fixpoint substitute_type (x : nat) (value : index) (kind : ty) : ty :=
  match kind with
  | Natural => Natural
  | Vector length => Vector (substitute_index x value length)
  | Pi y allowance domain codomain =>
      Pi y allowance (substitute_type x value domain)
        (if Nat.eqb x y then codomain else substitute_type x value codomain)
  end.

Inductive IndexDemand (env : context) : index -> demand -> Prop :=
| NaturalVariable : forall x entry,
    lookup env x = Some entry -> annotation entry = Natural ->
    IndexDemand env (IndexVar x) [(x, 1)]
| NaturalLiteral : forall n, IndexDemand env (IndexLit n) []
| NaturalAddition : forall left right p q,
    IndexDemand env left p -> IndexDemand env right q ->
    IndexDemand env (IndexAdd left right) (p ++ q).

Fixpoint index_demand (env : context) (i : index) : option demand :=
  match i with
  | IndexVar x =>
      match lookup env x with
      | Some {| annotation := Natural |} => Some [(x, 1)]
      | _ => None
      end
  | IndexLit _ => Some []
  | IndexAdd lhs rhs =>
      match index_demand env lhs, index_demand env rhs with
      | Some p, Some q => Some (p ++ q)
      | _, _ => None
      end
  end.

Lemma index_demand_sound : forall env i d,
  index_demand env i = Some d -> IndexDemand env i d.
Proof.
  intros env i. induction i as [x | n | left IHleft right IHright]; intros d checked.
  - cbn in checked. destruct (lookup env x) as [[y kind row] |] eqn:found;
      try discriminate. destruct kind; inversion checked; subst.
    eapply NaturalVariable; [exact found | reflexivity].
  - inversion checked. constructor.
  - cbn in checked. destruct (index_demand env left), (index_demand env right);
      inversion checked; subst. constructor; auto.
Qed.

Inductive TypeDemand (env : context) : ty -> demand -> Prop :=
| TypeNatural : TypeDemand env Natural []
| TypeVector : forall length d,
    IndexDemand env length d -> TypeDemand env (Vector length) d
| TypePi : forall x allowance domain codomain a b,
    fresh env x = true -> TypeDemand env domain a ->
    TypeDemand ({| binder := x; annotation := domain; type_uses := a |} :: env)
      codomain b ->
    TypeDemand env (Pi x allowance domain codomain) (a ++ without x b).

Fixpoint type_demand (env : context) (kind : ty) : option demand :=
  match kind with
  | Natural => Some []
  | Vector length => index_demand env length
  | Pi x _ domain codomain =>
      if fresh env x then
        match type_demand env domain with
        | None => None
        | Some a =>
            option_map (fun b => a ++ without x b)
              (type_demand ({| binder := x; annotation := domain; type_uses := a |} :: env)
                codomain)
        end
      else None
  end.

Lemma type_demand_sound : forall kind env d,
  type_demand env kind = Some d -> TypeDemand env kind d.
Proof.
  induction kind as [| length | x allowance domain IHdomain codomain IHcodomain];
    intros env d checked.
  - inversion checked. constructor.
  - constructor. now apply index_demand_sound.
  - cbn in checked. destruct (fresh env x) eqn:new; try discriminate.
    destruct (type_demand env domain) as [a |] eqn:domain_checked; try discriminate.
    destruct (type_demand ({| binder := x; annotation := domain; type_uses := a |} :: env)
      codomain) as [b |] eqn:codomain_checked; inversion checked; subst.
    constructor; auto.
Qed.

Inductive Extends : context -> list binding -> context -> Prop :=
| TelescopeDone : forall env, Extends env [] env
| TelescopeStep : forall env entry rest result row,
    fresh env (binder entry) = true ->
    TypeDemand env (annotation entry) row -> same_demand (type_uses entry) row ->
    Extends ({| binder := binder entry; annotation := annotation entry; type_uses := row |} :: env)
      rest result -> Extends env (entry :: rest) result.

Fixpoint check_telescope (env : context) (entries : list binding) : option context :=
  match entries with
  | [] => Some env
  | entry :: rest =>
      if fresh env (binder entry) then
        match type_demand env (annotation entry) with
        | None => None
        | Some row =>
            if demand_eqb (type_uses entry) row then
              check_telescope
                ({| binder := binder entry; annotation := annotation entry; type_uses := row |} :: env)
                rest
            else None
        end
      else None
  end.

Lemma check_telescope_sound : forall entries env result,
  check_telescope env entries = Some result -> Extends env entries result.
Proof.
  induction entries as [| entry rest IH]; intros env result checked.
  - inversion checked. constructor.
  - cbn in checked. destruct (fresh env (binder entry)) eqn:new; try discriminate.
    destruct (type_demand env (annotation entry)) as [row |] eqn:typed; try discriminate.
    destruct (demand_eqb (type_uses entry) row) eqn:equal; try discriminate.
    eapply TelescopeStep; eauto using type_demand_sound, demand_eqb_sound.
Qed.

Inductive term : Type :=
| Var (x : nat)
| NatValue (i : index)
| Lambda (x allowance : nat) (domain : ty) (body : term)
| ApplyNat (callee : term) (argument : index)
| ApplyValue (callee argument : term)
| LetNat (x allowance : nat) (initializer : index) (body : term).

Record judgment := {
  result_type : ty;
  computation_demand : demand;
  type_demand_row : demand;
}.

Inductive DerivesWith (allows : nat -> nat -> Prop) (env : context) : term -> judgment -> Prop :=
| GradeVar : forall x entry row,
    lookup env x = Some entry -> TypeDemand env (annotation entry) row ->
    same_demand (type_uses entry) row ->
    DerivesWith allows env (Var x) {| result_type := annotation entry;
      computation_demand := [(x, 1)]; type_demand_row := type_uses entry |}
| GradeNat : forall i d, IndexDemand env i d ->
    DerivesWith allows env (NatValue i) {| result_type := Natural;
      computation_demand := d; type_demand_row := [] |}
| GradeLambda : forall x allowance domain body codomain a u v,
    fresh env x = true -> TypeDemand env domain a ->
    DerivesWith allows ({| binder := x; annotation := domain; type_uses := a |} :: env) body
      {| result_type := codomain; computation_demand := u; type_demand_row := v |} ->
    allows (uses u x) allowance ->
    DerivesWith allows env (Lambda x allowance domain body) {| result_type := Pi x allowance domain codomain;
      computation_demand := without x u; type_demand_row := a ++ without x v |}
| GradeApplyNat : forall callee argument x allowance codomain w v z b output,
    DerivesWith allows env callee {| result_type := Pi x allowance Natural codomain;
      computation_demand := w; type_demand_row := v |} ->
    fresh env x = true -> IndexDemand env argument z ->
    TypeDemand ({| binder := x; annotation := Natural; type_uses := [] |} :: env) codomain b ->
    TypeDemand env (substitute_type x argument codomain) output ->
    same_demand (substitute_demand x z b) output ->
    DerivesWith allows env (ApplyNat callee argument) {| result_type := substitute_type x argument codomain;
      computation_demand := w ++ scale allowance z; type_demand_row := substitute_demand x z b |}
| GradeApplyValue : forall callee argument x allowance domain codomain kind w v z a b,
    DerivesWith allows env callee {| result_type := Pi x allowance domain codomain;
      computation_demand := w; type_demand_row := v |} ->
    DerivesWith allows env argument {| result_type := kind;
      computation_demand := z; type_demand_row := a |} ->
    canonical_type [] kind = canonical_type [] domain ->
    fresh env x = true -> TypeDemand env codomain b ->
    DerivesWith allows env (ApplyValue callee argument) {| result_type := codomain;
      computation_demand := w ++ scale allowance z; type_demand_row := b |}
| GradeLetNat : forall x allowance initializer body kind z u v output,
    fresh env x = true -> IndexDemand env initializer z ->
    DerivesWith allows ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body
      {| result_type := kind; computation_demand := u; type_demand_row := v |} ->
    allows (uses u x) allowance ->
    TypeDemand env (substitute_type x initializer kind) output ->
    same_demand (substitute_demand x z v) output ->
    DerivesWith allows env (LetNat x allowance initializer body)
      {| result_type := substitute_type x initializer kind;
        computation_demand := z ++ without x u; type_demand_row := substitute_demand x z v |}.

Fixpoint infer_with (allowsb : nat -> nat -> bool) (env : context) (subject : term) : option judgment :=
  match subject with
  | Var x =>
      match lookup env x with
      | None => None
      | Some entry =>
          match type_demand env (annotation entry) with
          | Some row =>
              if demand_eqb (type_uses entry) row then
                Some {| result_type := annotation entry; computation_demand := [(x, 1)];
                  type_demand_row := type_uses entry |}
              else None
          | None => None
          end
      end
  | NatValue i => option_map (fun d => {| result_type := Natural;
      computation_demand := d; type_demand_row := [] |}) (index_demand env i)
  | Lambda x allowance domain body =>
      if fresh env x then
        match type_demand env domain with
        | None => None
        | Some a =>
            match infer_with allowsb ({| binder := x; annotation := domain; type_uses := a |} :: env) body with
            | Some result =>
                if allowsb (uses (computation_demand result) x) allowance then
                  Some {| result_type := Pi x allowance domain (result_type result);
                    computation_demand := without x (computation_demand result);
                    type_demand_row := a ++ without x (type_demand_row result) |}
                else None
            | None => None
            end
        end
      else None
  | ApplyNat callee argument =>
      match infer_with allowsb env callee with
      | Some {| result_type := Pi x allowance Natural codomain; computation_demand := w |} =>
          if fresh env x then
            let specialized := substitute_type x argument codomain in
            let extended := {| binder := x; annotation := Natural; type_uses := [] |} :: env in
            match index_demand env argument, type_demand extended codomain, type_demand env specialized with
            | Some z, Some b, Some output =>
                let v := substitute_demand x z b in
                if demand_eqb v output then
                  Some {| result_type := specialized;
                    computation_demand := w ++ scale allowance z; type_demand_row := v |}
                else None
            | _, _, _ => None
            end
          else None
      | _ => None
      end
  | ApplyValue callee argument =>
      match infer_with allowsb env callee, infer_with allowsb env argument with
      | Some {| result_type := Pi x allowance domain codomain; computation_demand := w |},
        Some {| result_type := kind; computation_demand := z |} =>
          if fresh env x then
            if ty_eq_dec (canonical_type [] kind) (canonical_type [] domain) then
              option_map (fun b => {| result_type := codomain;
                computation_demand := w ++ scale allowance z; type_demand_row := b |})
                (type_demand env codomain)
            else None
          else None
      | _, _ => None
      end
  | LetNat x allowance initializer body =>
      if fresh env x then
        let extended := {| binder := x; annotation := Natural; type_uses := [] |} :: env in
        match index_demand env initializer, infer_with allowsb extended body with
        | Some z, Some {| result_type := kind; computation_demand := u; type_demand_row := v |} =>
            let specialized := substitute_type x initializer kind in
            match type_demand env specialized with
            | Some output =>
                let substituted := substitute_demand x z v in
                if allowsb (uses u x) allowance && demand_eqb substituted output then
                  Some {| result_type := specialized; computation_demand := z ++ without x u;
                    type_demand_row := substituted |}
                else None
            | None => None
            end
        | _, _ => None
        end
      else None
  end.

Lemma infer_with_sound : forall (allows : nat -> nat -> Prop) allowsb,
  (forall demand allowance, allowsb demand allowance = true -> allows demand allowance) ->
  forall subject env result,
    infer_with allowsb env subject = Some result -> DerivesWith allows env subject result.
Proof.
  intros allows allowsb admission_sound.
  induction subject as [x | i | x allowance domain body IH | callee IH argument | callee IHc argument IHa
    | x allowance initializer body IH];
    intros env result checked; cbn in checked.
  - destruct (lookup env x) as [entry |] eqn:found; try discriminate.
    destruct (type_demand env (annotation entry)) as [row |] eqn:typed; try discriminate.
    destruct (demand_eqb (type_uses entry) row) eqn:equal; inversion checked; subst.
    eapply GradeVar; eauto using type_demand_sound, demand_eqb_sound.
  - destruct (index_demand env i) eqn:used; inversion checked; subst.
    constructor. now apply index_demand_sound.
  - destruct (fresh env x) eqn:new; try discriminate.
    destruct (type_demand env domain) as [a |] eqn:typed; try discriminate.
    destruct (infer_with allowsb ({| binder := x; annotation := domain; type_uses := a |} :: env)
      body) as [[codomain u v] |] eqn:body_checked; try discriminate.
    cbn in checked. destruct (allowsb (uses u x) allowance) eqn:admitted;
      inversion checked; subst.
    constructor; eauto using type_demand_sound.
  - destruct (infer_with allowsb env callee) as [[kind w v] |] eqn:callee_checked; try discriminate.
    destruct kind as [| | x allowance domain codomain]; try discriminate.
    destruct domain; try discriminate.
    destruct (fresh env x) eqn:new; try discriminate.
    destruct (index_demand env argument) as [z |] eqn:index_checked; try discriminate.
    destruct (type_demand ({| binder := x; annotation := Natural; type_uses := [] |} :: env)
      codomain) as [b |] eqn:codomain_checked; try discriminate.
    destruct (type_demand env (substitute_type x argument codomain)) as [output |]
      eqn:output_checked; try discriminate.
    destruct (demand_eqb (substitute_demand x z b) output) eqn:equal;
      inversion checked; subst.
    eapply GradeApplyNat; eauto using index_demand_sound, type_demand_sound, demand_eqb_sound.
  - destruct (infer_with allowsb env callee) as [[function w v] |] eqn:callee_checked; try discriminate.
    destruct function as [| | x allowance domain codomain]; try discriminate.
    destruct (infer_with allowsb env argument) as [[kind z a] |] eqn:argument_checked; try discriminate.
    destruct (fresh env x) eqn:new; try discriminate.
    destruct (ty_eq_dec (canonical_type [] kind) (canonical_type [] domain)); try discriminate.
    destruct (type_demand env codomain) as [b |] eqn:typed; inversion checked; subst.
    eapply GradeApplyValue with (v := v) (a := a); eauto using type_demand_sound.
  - destruct (fresh env x) eqn:new; try discriminate.
    destruct (index_demand env initializer) as [z |] eqn:initializer_checked; try discriminate.
    destruct (infer_with allowsb ({| binder := x; annotation := Natural; type_uses := [] |} :: env) body)
      as [[kind u v] |] eqn:body_checked; try discriminate.
    destruct (type_demand env (substitute_type x initializer kind)) as [output |] eqn:typed; try discriminate.
    destruct (allowsb (uses u x) allowance && demand_eqb (substitute_demand x z v) output)
      eqn:admitted; inversion checked; subst.
    apply andb_true_iff in admitted as [allowed agrees].
    eapply GradeLetNat; eauto using index_demand_sound, type_demand_sound, demand_eqb_sound.
Qed.

Lemma derives_type_demand : forall allows env subject result,
  DerivesWith allows env subject result ->
  exists row, TypeDemand env (result_type result) row /\ same_demand (type_demand_row result) row.
Proof.
  intros allows env subject result derivation. induction derivation; cbn.
  - exists row. auto.
  - exists []. split; [apply TypeNatural | intros name; reflexivity].
  - destruct IHderivation as [codomain_row [typed agrees]].
    exists (a ++ without x codomain_row). split.
    + now apply TypePi.
    + intro name. rewrite !uses_append, !uses_without.
      destruct (Nat.eqb name x); [reflexivity | now rewrite agrees].
  - exists output. auto.
  - exists b. split; [assumption | intros name; reflexivity].
  - exists output. auto.
Qed.

Definition check_with (allowsb : nat -> nat -> bool) (entries : list binding) (subject : term) : option judgment :=
  match check_telescope [] entries with
  | Some env => infer_with allowsb env subject
  | None => None
  end.

Definition Derives := DerivesWith (@eq nat).
Definition infer := infer_with Nat.eqb.
Definition check := check_with Nat.eqb.

Lemma infer_sound : forall subject env result,
  infer env subject = Some result -> Derives env subject result.
Proof.
  apply infer_with_sound. intros. now apply Nat.eqb_eq.
Qed.

Theorem check_sound : forall entries subject result,
  check entries subject = Some result ->
  exists env row, Extends [] entries env /\ Derives env subject result /\
    TypeDemand env (result_type result) row /\ same_demand (type_demand_row result) row.
Proof.
  intros entries subject result checked. unfold check, check_with in checked.
  destruct (check_telescope [] entries) as [env |] eqn:telescope; try discriminate.
  apply infer_sound in checked.
  destruct (derives_type_demand _ env subject result checked) as [row [typed agrees]].
  exists env, row. auto using check_telescope_sound.
Qed.

Definition rewrite_binding (x : nat) (argument : index) (z : demand) (entry : binding) : binding :=
  {| binder := binder entry; annotation := substitute_type x argument (annotation entry);
     type_uses := substitute_demand x z (type_uses entry) |}.

Definition substitute_telescope (prefix : list binding) (x : nat) (argument : index)
    (suffix : list binding) : option (list binding) :=
  match check_telescope [] prefix with
  | None => None
  | Some env =>
      let bound := {| binder := x; annotation := Natural; type_uses := [] |} in
      match index_demand env argument, check_telescope env (bound :: suffix) with
      | Some z, Some _ =>
          let rewritten := map (rewrite_binding x argument z) suffix in
          match check_telescope env rewritten with
          | Some _ => Some rewritten
          | None => None
          end
      | _, _ => None
      end
  end.

Theorem substitute_telescope_sound : forall prefix x argument suffix rewritten,
  substitute_telescope prefix x argument suffix = Some rewritten ->
  exists env before after z,
    Extends [] prefix env /\ IndexDemand env argument z /\
    Extends env ({| binder := x; annotation := Natural; type_uses := [] |} :: suffix) before /\
    rewritten = map (rewrite_binding x argument z) suffix /\ Extends env rewritten after.
Proof.
  intros prefix x argument suffix rewritten checked. unfold substitute_telescope in checked.
  destruct (check_telescope [] prefix) as [env |] eqn:prefix_checked; try discriminate.
  destruct (index_demand env argument) as [z |] eqn:index_checked; try discriminate.
  destruct (check_telescope env ({| binder := x; annotation := Natural; type_uses := [] |} :: suffix))
    as [before |] eqn:before_checked; try discriminate.
  destruct (check_telescope env (map (rewrite_binding x argument z) suffix))
    as [after |] eqn:after_checked; inversion checked; subst.
  exists env, before, after, z.
  repeat split; eauto using check_telescope_sound, index_demand_sound.
Qed.

Definition natural_binding (x : nat) := {| binder := x; annotation := Natural; type_uses := [] |}.
Definition preserve_length := Lambda 1 0 Natural (Lambda 2 1 (Vector (IndexVar 1)) (Var 2)).
Definition twice (x : nat) := IndexAdd (IndexVar x) (IndexVar x).

Example separate_computation_and_type_use :
  check [natural_binding 1] (Lambda 2 1 (Vector (IndexVar 1)) (Var 2)) =
    Some {| result_type := Pi 2 1 (Vector (IndexVar 1)) (Vector (IndexVar 1));
      computation_demand := []; type_demand_row := [(1, 1); (1, 1)] |}.
Proof. reflexivity. Qed.

Example specialize_dependent_function :
  match check [natural_binding 0] (ApplyNat preserve_length (twice 0)) with
  | Some result => result_type result = Pi 2 1 (Vector (twice 0)) (Vector (twice 0)) /\
      uses (computation_demand result) 0 = 0 /\ uses (type_demand_row result) 0 = 4
  | None => False
  end.
Proof. repeat split. Qed.

Example scale_computation_through_application :
  match check [natural_binding 0]
    (ApplyNat (Lambda 1 2 Natural (NatValue (twice 1))) (twice 0)) with
  | Some result => uses (computation_demand result) 0 = 4 /\
      uses (type_demand_row result) 0 = 0
  | None => False
  end.
Proof. split; reflexivity. Qed.

Example reject_wrong_exact_allowance :
  check [] (Lambda 1 1 Natural (NatValue (twice 1))) = None.
Proof. reflexivity. Qed.

Example reject_unbound_type_index : check [] (Lambda 1 1 (Vector (IndexVar 0)) (Var 1)) = None.
Proof. reflexivity. Qed.

Example reject_capture_of_nested_type_binder :
  check [{| binder := 0; annotation := Pi 1 0 Natural (Vector (IndexVar 1)); type_uses := [] |}]
    (Lambda 1 0 Natural (Var 0)) = None.
Proof. reflexivity. Qed.

Definition dependent_entry (x : nat) (length : index) (row : demand) :=
  {| binder := x; annotation := Vector length; type_uses := row |}.

Example rewrite_later_telescope_rows :
  substitute_telescope [natural_binding 0] 1 (twice 0)
    [dependent_entry 2 (IndexVar 1) [(1, 1)]; dependent_entry 3 (twice 1) [(1, 2)]] =
    Some [dependent_entry 2 (twice 0) [(0, 1); (0, 1)];
          dependent_entry 3 (IndexAdd (twice 0) (twice 0)) [(0, 2); (0, 2)]].
Proof. reflexivity. Qed.

Example reject_stale_type_use_certificate :
  check [natural_binding 0; dependent_entry 2 (twice 0) [(0, 1)]] (Var 2) = None.
Proof. reflexivity. Qed.

Example reject_stale_substitution_row :
  substitute_telescope [natural_binding 0] 1 (twice 0)
    [dependent_entry 2 (IndexVar 1) [(1, 1)]; dependent_entry 3 (twice 1) [(1, 1)]] = None.
Proof. reflexivity. Qed.

End GradedPure.
