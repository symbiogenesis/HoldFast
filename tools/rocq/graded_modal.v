(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool List.
Require Import graded_pure graded_domains.
Import ListNotations.

Module GradedModal.
Import GradedPure.

(* A type index can refer to the contents of a box. Natural index expressions
   look up variables in the natural-number part of the scope.
   See [modal elimination](../../docs/extensions/graded-foundation.md#dependent-data-and-elimination). *)
Inductive type_index :=
| PlainIndex (value : index)
| BoxContents (name : nat)
| PromotedContents (grade : nat) (value : index).

Inductive kind :=
| NatKind
| BoxNat (grade : nat)
| VecKind (length : type_index)
| ArrowKind (allowance : nat) (domain codomain : kind)
| ProductKind (first second : kind).

Definition env := list (nat * kind).
Definition find_kind (scope : env) (name : nat) : option kind :=
  option_map snd (find (fun entry => Nat.eqb name (fst entry)) scope).
Definition is_fresh (scope : env) (name : nat) : bool :=
  match find_kind scope name with None => true | Some _ => false end.

Fixpoint naturals (scope : env) : context :=
  match scope with
  | [] => []
  | (name, NatKind) :: rest => natural_binding name :: naturals rest
  | _ :: rest => naturals rest
  end.

Inductive IndexUses (scope : env) : type_index -> demand -> Prop :=
| PlainUses : forall i d, IndexDemand (naturals scope) i d ->
    IndexUses scope (PlainIndex i) d
| BoxContentsUses : forall name q, find_kind scope name = Some (BoxNat q) ->
    IndexUses scope (BoxContents name) [(name, 1)]
| PromotedContentsUses : forall q i d, IndexDemand (naturals scope) i d ->
    IndexUses scope (PromotedContents q i) (scale q d).

Definition index_uses (scope : env) (i : type_index) : option demand :=
  match i with
  | PlainIndex value => index_demand (naturals scope) value
  | BoxContents name =>
      match find_kind scope name with
      | Some (BoxNat _) => Some [(name, 1)]
      | _ => None
      end
  | PromotedContents q value => option_map (scale q) (index_demand (naturals scope) value)
  end.

Lemma index_uses_sound : forall scope i d,
  index_uses scope i = Some d -> IndexUses scope i d.
Proof.
  intros scope [value | name | q value] d checked; cbn in checked.
  - constructor. now apply index_demand_sound.
  - destruct (find_kind scope name) as [k |] eqn:found; try discriminate.
    destruct k; inversion checked; subst. eapply BoxContentsUses; eassumption.
  - destruct (index_demand (naturals scope) value) eqn:used;
      inversion checked; subst. constructor. now apply index_demand_sound.
Qed.

Inductive TypeUses (scope : env) : kind -> demand -> Prop :=
| NatUses : TypeUses scope NatKind []
| BoxUses : forall q, TypeUses scope (BoxNat q) []
| VecUses : forall i d, IndexUses scope i d -> TypeUses scope (VecKind i) d
| ArrowUses : forall q a b d e, TypeUses scope a d -> TypeUses scope b e ->
    TypeUses scope (ArrowKind q a b) (d ++ e)
| ProductUses : forall a b d e, TypeUses scope a d -> TypeUses scope b e ->
    TypeUses scope (ProductKind a b) (d ++ e).

Fixpoint type_uses (scope : env) (k : kind) : option demand :=
  match k with
  | NatKind | BoxNat _ => Some []
  | VecKind i => index_uses scope i
  | ArrowKind _ a b | ProductKind a b =>
      match type_uses scope a, type_uses scope b with
      | Some d, Some e => Some (d ++ e)
      | _, _ => None
      end
  end.

Lemma type_uses_sound : forall k scope d,
  type_uses scope k = Some d -> TypeUses scope k d.
Proof.
  induction k; intros scope d checked; cbn in checked.
  - inversion checked. constructor.
  - inversion checked. constructor.
  - constructor. now apply index_uses_sound.
  - destruct (type_uses scope k1) eqn:left, (type_uses scope k2) eqn:right;
      inversion checked; subst. constructor; auto.
  - destruct (type_uses scope k1) eqn:left, (type_uses scope k2) eqn:right;
      inversion checked; subst. constructor; auto.
Qed.

Inductive WellFormed : env -> Prop :=
| EmptyScope : WellFormed []
| ExtendScope : forall scope name k d, WellFormed scope ->
    is_fresh scope name = true -> TypeUses scope k d ->
    WellFormed ((name, k) :: scope).

Fixpoint well_formed (scope : env) : bool :=
  match scope with
  | [] => true
  | (name, k) :: outer =>
      match type_uses outer k with
      | Some _ => is_fresh outer name && well_formed outer
      | None => false
      end
  end.

Lemma well_formed_sound : forall scope, well_formed scope = true -> WellFormed scope.
Proof.
  induction scope as [| [name k] outer IH]; intros checked.
  - constructor.
  - cbn in checked. destruct (type_uses outer k) eqn:typed; try discriminate.
    apply andb_true_iff in checked as [fresh checked].
    eapply ExtendScope; eauto using type_uses_sound.
Qed.

Inductive boxed :=
| BoxName (name : nat)
| PromoteNat (grade : nat) (value : index).

Inductive BoxDerives (scope : env) : boxed -> nat -> demand -> type_index -> Prop :=
| NamedBox : forall name q, find_kind scope name = Some (BoxNat q) ->
    BoxDerives scope (BoxName name) q [(name, 1)] (BoxContents name)
| PromotedBox : forall q i d, IndexDemand (naturals scope) i d ->
    BoxDerives scope (PromoteNat q i) q (scale q d) (PromotedContents q i).

Definition infer_box (scope : env) (subject : boxed) : option (nat * demand * type_index) :=
  match subject with
  | BoxName name =>
      match find_kind scope name with
      | Some (BoxNat q) => Some (q, [(name, 1)], BoxContents name)
      | _ => None
      end
  | PromoteNat q i =>
      option_map (fun d => (q, scale q d, PromotedContents q i))
        (index_demand (naturals scope) i)
  end.

Lemma infer_box_sound : forall scope subject q d contents,
  infer_box scope subject = Some (q, d, contents) -> BoxDerives scope subject q d contents.
Proof.
  intros scope [name | q i] q' d contents checked; cbn in checked.
  - destruct (find_kind scope name) as [k |] eqn:found; try discriminate.
    destruct k; inversion checked; subst. now constructor.
  - destruct (index_demand (naturals scope) i) eqn:used;
      inversion checked; subst. constructor. now apply index_demand_sound.
Qed.

(* A well-formed motive refers to its box binder through BoxContents. Since
   kinds introduce no binders, replacement leaves the contents' free names in scope. *)
Fixpoint specialize (binder : nat) (contents : type_index) (k : kind) : kind :=
  match k with
  | VecKind (BoxContents name) => if Nat.eqb name binder then VecKind contents else k
  | ArrowKind q a b => ArrowKind q (specialize binder contents a) (specialize binder contents b)
  | ProductKind a b => ProductKind (specialize binder contents a) (specialize binder contents b)
  | _ => k
  end.

Definition kind_eq_dec : forall left right : kind, {left = right} + {left <> right}.
Proof. repeat decide equality. Defined.

Inductive value :=
| Name (name : nat)
| NaturalValue (payload : index)
| BoxValue (payload : boxed)
| Lambda (name allowance : nat) (domain : kind) (body : value)
| Pair (left right : value)
| LetBox (name motive_name : nat) (subject : boxed) (motive : kind) (body : value).

Record usage := {
  value_kind : kind;
  subject_uses : demand;
  result_type_uses : demand;
}.

Definition used (k : kind) (u v : demand) : usage :=
  {| value_kind := k; subject_uses := u; result_type_uses := v |}.

Definition binder_checks (scope : env) (name motive_name : nat) : bool :=
  is_fresh scope name && is_fresh scope motive_name && negb (Nat.eqb name motive_name).

Inductive DerivesWith (allows : nat -> nat -> Prop) (scope : env) : value -> usage -> Prop :=
| NameRule : forall name k row, find_kind scope name = Some k -> TypeUses scope k row ->
    DerivesWith allows scope (Name name) (used k [(name, 1)] row)
| NatRule : forall i d, IndexDemand (naturals scope) i d ->
    DerivesWith allows scope (NaturalValue i) (used NatKind d [])
| BoxRule : forall payload q d contents, BoxDerives scope payload q d contents ->
    DerivesWith allows scope (BoxValue payload) (used (BoxNat q) d [])
| LambdaRule : forall name allowance domain body codomain a u v row,
    is_fresh scope name = true -> TypeUses scope domain a ->
    DerivesWith allows ((name, domain) :: scope) body (used codomain u v) ->
    allows (uses u name) allowance -> TypeUses scope (ArrowKind allowance domain codomain) row ->
    DerivesWith allows scope (Lambda name allowance domain body)
      (used (ArrowKind allowance domain codomain) (without name u) row)
| PairRule : forall left right a b u v w z,
    DerivesWith allows scope left (used a u v) -> DerivesWith allows scope right (used b w z) ->
    DerivesWith allows scope (Pair left right) (used (ProductKind a b) (u ++ w) (v ++ z))
| LetBoxRule : forall name motive_name subject motive body q z contents w body_row motive_row output,
    is_fresh scope name = true -> is_fresh scope motive_name = true -> name <> motive_name ->
    BoxDerives scope subject q z contents ->
    TypeUses ((motive_name, BoxNat q) :: scope) motive motive_row ->
    DerivesWith allows ((name, NatKind) :: scope) body
      (used (specialize motive_name (PromotedContents q (IndexVar name)) motive) w body_row) ->
    allows (uses w name) q ->
    same_demand body_row (substitute_demand motive_name (scale q [(name, 1)]) motive_row) ->
    TypeUses scope (specialize motive_name contents motive) output ->
    same_demand output (substitute_demand motive_name z motive_row) ->
    DerivesWith allows scope (LetBox name motive_name subject motive body)
      (used (specialize motive_name contents motive) (without name w ++ z) output).

Definition Derives := DerivesWith (@GradedDomains.allows GradedDomains.NatExact).

Definition bind_option {A B : Type} (maybe : option A) (next : A -> option B) : option B :=
  match maybe with Some item => next item | None => None end.
Local Notation "'let?' x ':=' a 'in' b" := (bind_option a (fun x => b))
  (at level 10, x name, a at level 100, b at level 200).

Fixpoint infer_with (allowsb : nat -> nat -> bool) (scope : env) (subject : value) : option usage :=
  match subject with
  | Name name =>
      let? k := find_kind scope name in
      let? row := type_uses scope k in Some (used k [(name, 1)] row)
  | NaturalValue i => option_map (fun d => used NatKind d []) (index_demand (naturals scope) i)
  | BoxValue payload =>
      let? data := infer_box scope payload in
      let '(q, d, _) := data in Some (used (BoxNat q) d [])
  | Lambda name allowance domain body =>
      if is_fresh scope name then
        let? _ := type_uses scope domain in
        let? result := infer_with allowsb ((name, domain) :: scope) body in
        let k := ArrowKind allowance domain (value_kind result) in
        if allowsb (uses (subject_uses result) name) allowance then
          let? row := type_uses scope k in Some (used k (without name (subject_uses result)) row)
        else None
      else None
  | Pair first second =>
      let? a := infer_with allowsb scope first in
      let? b := infer_with allowsb scope second in
      Some (used (ProductKind (value_kind a) (value_kind b))
        (subject_uses a ++ subject_uses b) (result_type_uses a ++ result_type_uses b))
  | LetBox name motive_name payload motive body =>
      if binder_checks scope name motive_name then
        let? data := infer_box scope payload in
        let '(q, z, contents) := data in
        let? motive_row := type_uses ((motive_name, BoxNat q) :: scope) motive in
        let? result := infer_with allowsb ((name, NatKind) :: scope) body in
        let expected := specialize motive_name (PromotedContents q (IndexVar name)) motive in
        let k := specialize motive_name contents motive in
        if kind_eq_dec (value_kind result) expected then
          let? output := type_uses scope k in
          if allowsb (uses (subject_uses result) name) q
             && demand_eqb (result_type_uses result)
                           (substitute_demand motive_name (scale q [(name, 1)]) motive_row)
             && demand_eqb output (substitute_demand motive_name z motive_row)
          then Some (used k (without name (subject_uses result) ++ z) output) else None
        else None
      else None
  end.

Lemma infer_with_sound : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall subject scope result,
    infer_with allowsb scope subject = Some result -> DerivesWith allows scope subject result.
Proof.
  intros allows allowsb admission_sound.
  induction subject as [name | i | payload | name allowance domain body IH | left IHl right IHr
    | name motive_name payload motive body IH]; intros scope result checked; cbn in checked.
  - destruct (find_kind scope name) eqn:found; try discriminate.
    cbn in checked. destruct (type_uses scope k) eqn:typed; inversion checked; subst.
    constructor; auto using type_uses_sound.
  - destruct (index_demand (naturals scope) i) eqn:used_index; inversion checked; subst.
    constructor. now apply index_demand_sound.
  - destruct (infer_box scope payload) as [[[q d] contents] |] eqn:boxed_ok;
      inversion checked; subst. econstructor. eapply infer_box_sound; eassumption.
  - destruct (is_fresh scope name) eqn:fresh; try discriminate.
    destruct (type_uses scope domain) eqn:typed; try discriminate.
    cbn in checked. destruct (infer_with allowsb ((name, domain) :: scope) body) as [[k u v] |] eqn:body_ok;
      try discriminate.
    cbn in checked. destruct (allowsb (uses u name) allowance) eqn:bound; try discriminate.
    destruct (type_uses scope k) eqn:formed; inversion checked; subst.
    eapply LambdaRule; eauto using admission_sound, type_uses_sound, ArrowUses.
  - destruct (infer_with allowsb scope left) as [[a u v] |] eqn:left_ok; try discriminate.
    cbn in checked. destruct (infer_with allowsb scope right) as [[b w z] |] eqn:right_ok;
      inversion checked; subst. constructor; auto.
  - destruct (binder_checks scope name motive_name) eqn:fresh; try discriminate.
    destruct (infer_box scope payload) as [[[q z] contents] |] eqn:boxed_ok; try discriminate.
    cbn [bind_option] in checked. destruct (type_uses ((motive_name, BoxNat q) :: scope) motive)
      as [motive_row |] eqn:motive_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_with allowsb ((name, NatKind) :: scope) body) as [[k w row] |] eqn:body_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec k (specialize motive_name (PromotedContents q (IndexVar name)) motive))
      as [same_kind | different]; try discriminate.
    destruct (type_uses scope (specialize motive_name contents motive)) as [output |] eqn:out_ok;
      try discriminate.
    cbn [bind_option] in checked.
    change ((if allowsb (uses w name) q
      && demand_eqb row (substitute_demand motive_name (scale q [(name, 1)]) motive_row)
      && demand_eqb output (substitute_demand motive_name z motive_row)
      then Some (used (specialize motive_name contents motive) (without name w ++ z) output)
      else None) = Some result) in checked.
    destruct (allowsb (uses w name) q
      && demand_eqb row (substitute_demand motive_name (scale q [(name, 1)]) motive_row)
      && demand_eqb output (substitute_demand motive_name z motive_row)) eqn:agrees;
      inversion checked; subst.
    unfold binder_checks in fresh.
    apply andb_true_iff in fresh as [fresh distinct].
    apply andb_true_iff in fresh as [fresh_name fresh_motive].
    apply negb_true_iff, Nat.eqb_neq in distinct.
    apply andb_true_iff in agrees as [agrees out_demand].
    apply andb_true_iff in agrees as [bound body_demand].
    eapply LetBoxRule; eauto using admission_sound, infer_box_sound, type_uses_sound, demand_eqb_sound.
Qed.

Definition check_with (allowsb : nat -> nat -> bool) (scope : env) (subject : value) : option usage :=
  if well_formed scope then infer_with allowsb scope subject else None.

Definition check := check_with (@GradedDomains.allowsb GradedDomains.NatExact).
Definition bounded_check := check_with (@GradedDomains.allowsb GradedDomains.NatBound).

Theorem check_with_sound : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall scope subject result,
    check_with allowsb scope subject = Some result -> WellFormed scope /\ DerivesWith allows scope subject result.
Proof.
  intros allows allowsb admission_sound scope subject result checked. unfold check_with in checked.
  destruct (well_formed scope) eqn:valid; try discriminate.
  split; eauto using well_formed_sound, infer_with_sound.
Qed.

Theorem check_sound : forall scope subject result,
  check scope subject = Some result -> WellFormed scope /\ Derives scope subject result.
Proof.
  unfold check, Derives. apply check_with_sound. intros. now apply Nat.eqb_eq.
Qed.

Theorem bounded_check_sound : forall scope subject result,
  bounded_check scope subject = Some result ->
  WellFormed scope /\ DerivesWith (@GradedDomains.allows GradedDomains.NatBound) scope subject result.
Proof.
  unfold bounded_check. apply check_with_sound. intros. now apply Nat.leb_le.
Qed.

Lemma uses_scale : forall q row name, uses (scale q row) name = q * uses row name.
Proof.
  intros q row. induction row as [| [k n] rest IH]; intros name; cbn.
  - now rewrite Nat.mul_0_r.
  - rewrite IH, Nat.mul_add_distr_l. now destruct (name =? k); cbn; rewrite ?Nat.mul_0_r.
Qed.

Lemma absent_natural : forall scope name,
  find_kind scope name = None -> lookup (naturals scope) name = None.
Proof.
  induction scope as [| [key k] rest IH]; intros name absent; [reflexivity |].
  unfold find_kind in absent. cbn in absent.
  destruct (name =? key) eqn:equal; try discriminate.
  destruct k; cbn; try now apply IH.
  unfold lookup. cbn. rewrite equal. now apply IH.
Qed.

Lemma zero_natural_use : forall scope i row name,
  IndexDemand (naturals scope) i row -> find_kind scope name = None -> uses row name = 0.
Proof.
  intros scope i row name demand_index absent.
  apply absent_natural in absent. remember (naturals scope) as ctx. clear Heqctx.
  induction demand_index as [key b found natural | n | l r d e dl IHl dr IHr].
  - cbn. destruct (name =? key) eqn:equal; [| reflexivity].
    apply Nat.eqb_eq in equal. subst key. congruence.
  - reflexivity.
  - now rewrite uses_append, IHl, IHr.
Qed.

Lemma zero_type_use : forall scope k row name,
  TypeUses scope k row -> find_kind scope name = None -> uses row name = 0.
Proof.
  intros scope k row name typed absent.
  induction typed as [| q | i d index_typed | q a b d e dl IHl dr IHr | a b d e dl IHl dr IHr].
  - reflexivity.
  - reflexivity.
  - destruct index_typed as [i d natural | key q found | q i d natural].
    + eapply zero_natural_use; eauto.
    + cbn. destruct (name =? key) eqn:equal; [| reflexivity].
      apply Nat.eqb_eq in equal. subst key. congruence.
    + rewrite uses_scale. rewrite (zero_natural_use scope i d name natural absent).
      now rewrite Nat.mul_0_r.
  - now rewrite uses_append, IHl, IHr.
  - now rewrite uses_append, IHl, IHr.
Qed.

Theorem checked_let_box_demands_with : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall scope name motive_name payload motive body result,
  check_with allowsb scope (LetBox name motive_name payload motive body) = Some result ->
  exists q z contents w body_row motive_row,
    BoxDerives scope payload q z contents /\
    TypeUses ((motive_name, BoxNat q) :: scope) motive motive_row /\
    DerivesWith allows ((name, NatKind) :: scope) body
      (used (specialize motive_name (PromotedContents q (IndexVar name)) motive) w body_row) /\
    allows (uses w name) q /\
    uses body_row name = q * uses motive_row motive_name /\
    value_kind result = specialize motive_name contents motive /\
    (forall x, uses (subject_uses result) x =
      (if x =? name then 0 else uses w x) + uses z x) /\
    (forall x, uses (result_type_uses result) x =
      (if x =? motive_name then 0 else uses motive_row x) + uses motive_row motive_name * uses z x).
Proof.
  intros allows allowsb admission_sound scope name motive_name payload motive body result checked.
  pose proof (check_with_sound allows allowsb admission_sound _ _ _ checked) as [_ derivation].
  inversion derivation as [| | | | | x p b m t q z contents w body_row motive_row output
    fresh_name fresh_motive distinct boxed_ok motive_ok body_ok bound body_demand out_kind out_demand];
    subst.
  do 6 eexists. repeat split; eauto.
  - rewrite (body_demand name).
    unfold substitute_demand. rewrite uses_append, uses_without, !uses_scale.
    apply Nat.eqb_neq in distinct. cbn. rewrite distinct, Nat.eqb_refl, Nat.mul_1_r.
    assert (uses motive_row name = 0) as absent.
    { eapply zero_type_use; [exact motive_ok |]. unfold find_kind. cbn.
      rewrite distinct. unfold is_fresh in fresh_name. fold (find_kind scope name).
      now destruct (find_kind scope name). }
    rewrite absent, Nat.mul_comm. reflexivity.
  - intros. cbn [subject_uses used]. now rewrite uses_append, uses_without.
  - intros. cbn [result_type_uses used]. rewrite (out_demand x).
    now unfold substitute_demand; rewrite uses_append, uses_without, uses_scale.
Qed.

Definition checked_let_box_demands := checked_let_box_demands_with
  (@GradedDomains.allows GradedDomains.NatExact)
  (@GradedDomains.allowsb GradedDomains.NatExact)
  (fun actual allowance => proj1 (Nat.eqb_eq actual allowance)).

Definition bounded_checked_let_box_demands := checked_let_box_demands_with
  (@GradedDomains.allows GradedDomains.NatBound)
  (@GradedDomains.allowsb GradedDomains.NatBound)
  (fun actual allowance => proj1 (Nat.leb_le actual allowance)).

Definition type_identity (length : type_index) : kind :=
  ArrowKind 1 (VecKind length) (VecKind length).

Definition vec_identity (length : type_index) : value :=
  Lambda 3 1 (VecKind length) (Name 3).

Definition promoted_twice (name : nat) : boxed :=
  PromoteNat 2 (IndexAdd (IndexVar name) (IndexVar name)).

Example promotion_scales_term_demand :
  check [(0, NatKind)] (BoxValue (promoted_twice 0)) =
    Some (used (BoxNat 2) [(0, 2); (0, 2)] []).
Proof. reflexivity. Qed.

Definition dependent_use (q : nat) : value :=
  LetBox 1 2 (BoxName 0) (ProductKind NatKind (type_identity (BoxContents 2)))
    (Pair (NaturalValue (IndexAdd (IndexVar 1) (IndexVar 1)))
      (vec_identity (PromotedContents q (IndexVar 1)))).

Example bounded_elimination_keeps_exact_type_use :
  bounded_check [(0, BoxNat 3)] (dependent_use 3) =
    Some (used (ProductKind NatKind (type_identity (BoxContents 0))) [(0, 1)] [(0, 1); (0, 1)]).
Proof. reflexivity. Qed.

Example reject_exact_underuse : check [(0, BoxNat 3)] (dependent_use 3) = None.
Proof. reflexivity. Qed.

Example reject_bounded_overuse : bounded_check [(0, BoxNat 1)] (dependent_use 1) = None.
Proof. reflexivity. Qed.

Example dependent_elimination_of_abstract_box :
  check [(0, BoxNat 2)] (dependent_use 2) =
    Some (used (ProductKind NatKind (type_identity (BoxContents 0))) [(0, 1)] [(0, 1); (0, 1)]).
Proof. reflexivity. Qed.

Example dependent_elimination_of_promoted_box :
  check [(0, NatKind)]
    (LetBox 1 2 (promoted_twice 0) (ProductKind NatKind (type_identity (BoxContents 2)))
      (Pair (NaturalValue (IndexAdd (IndexVar 1) (IndexVar 1)))
        (vec_identity (PromotedContents 2 (IndexVar 1))))) =
    Some (used (ProductKind NatKind
      (type_identity (PromotedContents 2 (IndexAdd (IndexVar 0) (IndexVar 0)))))
      [(0, 2); (0, 2)] [(0, 2); (0, 2); (0, 2); (0, 2)]).
Proof. reflexivity. Qed.

Example zero_use_keeps_logical_motive :
  check [(0, BoxNat 0)]
    (LetBox 1 2 (BoxName 0) (type_identity (BoxContents 2))
      (vec_identity (PromotedContents 0 (IndexVar 1)))) =
    Some (used (type_identity (BoxContents 0)) [(0, 1)] [(0, 1); (0, 1)]).
Proof. reflexivity. Qed.

Example reject_wrong_exact_box_grade :
  check [(0, BoxNat 1)] (dependent_use 1) = None.
Proof. reflexivity. Qed.

Example reject_wrong_motive_specialization :
  check [(0, BoxNat 2)] (dependent_use 1) = None.
Proof. reflexivity. Qed.

Example reject_bypassing_open :
  check [(0, BoxNat 2)] (NaturalValue (IndexVar 0)) = None.
Proof. reflexivity. Qed.

Example reject_computing_with_zero_use_payload :
  check [(0, BoxNat 0)] (LetBox 1 2 (BoxName 0) NatKind (NaturalValue (IndexVar 1))) = None.
Proof. reflexivity. Qed.

End GradedModal.
