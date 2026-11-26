(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool List.
Require Import graded_pure graded_domains.
Import ListNotations.

Module GradedModal.
Import GradedPure.

Inductive extent :=
| ExtentField
| ExtentLiteral (n : nat)
| ExtentAdd (left right : extent).

Record indexed_shape := {
  record_id : nat;
  payload_extent : extent
}.

Fixpoint instantiate_extent (family : extent) (field : index) : index :=
  match family with
  | ExtentField => field
  | ExtentLiteral n => IndexLit n
  | ExtentAdd lhs rhs => IndexAdd (instantiate_extent lhs field) (instantiate_extent rhs field)
  end.

Lemma instantiate_extent_typed : forall scope family field d,
  IndexDemand scope field d ->
  exists row, IndexDemand scope (instantiate_extent family field) row.
Proof.
  intros scope family. induction family as [| n | lhs IHl rhs IHr]; intros field d typed; cbn.
  - now exists d.
  - exists []. constructor.
  - destruct (IHl field d typed) as [l dl], (IHr field d typed) as [r dr].
    exists (l ++ r). now constructor.
Qed.

Inductive indexed :=
| IndexedName (name : nat)
| BuildIndexed (shape : indexed_shape) (length : index) (payload : nat).

(* A type index can refer to the contents of a box or the length of an indexed
   pair. An explicit pair constructor contributes both fields before projection.
   See [modal elimination](../../docs/extensions/graded-foundation.md#dependent-data-and-elimination). *)
Inductive type_index :=
| PlainIndex (value : index)
| BoxContents (name : nat)
| PromotedContents (grade : nat) (value : index)
| IndexedLength (shape : indexed_shape) (pair : indexed).

Inductive kind :=
| NatKind
| BoxKind (grade : nat) (payload : kind)
| IndexedKind (shape : indexed_shape)
| VecKind (length : type_index)
| ArrowKind (allowance : nat) (domain codomain : kind)
| ProductKind (first second : kind)
| BoolKind
| SumKind (left right : kind)
| PiKind (name allowance : nat) (domain codomain : kind).

Abbreviation BoxNat grade := (BoxKind grade NatKind).

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

Definition payload_kind (shape : indexed_shape) (length : index) : kind :=
  VecKind (PlainIndex (instantiate_extent (payload_extent shape) length)).
Definition index_eq_dec : forall left right : index, {left = right} + {left <> right}.
Proof. repeat decide equality. Defined.
Definition indexed_shape_eq_dec : forall left right : indexed_shape, {left = right} + {left <> right}.
Proof. repeat decide equality. Defined.

Inductive IndexedUses (scope : env) (shape : indexed_shape) : indexed -> demand -> Prop :=
| IndexedNameUses : forall name, find_kind scope name = Some (IndexedKind shape) ->
    IndexedUses scope shape (IndexedName name) [(name, 1)]
| BuildIndexedUses : forall length payload d,
    IndexDemand (naturals scope) length d -> find_kind scope payload = Some (payload_kind shape length) ->
    IndexedUses scope shape (BuildIndexed shape length payload) (d ++ [(payload, 1)]).

Definition indexed_uses (scope : env) (shape : indexed_shape) (pair : indexed) : option demand :=
  match pair with
  | IndexedName name =>
      match find_kind scope name with
      | Some (IndexedKind actual) =>
          if indexed_shape_eq_dec actual shape then Some [(name, 1)] else None
      | _ => None
      end
  | BuildIndexed actual length payload =>
      match find_kind scope payload, index_demand (naturals scope) length with
      | Some (VecKind (PlainIndex expected)), Some d =>
          if indexed_shape_eq_dec actual shape then
            if index_eq_dec expected (instantiate_extent (payload_extent shape) length)
            then Some (d ++ [(payload, 1)]) else None
          else None
      | _, _ => None
      end
  end.

Lemma indexed_uses_sound : forall scope shape pair row,
  indexed_uses scope shape pair = Some row -> IndexedUses scope shape pair row.
Proof.
  intros scope shape [name | actual length payload] row checked; cbn in checked.
  - destruct (find_kind scope name) as [k |] eqn:found; try discriminate.
    destruct k as [| | actual | | | | | |]; try discriminate.
    destruct (indexed_shape_eq_dec actual shape); inversion checked; subst. now constructor.
  - destruct (find_kind scope payload) as [k |] eqn:found; try discriminate.
    destruct k as [| | | [expected | | |] | | | | |]; try discriminate.
    destruct (index_demand (naturals scope) length) as [d |] eqn:length_ok; try discriminate.
    destruct (indexed_shape_eq_dec actual shape); try discriminate.
    destruct (index_eq_dec expected (instantiate_extent (payload_extent shape) length));
      inversion checked; subst. constructor; auto using index_demand_sound.
Qed.

Inductive IndexUses (scope : env) : type_index -> demand -> Prop :=
| PlainUses : forall i d, IndexDemand (naturals scope) i d ->
    IndexUses scope (PlainIndex i) d
| BoxContentsUses : forall name q, find_kind scope name = Some (BoxNat q) ->
    IndexUses scope (BoxContents name) [(name, 1)]
| PromotedContentsUses : forall q i d, IndexDemand (naturals scope) i d ->
    IndexUses scope (PromotedContents q i) (scale q d)
| IndexedLengthUses : forall shape pair d, IndexedUses scope shape pair d ->
    IndexUses scope (IndexedLength shape pair) d.

Definition index_uses (scope : env) (i : type_index) : option demand :=
  match i with
  | PlainIndex value => index_demand (naturals scope) value
  | BoxContents name =>
      match find_kind scope name with
      | Some (BoxNat _) => Some [(name, 1)]
      | _ => None
      end
  | PromotedContents q value => option_map (scale q) (index_demand (naturals scope) value)
  | IndexedLength shape packed => indexed_uses scope shape packed
  end.

Lemma index_uses_sound : forall scope i d,
  index_uses scope i = Some d -> IndexUses scope i d.
Proof.
  intros scope [value | name | q value | shape pair] d checked; cbn in checked.
  - constructor. now apply index_demand_sound.
  - destruct (find_kind scope name) as [k |] eqn:found; try discriminate.
    destruct k as [| q [| | | | | | | |] | | | | | | |]; inversion checked; subst.
    eapply BoxContentsUses; eassumption.
  - destruct (index_demand (naturals scope) value) eqn:used;
      inversion checked; subst. constructor. now apply index_demand_sound.
  - constructor. now apply indexed_uses_sound.
Qed.

Inductive TypeUses (scope : env) : kind -> demand -> Prop :=
| NatUses : TypeUses scope NatKind []
| BoxUses : forall q payload_k d, TypeUses scope payload_k d ->
    TypeUses scope (BoxKind q payload_k) d
| IndexedKindUses : forall shape, TypeUses scope (IndexedKind shape) []
| VecUses : forall i d, IndexUses scope i d -> TypeUses scope (VecKind i) d
| ArrowUses : forall q a b d e, TypeUses scope a d -> TypeUses scope b e ->
    TypeUses scope (ArrowKind q a b) (d ++ e)
| ProductUses : forall a b d e, TypeUses scope a d -> TypeUses scope b e ->
    TypeUses scope (ProductKind a b) (d ++ e)
| BoolUses : TypeUses scope BoolKind []
| SumUses : forall a b d e, TypeUses scope a d -> TypeUses scope b e ->
    TypeUses scope (SumKind a b) (d ++ e)
| PiUses : forall x allowance a b d e,
    is_fresh scope x = true -> TypeUses scope a d ->
    TypeUses ((x, a) :: scope) b e ->
    TypeUses scope (PiKind x allowance a b) (d ++ without x e).

Fixpoint type_uses (scope : env) (k : kind) : option demand :=
  match k with
  | NatKind | IndexedKind _ | BoolKind => Some []
  | BoxKind _ payload_k => type_uses scope payload_k
  | VecKind i => index_uses scope i
  | ArrowKind _ a b | ProductKind a b | SumKind a b =>
      match type_uses scope a, type_uses scope b with
      | Some d, Some e => Some (d ++ e)
      | _, _ => None
      end
  | PiKind x _ a b =>
      if is_fresh scope x then
        match type_uses scope a, type_uses ((x, a) :: scope) b with
        | Some d, Some e => Some (d ++ without x e)
        | _, _ => None
        end
      else None
  end.

Lemma type_uses_sound : forall k scope d,
  type_uses scope k = Some d -> TypeUses scope k d.
Proof.
  induction k as [| q payload IH | shape | i | allowance a IHa b IHb
    | a IHa b IHb | | a IHa b IHb | x allowance a IHa b IHb];
    intros scope d checked; cbn in checked.
  - inversion checked. constructor.
  - constructor. auto.
  - inversion checked. constructor.
  - constructor. now apply index_uses_sound.
  - destruct (type_uses scope a) eqn:left, (type_uses scope b) eqn:right;
      inversion checked; subst. constructor; auto.
  - destruct (type_uses scope a) eqn:left, (type_uses scope b) eqn:right;
      inversion checked; subst. constructor; auto.
  - inversion checked. constructor.
  - destruct (type_uses scope a) eqn:left, (type_uses scope b) eqn:right;
      inversion checked; subst. constructor; auto.
  - destruct (is_fresh scope x) eqn:fresh; try discriminate.
    destruct (type_uses scope a) eqn:left, (type_uses ((x, a) :: scope) b) eqn:right;
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
    destruct k as [| q [| | | | | | | |] | | | | | | |]; inversion checked; subst.
    now constructor.
  - destruct (index_demand (naturals scope) i) eqn:used;
      inversion checked; subst. constructor. now apply index_demand_sound.
Qed.

(* Kinds introduce no binders. Replacing their indices keeps the replacement's
   free names in scope. *)
Fixpoint map_indices (replace : type_index -> type_index) (k : kind) : kind :=
  match k with
  | BoxKind q payload => BoxKind q (map_indices replace payload)
  | VecKind i => VecKind (replace i)
  | ArrowKind q a b => ArrowKind q (map_indices replace a) (map_indices replace b)
  | ProductKind a b => ProductKind (map_indices replace a) (map_indices replace b)
  | SumKind a b => SumKind (map_indices replace a) (map_indices replace b)
  | _ => k
  end.

Definition substitute_indexed_pair (x : nat) (value : index) (p : indexed) : indexed :=
  match p with
  | IndexedName _ => p
  | BuildIndexed shape length payload =>
      BuildIndexed shape (substitute_index x value length) payload
  end.

Definition substitute_type_index (x : nat) (value : index) (ti : type_index) : type_index :=
  match ti with
  | PlainIndex i => PlainIndex (substitute_index x value i)
  | BoxContents _ => ti
  | PromotedContents q i => PromotedContents q (substitute_index x value i)
  | IndexedLength shape p => IndexedLength shape (substitute_indexed_pair x value p)
  end.

Fixpoint substitute_kind (x : nat) (value : index) (k : kind) : kind :=
  match k with
  | NatKind | IndexedKind _ | BoolKind => k
  | BoxKind q payload => BoxKind q (substitute_kind x value payload)
  | VecKind i => VecKind (substitute_type_index x value i)
  | ArrowKind allowance a b =>
      ArrowKind allowance (substitute_kind x value a) (substitute_kind x value b)
  | ProductKind a b =>
      ProductKind (substitute_kind x value a) (substitute_kind x value b)
  | SumKind a b =>
      SumKind (substitute_kind x value a) (substitute_kind x value b)
  | PiKind y allowance a b =>
      PiKind y allowance (substitute_kind x value a)
        (if Nat.eqb x y then b else substitute_kind x value b)
  end.

Definition specialize (binder : nat) (contents : type_index) : kind -> kind :=
  map_indices (fun i => match i with
    | BoxContents name => if Nat.eqb name binder then contents else i
    | _ => i
    end).

Definition specialize_indexed (binder : nat) (replacement : indexed) : kind -> kind :=
  map_indices (fun i => match i with
    | IndexedLength shape (IndexedName name) =>
        if Nat.eqb name binder then IndexedLength shape replacement else i
    | _ => i
    end).

Definition kind_eq_dec : forall left right : kind, {left = right} + {left <> right}.
Proof. repeat decide equality. Defined.

Inductive value :=
| Name (name : nat)
| NaturalValue (payload : index)
| BoxValue (payload : boxed)
| IndexedValue (shape : indexed_shape) (payload : indexed)
| Lambda (name allowance : nat) (domain : kind) (body : value)
| Pair (left right : value)
| LetBox (name motive_name : nat) (subject : boxed) (motive : kind) (body : value)
| LetIndexed (shape : indexed_shape) (length payload motive_name : nat)
    (subject : indexed) (motive : kind) (body : value)
| Apply (callee argument : value)
| LetBoxValue (name motive_name : nat) (subject : value) (motive : kind) (body : value)
| PromoteValue (grade : nat) (inner : value)
| BoolLit (b : bool)
| IfValue (cond then_b else_b : value)
| InlValue (right : kind) (v : value)
| InrValue (left : kind) (v : value)
| MatchSum (l_name r_name : nat) (scrutinee l_body r_body : value)
| LetNatValue (name allowance : nat) (init : index) (body : value)
| DepLambda (name allowance : nat) (domain : kind) (body : value)
| ApplyNatValue (callee : value) (argument : index).

Fixpoint join_keys (keys : list nat) (d1 d2 : demand) : demand :=
  match keys with
  | [] => []
  | k :: rest =>
      if existsb (Nat.eqb k) rest
      then join_keys rest d1 d2
      else (k, Nat.max (uses d1 k) (uses d2 k)) :: join_keys rest d1 d2
  end.

Definition join_demand (d1 d2 : demand) : demand :=
  join_keys (map fst (d1 ++ d2)) d1 d2.

Lemma join_keys_fst_subset : forall keys d1 d2 x,
  In x (map fst (join_keys keys d1 d2)) -> In x keys.
Proof.
  induction keys as [| k rest IH]; intros d1 d2 x present; cbn in *.
  - contradiction.
  - destruct (existsb (Nat.eqb k) rest) eqn:dup.
    + right. eapply IH; eassumption.
    + cbn in present. destruct present as [-> | present].
      * now left.
      * right. eapply IH; eassumption.
Qed.

Lemma uses_join_keys_in : forall keys d1 d2 x,
  In x keys -> uses (join_keys keys d1 d2) x = Nat.max (uses d1 x) (uses d2 x).
Proof.
  induction keys as [| k rest IH]; intros d1 d2 x present; cbn in *.
  - contradiction.
  - destruct (existsb (Nat.eqb k) rest) eqn:dup.
    + apply existsb_exists in dup as [y [yin yeq]].
      apply Nat.eqb_eq in yeq. subst y.
      destruct present as [<- | present]; now apply IH.
    + cbn. destruct present as [-> | present].
      * rewrite Nat.eqb_refl.
        assert (absent_rest : ~ In x (map fst (join_keys rest d1 d2))).
        { intro in_rest. apply join_keys_fst_subset in in_rest.
          assert (found : existsb (Nat.eqb x) rest = true).
          { apply existsb_exists. exists x. split; [exact in_rest | apply Nat.eqb_refl]. }
          congruence. }
        rewrite (absent_use _ _ absent_rest). apply Nat.add_0_r.
      * destruct (Nat.eqb x k) eqn:eq.
        -- apply Nat.eqb_eq in eq. subst k.
           assert (found : existsb (Nat.eqb x) rest = true).
           { apply existsb_exists. exists x. split; [exact present | apply Nat.eqb_refl]. }
           congruence.
        -- cbn. now apply IH.
Qed.

Lemma uses_join_demand : forall d1 d2 x,
  uses (join_demand d1 d2) x = Nat.max (uses d1 x) (uses d2 x).
Proof.
  intros d1 d2 x. unfold join_demand.
  destruct (in_dec Nat.eq_dec x (map fst (d1 ++ d2))) as [present | absent].
  - now apply uses_join_keys_in.
  - assert (not_joined : ~ In x (map fst (join_keys (map fst (d1 ++ d2)) d1 d2))).
    { intro in_joined. apply join_keys_fst_subset in in_joined. contradiction. }
    rewrite (absent_use _ _ not_joined).
    rewrite map_app in absent.
    rewrite !absent_use; [reflexivity | |]; intro H; apply absent, in_or_app; auto.
Qed.

Definition BranchDemand (exact_branches : bool) (d1 d2 d : demand) : Prop :=
  if exact_branches then same_demand d1 d2 /\ same_demand d d1
  else same_demand d (join_demand d1 d2).

Definition branch_demand (exact_branches : bool) (d1 d2 : demand) : option demand :=
  if exact_branches then
    if demand_eqb d1 d2 then Some d1 else None
  else
    Some (join_demand d1 d2).

Lemma branch_demand_sound : forall exact_branches d1 d2 d,
  branch_demand exact_branches d1 d2 = Some d -> BranchDemand exact_branches d1 d2 d.
Proof.
  intros [|] d1 d2 d checked; cbn in checked.
  - destruct (demand_eqb d1 d2) eqn:eq; inversion checked; subst.
    split; [now apply demand_eqb_sound | intro x; reflexivity].
  - inversion checked; subst. intro x. reflexivity.
Qed.

Record usage := {
  value_kind : kind;
  subject_uses : demand;
  result_type_uses : demand;
}.

Definition used (k : kind) (u v : demand) : usage :=
  {| value_kind := k; subject_uses := u; result_type_uses := v |}.

Definition binder_checks (scope : env) (name motive_name : nat) : bool :=
  is_fresh scope name && is_fresh scope motive_name && negb (Nat.eqb name motive_name).

Definition indexed_scope (scope : env) (shape : indexed_shape) (length payload : nat) : env :=
  (payload, payload_kind shape (IndexVar length)) :: (length, NatKind) :: scope.

Definition indexed_binders (scope : env) (shape : indexed_shape) (length payload motive_name : nat) : bool :=
  is_fresh scope length && is_fresh ((length, NatKind) :: scope) payload &&
  is_fresh (indexed_scope scope shape length payload) motive_name.

Definition fields_used (length payload : nat) : demand := [(length, 1); (payload, 1)].

(* Both fields must admit the same grade under the selected order. *)
Definition tensor_grade (row : demand) (length payload : nat) : nat :=
  Nat.max (uses row length) (uses row payload).

Inductive DerivesWith (allows : nat -> nat -> Prop) (scope : env) : value -> usage -> Prop :=
| NameRule : forall name k row, find_kind scope name = Some k -> TypeUses scope k row ->
    DerivesWith allows scope (Name name) (used k [(name, 1)] row)
| NatRule : forall i d, IndexDemand (naturals scope) i d ->
    DerivesWith allows scope (NaturalValue i) (used NatKind d [])
| BoxRule : forall payload q d contents, BoxDerives scope payload q d contents ->
    DerivesWith allows scope (BoxValue payload) (used (BoxNat q) d [])
| IndexedRule : forall shape pair d, IndexedUses scope shape pair d ->
    DerivesWith allows scope (IndexedValue shape pair) (used (IndexedKind shape) d [])
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
      (used (specialize motive_name contents motive) (without name w ++ z) output)
| LetIndexedRule : forall shape length payload motive_name subject motive body z w body_row motive_row output s,
    indexed_binders scope shape length payload motive_name = true ->
    IndexedUses scope shape subject z ->
    TypeUses ((motive_name, IndexedKind shape) :: scope) motive motive_row ->
    DerivesWith allows (indexed_scope scope shape length payload) body
      (used (specialize_indexed motive_name (BuildIndexed shape (IndexVar length) payload) motive) w body_row) ->
    allows (uses w length) s -> allows (uses w payload) s ->
    same_demand body_row (substitute_demand motive_name (fields_used length payload) motive_row) ->
    TypeUses scope (specialize_indexed motive_name subject motive) output ->
    same_demand output (substitute_demand motive_name z motive_row) ->
    DerivesWith allows scope (LetIndexed shape length payload motive_name subject motive body)
      (used (specialize_indexed motive_name subject motive) (without length (without payload w) ++ scale s z) output)
  | ApplyRule : forall callee argument allowance domain codomain w v z a b,
      DerivesWith allows scope callee (used (ArrowKind allowance domain codomain) w v) ->
      DerivesWith allows scope argument (used domain z a) ->
      TypeUses scope codomain b ->
      DerivesWith allows scope (Apply callee argument)
        (used codomain (w ++ scale allowance z) b)
  | LetBoxValueRule : forall name motive_name subject motive body q z subj_row w body_row motive_row output,
      is_fresh scope name = true -> is_fresh scope motive_name = true -> name <> motive_name ->
      DerivesWith allows scope subject (used (BoxNat q) z subj_row) ->
      TypeUses ((motive_name, BoxNat q) :: scope) motive motive_row ->
      uses motive_row motive_name = 0 ->
      DerivesWith allows ((name, NatKind) :: scope) body (used motive w body_row) ->
      allows (uses w name) q ->
      same_demand body_row motive_row ->
      TypeUses scope motive output ->
      same_demand output motive_row ->
      DerivesWith allows scope (LetBoxValue name motive_name subject motive body)
        (used motive (without name w ++ z) output).

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
  | IndexedValue shape packed =>
      option_map (fun d => used (IndexedKind shape) d []) (indexed_uses scope shape packed)
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
  | LetIndexed shape length payload motive_name packed motive body =>
      if indexed_binders scope shape length payload motive_name then
        let? z := indexed_uses scope shape packed in
        let? motive_row := type_uses ((motive_name, IndexedKind shape) :: scope) motive in
        let? result := infer_with allowsb (indexed_scope scope shape length payload) body in
        let expected := specialize_indexed motive_name (BuildIndexed shape (IndexVar length) payload) motive in
        let k := specialize_indexed motive_name packed motive in
        if kind_eq_dec (value_kind result) expected then
          let? output := type_uses scope k in
          let w := subject_uses result in
          let s := tensor_grade w length payload in
          if allowsb (uses w length) s && allowsb (uses w payload) s
             && demand_eqb (result_type_uses result)
                           (substitute_demand motive_name (fields_used length payload) motive_row)
             && demand_eqb output (substitute_demand motive_name z motive_row)
          then Some (used k (without length (without payload w) ++ scale s z) output) else None
        else None
      else None
  | Apply callee argument =>
      let? fn := infer_with allowsb scope callee in
      let? arg := infer_with allowsb scope argument in
      match value_kind fn with
      | ArrowKind allowance domain codomain =>
          if kind_eq_dec (value_kind arg) domain then
            let? b := type_uses scope codomain in
            Some (used codomain (subject_uses fn ++ scale allowance (subject_uses arg)) b)
          else None
      | _ => None
      end
  | LetBoxValue name motive_name subject motive body =>
      if binder_checks scope name motive_name then
        let? subj := infer_with allowsb scope subject in
        match value_kind subj with
        | BoxNat q =>
            let? motive_row := type_uses ((motive_name, BoxNat q) :: scope) motive in
            if Nat.eqb (uses motive_row motive_name) 0 then
              let? result := infer_with allowsb ((name, NatKind) :: scope) body in
              if kind_eq_dec (value_kind result) motive then
                let? output := type_uses scope motive in
                if allowsb (uses (subject_uses result) name) q
                   && demand_eqb (result_type_uses result) motive_row
                   && demand_eqb output motive_row
                then Some (used motive (without name (subject_uses result) ++ subject_uses subj) output)
                else None
              else None
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

Lemma infer_with_sound : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall subject scope result,
    infer_with allowsb scope subject = Some result -> DerivesWith allows scope subject result.
Proof.
  intros allows allowsb admission_sound.
  induction subject as [name | i | payload | shape pair | name allowance domain body IH | left IHl right IHr
    | name motive_name payload motive body IH | shape length field motive_name pair motive body IH
    | callee IHc argument IHa | name motive_name subject IHs motive body IHb
    | q inner IH | b | cond IHc th IHt el IHe | right_k inner IH | left_k inner IH
    | ln rn scrut IHs lb IHl rb IHr | name allowance init body IH
    | name allowance domain body IH | callee IH arg];
    intros scope result checked; cbn in checked; try discriminate.
  - destruct (find_kind scope name) eqn:found; try discriminate.
    cbn in checked. destruct (type_uses scope k) eqn:typed; inversion checked; subst.
    constructor; auto using type_uses_sound.
  - destruct (index_demand (naturals scope) i) eqn:used_index; inversion checked; subst.
    constructor. now apply index_demand_sound.
  - destruct (infer_box scope payload) as [[[q d] contents] |] eqn:boxed_ok;
      inversion checked; subst. econstructor. eapply infer_box_sound; eassumption.
  - destruct (indexed_uses scope shape pair) as [row |] eqn:pair_ok; inversion checked; subst.
    constructor. now apply indexed_uses_sound.
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
  - destruct (indexed_binders scope shape length field motive_name) eqn:fresh; try discriminate.
    destruct (indexed_uses scope shape pair) as [z |] eqn:pair_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (type_uses ((motive_name, IndexedKind shape) :: scope) motive) as [motive_row |] eqn:motive_ok;
      try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_with allowsb (indexed_scope scope shape length field) body) as [[k w row] |] eqn:body_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec k (specialize_indexed motive_name (BuildIndexed shape (IndexVar length) field) motive))
      as [same_kind | different]; try discriminate.
    destruct (type_uses scope (specialize_indexed motive_name pair motive)) as [output |] eqn:out_ok;
      try discriminate.
    cbn [bind_option] in checked.
    set (s := tensor_grade w length field) in *.
    destruct (allowsb (uses w length) s && allowsb (uses w field) s
      && demand_eqb row (substitute_demand motive_name (fields_used length field) motive_row)
      && demand_eqb output (substitute_demand motive_name z motive_row)) eqn:agrees;
      inversion checked; subst.
    apply andb_true_iff in agrees as [agrees out_demand].
    apply andb_true_iff in agrees as [bounds body_demand].
    apply andb_true_iff in bounds as [length_bound field_bound].
    eapply LetIndexedRule; eauto using admission_sound, indexed_uses_sound, type_uses_sound, demand_eqb_sound.
  - destruct (infer_with allowsb scope callee) as [[fk w v] |] eqn:fn_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_with allowsb scope argument) as [[ak z a] |] eqn:arg_ok; try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct fk as [| | | | allowance domain codomain | | | |]; try discriminate.
    destruct (kind_eq_dec ak domain) as [same_domain | different]; try discriminate.
    destruct (type_uses scope codomain) as [b |] eqn:out_ok; inversion checked; subst.
    eapply ApplyRule; eauto using type_uses_sound.
  - destruct (binder_checks scope name motive_name) eqn:fresh; try discriminate.
    destruct (infer_with allowsb scope subject) as [[sk z subj_row] |] eqn:subj_ok; try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct sk as [| q [| | | | | | | |] | | | | | | |]; try discriminate.
    destruct (type_uses ((motive_name, BoxNat q) :: scope) motive) as [motive_row |] eqn:motive_ok;
      try discriminate.
    cbn [bind_option] in checked.
    destruct (Nat.eqb (uses motive_row motive_name) 0) eqn:motive_unused; try discriminate.
    destruct (infer_with allowsb ((name, NatKind) :: scope) body) as [[bk w row] |] eqn:body_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec bk motive) as [same_kind | different]; try discriminate.
    destruct (type_uses scope motive) as [output |] eqn:out_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (allowsb (uses w name) q && demand_eqb row motive_row && demand_eqb output motive_row)
      eqn:agrees; inversion checked; subst.
    unfold binder_checks in fresh.
    apply andb_true_iff in fresh as [fresh distinct].
    apply andb_true_iff in fresh as [fresh_name fresh_motive].
    apply negb_true_iff, Nat.eqb_neq in distinct.
    apply Nat.eqb_eq in motive_unused.
    apply andb_true_iff in agrees as [agrees out_demand].
    apply andb_true_iff in agrees as [bound body_demand].
    eapply LetBoxValueRule; eauto using admission_sound, type_uses_sound, demand_eqb_sound.
Qed.

Definition check_with (allowsb : nat -> nat -> bool) (scope : env) (subject : value) : option usage :=
  if well_formed scope then infer_with allowsb scope subject else None.

Theorem check_with_sound : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall scope subject result,
    check_with allowsb scope subject = Some result -> WellFormed scope /\ DerivesWith allows scope subject result.
Proof.
  intros allows allowsb admission_sound scope subject result checked. unfold check_with in checked.
  destruct (well_formed scope) eqn:valid; try discriminate.
  split; eauto using well_formed_sound, infer_with_sound.
Qed.

Inductive DerivesModal (allows : nat -> nat -> Prop) (exact_branches : bool) (scope : env) : value -> usage -> Prop :=
| ModalNameRule : forall name k row, find_kind scope name = Some k -> TypeUses scope k row ->
    DerivesModal allows exact_branches scope (Name name) (used k [(name, 1)] row)
| ModalNatRule : forall i d, IndexDemand (naturals scope) i d ->
    DerivesModal allows exact_branches scope (NaturalValue i) (used NatKind d [])
| ModalBoxRule : forall payload q d contents, BoxDerives scope payload q d contents ->
    DerivesModal allows exact_branches scope (BoxValue payload) (used (BoxNat q) d [])
| ModalIndexedRule : forall shape pair d, IndexedUses scope shape pair d ->
    DerivesModal allows exact_branches scope (IndexedValue shape pair) (used (IndexedKind shape) d [])
| ModalLambdaRule : forall name allowance domain body codomain a u v row,
    is_fresh scope name = true -> TypeUses scope domain a ->
    DerivesModal allows exact_branches ((name, domain) :: scope) body (used codomain u v) ->
    allows (uses u name) allowance -> TypeUses scope (ArrowKind allowance domain codomain) row ->
    DerivesModal allows exact_branches scope (Lambda name allowance domain body)
      (used (ArrowKind allowance domain codomain) (without name u) row)
| ModalPairRule : forall left right a b u v w z,
    DerivesModal allows exact_branches scope left (used a u v) ->
    DerivesModal allows exact_branches scope right (used b w z) ->
    DerivesModal allows exact_branches scope (Pair left right) (used (ProductKind a b) (u ++ w) (v ++ z))
| ModalLetBoxRule : forall name motive_name subject motive body q z contents w body_row motive_row output,
    is_fresh scope name = true -> is_fresh scope motive_name = true -> name <> motive_name ->
    BoxDerives scope subject q z contents ->
    TypeUses ((motive_name, BoxNat q) :: scope) motive motive_row ->
    DerivesModal allows exact_branches ((name, NatKind) :: scope) body
      (used (specialize motive_name (PromotedContents q (IndexVar name)) motive) w body_row) ->
    allows (uses w name) q ->
    same_demand body_row (substitute_demand motive_name (scale q [(name, 1)]) motive_row) ->
    TypeUses scope (specialize motive_name contents motive) output ->
    same_demand output (substitute_demand motive_name z motive_row) ->
    DerivesModal allows exact_branches scope (LetBox name motive_name subject motive body)
      (used (specialize motive_name contents motive) (without name w ++ z) output)
| ModalLetIndexedRule : forall shape length payload motive_name subject motive body z w body_row motive_row output s,
    indexed_binders scope shape length payload motive_name = true ->
    IndexedUses scope shape subject z ->
    TypeUses ((motive_name, IndexedKind shape) :: scope) motive motive_row ->
    DerivesModal allows exact_branches (indexed_scope scope shape length payload) body
      (used (specialize_indexed motive_name (BuildIndexed shape (IndexVar length) payload) motive) w body_row) ->
    allows (uses w length) s -> allows (uses w payload) s ->
    same_demand body_row (substitute_demand motive_name (fields_used length payload) motive_row) ->
    TypeUses scope (specialize_indexed motive_name subject motive) output ->
    same_demand output (substitute_demand motive_name z motive_row) ->
    DerivesModal allows exact_branches scope (LetIndexed shape length payload motive_name subject motive body)
      (used (specialize_indexed motive_name subject motive) (without length (without payload w) ++ scale s z) output)
| ModalApplyRule : forall callee argument allowance domain codomain w v z a b,
    DerivesModal allows exact_branches scope callee (used (ArrowKind allowance domain codomain) w v) ->
    DerivesModal allows exact_branches scope argument (used domain z a) ->
    TypeUses scope codomain b ->
    DerivesModal allows exact_branches scope (Apply callee argument)
      (used codomain (w ++ scale allowance z) b)
| ModalLetBoxValueRule : forall name motive_name subject motive body q payload_k z subj_row w body_row motive_row output,
    is_fresh scope name = true -> is_fresh scope motive_name = true -> name <> motive_name ->
    DerivesModal allows exact_branches scope subject (used (BoxKind q payload_k) z subj_row) ->
    TypeUses ((motive_name, BoxKind q payload_k) :: scope) motive motive_row ->
    uses motive_row motive_name = 0 ->
    DerivesModal allows exact_branches ((name, payload_k) :: scope) body (used motive w body_row) ->
    allows (uses w name) q ->
    same_demand body_row motive_row ->
    TypeUses scope motive output ->
    same_demand output motive_row ->
    DerivesModal allows exact_branches scope (LetBoxValue name motive_name subject motive body)
      (used motive (without name w ++ z) output)
| ModalPromoteRule : forall q inner k u v,
    DerivesModal allows exact_branches scope inner (used k u v) ->
    DerivesModal allows exact_branches scope (PromoteValue q inner) (used (BoxKind q k) (scale q u) v)
| ModalBoolRule : forall b,
    DerivesModal allows exact_branches scope (BoolLit b) (used BoolKind [] [])
| ModalIfRule : forall cond then_b else_b out_k u_cond v_cond u1 v1 u2 v2 u_branch v_branch,
    DerivesModal allows exact_branches scope cond (used BoolKind u_cond v_cond) ->
    DerivesModal allows exact_branches scope then_b (used out_k u1 v1) ->
    DerivesModal allows exact_branches scope else_b (used out_k u2 v2) ->
    BranchDemand exact_branches u1 u2 u_branch ->
    BranchDemand exact_branches v1 v2 v_branch ->
    DerivesModal allows exact_branches scope (IfValue cond then_b else_b)
      (used out_k (u_cond ++ u_branch) v_branch)
| ModalInlRule : forall right_k inner left_k u d r,
    DerivesModal allows exact_branches scope inner (used left_k u d) ->
    TypeUses scope right_k r ->
    DerivesModal allows exact_branches scope (InlValue right_k inner)
      (used (SumKind left_k right_k) u (d ++ r))
| ModalInrRule : forall left_k inner right_k l u d,
    TypeUses scope left_k l ->
    DerivesModal allows exact_branches scope inner (used right_k u d) ->
    DerivesModal allows exact_branches scope (InrValue left_k inner)
      (used (SumKind left_k right_k) u (l ++ d))
| ModalMatchSumRule : forall l_name r_name scrutinee l_body r_body left_k right_k out_k
    u_scrut v_scrut u1 v1 u2 v2 u_branch out_row s,
    is_fresh scope l_name = true -> is_fresh scope r_name = true ->
    DerivesModal allows exact_branches scope scrutinee (used (SumKind left_k right_k) u_scrut v_scrut) ->
    DerivesModal allows exact_branches ((l_name, left_k) :: scope) l_body (used out_k u1 v1) ->
    DerivesModal allows exact_branches ((r_name, right_k) :: scope) r_body (used out_k u2 v2) ->
    s = Nat.max 1 (Nat.max (uses u1 l_name) (uses u2 r_name)) ->
    allows (uses u1 l_name) s -> allows (uses u2 r_name) s ->
    BranchDemand exact_branches (without l_name u1) (without r_name u2) u_branch ->
    TypeUses scope out_k out_row ->
    same_demand v1 out_row -> same_demand v2 out_row ->
    DerivesModal allows exact_branches scope (MatchSum l_name r_name scrutinee l_body r_body)
      (used out_k (scale s u_scrut ++ u_branch) out_row)
| ModalLetNatRule : forall name allowance init body k z w body_row output,
    is_fresh scope name = true -> IndexDemand (naturals scope) init z ->
    DerivesModal allows exact_branches ((name, NatKind) :: scope) body (used k w body_row) ->
    allows (uses w name) allowance ->
    TypeUses scope (substitute_kind name init k) output ->
    same_demand (substitute_demand name z body_row) output ->
    DerivesModal allows exact_branches scope (LetNatValue name allowance init body)
      (used (substitute_kind name init k) (z ++ without name w) output)
| ModalDepLambdaRule : forall name allowance domain body codomain a u v row,
    is_fresh scope name = true -> TypeUses scope domain a ->
    DerivesModal allows exact_branches ((name, domain) :: scope) body (used codomain u v) ->
    allows (uses u name) allowance ->
    TypeUses scope (PiKind name allowance domain codomain) row ->
    DerivesModal allows exact_branches scope (DepLambda name allowance domain body)
      (used (PiKind name allowance domain codomain) (without name u) row)
| ModalApplyNatRule : forall callee arg_index x allowance codomain w v z b output,
    DerivesModal allows exact_branches scope callee (used (PiKind x allowance NatKind codomain) w v) ->
    IndexDemand (naturals scope) arg_index z ->
    TypeUses ((x, NatKind) :: scope) codomain b ->
    TypeUses scope (substitute_kind x arg_index codomain) output ->
    same_demand (substitute_demand x z b) output ->
    DerivesModal allows exact_branches scope (ApplyNatValue callee arg_index)
      (used (substitute_kind x arg_index codomain) (w ++ scale allowance z) output).

Fixpoint infer_modal (allowsb : nat -> nat -> bool) (exact_branches : bool)
    (scope : env) (subject : value) : option usage :=
  match subject with
  | Name name =>
      let? k := find_kind scope name in
      let? row := type_uses scope k in Some (used k [(name, 1)] row)
  | NaturalValue i => option_map (fun d => used NatKind d []) (index_demand (naturals scope) i)
  | BoxValue payload =>
      let? data := infer_box scope payload in
      let '(q, d, _) := data in Some (used (BoxNat q) d [])
  | IndexedValue shape packed =>
      option_map (fun d => used (IndexedKind shape) d []) (indexed_uses scope shape packed)
  | Lambda name allowance domain body =>
      if is_fresh scope name then
        let? _ := type_uses scope domain in
        let? result := infer_modal allowsb exact_branches ((name, domain) :: scope) body in
        let k := ArrowKind allowance domain (value_kind result) in
        if allowsb (uses (subject_uses result) name) allowance then
          let? row := type_uses scope k in Some (used k (without name (subject_uses result)) row)
        else None
      else None
  | Pair first second =>
      let? a := infer_modal allowsb exact_branches scope first in
      let? b := infer_modal allowsb exact_branches scope second in
      Some (used (ProductKind (value_kind a) (value_kind b))
        (subject_uses a ++ subject_uses b) (result_type_uses a ++ result_type_uses b))
  | LetBox name motive_name payload motive body =>
      if binder_checks scope name motive_name then
        let? data := infer_box scope payload in
        let '(q, z, contents) := data in
        let? motive_row := type_uses ((motive_name, BoxNat q) :: scope) motive in
        let? result := infer_modal allowsb exact_branches ((name, NatKind) :: scope) body in
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
  | LetIndexed shape length payload motive_name packed motive body =>
      if indexed_binders scope shape length payload motive_name then
        let? z := indexed_uses scope shape packed in
        let? motive_row := type_uses ((motive_name, IndexedKind shape) :: scope) motive in
        let? result := infer_modal allowsb exact_branches (indexed_scope scope shape length payload) body in
        let expected := specialize_indexed motive_name (BuildIndexed shape (IndexVar length) payload) motive in
        let k := specialize_indexed motive_name packed motive in
        if kind_eq_dec (value_kind result) expected then
          let? output := type_uses scope k in
          let w := subject_uses result in
          let s := tensor_grade w length payload in
          if allowsb (uses w length) s && allowsb (uses w payload) s
             && demand_eqb (result_type_uses result)
                           (substitute_demand motive_name (fields_used length payload) motive_row)
             && demand_eqb output (substitute_demand motive_name z motive_row)
          then Some (used k (without length (without payload w) ++ scale s z) output) else None
        else None
      else None
  | Apply callee argument =>
      let? fn := infer_modal allowsb exact_branches scope callee in
      let? arg := infer_modal allowsb exact_branches scope argument in
      match value_kind fn with
      | ArrowKind allowance domain codomain =>
          if kind_eq_dec (value_kind arg) domain then
            let? b := type_uses scope codomain in
            Some (used codomain (subject_uses fn ++ scale allowance (subject_uses arg)) b)
          else None
      | _ => None
      end
  | LetBoxValue name motive_name subject motive body =>
      if binder_checks scope name motive_name then
        let? subj := infer_modal allowsb exact_branches scope subject in
        match value_kind subj with
        | BoxKind q payload_k =>
            let? motive_row := type_uses ((motive_name, BoxKind q payload_k) :: scope) motive in
            if Nat.eqb (uses motive_row motive_name) 0 then
              let? result := infer_modal allowsb exact_branches ((name, payload_k) :: scope) body in
              if kind_eq_dec (value_kind result) motive then
                let? output := type_uses scope motive in
                if allowsb (uses (subject_uses result) name) q
                   && demand_eqb (result_type_uses result) motive_row
                   && demand_eqb output motive_row
                then Some (used motive (without name (subject_uses result) ++ subject_uses subj) output)
                else None
              else None
            else None
        | _ => None
        end
      else None
  | PromoteValue q inner =>
      let? res := infer_modal allowsb exact_branches scope inner in
      Some (used (BoxKind q (value_kind res)) (scale q (subject_uses res)) (result_type_uses res))
  | BoolLit _ => Some (used BoolKind [] [])
  | IfValue cond then_b else_b =>
      let? c := infer_modal allowsb exact_branches scope cond in
      match value_kind c with
      | BoolKind =>
          let? t := infer_modal allowsb exact_branches scope then_b in
          let? e := infer_modal allowsb exact_branches scope else_b in
          if kind_eq_dec (value_kind t) (value_kind e) then
            let? u_branch := branch_demand exact_branches (subject_uses t) (subject_uses e) in
            let? v_branch := branch_demand exact_branches (result_type_uses t) (result_type_uses e) in
            Some (used (value_kind t) (subject_uses c ++ u_branch) v_branch)
          else None
      | _ => None
      end
  | InlValue right_k inner =>
      let? res := infer_modal allowsb exact_branches scope inner in
      let? r := type_uses scope right_k in
      Some (used (SumKind (value_kind res) right_k) (subject_uses res) (result_type_uses res ++ r))
  | InrValue left_k inner =>
      let? l := type_uses scope left_k in
      let? res := infer_modal allowsb exact_branches scope inner in
      Some (used (SumKind left_k (value_kind res)) (subject_uses res) (l ++ result_type_uses res))
  | MatchSum l_name r_name scrutinee l_body r_body =>
      if is_fresh scope l_name && is_fresh scope r_name then
        let? scrut := infer_modal allowsb exact_branches scope scrutinee in
        match value_kind scrut with
        | SumKind left_k right_k =>
            let? l_res := infer_modal allowsb exact_branches ((l_name, left_k) :: scope) l_body in
            let? r_res := infer_modal allowsb exact_branches ((r_name, right_k) :: scope) r_body in
            if kind_eq_dec (value_kind l_res) (value_kind r_res) then
              let? out_row := type_uses scope (value_kind l_res) in
              let s := Nat.max 1 (Nat.max (uses (subject_uses l_res) l_name)
                                          (uses (subject_uses r_res) r_name)) in
              if allowsb (uses (subject_uses l_res) l_name) s
                 && allowsb (uses (subject_uses r_res) r_name) s
                 && demand_eqb (result_type_uses l_res) out_row
                 && demand_eqb (result_type_uses r_res) out_row then
                let? u_branch := branch_demand exact_branches
                                   (without l_name (subject_uses l_res))
                                   (without r_name (subject_uses r_res)) in
                Some (used (value_kind l_res) (scale s (subject_uses scrut) ++ u_branch) out_row)
              else None
            else None
        | _ => None
        end
      else None
  | LetNatValue name allowance init body =>
      if is_fresh scope name then
        let? z := index_demand (naturals scope) init in
        let? res := infer_modal allowsb exact_branches ((name, NatKind) :: scope) body in
        let specialized := substitute_kind name init (value_kind res) in
        let? output := type_uses scope specialized in
        if allowsb (uses (subject_uses res) name) allowance
           && demand_eqb (substitute_demand name z (result_type_uses res)) output then
          Some (used specialized (z ++ without name (subject_uses res)) output)
        else None
      else None
  | DepLambda name allowance domain body =>
      if is_fresh scope name then
        let? _ := type_uses scope domain in
        let? result := infer_modal allowsb exact_branches ((name, domain) :: scope) body in
        let k := PiKind name allowance domain (value_kind result) in
        if allowsb (uses (subject_uses result) name) allowance then
          let? row := type_uses scope k in Some (used k (without name (subject_uses result)) row)
        else None
      else None
  | ApplyNatValue callee arg_index =>
      let? fn := infer_modal allowsb exact_branches scope callee in
      match value_kind fn with
      | PiKind x allowance NatKind codomain =>
          let? z := index_demand (naturals scope) arg_index in
          let? b := type_uses ((x, NatKind) :: scope) codomain in
          let specialized := substitute_kind x arg_index codomain in
          let? output := type_uses scope specialized in
          if demand_eqb (substitute_demand x z b) output then
            Some (used specialized (subject_uses fn ++ scale allowance z) output)
          else None
      | _ => None
      end
  end.

Lemma infer_modal_sound : forall (allows : nat -> nat -> Prop) allowsb exact_branches,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall subject scope result,
    infer_modal allowsb exact_branches scope subject = Some result ->
    DerivesModal allows exact_branches scope subject result.
Proof.
  intros allows allowsb exact_branches admission_sound.
  induction subject as [name | i | payload | shape pair | name allowance domain body IH | left IHl right IHr
    | name motive_name payload motive body IH | shape length field motive_name pair motive body IH
    | callee IHc argument IHa | name motive_name subject IHs motive body IHb
    | q inner IH | b | cond IHc th IHt el IHe | right_k inner IH | left_k inner IH
    | ln rn scrut IHs lb IHl rb IHr | name allowance init body IH
    | name allowance domain body IH | callee IH arg];
    intros scope result checked; cbn in checked.
  - destruct (find_kind scope name) eqn:found; try discriminate.
    cbn in checked. destruct (type_uses scope k) eqn:typed; inversion checked; subst.
    constructor; auto using type_uses_sound.
  - destruct (index_demand (naturals scope) i) eqn:used_index; inversion checked; subst.
    constructor. now apply index_demand_sound.
  - destruct (infer_box scope payload) as [[[q d] contents] |] eqn:boxed_ok;
      inversion checked; subst. econstructor. eapply infer_box_sound; eassumption.
  - destruct (indexed_uses scope shape pair) as [row |] eqn:pair_ok; inversion checked; subst.
    constructor. now apply indexed_uses_sound.
  - destruct (is_fresh scope name) eqn:fresh; try discriminate.
    destruct (type_uses scope domain) eqn:typed; try discriminate.
    cbn in checked. destruct (infer_modal allowsb exact_branches ((name, domain) :: scope) body) as [[k u v] |] eqn:body_ok;
      try discriminate.
    cbn in checked. destruct (allowsb (uses u name) allowance) eqn:bound; try discriminate.
    destruct (type_uses scope k) eqn:formed; inversion checked; subst.
    eapply ModalLambdaRule; eauto using admission_sound, type_uses_sound, ArrowUses.
  - destruct (infer_modal allowsb exact_branches scope left) as [[a u v] |] eqn:left_ok; try discriminate.
    cbn in checked. destruct (infer_modal allowsb exact_branches scope right) as [[b w z] |] eqn:right_ok;
      inversion checked; subst. constructor; auto.
  - destruct (binder_checks scope name motive_name) eqn:fresh; try discriminate.
    destruct (infer_box scope payload) as [[[q z] contents] |] eqn:boxed_ok; try discriminate.
    cbn [bind_option] in checked. destruct (type_uses ((motive_name, BoxNat q) :: scope) motive)
      as [motive_row |] eqn:motive_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches ((name, NatKind) :: scope) body) as [[k w row] |] eqn:body_ok;
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
    eapply ModalLetBoxRule; eauto using admission_sound, infer_box_sound, type_uses_sound, demand_eqb_sound.
  - destruct (indexed_binders scope shape length field motive_name) eqn:fresh; try discriminate.
    destruct (indexed_uses scope shape pair) as [z |] eqn:pair_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (type_uses ((motive_name, IndexedKind shape) :: scope) motive) as [motive_row |] eqn:motive_ok;
      try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches (indexed_scope scope shape length field) body) as [[k w row] |] eqn:body_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec k (specialize_indexed motive_name (BuildIndexed shape (IndexVar length) field) motive))
      as [same_kind | different]; try discriminate.
    destruct (type_uses scope (specialize_indexed motive_name pair motive)) as [output |] eqn:out_ok;
      try discriminate.
    cbn [bind_option] in checked.
    set (s := tensor_grade w length field) in *.
    destruct (allowsb (uses w length) s && allowsb (uses w field) s
      && demand_eqb row (substitute_demand motive_name (fields_used length field) motive_row)
      && demand_eqb output (substitute_demand motive_name z motive_row)) eqn:agrees;
      inversion checked; subst.
    apply andb_true_iff in agrees as [agrees out_demand].
    apply andb_true_iff in agrees as [bounds body_demand].
    apply andb_true_iff in bounds as [length_bound field_bound].
    eapply ModalLetIndexedRule; eauto using admission_sound, indexed_uses_sound, type_uses_sound, demand_eqb_sound.
  - destruct (infer_modal allowsb exact_branches scope callee) as [[fk w v] |] eqn:fn_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches scope argument) as [[ak z a] |] eqn:arg_ok; try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct fk as [| | | | allowance domain codomain | | | |]; try discriminate.
    destruct (kind_eq_dec ak domain) as [same_domain | different]; try discriminate.
    destruct (type_uses scope codomain) as [b |] eqn:out_ok; inversion checked; subst.
    eapply ModalApplyRule; eauto using type_uses_sound.
  - destruct (binder_checks scope name motive_name) eqn:fresh; try discriminate.
    destruct (infer_modal allowsb exact_branches scope subject) as [[sk z subj_row] |] eqn:subj_ok; try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct sk as [| q payload_k | | | | | | |]; try discriminate.
    destruct (type_uses ((motive_name, BoxKind q payload_k) :: scope) motive) as [motive_row |] eqn:motive_ok;
      try discriminate.
    cbn [bind_option] in checked.
    destruct (Nat.eqb (uses motive_row motive_name) 0) eqn:motive_unused; try discriminate.
    destruct (infer_modal allowsb exact_branches ((name, payload_k) :: scope) body) as [[bk w row] |] eqn:body_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec bk motive) as [same_kind | different]; try discriminate.
    destruct (type_uses scope motive) as [output |] eqn:out_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (allowsb (uses w name) q && demand_eqb row motive_row && demand_eqb output motive_row)
      eqn:agrees; inversion checked; subst.
    unfold binder_checks in fresh.
    apply andb_true_iff in fresh as [fresh distinct].
    apply andb_true_iff in fresh as [fresh_name fresh_motive].
    apply negb_true_iff, Nat.eqb_neq in distinct.
    apply Nat.eqb_eq in motive_unused.
    apply andb_true_iff in agrees as [agrees out_demand].
    apply andb_true_iff in agrees as [bound body_demand].
    eapply ModalLetBoxValueRule; eauto using admission_sound, type_uses_sound, demand_eqb_sound.
  - destruct (infer_modal allowsb exact_branches scope inner) as [[k u v] |] eqn:inner_ok;
      inversion checked; subst.
    eapply ModalPromoteRule; eauto.
  - inversion checked; subst. constructor.
  - destruct (infer_modal allowsb exact_branches scope cond) as [[ck u_cond v_cond] |] eqn:cond_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct ck; try discriminate.
    destruct (infer_modal allowsb exact_branches scope th) as [[tk u1 v1] |] eqn:th_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches scope el) as [[ek u2 v2] |] eqn:el_ok; try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec tk ek) as [-> | different]; try discriminate.
    destruct (branch_demand exact_branches u1 u2) as [u_branch |] eqn:ub_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (branch_demand exact_branches v1 v2) as [v_branch |] eqn:vb_ok;
      inversion checked; subst.
    eapply ModalIfRule; eauto using branch_demand_sound.
  - destruct (infer_modal allowsb exact_branches scope inner) as [[lk u d] |] eqn:inner_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (type_uses scope right_k) as [r |] eqn:right_ok; inversion checked; subst.
    eapply ModalInlRule; eauto using type_uses_sound.
  - destruct (type_uses scope left_k) as [l |] eqn:left_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches scope inner) as [[rk u d] |] eqn:inner_ok;
      inversion checked; subst.
    eapply ModalInrRule; eauto using type_uses_sound.
  - destruct (is_fresh scope ln && is_fresh scope rn) eqn:fresh; try discriminate.
    apply andb_true_iff in fresh as [fresh_ln fresh_rn].
    destruct (infer_modal allowsb exact_branches scope scrut) as [[sk u_scrut v_scrut] |] eqn:scrut_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct sk as [| | | | | | | left_k right_k |]; try discriminate.
    destruct (infer_modal allowsb exact_branches ((ln, left_k) :: scope) lb) as [[lk u1 v1] |] eqn:lb_ok;
      try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches ((rn, right_k) :: scope) rb) as [[rk u2 v2] |] eqn:rb_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (kind_eq_dec lk rk) as [-> | different]; try discriminate.
    destruct (type_uses scope rk) as [out_row |] eqn:out_ok; try discriminate.
    cbn [bind_option] in checked.
    set (s := Nat.max 1 (Nat.max (uses u1 ln) (uses u2 rn))).
    change (match Nat.max (uses u1 ln) (uses u2 rn) with 0 => 1 | S m' => S m' end) with s in checked.
    destruct (allowsb (uses u1 ln) s && allowsb (uses u2 rn) s
      && demand_eqb v1 out_row && demand_eqb v2 out_row) eqn:agrees; try discriminate.
    cbn [bind_option] in checked.
    destruct (branch_demand exact_branches (without ln u1) (without rn u2)) as [u_branch |] eqn:ub_ok;
      inversion checked; subst.
    apply andb_true_iff in agrees as [agrees v2_eq].
    apply andb_true_iff in agrees as [agrees v1_eq].
    apply andb_true_iff in agrees as [l_bound r_bound].
    eapply ModalMatchSumRule;
      eauto using admission_sound, type_uses_sound, demand_eqb_sound, branch_demand_sound.
  - destruct (is_fresh scope name) eqn:fresh; try discriminate.
    destruct (index_demand (naturals scope) init) as [z |] eqn:init_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (infer_modal allowsb exact_branches ((name, NatKind) :: scope) body) as [[k w row] |] eqn:body_ok;
      try discriminate.
    cbn [bind_option value_kind subject_uses result_type_uses] in checked.
    destruct (type_uses scope (substitute_kind name init k)) as [output |] eqn:out_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (allowsb (uses w name) allowance && demand_eqb (substitute_demand name z row) output)
      eqn:agrees; inversion checked; subst.
    apply andb_true_iff in agrees as [bound same_out].
    eapply ModalLetNatRule; eauto using admission_sound, index_demand_sound, type_uses_sound, demand_eqb_sound.
  - destruct (is_fresh scope name) eqn:fresh; try discriminate.
    destruct (type_uses scope domain) eqn:typed; try discriminate.
    cbn in checked.
    destruct (infer_modal allowsb exact_branches ((name, domain) :: scope) body) as [[k u v] |] eqn:body_ok;
      try discriminate.
    cbn in checked. destruct (allowsb (uses u name) allowance) eqn:bound; try discriminate.
    destruct (type_uses ((name, domain) :: scope) k) as [b |] eqn:formed; try discriminate.
    cbn in checked. inversion checked; subst.
    eapply ModalDepLambdaRule; eauto using admission_sound, type_uses_sound, PiUses.
  - destruct (infer_modal allowsb exact_branches scope callee) as [[fk w v] |] eqn:fn_ok; try discriminate.
    cbn [bind_option value_kind subject_uses] in checked.
    destruct fk as [| | | | | | | | x allowance domain codomain]; try discriminate.
    destruct domain; try discriminate.
    destruct (index_demand (naturals scope) arg) as [z |] eqn:arg_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (type_uses ((x, NatKind) :: scope) codomain) as [b |] eqn:b_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (type_uses scope (substitute_kind x arg codomain)) as [output |] eqn:out_ok; try discriminate.
    cbn [bind_option] in checked.
    destruct (demand_eqb (substitute_demand x z b) output) eqn:agrees; inversion checked; subst.
    eapply ModalApplyNatRule; eauto using index_demand_sound, type_uses_sound, demand_eqb_sound.
Qed.

Definition presence_allows (actual allowance : nat) : Prop :=
  actual > 0 -> allowance > 0.

Definition presence_allowsb (actual allowance : nat) : bool :=
  implb (negb (Nat.eqb actual 0)) (negb (Nat.eqb allowance 0)).

Lemma presence_allowsb_sound : forall actual allowance,
  presence_allowsb actual allowance = true -> presence_allows actual allowance.
Proof.
  intros [| a] [| b] checked pos; cbn in checked; try discriminate;
    try inversion pos; apply Nat.lt_0_succ.
Qed.

Definition check_modal (allowsb : nat -> nat -> bool) (exact_branches : bool)
    (scope : env) (subject : value) : option usage :=
  if well_formed scope then infer_modal allowsb exact_branches scope subject else None.

Definition check := check_modal (@GradedDomains.allowsb GradedDomains.NatExact) true.
Definition bounded_check := check_modal (@GradedDomains.allowsb GradedDomains.NatBound) false.
Definition presence_check := check_modal presence_allowsb false.

Theorem check_modal_sound : forall (allows : nat -> nat -> Prop) allowsb exact_branches,
  (forall actual allowance, allowsb actual allowance = true -> allows actual allowance) ->
  forall scope subject result,
    check_modal allowsb exact_branches scope subject = Some result ->
    WellFormed scope /\ DerivesModal allows exact_branches scope subject result.
Proof.
  intros allows allowsb exact_branches admission_sound scope subject result checked.
  unfold check_modal in checked.
  destruct (well_formed scope) eqn:valid; try discriminate.
  split; eauto using well_formed_sound, infer_modal_sound.
Qed.

Theorem check_sound : forall scope subject result,
  check scope subject = Some result ->
  WellFormed scope /\ DerivesModal (@GradedDomains.allows GradedDomains.NatExact) true scope subject result.
Proof.
  unfold check. apply check_modal_sound. intros. now apply Nat.eqb_eq.
Qed.

Theorem bounded_check_sound : forall scope subject result,
  bounded_check scope subject = Some result ->
  WellFormed scope /\ DerivesModal (@GradedDomains.allows GradedDomains.NatBound) false scope subject result.
Proof.
  unfold bounded_check. apply check_modal_sound. intros. now apply Nat.leb_le.
Qed.

Theorem presence_check_sound : forall scope subject result,
  presence_check scope subject = Some result ->
  WellFormed scope /\ DerivesModal presence_allows false scope subject result.
Proof.
  unfold presence_check. apply check_modal_sound. exact presence_allowsb_sound.
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
  intros scope k row name typed. revert name.
  induction typed; intros name absent.
  - reflexivity.
  - now apply IHtyped.
  - reflexivity.
  - destruct H as [i d natural | key q found | q i d natural | shape pair d pair_typed].
    + eapply zero_natural_use; eauto.
    + cbn. destruct (name =? key) eqn:equal; [| reflexivity].
      apply Nat.eqb_eq in equal. subst key. congruence.
    + rewrite uses_scale. rewrite (zero_natural_use _ i d name natural absent).
      now rewrite Nat.mul_0_r.
    + destruct pair_typed as [key found | length payload d length_ok payload_ok].
      * cbn. destruct (name =? key) eqn:equal; [| reflexivity].
        apply Nat.eqb_eq in equal. subst key. congruence.
      * rewrite uses_append, (zero_natural_use _ length d name length_ok absent).
        cbn. destruct (name =? payload) eqn:equal; [| reflexivity].
        apply Nat.eqb_eq in equal. subst payload. congruence.
  - now rewrite uses_append, IHtyped1, IHtyped2.
  - now rewrite uses_append, IHtyped1, IHtyped2.
  - reflexivity.
  - now rewrite uses_append, IHtyped1, IHtyped2.
  - rewrite uses_append, uses_without, (IHtyped1 _ absent).
    destruct (Nat.eqb name x) eqn:equal; [reflexivity |].
    apply IHtyped2. unfold find_kind. cbn. rewrite equal. exact absent.
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
  inversion derivation as [| | | | | | x p b m t q z contents w body_row motive_row output
    fresh_name fresh_motive distinct boxed_ok motive_ok body_ok bound body_demand out_kind out_demand | | |];
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

Lemma indexed_scope_well_formed : forall scope shape length payload motive_name,
  WellFormed scope -> indexed_binders scope shape length payload motive_name = true ->
  WellFormed (indexed_scope scope shape length payload).
Proof.
  intros scope shape length payload motive_name outer checked.
  unfold indexed_binders in checked.
  apply andb_true_iff in checked as [fresh _].
  apply andb_true_iff in fresh as [fresh_length fresh_payload].
  unfold indexed_scope.
  assert (typed : IndexDemand (naturals ((length, NatKind) :: scope)) (IndexVar length) [(length, 1)]).
  { eapply NaturalVariable with (entry := natural_binding length).
    - cbn. now rewrite Nat.eqb_refl.
    - reflexivity. }
  destruct (instantiate_extent_typed _ (payload_extent shape) _ _ typed) as [row extent_typed].
  eapply ExtendScope with (d := row).
  - eapply ExtendScope with (d := []); eauto using NatUses.
  - exact fresh_payload.
  - now do 2 constructor.
Qed.

Theorem checked_let_indexed_demands_with : forall (allows : nat -> nat -> Prop) allowsb,
  (forall actual advertised, allowsb actual advertised = true -> allows actual advertised) ->
  forall scope shape length payload motive_name subject motive body result,
  check_with allowsb scope (LetIndexed shape length payload motive_name subject motive body) = Some result ->
  WellFormed (indexed_scope scope shape length payload) /\
  exists z w body_row motive_row s,
    IndexedUses scope shape subject z /\
    TypeUses ((motive_name, IndexedKind shape) :: scope) motive motive_row /\
    DerivesWith allows (indexed_scope scope shape length payload) body
      (used (specialize_indexed motive_name (BuildIndexed shape (IndexVar length) payload) motive) w body_row) /\
    allows (uses w length) s /\ allows (uses w payload) s /\
    same_demand body_row (substitute_demand motive_name (fields_used length payload) motive_row) /\
    value_kind result = specialize_indexed motive_name subject motive /\
    (forall x, uses (subject_uses result) x =
      (if (x =? length) || (x =? payload) then 0 else uses w x) + s * uses z x) /\
    same_demand (result_type_uses result) (substitute_demand motive_name z motive_row).
Proof.
  intros allows allowsb admission_sound scope shape length payload motive_name subject motive body result checked.
  pose proof (check_with_sound allows allowsb admission_sound _ _ _ checked) as [outer derivation].
  inversion derivation as [| | | | | | | indicated_shape l p n t m b z w body_row motive_row output s
    fresh pair_ok motive_ok body_ok length_ok payload_ok body_demand out_kind out_demand | |]; subst.
  split; [eauto using indexed_scope_well_formed |].
  exists z, w, body_row, motive_row, s. repeat apply conj; try assumption; try reflexivity.
  intro x. cbn [subject_uses used]. rewrite uses_append, !uses_without, uses_scale.
  now destruct (x =? length), (x =? payload).
Qed.

Definition checked_let_indexed_demands := checked_let_indexed_demands_with
  (@GradedDomains.allows GradedDomains.NatExact)
  (@GradedDomains.allowsb GradedDomains.NatExact)
  (fun actual allowance => proj1 (Nat.eqb_eq actual allowance)).

Definition bounded_checked_let_indexed_demands := checked_let_indexed_demands_with
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

Example box_interface_application :
  check [(0, NatKind)]
    (Apply (Lambda 1 1 (BoxNat 2) (LetBox 2 3 (BoxName 1) NatKind (NaturalValue (IndexAdd (IndexVar 2) (IndexVar 2)))))
      (BoxValue (promoted_twice 0))) =
    Some (used NatKind [(0, 2); (0, 2)] []).
Proof. reflexivity. Qed.

Example reject_mismatched_box_grade_application :
  check [(0, NatKind)]
    (Apply (Lambda 1 1 (BoxNat 2) (LetBox 2 3 (BoxName 1) NatKind (NaturalValue (IndexAdd (IndexVar 2) (IndexVar 2)))))
      (BoxValue (PromoteNat 1 (IndexVar 0)))) = None.
Proof. reflexivity. Qed.

Example promote_and_open_nested_box :
  check [(0, NatKind)]
    (LetBoxValue 1 2 (PromoteValue 1 (BoxValue (PromoteNat 2 (IndexVar 0)))) NatKind
      (LetBox 3 4 (BoxName 1) NatKind (NaturalValue (IndexAdd (IndexVar 3) (IndexVar 3))))) =
    Some (used NatKind [(0, 2)] []).
Proof. reflexivity. Qed.

Example promote_and_open_vector_box :
  check [(1, VecKind (PlainIndex (IndexVar 0))); (0, NatKind)]
    (LetBoxValue 2 3 (PromoteValue 2 (Name 1))
      (ProductKind (VecKind (PlainIndex (IndexVar 0))) (VecKind (PlainIndex (IndexVar 0))))
      (Pair (Name 2) (Name 2))) =
    Some (used (ProductKind (VecKind (PlainIndex (IndexVar 0))) (VecKind (PlainIndex (IndexVar 0))))
      [(1, 2)] [(0, 1); (0, 1)]).
Proof. reflexivity. Qed.

Example exact_if_requires_matching_branches :
  check [(1, NatKind); (0, BoolKind)]
    (IfValue (Name 0) (NaturalValue (IndexVar 1)) (NaturalValue (IndexVar 1))) =
    Some (used NatKind [(0, 1); (1, 1)] []) /\
  check [(2, NatKind); (1, NatKind); (0, BoolKind)]
    (IfValue (Name 0) (NaturalValue (IndexVar 1)) (NaturalValue (IndexVar 2))) = None.
Proof. split; reflexivity. Qed.

Example bounded_if_joins_branches_with_max :
  bounded_check [(2, NatKind); (1, NatKind); (0, BoolKind)]
    (IfValue (Name 0)
      (NaturalValue (IndexAdd (IndexVar 1) (IndexVar 1)))
      (NaturalValue (IndexAdd (IndexVar 1) (IndexVar 2)))) =
    Some (used NatKind [(0, 1); (1, 2); (2, 1)] []).
Proof. reflexivity. Qed.

Example match_sum_exact_and_bounded :
  check [(0, SumKind NatKind BoolKind)]
    (MatchSum 1 2 (Name 0) (NaturalValue (IndexVar 1))
      (IfValue (Name 2) (NaturalValue (IndexLit 1)) (NaturalValue (IndexLit 0)))) =
    Some (used NatKind [(0, 1)] []) /\
  check [(0, SumKind NatKind BoolKind)]
    (MatchSum 1 2 (Name 0) (NaturalValue (IndexLit 1)) (NaturalValue (IndexLit 0))) = None /\
  bounded_check [(0, SumKind NatKind BoolKind)]
    (MatchSum 1 2 (Name 0) (NaturalValue (IndexLit 1)) (NaturalValue (IndexLit 0))) =
    Some (used NatKind [(0, 1)] []).
Proof. repeat split; reflexivity. Qed.

Example let_nat_value_substitutes_index :
  check [(1, VecKind (PlainIndex (IndexAdd (IndexVar 0) (IndexVar 0)))); (0, NatKind)]
    (LetNatValue 2 0 (IndexAdd (IndexVar 0) (IndexVar 0))
      (Lambda 3 1 (VecKind (PlainIndex (IndexVar 2))) (Name 3))) =
    Some (used (ArrowKind 1 (VecKind (PlainIndex (IndexAdd (IndexVar 0) (IndexVar 0))))
                           (VecKind (PlainIndex (IndexAdd (IndexVar 0) (IndexVar 0)))))
      [(0, 1); (0, 1)] [(0, 1); (0, 1); (0, 1); (0, 1)]).
Proof. reflexivity. Qed.

Example presence_domain_checks_and_rejects :
  presence_check [(1, NatKind); (0, BoolKind)]
    (IfValue (Name 0) (NaturalValue (IndexAdd (IndexVar 1) (IndexVar 1))) (NaturalValue (IndexLit 0))) =
    Some (used NatKind [(0, 1); (1, 2)] []) /\
  presence_allowsb 2 1 = true /\
  presence_allowsb 1 0 = false.
Proof. repeat split; reflexivity. Qed.

End GradedModal.
