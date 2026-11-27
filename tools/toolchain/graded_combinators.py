# SPDX-License-Identifier: Apache-2.0
"""Derived distributive modality combinators over graded structures (Q25bz).

Inspects declared ``Pair``/``record``, ``Sum``/``union``, and ``Box`` structures
together with grade domain rules (contraction/``Dup``, weakening, and semiring
distributivity), enforces resource/authority boundaries, and emits inspectable
HoldFast source alongside replayable Rocq proofs audited for zero axioms.
"""

import hashlib
import re
import subprocess
import tempfile
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from toolchain import graded_inference as gi
from toolchain import graded_source, proofenv, solver_ledger

_ROCQ_SUPPORT = ("graded_pure.v", "graded_domains.v", "graded_semiring.v")


@dataclass(frozen=True)
class BaseType:
    """Leaf or named resource type with explicit structural authority flags."""

    name: str
    duplicable: bool = True
    disposable: bool = True
    owned: bool = False


NAT_TYPE = BaseType("Nat")
BOOL_TYPE = BaseType("bool")
UNIT_TYPE = BaseType("Unit")


@dataclass(frozen=True)
class PairType:
    """Product / two-field record structure."""

    left: CombinatorType
    right: CombinatorType
    record_name: str = "Pair"


@dataclass(frozen=True)
class SumType:
    """Binary sum / two-constructor union structure."""

    left: CombinatorType
    right: CombinatorType
    union_name: str = "Either"
    left_ctor: str = "Left"
    right_ctor: str = "Right"


@dataclass(frozen=True)
class BoxType:
    """Graded comonadic box ``Box<payload, grade>``."""

    payload: CombinatorType
    grade: gi.GradeExpr
    record_name: str = "Box"


@dataclass(frozen=True)
class ArrowType:
    """Graded function type ``Fn(domain @ allowance) -> codomain``."""

    allowance: gi.GradeExpr
    domain: CombinatorType
    codomain: CombinatorType


type CombinatorType = BaseType | PairType | SumType | BoxType | ArrowType


@dataclass(frozen=True)
class RecordDecl:
    """Inspected HoldFast record declaration."""

    name: str
    generics: tuple[str, ...]
    fields: tuple[tuple[str, str, str | None], ...]


@dataclass(frozen=True)
class UnionDecl:
    """Inspected HoldFast union declaration."""

    name: str
    generics: tuple[str, ...]
    variants: tuple[tuple[str, str, str], ...]


@dataclass(frozen=True)
class StructureSpec:
    """Inspected structure environment extracted from HoldFast declarations."""

    records: Mapping[str, RecordDecl]
    unions: Mapping[str, UnionDecl]
    box_domain: gi.InferenceDomain | None = None


@dataclass(frozen=True)
class DomainCombinatorRules:
    """Grade domain structural capabilities governing combinator derivation."""

    domain: gi.InferenceDomain
    admits_contraction: bool
    admits_weakening: bool
    admits_pairing: bool
    exact_equality: bool


def default_domain_rules(
    domain: str | gi.InferenceDomain | graded_source.GradeDomain,
    *,
    admits_pairing: bool | None = None,
) -> DomainCombinatorRules:
    """Return the canonical structural rules for ``domain``."""
    resolved = gi.coerce_domain(domain)
    if resolved == gi.InferenceDomain.NAT_EXACT:
        return DomainCombinatorRules(
            domain=resolved,
            admits_contraction=True,
            admits_weakening=False,
            admits_pairing=True if admits_pairing is None else admits_pairing,
            exact_equality=True,
        )
    if resolved == gi.InferenceDomain.NAT_BOUND:
        return DomainCombinatorRules(
            domain=resolved,
            admits_contraction=True,
            admits_weakening=True,
            admits_pairing=True if admits_pairing is None else admits_pairing,
            exact_equality=False,
        )
    if resolved == gi.InferenceDomain.PRESENCE:
        return DomainCombinatorRules(
            domain=resolved,
            admits_contraction=True,
            admits_weakening=True,
            admits_pairing=True if admits_pairing is None else admits_pairing,
            exact_equality=False,
        )
    if resolved == gi.InferenceDomain.LINEAR:
        return DomainCombinatorRules(
            domain=resolved,
            admits_contraction=False,
            admits_weakening=False,
            admits_pairing=False if admits_pairing is None else admits_pairing,
            exact_equality=True,
        )
    # Affine: at most once; allows weakening (for disposable payloads) but forbids contraction > 1.
    return DomainCombinatorRules(
        domain=resolved,
        admits_contraction=False,
        admits_weakening=True,
        admits_pairing=True if admits_pairing is None else admits_pairing,
        exact_equality=False,
    )


_RECORD_RE = re.compile(
    r"(?:public\s+)?record\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<([^>]*)>)?\s*\(([^)]*)\)\s*;",
    re.MULTILINE,
)
_UNION_RE = re.compile(
    r"(?:public\s+)?union\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<([^>]*)>)?\s*\{([^}]*)\}\s*;",
    re.MULTILINE | re.DOTALL,
)
_CTOR_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*\(\s*([^)]+)\s*\)")


def inspect_holdfast_structures(source: str) -> StructureSpec:
    """Inspect HoldFast ``record`` and ``union`` declarations from source text."""
    records: dict[str, RecordDecl] = {}
    box_domain: gi.InferenceDomain | None = None
    for match in _RECORD_RE.finditer(source):
        name = match.group(1)
        raw_generics = match.group(2) or ""
        generics = tuple(part.strip() for part in raw_generics.split(",") if part.strip())
        if name == "Box":
            for gen in generics:
                if "grade" in gen and ":" in gen:
                    dom_name = gen.split(":", 1)[1].strip()
                    box_domain = gi.coerce_domain(dom_name)
        fields: list[tuple[str, str, str | None]] = []
        raw_body = match.group(3)
        if not isinstance(raw_body, str):
            continue
        for raw_field in raw_body.split(","):
            entry = raw_field.strip()
            if not entry:
                continue
            grade_part: str | None = None
            if "@" in entry:
                head_raw, grade_raw = entry.split("@", 1)
                head = head_raw.strip()
                grade_part = grade_raw.strip()
            else:
                head = entry
            parts = head.rsplit(None, 1)
            if len(parts) != 2:
                raise ValueError(f"unsupported record field syntax in {name!r}: {entry!r}")
            fields.append((parts[1], parts[0], grade_part))
        records[name] = RecordDecl(name, generics, tuple(fields))

    unions: dict[str, UnionDecl] = {}
    for match in _UNION_RE.finditer(source):
        name = match.group(1)
        raw_generics = match.group(2) or ""
        generics = tuple(part.strip() for part in raw_generics.split(",") if part.strip())
        variants: list[tuple[str, str, str]] = []
        for ctor_match in _CTOR_RE.finditer(match.group(3)):
            ctor_name = ctor_match.group(1)
            arg_parts = ctor_match.group(2).strip().rsplit(None, 1)
            if len(arg_parts) != 2:
                raise ValueError(f"unsupported union constructor syntax in {name!r}: {ctor_match.group(0)!r}")
            variants.append((ctor_name, arg_parts[0], arg_parts[1]))
        unions[name] = UnionDecl(name, generics, tuple(variants))

    return StructureSpec(records=records, unions=unions, box_domain=box_domain)


type CombinatorName = Literal[
    "dist_pair",
    "pull_pair",
    "push_sum",
    "flatten_box",
    "duplicate_box",
    "extract_box",
    "weaken_box",
]
type RefusalKind = Literal["authority", "domain", "structure", "grade"]


class CombinatorRefusalError(ValueError):
    """Raised when deriving a combinator violates domain, structure, or resource authority rules."""

    def __init__(self, combinator: str, kind: RefusalKind, reason: str) -> None:
        super().__init__(f"{combinator} refused ({kind}): {reason}")
        self.combinator = combinator
        self.kind: RefusalKind = kind
        self.reason = reason


@dataclass(frozen=True)
class CombinatorRefusal:
    """Structured refusal verdict for an invalid combinator derivation."""

    combinator: CombinatorName
    domain: gi.InferenceDomain
    kind: RefusalKind
    reason: str


@dataclass(frozen=True)
class CombinatorDerivation:
    """Verified combinator derivation with HoldFast source and replayable Rocq proof."""

    combinator: CombinatorName
    domain: gi.InferenceDomain
    signature: ArrowType
    holdfast_source: str
    gallina: str
    module_name: str
    theorem_name: str
    source_sha256: str


def _is_duplicable(ty: CombinatorType) -> bool:
    if isinstance(ty, BaseType):
        return ty.duplicable and not ty.owned
    if isinstance(ty, (PairType, SumType)):
        return _is_duplicable(ty.left) and _is_duplicable(ty.right)
    if isinstance(ty, BoxType):
        return _is_duplicable(ty.payload)
    return True


def _is_disposable(ty: CombinatorType) -> bool:
    if isinstance(ty, BaseType):
        return ty.disposable and not ty.owned
    if isinstance(ty, (PairType, SumType)):
        return _is_disposable(ty.left) and _is_disposable(ty.right)
    if isinstance(ty, BoxType):
        return _is_disposable(ty.payload)
    return True


def _lit_value(expr: gi.GradeExpr) -> int | None:
    return expr.value if isinstance(expr, gi.GradeLit) else None


def _expr_could_exceed_one(expr: gi.GradeExpr) -> bool:
    val = _lit_value(expr)
    if val is not None:
        return val > 1
    if isinstance(expr, gi.GradeAdd):
        lv = _lit_value(expr.lhs)
        rv = _lit_value(expr.rhs)
        if lv is not None and rv is not None:
            return (lv + rv) > 1
        return True
    if isinstance(expr, gi.GradeMul):
        lv = _lit_value(expr.lhs)
        rv = _lit_value(expr.rhs)
        if lv is not None and rv is not None:
            return (lv * rv) > 1
        return True
    return True


def _expr_could_be_zero(expr: gi.GradeExpr) -> bool:
    val = _lit_value(expr)
    if val is not None:
        return val == 0
    if isinstance(expr, gi.GradeAdd):
        return _expr_could_be_zero(expr.lhs) and _expr_could_be_zero(expr.rhs)
    if isinstance(expr, gi.GradeMul):
        return _expr_could_be_zero(expr.lhs) or _expr_could_be_zero(expr.rhs)
    return True


def _expr_definitely_ge_one(expr: gi.GradeExpr) -> bool:
    res = gi.solve_constraints(
        [gi.GradeConstraint(gi.GradeLit(1), "le", expr)],
        gi.InferenceDomain.NAT_BOUND,
    )
    return res.ok


def _format_grade_hf(expr: gi.GradeExpr) -> str:
    if isinstance(expr, gi.GradeLit):
        return str(expr.value)
    if isinstance(expr, gi.GradeVar):
        return str(expr.var_id)
    if isinstance(expr, gi.GradeAdd):
        return f"({_format_grade_hf(expr.lhs)} + {_format_grade_hf(expr.rhs)})"
    if isinstance(expr, gi.GradeMul):
        return f"({_format_grade_hf(expr.lhs)} * {_format_grade_hf(expr.rhs)})"
    return f"join({_format_grade_hf(expr.lhs)}, {_format_grade_hf(expr.rhs)})"


def _format_type_hf(ty: CombinatorType) -> str:
    if isinstance(ty, BaseType):
        return ty.name
    if isinstance(ty, PairType):
        return f"({_format_type_hf(ty.left)}, {_format_type_hf(ty.right)})"
    if isinstance(ty, SumType):
        return f"{ty.union_name}<{_format_type_hf(ty.left)}, {_format_type_hf(ty.right)}>"
    if isinstance(ty, BoxType):
        return f"{ty.record_name}<{_format_type_hf(ty.payload)}, {_format_grade_hf(ty.grade)}>"
    return f"Fn({_format_type_hf(ty.domain)} arg @ {_format_grade_hf(ty.allowance)}) -> {_format_type_hf(ty.codomain)}"


def _collect_grade_vars(expr: gi.GradeExpr) -> set[int | str]:
    if isinstance(expr, gi.GradeLit):
        return set()
    if isinstance(expr, gi.GradeVar):
        return {expr.var_id}
    return _collect_grade_vars(expr.lhs) | _collect_grade_vars(expr.rhs)


def _collect_type_grade_vars(ty: CombinatorType) -> set[int | str]:
    if isinstance(ty, BaseType):
        return set()
    if isinstance(ty, (PairType, SumType)):
        return _collect_type_grade_vars(ty.left) | _collect_type_grade_vars(ty.right)
    if isinstance(ty, BoxType):
        return _collect_grade_vars(ty.grade) | _collect_type_grade_vars(ty.payload)
    return _collect_grade_vars(ty.allowance) | _collect_type_grade_vars(ty.domain) | _collect_type_grade_vars(ty.codomain)


def _collect_base_names(ty: CombinatorType) -> set[str]:
    if isinstance(ty, BaseType):
        return {ty.name}
    if isinstance(ty, (PairType, SumType)):
        return _collect_base_names(ty.left) | _collect_base_names(ty.right)
    if isinstance(ty, BoxType):
        return _collect_base_names(ty.payload)
    return _collect_base_names(ty.domain) | _collect_base_names(ty.codomain)


def _emit_grade_coq(expr: gi.GradeExpr, var_map: Mapping[int | str, int]) -> str:
    if isinstance(expr, gi.GradeLit):
        return f"(GLit {expr.value})"
    if isinstance(expr, gi.GradeVar):
        return f"(GVar {var_map[expr.var_id]})"
    if isinstance(expr, gi.GradeAdd):
        return f"(GAdd {_emit_grade_coq(expr.lhs, var_map)} {_emit_grade_coq(expr.rhs, var_map)})"
    if isinstance(expr, gi.GradeMul):
        return f"(GMul {_emit_grade_coq(expr.lhs, var_map)} {_emit_grade_coq(expr.rhs, var_map)})"
    raise ValueError("GradeJoin is not directly supported in combinator Gallina expressions")


def _emit_type_coq(
    ty: CombinatorType,
    base_map: Mapping[str, int],
    var_map: Mapping[int | str, int],
) -> str:
    if isinstance(ty, BaseType):
        if ty.name == "Unit":
            return "CUnitTy"
        return f"(CBase {base_map[ty.name]})"
    if isinstance(ty, PairType):
        return f"(CProd {_emit_type_coq(ty.left, base_map, var_map)} {_emit_type_coq(ty.right, base_map, var_map)})"
    if isinstance(ty, SumType):
        return f"(CSum {_emit_type_coq(ty.left, base_map, var_map)} {_emit_type_coq(ty.right, base_map, var_map)})"
    if isinstance(ty, BoxType):
        return f"(CBox {_emit_grade_coq(ty.grade, var_map)} {_emit_type_coq(ty.payload, base_map, var_map)})"
    return (
        f"(CArr {_emit_grade_coq(ty.allowance, var_map)} "
        f"{_emit_type_coq(ty.domain, base_map, var_map)} "
        f"{_emit_type_coq(ty.codomain, base_map, var_map)})"
    )


COMBINATOR_KERNEL_GALLINA = """
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
  forall x, allows (puses d1 x) (puses d x) /\\ allows (puses d2 x) (puses d x).

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
  forall rho, eval_grade rho a <= eval_grade rho b /\\ eval_grade rho b <= 1.

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

Definition presence_grade_leb (a b : grade_expr) : bool :=
  grade_leb a b.

Lemma presence_grade_leb_sound : forall a b,
  presence_grade_leb a b = true -> presence_grade_le a b.
Proof.
  intros a b H rho Hpos. unfold presence_grade_leb in H.
  pose proof (grade_leb_sound a b H rho) as Hle. lia.
Qed.

Lemma presence_zero : presence_grade_le (GLit 0) (GLit 0).
Proof. intros rho H. cbn in H. lia. Qed.

Lemma exact_zero : grade_eq (GLit 0) (GLit 0).
Proof. intro rho. reflexivity. Qed.

Lemma bound_zero : grade_le (GLit 0) (GLit 0).
Proof. intro rho. cbn. lia. Qed.

End CombinatorKernel.
"""


def rocq_domain_config(domain: gi.InferenceDomain) -> tuple[str, str, str, str]:
    """Return ``(allows_prop, allowsb_fn, sound_lemma, zero_lemma)`` in ``CombinatorKernel``."""
    if domain in {gi.InferenceDomain.NAT_EXACT, gi.InferenceDomain.LINEAR}:
        return (
            "GradedSemiring.grade_eq",
            "GradedSemiring.grade_eqb",
            "GradedSemiring.grade_eqb_sound",
            "CombinatorKernel.exact_zero",
        )
    if domain == gi.InferenceDomain.NAT_BOUND:
        return (
            "GradedSemiring.grade_le",
            "GradedSemiring.grade_leb",
            "GradedSemiring.grade_leb_sound",
            "CombinatorKernel.bound_zero",
        )
    if domain == gi.InferenceDomain.AFFINE:
        return (
            "CombinatorKernel.affine_le",
            "CombinatorKernel.affine_leb",
            "CombinatorKernel.affine_leb_sound",
            "CombinatorKernel.affine_zero",
        )
    return (
        "CombinatorKernel.presence_grade_le",
        "CombinatorKernel.presence_grade_leb",
        "CombinatorKernel.presence_grade_leb_sound",
        "CombinatorKernel.presence_zero",
    )


def _check_domain_allows(
    lhs: gi.GradeExpr,
    rhs: gi.GradeExpr,
    domain: gi.InferenceDomain,
) -> gi.InferenceResult:
    return gi.solve_constraints(
        [gi.GradeConstraint(lhs, "le", rhs, (), "combinator admission")],
        domain,
    )


_DEFAULT_GRADE = gi.GradeLit(1)


def _derive_plan(
    combinator: CombinatorName,
    rules: DomainCombinatorRules,
    *,
    payload_type: CombinatorType | None = None,
    pair_type: PairType | None = None,
    sum_type: SumType | None = None,
    grade: gi.GradeExpr = _DEFAULT_GRADE,
    inner_grade: gi.GradeExpr = _DEFAULT_GRADE,
    target_grade: gi.GradeExpr | None = None,
    structure: StructureSpec | None = None,
) -> tuple[ArrowType, str, str] | CombinatorRefusal:
    domain = rules.domain
    if structure is not None and structure.box_domain is not None and structure.box_domain != domain:
        return CombinatorRefusal(
            combinator,
            domain,
            "domain",
            f"declared Box domain {structure.box_domain.value} conflicts with {domain.value}",
        )

    if combinator == "dist_pair":
        if pair_type is None:
            return CombinatorRefusal(combinator, domain, "structure", "dist_pair requires a PairType")
        if structure is not None and pair_type.record_name not in structure.records and pair_type.record_name != "Pair":
            return CombinatorRefusal(
                combinator,
                domain,
                "structure",
                f"undeclared record structure {pair_type.record_name!r}",
            )
        if not _is_duplicable(pair_type) and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot scale or duplicate non-duplicable/owned pair fields across Box",
            )
        if not _is_disposable(pair_type) and _expr_could_be_zero(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot discard non-disposable/owned pair fields at grade 0",
            )
        if domain == gi.InferenceDomain.AFFINE and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "grade",
                "Affine Box grade cannot exceed 1",
            )
        input_ty = BoxType(pair_type, grade)
        output_ty = PairType(BoxType(pair_type.left, grade), BoxType(pair_type.right, grade), pair_type.record_name)
        sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)

        def coq_term(bmap: Mapping[str, int], vmap: Mapping[int | str, int]) -> str:
            qg = _emit_grade_coq(grade, vmap)
            in_c = _emit_type_coq(input_ty, bmap, vmap)
            return (
                f"(CLam 1 (GLit 1) {in_c} "
                f"(CLetBox 2 (GLit 1) (CVar 1) "
                f"(CLetPair 3 4 {qg} (CVar 2) "
                f"(CPair (CPromote {qg} (CVar 3)) (CPromote {qg} (CVar 4))))))"
            )

        q_hf = _format_grade_hf(grade)
        hf = (
            f"public definition {_format_type_hf(output_ty)} DistPair("
            f"{_format_type_hf(input_ty)} boxed @ {domain.value}(1)) =>\n"
            f"    match (boxed) as whole : {_format_type_hf(output_ty)} {{\n"
            f"        Box(pair) => match (pair) as p : {_format_type_hf(output_ty)} {{\n"
            f"            {pair_type.record_name}(left, right) => "
            f"(Box<{_format_type_hf(pair_type.left)}, {q_hf}>(left), "
            f"Box<{_format_type_hf(pair_type.right)}, {q_hf}>(right)),\n"
            f"        }},\n"
            f"    }};"
        )
        return sig, hf, coq_term(
            {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))},
            {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))},
        )

    if combinator == "pull_pair":
        if pair_type is None:
            return CombinatorRefusal(combinator, domain, "structure", "pull_pair requires a PairType")
        if not rules.admits_pairing:
            return CombinatorRefusal(
                combinator,
                domain,
                "domain",
                f"domain {domain.value} does not admit pairing distribution for Box",
            )
        if not _is_duplicable(pair_type) and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot promote non-duplicable/owned pair fields beyond grade 1",
            )
        if not _is_disposable(pair_type) and _expr_could_be_zero(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot discard non-disposable/owned pair fields at grade 0",
            )
        if domain == gi.InferenceDomain.AFFINE and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "grade",
                "Affine Box grade cannot exceed 1",
            )
        input_ty = PairType(BoxType(pair_type.left, grade), BoxType(pair_type.right, grade), pair_type.record_name)
        output_ty = BoxType(pair_type, grade)
        sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)
        bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
        vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
        qg = _emit_grade_coq(grade, vmap)
        in_c = _emit_type_coq(input_ty, bmap, vmap)
        term_coq = (
            f"(CLam 1 (GLit 1) {in_c} "
            f"(CLetPair 2 3 (GLit 1) (CVar 1) "
            f"(CLetBox 4 (GLit 1) (CVar 2) "
            f"(CLetBox 5 (GLit 1) (CVar 3) "
            f"(CPromote {qg} (CPair (CVar 4) (CVar 5)))))))"
        )
        q_hf = _format_grade_hf(grade)
        hf = (
            f"public definition {_format_type_hf(output_ty)} PullPair("
            f"{_format_type_hf(input_ty)} pair @ {domain.value}(1)) =>\n"
            f"    match (pair) as p : {_format_type_hf(output_ty)} {{\n"
            f"        {pair_type.record_name}(bx, by) => match (bx) as _x : {_format_type_hf(output_ty)} {{\n"
            f"            Box(x) => match (by) as _y : {_format_type_hf(output_ty)} {{\n"
            f"                Box(y) => Box<{_format_type_hf(pair_type)}, {q_hf}>((x, y)),\n"
            f"            }},\n"
            f"        }},\n"
            f"    }};"
        )
        return sig, hf, term_coq

    if combinator == "push_sum":
        if sum_type is None:
            return CombinatorRefusal(combinator, domain, "structure", "push_sum requires a SumType")
        if structure is not None and sum_type.union_name not in structure.unions and sum_type.union_name != "Either":
            return CombinatorRefusal(
                combinator,
                domain,
                "structure",
                f"undeclared union structure {sum_type.union_name!r}",
            )
        if not _expr_definitely_ge_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "grade",
                "push_sum requires grade >= 1 to inspect sum constructor tags at runtime",
            )
        if not _is_duplicable(sum_type) and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot scale non-duplicable/owned sum payload beyond grade 1",
            )
        if domain == gi.InferenceDomain.AFFINE and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "grade",
                "Affine Box grade cannot exceed 1",
            )
        input_ty = BoxType(sum_type, grade)
        output_ty = SumType(
            BoxType(sum_type.left, grade),
            BoxType(sum_type.right, grade),
            sum_type.union_name,
            sum_type.left_ctor,
            sum_type.right_ctor,
        )
        sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)
        bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
        vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
        qg = _emit_grade_coq(grade, vmap)
        in_c = _emit_type_coq(input_ty, bmap, vmap)
        bl_c = _emit_type_coq(BoxType(sum_type.left, grade), bmap, vmap)
        br_c = _emit_type_coq(BoxType(sum_type.right, grade), bmap, vmap)
        term_coq = (
            f"(CLam 1 (GLit 1) {in_c} "
            f"(CLetBox 2 (GLit 1) (CVar 1) "
            f"(CMatchSum 3 4 {qg} (CVar 2) "
            f"(CInl {br_c} (CPromote {qg} (CVar 3))) "
            f"(CInr {bl_c} (CPromote {qg} (CVar 4))))))"
        )
        q_hf = _format_grade_hf(grade)
        hf = (
            f"public definition {_format_type_hf(output_ty)} PushSum("
            f"{_format_type_hf(input_ty)} boxed @ {domain.value}(1)) =>\n"
            f"    match (boxed) as whole : {_format_type_hf(output_ty)} {{\n"
            f"        Box(value) => match (value) as s : {_format_type_hf(output_ty)} {{\n"
            f"            {sum_type.left_ctor}(l) => {sum_type.left_ctor}(Box<{_format_type_hf(sum_type.left)}, {q_hf}>(l)),\n"
            f"            {sum_type.right_ctor}(r) => {sum_type.right_ctor}(Box<{_format_type_hf(sum_type.right)}, {q_hf}>(r)),\n"
            f"        }},\n"
            f"    }};"
        )
        return sig, hf, term_coq

    if payload_type is None:
        return CombinatorRefusal(combinator, domain, "structure", f"{combinator} requires a payload_type")

    if combinator == "flatten_box":
        if not _is_duplicable(payload_type) and (_expr_could_exceed_one(grade) or _expr_could_exceed_one(inner_grade)):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot flatten non-duplicable/owned resource with grade > 1",
            )
        if not _is_disposable(payload_type) and (_expr_could_be_zero(grade) or _expr_could_be_zero(inner_grade)):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot flatten non-disposable/owned resource to grade 0",
            )
        if domain == gi.InferenceDomain.AFFINE and (_expr_could_exceed_one(grade) or _expr_could_exceed_one(inner_grade)):
            return CombinatorRefusal(
                combinator,
                domain,
                "grade",
                "Affine Box grade cannot exceed 1",
            )
        prod_grade = gi.GradeMul(grade, inner_grade)
        input_ty = BoxType(BoxType(payload_type, inner_grade), grade)
        output_ty = BoxType(payload_type, prod_grade)
        sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)
        bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
        vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
        qg = _emit_grade_coq(grade, vmap)
        rg = _emit_grade_coq(inner_grade, vmap)
        in_c = _emit_type_coq(input_ty, bmap, vmap)
        term_coq = (
            f"(CLam 1 (GLit 1) {in_c} "
            f"(CLetBox 2 (GLit 1) (CVar 1) "
            f"(CLetBox 3 {qg} (CVar 2) "
            f"(CPromote (GMul {qg} {rg}) (CVar 3)))))"
        )
        hf = (
            f"public definition {_format_type_hf(output_ty)} FlattenBox("
            f"{_format_type_hf(input_ty)} boxed @ {domain.value}(1)) =>\n"
            f"    match (boxed) as outer : {_format_type_hf(output_ty)} {{\n"
            f"        Box(inner) => match (inner) as mid : {_format_type_hf(output_ty)} {{\n"
            f"            Box(x) => Box<{_format_type_hf(payload_type)}, {_format_grade_hf(prod_grade)}>(x),\n"
            f"        }},\n"
            f"    }};"
        )
        return sig, hf, term_coq

    if combinator == "duplicate_box":
        if not rules.admits_contraction or not _is_duplicable(payload_type):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                f"Dup/contraction is forbidden for domain {domain.value} or non-duplicable/owned payload",
            )
        if not _is_disposable(payload_type) and (_expr_could_be_zero(grade) or _expr_could_be_zero(inner_grade)):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot duplicate non-disposable/owned payload at grade 0",
            )
        prod_grade = gi.GradeMul(grade, inner_grade)
        input_ty = BoxType(payload_type, prod_grade)
        output_ty = BoxType(BoxType(payload_type, inner_grade), grade)
        sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)
        bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
        vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
        qg = _emit_grade_coq(grade, vmap)
        rg = _emit_grade_coq(inner_grade, vmap)
        in_c = _emit_type_coq(input_ty, bmap, vmap)
        term_coq = (
            f"(CLam 1 (GLit 1) {in_c} "
            f"(CLetBox 2 (GLit 1) (CVar 1) "
            f"(CPromote {qg} (CPromote {rg} (CVar 2)))))"
        )
        hf = (
            f"public definition {_format_type_hf(output_ty)} DuplicateBox("
            f"{_format_type_hf(input_ty)} boxed @ {domain.value}(1)) =>\n"
            f"    match (boxed) as whole : {_format_type_hf(output_ty)} {{\n"
            f"        Box(x) => Box<{_format_type_hf(BoxType(payload_type, inner_grade))}, {_format_grade_hf(grade)}>("
            f"Box<{_format_type_hf(payload_type)}, {_format_grade_hf(inner_grade)}>(x)),\n"
            f"    }};"
        )
        return sig, hf, term_coq

    if combinator == "extract_box":
        check_one = _check_domain_allows(gi.GradeLit(1), grade, domain)
        if not check_one.ok:
            return CombinatorRefusal(
                combinator,
                domain,
                "grade",
                f"extract_box requires Box<A, 1>, got grade {_format_grade_hf(grade)} in {domain.value}",
            )
        if not _is_disposable(payload_type) and _expr_could_exceed_one(grade):
            return CombinatorRefusal(
                combinator,
                domain,
                "authority",
                "cannot extract and discard excess uses of non-disposable/owned payload",
            )
        input_ty = BoxType(payload_type, grade)
        output_ty = payload_type
        sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)
        bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
        vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
        in_c = _emit_type_coq(input_ty, bmap, vmap)
        term_coq = (
            f"(CLam 1 (GLit 1) {in_c} "
            f"(CLetBox 2 (GLit 1) (CVar 1) (CVar 2)))"
        )
        hf = (
            f"public definition {_format_type_hf(output_ty)} ExtractBox("
            f"{_format_type_hf(input_ty)} boxed @ {domain.value}(1)) =>\n"
            f"    match (boxed) as whole : {_format_type_hf(output_ty)} {{\n"
            f"        Box(x) => x,\n"
            f"    }};"
        )
        return sig, hf, term_coq

    # weaken_box : Box<A, q'> -> Box<A, q>
    if target_grade is None:
        return CombinatorRefusal(combinator, domain, "grade", "weaken_box requires target_grade q")
    check = _check_domain_allows(target_grade, grade, domain)
    if not check.ok:
        return CombinatorRefusal(
            combinator,
            domain,
            "grade",
            f"unsound weakening from {_format_grade_hf(grade)} to {_format_grade_hf(target_grade)} in {domain.value}",
        )
    if not rules.admits_weakening:
        # Exact domains only allow weakening when target_grade == grade (already checked above).
        pass
    if not _is_disposable(payload_type) and _expr_could_be_zero(target_grade):
        return CombinatorRefusal(
            combinator,
            domain,
            "authority",
            "cannot weaken non-disposable/owned resource to grade 0",
        )
    if not _is_duplicable(payload_type) and _expr_could_exceed_one(grade):
        return CombinatorRefusal(
            combinator,
            domain,
            "authority",
            "cannot weaken non-duplicable/owned resource with grade > 1",
        )
    input_ty = BoxType(payload_type, grade)
    output_ty = BoxType(payload_type, target_grade)
    sig = ArrowType(gi.GradeLit(1), input_ty, output_ty)
    bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
    vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
    qg_out = _emit_grade_coq(target_grade, vmap)
    in_c = _emit_type_coq(input_ty, bmap, vmap)
    term_coq = (
        f"(CLam 1 (GLit 1) {in_c} "
        f"(CLetBox 2 (GLit 1) (CVar 1) (CPromote {qg_out} (CVar 2))))"
    )
    hf = (
        f"public definition {_format_type_hf(output_ty)} WeakenBox("
        f"{_format_type_hf(input_ty)} boxed @ {domain.value}(1)) =>\n"
        f"    match (boxed) as whole : {_format_type_hf(output_ty)} {{\n"
        f"        Box(x) => Box<{_format_type_hf(payload_type)}, {_format_grade_hf(target_grade)}>(x),\n"
        f"    }};"
    )
    return sig, hf, term_coq


def _emit_combinator_gallina(
    combinator: CombinatorName,
    domain: gi.InferenceDomain,
    sig: ArrowType,
    term_coq: str,
) -> tuple[str, str, str]:
    module_name = f"Derived_{combinator}"
    theorem_name = f"{combinator}_sound"
    allows_prop, allowsb_fn, sound_lemma, zero_lemma = rocq_domain_config(domain)
    bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
    vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
    sig_coq = _emit_type_coq(sig, bmap, vmap)

    lines = [
        "(* SPDX-License-Identifier: Apache-2.0 *)",
        "From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.",
        "Require Import graded_pure graded_domains graded_semiring.",
        "Import ListNotations GradedDomains GradedSemiring.",
        COMBINATOR_KERNEL_GALLINA,
        f"Module {module_name}.",
        "Import CombinatorKernel.",
        "",
        f"Definition candidate_term : cterm := {term_coq}.",
        f"Definition candidate_type : cty := {sig_coq}.",
        "",
        f"Theorem {combinator}_checked :",
        f"  cinfer {allowsb_fn} [] candidate_term =",
        "  Some {| cresult_type := candidate_type; cdemand_row := [] |}.",
        "Proof.",
        "  vm_compute. reflexivity.",
        "Qed.",
        "",
        f"Theorem {theorem_name} :",
        f"  CDerives {allows_prop} [] candidate_term",
        "    {| cresult_type := candidate_type; cdemand_row := [] |}.",
        "Proof.",
        f"  apply (cinfer_sound {allows_prop} {allowsb_fn} {sound_lemma} {zero_lemma}).",
        f"  exact {combinator}_checked.",
        "Qed.",
        "",
        f"End {module_name}.",
    ]
    return "\n".join(lines) + "\n", module_name, theorem_name


def verify_combinator(derivation: CombinatorDerivation) -> list[str]:
    """Replay a :class:`CombinatorDerivation` through Rocq and audit for zero axioms."""
    root = Path(__file__).resolve().parents[2]
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-combinator-") as tmp:
        directory = Path(tmp)
        graded_source._support(root, compiler, directory, _ROCQ_SUPPORT)
        unit = directory / "CombinatorProof.v"
        unit.write_text(derivation.gallina, encoding="utf-8", newline="\n")
        compiled = subprocess.run(
            [*compiler, unit.name],
            cwd=directory,
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            timeout=60,
        )
        if compiled.returncode != 0:
            raise ValueError(f"Rocq rejected derived combinator {derivation.combinator}: {compiled.stderr.strip()}")
        audit = directory / "CombinatorAudit.v"
        audit.write_text(
            f"Require Import CombinatorProof.\nPrint Assumptions {derivation.module_name}.{derivation.theorem_name}.\n",
            encoding="utf-8",
            newline="\n",
        )
        audited = subprocess.run(
            [*compiler, audit.name],
            cwd=directory,
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            timeout=60,
        )
        if audited.returncode != 0:
            raise ValueError(f"Rocq audit failed for {derivation.combinator}: {audited.stderr.strip()}")
        return solver_ledger.audit(audited.stdout, 1, derivation.module_name, ())


def try_derive_combinator(
    combinator: CombinatorName,
    *,
    domain: str | gi.InferenceDomain | graded_source.GradeDomain = gi.InferenceDomain.NAT_EXACT,
    payload_type: CombinatorType | None = None,
    pair_type: PairType | None = None,
    sum_type: SumType | None = None,
    grade: gi.GradeExpr = _DEFAULT_GRADE,
    inner_grade: gi.GradeExpr = _DEFAULT_GRADE,
    target_grade: gi.GradeExpr | None = None,
    rules: DomainCombinatorRules | None = None,
    structure: StructureSpec | None = None,
    verify_rocq: bool = False,
) -> CombinatorDerivation | CombinatorRefusal:
    """Attempt to derive a modality combinator, returning a structured refusal if invalid."""
    resolved_rules = rules if rules is not None else default_domain_rules(domain)
    plan = _derive_plan(
        combinator,
        resolved_rules,
        payload_type=payload_type,
        pair_type=pair_type,
        sum_type=sum_type,
        grade=grade,
        inner_grade=inner_grade,
        target_grade=target_grade,
        structure=structure,
    )
    if isinstance(plan, CombinatorRefusal):
        return plan
    sig, body_hf, term_coq = plan
    holdfast_source = "\n".join([
        "// SPDX-License-Identifier: Apache-2.0",
        "module DerivedCombinators;",
        f"public record Box<T, grade q : {resolved_rules.domain.value}>(T Value @ q);",
        body_hf,
    ]) + "\n"
    gallina, module_name, theorem_name = _emit_combinator_gallina(
        combinator, resolved_rules.domain, sig, term_coq
    )
    derivation = CombinatorDerivation(
        combinator=combinator,
        domain=resolved_rules.domain,
        signature=sig,
        holdfast_source=holdfast_source,
        gallina=gallina,
        module_name=module_name,
        theorem_name=theorem_name,
        source_sha256=hashlib.sha256(holdfast_source.encode("utf-8")).hexdigest(),
    )
    if verify_rocq:
        verify_combinator(derivation)
    return derivation


def derive_combinator(
    combinator: CombinatorName,
    *,
    domain: str | gi.InferenceDomain | graded_source.GradeDomain = gi.InferenceDomain.NAT_EXACT,
    payload_type: CombinatorType | None = None,
    pair_type: PairType | None = None,
    sum_type: SumType | None = None,
    grade: gi.GradeExpr = _DEFAULT_GRADE,
    inner_grade: gi.GradeExpr = _DEFAULT_GRADE,
    target_grade: gi.GradeExpr | None = None,
    rules: DomainCombinatorRules | None = None,
    structure: StructureSpec | None = None,
    verify_rocq: bool = False,
) -> CombinatorDerivation:
    """Derive a modality combinator or raise :class:`CombinatorRefusalError`."""
    outcome = try_derive_combinator(
        combinator,
        domain=domain,
        payload_type=payload_type,
        pair_type=pair_type,
        sum_type=sum_type,
        grade=grade,
        inner_grade=inner_grade,
        target_grade=target_grade,
        rules=rules,
        structure=structure,
        verify_rocq=verify_rocq,
    )
    if isinstance(outcome, CombinatorRefusal):
        raise CombinatorRefusalError(outcome.combinator, outcome.kind, outcome.reason)
    return outcome
