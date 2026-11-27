# SPDX-License-Identifier: Apache-2.0
"""Derived distributive modality combinators over graded structures (Q25bz).

Inspects declared ``Pair``/``record``, ``Sum``/``union``, and ``Box`` structures
together with grade domain rules (contraction/``Dup``, weakening, and semiring
distributivity), enforces resource/authority boundaries, and emits inspectable
HoldFast source alongside replayable Rocq proofs audited for zero axioms.
"""

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, cast

from toolchain import graded_inference as gi
from toolchain import graded_source, parser


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


def _node_text(node: object) -> str:
    if not isinstance(node, Mapping):
        raise TypeError(f"expected AST name mapping, got {node!r}")
    inner = node.get("name")
    if isinstance(inner, Mapping):
        return _node_text(inner)
    text = node.get("text")
    if not isinstance(text, str):
        raise TypeError(f"expected AST text field, got {node!r}")
    return text


def _span_text(source_bytes: bytes, node: object) -> str:
    if not isinstance(node, Mapping):
        raise TypeError(f"expected AST node mapping, got {node!r}")
    span = node.get("span")
    if not isinstance(span, list) or len(span) != 2 or not all(isinstance(x, int) for x in span):
        raise ValueError(f"missing byte span on AST node: {node!r}")
    return source_bytes[cast("int", span[0]):cast("int", span[1])].decode("utf-8").strip()


def inspect_holdfast_structures(
    source: str,
    *,
    parsed: Mapping[str, object] | None = None,
) -> StructureSpec:
    """Inspect HoldFast ``record`` and ``union`` declarations via the canonical HoldFast parser."""
    source_bytes = source.encode("utf-8")
    if parsed is None:
        root = Path(__file__).resolve().parents[2]
        with parser.cached_build(root) as compiled:
            ast_payload = cast("Mapping[str, object]", parser.parse_source(compiled, source_bytes, surface=True))
    else:
        ast_payload = parsed

    ast_root = ast_payload.get("ast")
    if not isinstance(ast_root, Mapping):
        raise TypeError("canonical parser output omitted 'ast' surface file")
    declarations = ast_root.get("declarations")
    if not isinstance(declarations, list):
        raise TypeError("canonical parser output omitted 'declarations'")

    records: dict[str, RecordDecl] = {}
    unions: dict[str, UnionDecl] = {}
    box_domain: gi.InferenceDomain | None = None

    for raw_decl in declarations:
        if not isinstance(raw_decl, Mapping):
            continue
        kind = raw_decl.get("kind")
        if kind == "record":
            name = _node_text(raw_decl.get("name"))
            raw_generics = cast("list[object]", raw_decl.get("generics") or [])
            generics = tuple(_span_text(source_bytes, gen) for gen in raw_generics)
            if name == "Box":
                for gen in raw_generics:
                    if isinstance(gen, Mapping) and gen.get("mode") == "grade" and gen.get("type") is not None:
                        box_domain = gi.coerce_domain(_span_text(source_bytes, gen.get("type")))
            fields: list[tuple[str, str, str | None]] = []
            for param in cast("list[object]", raw_decl.get("parameters") or []):
                if not isinstance(param, Mapping):
                    continue
                pname = _node_text(param.get("name"))
                ptype_node = param.get("type")
                if ptype_node is None:
                    raise ValueError(f"unsupported record field syntax in {name!r}: missing type on {pname!r}")
                grade_node = param.get("grade")
                grade_part = _span_text(source_bytes, grade_node) if grade_node is not None else None
                fields.append((pname, _span_text(source_bytes, ptype_node), grade_part))
            records[name] = RecordDecl(name, generics, tuple(fields))
        elif kind == "union":
            name = _node_text(raw_decl.get("name"))
            raw_generics = cast("list[object]", raw_decl.get("generics") or [])
            generics = tuple(_span_text(source_bytes, gen) for gen in raw_generics)
            variants: list[tuple[str, str, str]] = []
            for ctor in cast("list[object]", raw_decl.get("constructors") or []):
                if not isinstance(ctor, Mapping):
                    continue
                ctor_name = _node_text(ctor.get("name"))
                cparams = cast("list[object]", ctor.get("parameters") or [])
                if len(cparams) != 1 or not isinstance(cparams[0], Mapping) or cparams[0].get("type") is None:
                    raise ValueError(f"unsupported union constructor syntax in {name!r}: {ctor_name!r}")
                variants.append((
                    ctor_name,
                    _span_text(source_bytes, cparams[0].get("type")),
                    _node_text(cparams[0].get("name")),
                ))
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


def _collect_type_grade_vars(ty: CombinatorType) -> set[int | str]:
    if isinstance(ty, BaseType):
        return set()
    if isinstance(ty, (PairType, SumType)):
        return _collect_type_grade_vars(ty.left) | _collect_type_grade_vars(ty.right)
    if isinstance(ty, BoxType):
        return gi.expr_vars(ty.grade) | _collect_type_grade_vars(ty.payload)
    return gi.expr_vars(ty.allowance) | _collect_type_grade_vars(ty.domain) | _collect_type_grade_vars(ty.codomain)


def _collect_base_names(ty: CombinatorType) -> set[str]:
    if isinstance(ty, BaseType):
        return {ty.name}
    if isinstance(ty, (PairType, SumType)):
        return _collect_base_names(ty.left) | _collect_base_names(ty.right)
    if isinstance(ty, BoxType):
        return _collect_base_names(ty.payload)
    return _collect_base_names(ty.domain) | _collect_base_names(ty.codomain)


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
        return f"(CBox {gi.emit_grade_coq(ty.grade, var_map)} {_emit_type_coq(ty.payload, base_map, var_map)})"
    return (
        f"(CArr {gi.emit_grade_coq(ty.allowance, var_map)} "
        f"{_emit_type_coq(ty.domain, base_map, var_map)} "
        f"{_emit_type_coq(ty.codomain, base_map, var_map)})"
    )


# CombinatorKernel is mechanized in tools/rocq/graded_semiring.v and imported directly.


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
            qg = gi.emit_grade_coq(grade, vmap)
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
        qg = gi.emit_grade_coq(grade, vmap)
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
        qg = gi.emit_grade_coq(grade, vmap)
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
        qg = gi.emit_grade_coq(grade, vmap)
        rg = gi.emit_grade_coq(inner_grade, vmap)
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
        qg = gi.emit_grade_coq(grade, vmap)
        rg = gi.emit_grade_coq(inner_grade, vmap)
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
    qg_out = gi.emit_grade_coq(target_grade, vmap)
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


def emit_kernel_module_gallina(
    module_name: str,
    checked_name: str,
    theorem_name: str,
    domain: gi.InferenceDomain,
    term_coq: str,
    type_coq: str,
) -> tuple[str, str, str]:
    """Build a replayable Rocq verification unit backed by ``CombinatorKernel``."""
    allows_prop, allowsb_fn, sound_lemma, zero_lemma = rocq_domain_config(domain)
    lines = [
        "(* SPDX-License-Identifier: Apache-2.0 *)",
        "From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.",
        "Require Import graded_pure graded_domains graded_semiring.",
        "Import ListNotations GradedDomains GradedSemiring.",
        f"Module {module_name}.",
        "Import CombinatorKernel.",
        "",
        f"Definition candidate_term : cterm := {term_coq}.",
        f"Definition candidate_type : cty := {type_coq}.",
        "",
        f"Theorem {checked_name} :",
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
        f"  exact {checked_name}.",
        "Qed.",
        "",
        f"End {module_name}.",
    ]
    return "\n".join(lines) + "\n", module_name, theorem_name


def _emit_combinator_gallina(
    combinator: CombinatorName,
    domain: gi.InferenceDomain,
    sig: ArrowType,
    term_coq: str,
) -> tuple[str, str, str]:
    bmap = {name: idx for idx, name in enumerate(sorted(_collect_base_names(sig)))}
    vmap = {v: idx for idx, v in enumerate(sorted(_collect_type_grade_vars(sig), key=gi._var_sort_key))}
    sig_coq = _emit_type_coq(sig, bmap, vmap)
    return emit_kernel_module_gallina(
        f"Derived_{combinator}",
        f"{combinator}_checked",
        f"{combinator}_sound",
        domain,
        term_coq,
        sig_coq,
    )


def verify_combinator(derivation: CombinatorDerivation) -> list[str]:
    """Replay a :class:`CombinatorDerivation` through Rocq and audit for zero axioms."""
    return gi.replay_semiring_proof(
        derivation.gallina,
        "CombinatorProof.v",
        1,
        derivation.module_name,
        f"Rocq rejected derived combinator {derivation.combinator}",
        theorem_names=(derivation.theorem_name,),
        prefix="holdfast-combinator-",
    )


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
