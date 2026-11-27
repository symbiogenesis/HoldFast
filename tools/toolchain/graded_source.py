# SPDX-License-Identifier: Apache-2.0
"""Unified typed IR and Rocq Core replay checker for graded HoldFast sources."""

from __future__ import annotations

import contextlib
import hashlib
import json
import re
import subprocess
import tempfile
import threading
import time
from collections.abc import Callable, Mapping
from contextlib import ExitStack, suppress
from contextvars import ContextVar
from dataclasses import dataclass, field
from enum import StrEnum
from pathlib import Path
from types import MappingProxyType
from typing import TextIO, cast, override

from toolchain import graded_inference as gi
from toolchain import parser, proofenv, rocq_cache
from toolchain.ast import HoldFastError
from toolchain.elaborate_intrinsics import _IntrinsicsMixin
from toolchain.elaborate_protocol import _Protocol, syntax_nodes
from toolchain.elaborate_types import Node
from toolchain.source_file import ensure_unchanged, read_source


class GradeDomain(StrEnum):
    """Built-in grade semiring domains verified in Rocq."""

    EXACT = "NatExact"
    BOUND = "NatBound"
    PRESENCE = "Presence"
    LINEAR = "Linear"
    AFFINE = "Affine"
    SECURITY = "SecurityLoHi"


@dataclass(frozen=True)
class _DomainSpec:
    domain: GradeDomain
    rocq_domain: str
    base_domain: str
    check_fn: str
    sound_thm: str
    label: str
    subgraded: bool
    grade_type: str
    zero: str
    one: str
    many: str | None = None
    sample_values: tuple[str, ...] = ()


_DOMAIN_SPECS: dict[GradeDomain, _DomainSpec] = {
    GradeDomain.EXACT: _DomainSpec(
        domain=GradeDomain.EXACT,
        rocq_domain="NatExactJoin",
        base_domain="NatExact",
        check_fn="source_check_core",
        sound_thm="source_check_core_sound",
        label="exact",
        subgraded=False,
        grade_type="nat",
        zero="0",
        one="1",
        sample_values=("0", "1", "2"),
    ),
    GradeDomain.BOUND: _DomainSpec(
        domain=GradeDomain.BOUND,
        rocq_domain="NatBoundJoin",
        base_domain="NatBound",
        check_fn="source_check_core_sub",
        sound_thm="source_check_core_sub_sound",
        label="bounded",
        subgraded=True,
        grade_type="nat",
        zero="0",
        one="1",
        sample_values=("0", "1", "2"),
    ),
    GradeDomain.PRESENCE: _DomainSpec(
        domain=GradeDomain.PRESENCE,
        rocq_domain="PresenceJoin",
        base_domain="Presence",
        check_fn="source_check_core_sub",
        sound_thm="source_check_core_sub_sound",
        label="presence",
        subgraded=True,
        grade_type="bool",
        zero="false",
        one="true",
        many="true",
        sample_values=("false", "true"),
    ),
    GradeDomain.LINEAR: _DomainSpec(
        domain=GradeDomain.LINEAR,
        rocq_domain="LinearDomain",
        base_domain="LinearBase",
        check_fn="source_check_core",
        sound_thm="source_check_core_sound",
        label="linear",
        subgraded=False,
        grade_type="lin_grade",
        zero="LZero",
        one="LOne",
        many="LMany",
        sample_values=("LZero", "LOne", "LMany"),
    ),
    GradeDomain.AFFINE: _DomainSpec(
        domain=GradeDomain.AFFINE,
        rocq_domain="AffineDomain",
        base_domain="AffineBase",
        check_fn="source_check_core_sub",
        sound_thm="source_check_core_sub_sound",
        label="affine",
        subgraded=True,
        grade_type="aff_grade",
        zero="AZero",
        one="AOne",
        many="AMany",
        sample_values=("AZero", "AOne", "AMany"),
    ),
    GradeDomain.SECURITY: _DomainSpec(
        domain=GradeDomain.SECURITY,
        rocq_domain="SecurityLoHi",
        base_domain="SecurityBase",
        check_fn="source_check_core_sub",
        sound_thm="source_check_core_sub_sound",
        label="security",
        subgraded=True,
        grade_type="sec_grade",
        zero="Lo",
        one="Hi",
        many="Hi",
        sample_values=("Lo", "Hi"),
    ),
}


@dataclass(frozen=True)
class CustomDomainSpec:
    """Projection descriptor for a user-defined `domain` declaration."""

    name: str
    rocq_name: str
    carrier_key: str
    zero_expr: str
    one_expr: str
    add_expr: str
    mul_expr: str
    allows_expr: str
    allowsb_expr: str
    eqb_expr: str
    subgraded: bool = True
    gallina_prelude: str = ""
    sample_values: tuple[str, ...] = ()


_PRIMITIVES = frozenset({"Nat", "bool", "Vec", "Type", *GradeDomain})
_ROCQ_FILES = ("graded_pure.v", "graded_domains.v", "graded_source.v")
_MODAL_FILES = ("graded_pure.v", "graded_domains.v", "graded_modal.v", "graded_modal_source.v")
_CORE_FILES = ("graded_pure.v", "graded_domains.v", "graded_core.v", "graded_core_source.v")
SUPPORT_FILES = tuple(dict.fromkeys((*_ROCQ_FILES, *_MODAL_FILES, *_CORE_FILES)))
REPLAY_DEADLINE: ContextVar[float | None] = ContextVar("graded_replay_deadline", default=None)

_BOUND_ZERO_VALUES = {"0", "false", "LZero", "AZero", "Lo"}


def _name(node: object) -> str:
    n = cast("Node", node)
    inner = n.get("name")
    if isinstance(inner, dict):
        return cast("str", inner["text"])
    return cast("str", n["text"])


def _nat_val(node: Node) -> int:
    raw = node["value"]
    if isinstance(raw, int):
        return raw
    if isinstance(raw, str):
        return int(raw)
    raise ValueError(f"invalid nat literal value {raw!r}")


def _type_arg(node: Node) -> Node:
    return cast("Node", node["type"]) if node["kind"] == "type_argument" else node


def _span(node: Node) -> list[int]:
    return cast("list[int]", node["span"])


def _domain_spec(domain: GradeDomain) -> _DomainSpec:
    return _DOMAIN_SPECS[domain]


def _rocq_grade_sort_value(domain: GradeDomain | CustomDomainSpec, raw_lit: int | bool | str) -> str:
    if isinstance(domain, CustomDomainSpec):
        if isinstance(raw_lit, bool):
            return "true" if raw_lit else "false"
        if isinstance(raw_lit, int):
            return domain.zero_expr if raw_lit == 0 else domain.one_expr if raw_lit == 1 else str(raw_lit)
        return raw_lit
    spec = _domain_spec(domain)
    if domain in (GradeDomain.EXACT, GradeDomain.BOUND):
        if isinstance(raw_lit, bool):
            return "1" if raw_lit else "0"
        if isinstance(raw_lit, int):
            return str(raw_lit)
        if raw_lit in {"zero", "0"}:
            return "0"
        if raw_lit in {"one", "1"}:
            return "1"
        if raw_lit.isdigit():
            return raw_lit
        raise ValueError(f"invalid natural grade literal {raw_lit!r}")
    if domain == GradeDomain.PRESENCE:
        if isinstance(raw_lit, bool):
            return "true" if raw_lit else "false"
        if isinstance(raw_lit, int):
            return "true" if raw_lit > 0 else "false"
        low = raw_lit.lower()
        if low in {"0", "false", "zero"}:
            return "false"
        if low in {"1", "true", "one", "many"}:
            return "true"
        if raw_lit.isdigit():
            return "true" if int(raw_lit) > 0 else "false"
        raise ValueError(f"invalid presence grade literal {raw_lit!r}")
    if domain == GradeDomain.LINEAR:
        if isinstance(raw_lit, bool):
            return "LOne" if raw_lit else "LZero"
        if isinstance(raw_lit, int):
            return "LZero" if raw_lit == 0 else ("LOne" if raw_lit == 1 else "LMany")
        mapping = {"0": "LZero", "zero": "LZero", "lzero": "LZero",
                   "1": "LOne", "one": "LOne", "lone": "LOne",
                   "many": "LMany", "lmany": "LMany"}
        key = raw_lit.lower()
        if key in mapping:
            return mapping[key]
        if raw_lit.isdigit():
            return _rocq_grade_sort_value(domain, int(raw_lit))
        raise ValueError(f"invalid linear grade literal {raw_lit!r}")
    if domain == GradeDomain.AFFINE:
        if isinstance(raw_lit, bool):
            return "AOne" if raw_lit else "AZero"
        if isinstance(raw_lit, int):
            return "AZero" if raw_lit == 0 else ("AOne" if raw_lit == 1 else "AMany")
        mapping = {"0": "AZero", "zero": "AZero", "azero": "AZero",
                   "1": "AOne", "one": "AOne", "aone": "AOne",
                   "many": "AMany", "amany": "AMany"}
        key = raw_lit.lower()
        if key in mapping:
            return mapping[key]
        if raw_lit.isdigit():
            return _rocq_grade_sort_value(domain, int(raw_lit))
        raise ValueError(f"invalid affine grade literal {raw_lit!r}")
    if domain == GradeDomain.SECURITY:
        if isinstance(raw_lit, bool):
            return "Hi" if raw_lit else "Lo"
        if isinstance(raw_lit, int):
            return "Lo" if raw_lit == 0 else "Hi"
        mapping = {"0": "Lo", "zero": "Lo", "lo": "Lo", "low": "Lo", "false": "Lo",
                   "1": "Hi", "one": "Hi", "hi": "Hi", "high": "Hi", "many": "Hi", "true": "Hi"}
        key = raw_lit.lower()
        if key in mapping:
            return mapping[key]
        if raw_lit.isdigit():
            return _rocq_grade_sort_value(domain, int(raw_lit))
        raise ValueError(f"invalid security grade literal {raw_lit!r}")
    return spec.zero


def _add_grades(domain: GradeDomain | CustomDomainSpec, a: str, b: str) -> str:
    if isinstance(domain, CustomDomainSpec):
        return f"(@add {domain.rocq_name} {a} {b})"
    if domain in (GradeDomain.EXACT, GradeDomain.BOUND):
        if a.isdigit() and b.isdigit():
            return str(int(a) + int(b))
        return f"({a} + {b})"
    if domain == GradeDomain.PRESENCE:
        return "true" if ("true" in (a, b)) else ("false" if a == "false" and b == "false" else f"({a} || {b})")
    if domain == GradeDomain.LINEAR:
        if a == "LZero":
            return b
        if b == "LZero":
            return a
        return "LMany"
    if domain == GradeDomain.AFFINE:
        if a == "AZero":
            return b
        if b == "AZero":
            return a
        return "AMany"
    return "Hi" if ("Hi" in (a, b)) else "Lo"


def _mul_grades(domain: GradeDomain | CustomDomainSpec, a: str, b: str) -> str:
    if isinstance(domain, CustomDomainSpec):
        return f"(@mul {domain.rocq_name} {a} {b})"
    if domain in (GradeDomain.EXACT, GradeDomain.BOUND):
        if a.isdigit() and b.isdigit():
            return str(int(a) * int(b))
        return f"({a} * {b})"
    if domain == GradeDomain.PRESENCE:
        return "false" if ("false" in (a, b)) else ("true" if a == "true" and b == "true" else f"({a} && {b})")
    if domain == GradeDomain.LINEAR:
        if "LZero" in (a, b):
            return "LZero"
        if a == "LOne":
            return b
        if b == "LOne":
            return a
        return "LMany"
    if domain == GradeDomain.AFFINE:
        if "AZero" in (a, b):
            return "AZero"
        if a == "AOne":
            return b
        if b == "AOne":
            return a
        return "AMany"
    return "Hi" if (a == "Hi" and b == "Hi") else "Lo"


def _join_grades(domain: GradeDomain | CustomDomainSpec, a: str, b: str) -> str:
    if a == b:
        return a
    if isinstance(domain, CustomDomainSpec):
        return f"(@gjoin {domain.rocq_name} {a} {b})"
    if domain == GradeDomain.BOUND and a.isdigit() and b.isdigit():
        return str(max(int(a), int(b)))
    if domain == GradeDomain.PRESENCE:
        return "true" if ("true" in (a, b)) else "false"
    if domain == GradeDomain.AFFINE:
        order = {"AZero": 0, "AOne": 1, "AMany": 2}
        if a in order and b in order:
            return a if order[a] >= order[b] else b
    if domain == GradeDomain.SECURITY:
        return "Hi" if ("Hi" in (a, b)) else "Lo"
    return a


def _allows_concrete(domain: GradeDomain | CustomDomainSpec, actual: str, expected: str) -> bool:
    if actual == expected:
        return True
    if isinstance(domain, CustomDomainSpec):
        return False
    if domain == GradeDomain.BOUND and actual.isdigit() and expected.isdigit():
        return int(actual) <= int(expected)
    if domain == GradeDomain.PRESENCE:
        return actual == "false" or expected == "true"
    if domain == GradeDomain.AFFINE:
        order = {"AZero": 0, "AOne": 1, "AMany": 2}
        if actual in order and expected in order:
            return order[actual] <= order[expected]
    if domain == GradeDomain.SECURITY:
        return actual == "Lo" or expected == "Hi"
    return False


# ---------------------------------------------------------------------------
# Section 2: Typed Grade Expressions (GExpr)
# ---------------------------------------------------------------------------


class GExpr:
    """Symbolic or concrete grade semiring expression."""

    def has_var(self) -> bool:
        return False

    def has_hole(self) -> bool:
        return False


@dataclass(frozen=True)
class GLit(GExpr):
    value: int | bool | str

    @override
    def has_var(self) -> bool:
        return False


@dataclass(frozen=True)
class GVar(GExpr):
    name: str
    index: int

    @override
    def has_var(self) -> bool:
        return True


@dataclass(frozen=True)
class GAdd(GExpr):
    lhs: GExpr
    rhs: GExpr

    @override
    def has_var(self) -> bool:
        return self.lhs.has_var() or self.rhs.has_var()

    @override
    def has_hole(self) -> bool:
        return self.lhs.has_hole() or self.rhs.has_hole()


@dataclass(frozen=True)
class GMul(GExpr):
    lhs: GExpr
    rhs: GExpr

    @override
    def has_var(self) -> bool:
        return self.lhs.has_var() or self.rhs.has_var()

    @override
    def has_hole(self) -> bool:
        return self.lhs.has_hole() or self.rhs.has_hole()


@dataclass(frozen=True)
class GHole(GExpr):
    hole_id: str
    name: str
    span: tuple[int, ...] = ()

    @override
    def has_hole(self) -> bool:
        return True


def _gzero(domain: GradeDomain | CustomDomainSpec) -> GExpr:
    if isinstance(domain, CustomDomainSpec):
        return GLit(domain.zero_expr)
    return GLit(_domain_spec(domain).zero)


def _gone(domain: GradeDomain | CustomDomainSpec) -> GExpr:
    if isinstance(domain, CustomDomainSpec):
        return GLit(domain.one_expr)
    return GLit(_domain_spec(domain).one)


def _is_gzero(expr: GExpr, domain: GradeDomain | CustomDomainSpec) -> bool:
    if isinstance(expr, GLit):
        lit = _rocq_grade_sort_value(domain, expr.value)
        z = domain.zero_expr if isinstance(domain, CustomDomainSpec) else _domain_spec(domain).zero
        return lit == z
    return False


def _gexpr_subst(expr: GExpr, mapping: Mapping[str, GExpr]) -> GExpr:
    if isinstance(expr, GHole) and expr.hole_id in mapping:
        return mapping[expr.hole_id]
    if isinstance(expr, GAdd):
        return GAdd(_gexpr_subst(expr.lhs, mapping), _gexpr_subst(expr.rhs, mapping))
    if isinstance(expr, GMul):
        return GMul(_gexpr_subst(expr.lhs, mapping), _gexpr_subst(expr.rhs, mapping))
    return expr


def _eval_gexpr(expr: GExpr, domain: GradeDomain | CustomDomainSpec,
                gvar_env: Mapping[int, str] | None = None) -> str:
    if isinstance(expr, GLit):
        return _rocq_grade_sort_value(domain, expr.value)
    if isinstance(expr, GVar):
        if gvar_env is None or expr.index not in gvar_env:
            raise ValueError(f"unbound symbolic grade variable '{expr.name}'")
        return gvar_env[expr.index]
    if isinstance(expr, GAdd):
        return _add_grades(domain, _eval_gexpr(expr.lhs, domain, gvar_env),
                           _eval_gexpr(expr.rhs, domain, gvar_env))
    if isinstance(expr, GMul):
        return _mul_grades(domain, _eval_gexpr(expr.lhs, domain, gvar_env),
                           _eval_gexpr(expr.rhs, domain, gvar_env))
    raise ValueError(f"unsolved grade hole {expr!r}")


def _to_rocq_gexpr(expr: GExpr, domain: GradeDomain | CustomDomainSpec, rocq_dom: str = "_D") -> str:
    if isinstance(expr, GLit):
        return f"(@GLit {rocq_dom} {_rocq_grade_sort_value(domain, expr.value)})"
    if isinstance(expr, GVar):
        return f"(@GVar {rocq_dom} {expr.index})"
    if isinstance(expr, GAdd):
        return f"(@GAdd {rocq_dom} {_to_rocq_gexpr(expr.lhs, domain, rocq_dom)} {_to_rocq_gexpr(expr.rhs, domain, rocq_dom)})"
    if isinstance(expr, GMul):
        return f"(@GMul {rocq_dom} {_to_rocq_gexpr(expr.lhs, domain, rocq_dom)} {_to_rocq_gexpr(expr.rhs, domain, rocq_dom)})"
    raise ValueError(f"cannot serialize unsolved hole {expr!r}")


def _gexpr_add(lhs: GExpr, rhs: GExpr, domain: GradeDomain | CustomDomainSpec) -> GExpr:
    if _is_gzero(lhs, domain):
        return rhs
    if _is_gzero(rhs, domain):
        return lhs
    if isinstance(lhs, GLit) and isinstance(rhs, GLit):
        return GLit(_add_grades(domain, _rocq_grade_sort_value(domain, lhs.value),
                                _rocq_grade_sort_value(domain, rhs.value)))
    return GAdd(lhs, rhs)


def _gexpr_mul(lhs: GExpr, rhs: GExpr, domain: GradeDomain | CustomDomainSpec) -> GExpr:
    if _is_gzero(lhs, domain) or _is_gzero(rhs, domain):
        return _gzero(domain)
    if isinstance(lhs, GLit) and isinstance(rhs, GLit):
        return GLit(_mul_grades(domain, _rocq_grade_sort_value(domain, lhs.value),
                                _rocq_grade_sort_value(domain, rhs.value)))
    return GMul(lhs, rhs)


def _gexpr_join(lhs: GExpr, rhs: GExpr, domain: GradeDomain | CustomDomainSpec) -> GExpr:
    if lhs == rhs:
        return lhs
    if isinstance(lhs, GLit) and isinstance(rhs, GLit):
        return GLit(_join_grades(domain, _rocq_grade_sort_value(domain, lhs.value),
                                 _rocq_grade_sort_value(domain, rhs.value)))
    return lhs


# ---------------------------------------------------------------------------
# Section 3: Typed Python Core IR (Projecting 1-to-1 to GradedCore)
# ---------------------------------------------------------------------------


class IRIdx:
    """Natural index expression in the typed core IR."""


@dataclass(frozen=True)
class IRIdxVar(IRIdx):
    uid: int


@dataclass(frozen=True)
class IRIdxLit(IRIdx):
    value: int


@dataclass(frozen=True)
class IRIdxAdd(IRIdx):
    lhs: IRIdx
    rhs: IRIdx


@dataclass(frozen=True)
class IRIdxProm(IRIdx):
    grade: GExpr
    inner: IRIdx


@dataclass(frozen=True)
class IRIdxUnbox(IRIdx):
    uid: int


@dataclass(frozen=True)
class IRIdxFst(IRIdx):
    uid: int


@dataclass(frozen=True)
class IRIdxSnd(IRIdx):
    uid: int


@dataclass(frozen=True)
class IRIdxCase(IRIdx):
    uid: int
    left_uid: int
    right_uid: int
    left: IRIdx
    right: IRIdx


class IRTy:
    """Graded dependent type expression in the typed core IR."""


@dataclass(frozen=True)
class IRNat(IRTy):
    pass


@dataclass(frozen=True)
class IRBool(IRTy):
    pass


@dataclass(frozen=True)
class IRVec(IRTy):
    elem: IRTy
    length: IRIdx


@dataclass(frozen=True)
class IRUniv(IRTy):
    level: int = 0


@dataclass(frozen=True)
class IRTVar(IRTy):
    uid: int


@dataclass(frozen=True)
class IRTProm(IRTy):
    grade: GExpr
    inner: IRTy


@dataclass(frozen=True)
class IRTUnbox(IRTy):
    uid: int


@dataclass(frozen=True)
class IRPi(IRTy):
    uid: int
    s: GExpr
    r: GExpr | None
    dom: IRTy
    cod: IRTy


@dataclass(frozen=True)
class IRSigma(IRTy):
    uid: int
    r: GExpr
    fst_ty: IRTy
    snd_ty: IRTy
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRBox(IRTy):
    grade: GExpr
    inner: IRTy


@dataclass(frozen=True)
class IRSum(IRTy):
    lhs: IRTy
    rhs: IRTy
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRRecord(IRTy):
    rec_id: int
    fields: tuple[tuple[int, GExpr, IRTy], ...]
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRInd(IRTy):
    ind_id: int
    indices: tuple[IRIdx, ...]
    nominal_name: str | None = None


class IRTerm:
    """Graded dependent term expression in the typed core IR."""


@dataclass(frozen=True)
class IRVar(IRTerm):
    uid: int


@dataclass(frozen=True)
class IRNatVal(IRTerm):
    idx: IRIdx


@dataclass(frozen=True)
class IRBoolVal(IRTerm):
    value: bool


@dataclass(frozen=True)
class IRTypeVal(IRTerm):
    ty: IRTy


@dataclass(frozen=True)
class IRLam(IRTerm):
    uid: int
    name: str
    span: tuple[int, ...]
    s: GExpr
    r: GExpr | None
    dom: IRTy
    body: IRTerm
    explicit_r: bool = False


@dataclass(frozen=True)
class IRApp(IRTerm):
    fn: IRTerm
    arg: IRTerm


@dataclass(frozen=True)
class IRLet(IRTerm):
    uid: int
    name: str
    span: tuple[int, ...]
    s: GExpr
    r: GExpr | None
    ann: IRTy
    rhs: IRTerm
    body: IRTerm
    explicit_r: bool = False


@dataclass(frozen=True)
class IRPair(IRTerm):
    uid: int
    r: GExpr
    fst_ty: IRTy
    snd_ty: IRTy
    fst_val: IRTerm
    snd_val: IRTerm
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRLetPair(IRTerm):
    x_uid: int
    y_uid: int
    x_name: str
    y_name: str
    x_span: tuple[int, ...]
    y_span: tuple[int, ...]
    s: GExpr
    kappa: GExpr
    motive_uid: int
    motive: IRTy
    pair: IRTerm
    body: IRTerm


@dataclass(frozen=True)
class IRPromote(IRTerm):
    grade: GExpr
    val: IRTerm


@dataclass(frozen=True)
class IRLetBox(IRTerm):
    x_uid: int
    x_name: str
    x_span: tuple[int, ...]
    kappa: GExpr
    motive_uid: int
    motive: IRTy
    box_term: IRTerm
    body: IRTerm


@dataclass(frozen=True)
class IRInl(IRTerm):
    rhs_ty: IRTy
    val: IRTerm
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRInr(IRTerm):
    lhs_ty: IRTy
    val: IRTerm
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRMatchSum(IRTerm):
    x_uid: int
    y_uid: int
    x_name: str
    y_name: str
    x_span: tuple[int, ...]
    y_span: tuple[int, ...]
    s: GExpr
    kappa: GExpr
    motive_uid: int
    motive: IRTy
    scrut: IRTerm
    lbranch: IRTerm
    rbranch: IRTerm


@dataclass(frozen=True)
class IRIf(IRTerm):
    cond: IRTerm
    then_br: IRTerm
    else_br: IRTerm


@dataclass(frozen=True)
class IRRecordMk(IRTerm):
    rec_id: int
    fields: tuple[tuple[int, GExpr, IRTy, IRTerm], ...]
    nominal_name: str | None = None


@dataclass(frozen=True)
class IRMatchRecord(IRTerm):
    rec_id: int
    s: GExpr
    motive_uid: int
    motive: IRTy
    scrut: IRTerm
    binders: tuple[tuple[int, str, tuple[int, ...]], ...]
    body: IRTerm


@dataclass(frozen=True)
class IRSubgrade(IRTerm):
    target: IRTy
    body: IRTerm


@dataclass(frozen=True)
class IRFix(IRTerm):
    n_uid: int
    rec_uid: int
    n_name: str
    rec_name: str
    n_span: tuple[int, ...]
    rec_span: tuple[int, ...]
    s_rec: GExpr
    motive_uid: int
    motive: IRTy
    scrut: IRTerm
    base: IRTerm
    step: IRTerm


def _db_idx(env_uids: list[int], uid: int) -> int:
    # env_uids stores binders innermost-first (index 0 = innermost).
    try:
        return env_uids.index(uid)
    except ValueError as err:
        raise ValueError(f"internal IR scoping error: binder uid {uid} not in scope {env_uids}") from err


def _subst_gexpr_idx(idx: IRIdx, mapping: Mapping[str, GExpr]) -> IRIdx:
    if isinstance(idx, (IRIdxVar, IRIdxLit, IRIdxUnbox, IRIdxFst, IRIdxSnd)):
        return idx
    if isinstance(idx, IRIdxAdd):
        return IRIdxAdd(_subst_gexpr_idx(idx.lhs, mapping), _subst_gexpr_idx(idx.rhs, mapping))
    if isinstance(idx, IRIdxProm):
        return IRIdxProm(_gexpr_subst(idx.grade, mapping), _subst_gexpr_idx(idx.inner, mapping))
    if isinstance(idx, IRIdxCase):
        return IRIdxCase(idx.uid, idx.left_uid, idx.right_uid,
                         _subst_gexpr_idx(idx.left, mapping), _subst_gexpr_idx(idx.right, mapping))
    return idx


def _subst_gexpr_ty(ty: IRTy, mapping: Mapping[str, GExpr]) -> IRTy:
    if isinstance(ty, (IRNat, IRBool, IRUniv, IRTVar, IRTUnbox)):
        return ty
    if isinstance(ty, IRVec):
        return IRVec(_subst_gexpr_ty(ty.elem, mapping), _subst_gexpr_idx(ty.length, mapping))
    if isinstance(ty, IRTProm):
        return IRTProm(_gexpr_subst(ty.grade, mapping), _subst_gexpr_ty(ty.inner, mapping))
    if isinstance(ty, IRPi):
        return IRPi(
            ty.uid,
            _gexpr_subst(ty.s, mapping),
            None if ty.r is None else _gexpr_subst(ty.r, mapping),
            _subst_gexpr_ty(ty.dom, mapping),
            _subst_gexpr_ty(ty.cod, mapping),
        )
    if isinstance(ty, IRSigma):
        return IRSigma(ty.uid, _gexpr_subst(ty.r, mapping),
                       _subst_gexpr_ty(ty.fst_ty, mapping), _subst_gexpr_ty(ty.snd_ty, mapping),
                       ty.nominal_name)
    if isinstance(ty, IRBox):
        return IRBox(_gexpr_subst(ty.grade, mapping), _subst_gexpr_ty(ty.inner, mapping))
    if isinstance(ty, IRSum):
        return IRSum(_subst_gexpr_ty(ty.lhs, mapping), _subst_gexpr_ty(ty.rhs, mapping), ty.nominal_name)
    if isinstance(ty, IRRecord):
        return IRRecord(ty.rec_id, tuple((fn, _gexpr_subst(fg, mapping), _subst_gexpr_ty(ft, mapping))
                                         for fn, fg, ft in ty.fields), ty.nominal_name)
    if isinstance(ty, IRInd):
        return IRInd(ty.ind_id, tuple(_subst_gexpr_idx(i, mapping) for i in ty.indices), ty.nominal_name)
    return ty


def _subst_gexpr_term(term: IRTerm, mapping: Mapping[str, GExpr]) -> IRTerm:
    if isinstance(term, (IRVar, IRBoolVal)):
        return term
    if isinstance(term, IRNatVal):
        return IRNatVal(_subst_gexpr_idx(term.idx, mapping))
    if isinstance(term, IRTypeVal):
        return IRTypeVal(_subst_gexpr_ty(term.ty, mapping))
    if isinstance(term, IRLam):
        return IRLam(term.uid, term.name, term.span,
                     _gexpr_subst(term.s, mapping),
                     None if term.r is None else _gexpr_subst(term.r, mapping),
                     _subst_gexpr_ty(term.dom, mapping),
                     _subst_gexpr_term(term.body, mapping),
                     term.explicit_r)
    if isinstance(term, IRApp):
        return IRApp(_subst_gexpr_term(term.fn, mapping), _subst_gexpr_term(term.arg, mapping))
    if isinstance(term, IRLet):
        return IRLet(term.uid, term.name, term.span,
                     _gexpr_subst(term.s, mapping),
                     None if term.r is None else _gexpr_subst(term.r, mapping),
                     _subst_gexpr_ty(term.ann, mapping),
                     _subst_gexpr_term(term.rhs, mapping),
                     _subst_gexpr_term(term.body, mapping),
                     term.explicit_r)
    if isinstance(term, IRPair):
        return IRPair(term.uid, _gexpr_subst(term.r, mapping),
                      _subst_gexpr_ty(term.fst_ty, mapping), _subst_gexpr_ty(term.snd_ty, mapping),
                      _subst_gexpr_term(term.fst_val, mapping), _subst_gexpr_term(term.snd_val, mapping),
                      term.nominal_name)
    if isinstance(term, IRLetPair):
        return IRLetPair(term.x_uid, term.y_uid, term.x_name, term.y_name, term.x_span, term.y_span,
                         _gexpr_subst(term.s, mapping), _gexpr_subst(term.kappa, mapping),
                         term.motive_uid, _subst_gexpr_ty(term.motive, mapping),
                         _subst_gexpr_term(term.pair, mapping), _subst_gexpr_term(term.body, mapping))
    if isinstance(term, IRPromote):
        return IRPromote(_gexpr_subst(term.grade, mapping), _subst_gexpr_term(term.val, mapping))
    if isinstance(term, IRLetBox):
        return IRLetBox(term.x_uid, term.x_name, term.x_span, _gexpr_subst(term.kappa, mapping),
                        term.motive_uid, _subst_gexpr_ty(term.motive, mapping),
                        _subst_gexpr_term(term.box_term, mapping), _subst_gexpr_term(term.body, mapping))
    if isinstance(term, IRInl):
        return IRInl(_subst_gexpr_ty(term.rhs_ty, mapping), _subst_gexpr_term(term.val, mapping), term.nominal_name)
    if isinstance(term, IRInr):
        return IRInr(_subst_gexpr_ty(term.lhs_ty, mapping), _subst_gexpr_term(term.val, mapping), term.nominal_name)
    if isinstance(term, IRMatchSum):
        return IRMatchSum(term.x_uid, term.y_uid, term.x_name, term.y_name, term.x_span, term.y_span,
                          _gexpr_subst(term.s, mapping), _gexpr_subst(term.kappa, mapping),
                          term.motive_uid, _subst_gexpr_ty(term.motive, mapping),
                          _subst_gexpr_term(term.scrut, mapping),
                          _subst_gexpr_term(term.lbranch, mapping),
                          _subst_gexpr_term(term.rbranch, mapping))
    if isinstance(term, IRIf):
        return IRIf(_subst_gexpr_term(term.cond, mapping),
                    _subst_gexpr_term(term.then_br, mapping),
                    _subst_gexpr_term(term.else_br, mapping))
    if isinstance(term, IRRecordMk):
        return IRRecordMk(
            term.rec_id,
            tuple((fn, _gexpr_subst(fg, mapping), _subst_gexpr_ty(ft, mapping), _subst_gexpr_term(fv, mapping))
                  for fn, fg, ft, fv in term.fields),
            term.nominal_name,
        )
    if isinstance(term, IRMatchRecord):
        return IRMatchRecord(term.rec_id, _gexpr_subst(term.s, mapping),
                             term.motive_uid, _subst_gexpr_ty(term.motive, mapping),
                             _subst_gexpr_term(term.scrut, mapping), term.binders,
                             _subst_gexpr_term(term.body, mapping))
    if isinstance(term, IRSubgrade):
        return IRSubgrade(_subst_gexpr_ty(term.target, mapping), _subst_gexpr_term(term.body, mapping))
    if isinstance(term, IRFix):
        return IRFix(term.n_uid, term.rec_uid, term.n_name, term.rec_name, term.n_span, term.rec_span,
                     _gexpr_subst(term.s_rec, mapping), term.motive_uid, _subst_gexpr_ty(term.motive, mapping),
                     _subst_gexpr_term(term.scrut, mapping),
                     _subst_gexpr_term(term.base, mapping),
                     _subst_gexpr_term(term.step, mapping))
    return term


def _subst_uid_idx(idx: IRIdx, target_uid: int, rep_idx: IRIdx) -> IRIdx:
    if isinstance(idx, IRIdxVar):
        return rep_idx if idx.uid == target_uid else idx
    if isinstance(idx, IRIdxLit):
        return idx
    if isinstance(idx, IRIdxAdd):
        return IRIdxAdd(_subst_uid_idx(idx.lhs, target_uid, rep_idx), _subst_uid_idx(idx.rhs, target_uid, rep_idx))
    if isinstance(idx, IRIdxProm):
        return IRIdxProm(idx.grade, _subst_uid_idx(idx.inner, target_uid, rep_idx))
    if isinstance(idx, (IRIdxUnbox, IRIdxFst, IRIdxSnd)):
        if idx.uid == target_uid and isinstance(rep_idx, IRIdxVar):
            return type(idx)(rep_idx.uid)
        return idx
    if isinstance(idx, IRIdxCase):
        scrut_uid = rep_idx.uid if idx.uid == target_uid and isinstance(rep_idx, IRIdxVar) else idx.uid
        return IRIdxCase(
            scrut_uid,
            idx.left_uid,
            idx.right_uid,
            _subst_uid_idx(idx.left, target_uid, rep_idx),
            _subst_uid_idx(idx.right, target_uid, rep_idx),
        )
    return idx


def _subst_uid_ty(ty: IRTy, target_uid: int, rep_ty: IRTy | None = None, rep_idx: IRIdx | None = None) -> IRTy:
    if isinstance(ty, (IRNat, IRBool, IRUniv)):
        return ty
    if isinstance(ty, IRVec):
        new_len = _subst_uid_idx(ty.length, target_uid, rep_idx) if rep_idx is not None else ty.length
        return IRVec(_subst_uid_ty(ty.elem, target_uid, rep_ty, rep_idx), new_len)
    if isinstance(ty, IRTVar):
        return rep_ty if (ty.uid == target_uid and rep_ty is not None) else ty
    if isinstance(ty, IRTProm):
        return IRTProm(ty.grade, _subst_uid_ty(ty.inner, target_uid, rep_ty, rep_idx))
    if isinstance(ty, IRTUnbox):
        return ty
    if isinstance(ty, IRPi):
        return IRPi(
            ty.uid,
            ty.s,
            ty.r,
            _subst_uid_ty(ty.dom, target_uid, rep_ty, rep_idx),
            ty.cod if ty.uid == target_uid else _subst_uid_ty(ty.cod, target_uid, rep_ty, rep_idx),
        )
    if isinstance(ty, IRSigma):
        return IRSigma(
            ty.uid,
            ty.r,
            _subst_uid_ty(ty.fst_ty, target_uid, rep_ty, rep_idx),
            ty.snd_ty if ty.uid == target_uid else _subst_uid_ty(ty.snd_ty, target_uid, rep_ty, rep_idx),
            ty.nominal_name,
        )
    if isinstance(ty, IRBox):
        return IRBox(ty.grade, _subst_uid_ty(ty.inner, target_uid, rep_ty, rep_idx))
    if isinstance(ty, IRSum):
        return IRSum(
            _subst_uid_ty(ty.lhs, target_uid, rep_ty, rep_idx),
            _subst_uid_ty(ty.rhs, target_uid, rep_ty, rep_idx),
            ty.nominal_name,
        )
    if isinstance(ty, IRRecord):
        return IRRecord(
            ty.rec_id,
            tuple((fn, fg, _subst_uid_ty(ft, target_uid, rep_ty, rep_idx)) for fn, fg, ft in ty.fields),
            ty.nominal_name,
        )
    if isinstance(ty, IRInd):
        return IRInd(
            ty.ind_id,
            tuple(_subst_uid_idx(i, target_uid, rep_idx) if rep_idx is not None else i for i in ty.indices),
            ty.nominal_name,
        )
    return ty


@dataclass
class _IRAnalyzer:
    """Computes computation and type-use demands mirroring `GradedCore.core_infer`."""

    domain: GradeDomain | CustomDomainSpec
    gvar_env: Mapping[int, str] | None = None
    env_types: dict[int, IRTy] = field(default_factory=dict)
    infer_holes: bool = False
    constraints: list[gi.GradeConstraint] = field(default_factory=list)

    def zero(self) -> GExpr:
        return _gzero(self.domain)

    def one(self) -> GExpr:
        return _gone(self.domain)

    def add(self, a: GExpr, b: GExpr) -> GExpr:
        return _gexpr_add(a, b, self.domain)

    def mul(self, a: GExpr, b: GExpr) -> GExpr:
        return _gexpr_mul(a, b, self.domain)

    def add_maps(self, a: dict[int, GExpr], b: dict[int, GExpr]) -> dict[int, GExpr]:
        out = dict(a)
        for uid, val in b.items():
            out[uid] = self.add(out[uid], val) if uid in out else val
        return out

    def scale_map(self, q: GExpr, a: dict[int, GExpr]) -> dict[int, GExpr]:
        if _is_gzero(q, self.domain):
            return {}
        return {uid: self.mul(q, val) for uid, val in a.items()}

    def branch_map(self, a: dict[int, GExpr], b: dict[int, GExpr]) -> dict[int, GExpr]:
        keys = set(a) | set(b)
        out: dict[int, GExpr] = {}
        for uid in keys:
            va = a.get(uid, self.zero())
            vb = b.get(uid, self.zero())
            out[uid] = _gexpr_join(va, vb, self.domain)
        return out

    def idx_demand(self, idx: IRIdx) -> dict[int, GExpr]:
        if isinstance(idx, (IRIdxVar, IRIdxUnbox, IRIdxFst, IRIdxSnd)):
            return {idx.uid: self.one()}
        if isinstance(idx, IRIdxLit):
            return {}
        if isinstance(idx, IRIdxAdd):
            return self.add_maps(self.idx_demand(idx.lhs), self.idx_demand(idx.rhs))
        if isinstance(idx, IRIdxProm):
            return self.scale_map(idx.grade, self.idx_demand(idx.inner))
        if isinstance(idx, IRIdxCase):
            dl = self.idx_demand(idx.left)
            dr = self.idx_demand(idx.right)
            ul = dl.pop(idx.left_uid, self.zero())
            ur = dr.pop(idx.right_uid, self.zero())
            s = _gexpr_join(ul, ur, self.domain)
            if _is_gzero(s, self.domain):
                s = self.one()
            return self.add_maps({idx.uid: s}, self.branch_map(dl, dr))
        return {}

    def ty_demand(self, ty: IRTy) -> dict[int, GExpr]:
        if isinstance(ty, (IRNat, IRBool, IRUniv)):
            return {}
        if isinstance(ty, IRVec):
            return self.add_maps(self.ty_demand(ty.elem), self.idx_demand(ty.length))
        if isinstance(ty, (IRTVar, IRTUnbox)):
            return {ty.uid: self.one()}
        if isinstance(ty, IRTProm):
            return self.scale_map(ty.grade, self.ty_demand(ty.inner))
        if isinstance(ty, IRPi):
            da = self.ty_demand(ty.dom)
            old = self.env_types.get(ty.uid)
            self.env_types[ty.uid] = ty.dom
            db = self.ty_demand(ty.cod)
            if old is None:
                self.env_types.pop(ty.uid, None)
            else:
                self.env_types[ty.uid] = old
            db.pop(ty.uid, None)
            return self.add_maps(da, db)
        if isinstance(ty, IRSigma):
            da = self.ty_demand(ty.fst_ty)
            old = self.env_types.get(ty.uid)
            self.env_types[ty.uid] = ty.fst_ty
            db = self.ty_demand(ty.snd_ty)
            if old is None:
                self.env_types.pop(ty.uid, None)
            else:
                self.env_types[ty.uid] = old
            db.pop(ty.uid, None)
            return self.add_maps(da, db)
        if isinstance(ty, IRBox):
            return self.ty_demand(ty.inner)
        if isinstance(ty, IRSum):
            return self.add_maps(self.ty_demand(ty.lhs), self.ty_demand(ty.rhs))
        if isinstance(ty, IRRecord):
            out: dict[int, GExpr] = {}
            for _, _, ft in ty.fields:
                out = self.add_maps(out, self.ty_demand(ft))
            return out
        if isinstance(ty, IRInd):
            out = {}
            for i in ty.indices:
                out = self.add_maps(out, self.idx_demand(i))
            return out
        return {}

    def _app_ty(self, dom: IRTy, cod: IRTy, arg: IRTerm, binder_uid: int) -> IRTy:
        if isinstance(dom, IRNat):
            if isinstance(arg, IRNatVal):
                return _subst_uid_ty(cod, binder_uid, rep_idx=arg.idx)
            if isinstance(arg, IRVar):
                return _subst_uid_ty(cod, binder_uid, rep_idx=IRIdxVar(arg.uid))
        elif isinstance(dom, IRUniv):
            if isinstance(arg, IRTypeVal):
                return _subst_uid_ty(cod, binder_uid, rep_ty=arg.ty)
            if isinstance(arg, IRVar):
                return _subst_uid_ty(cod, binder_uid, rep_ty=IRTVar(arg.uid))
        elif isinstance(arg, IRVar):
            return _subst_uid_ty(cod, binder_uid, rep_idx=IRIdxVar(arg.uid), rep_ty=IRTVar(arg.uid))
        return _subst_uid_ty(cod, binder_uid)

    def _ty_uses_uid(self, ty: IRTy, uid: int) -> bool:
        return uid in self.ty_demand(ty)

    def infer(self, term: IRTerm) -> tuple[IRTy, dict[int, GExpr], dict[int, GExpr]]:
        """Return `(result_type, comp_demand_by_uid, type_demand_by_uid)`."""
        if isinstance(term, IRVar):
            ann = self.env_types.get(term.uid)
            if ann is None:
                return IRNat(), {term.uid: self.one()}, {}
            return ann, {term.uid: self.one()}, self.ty_demand(ann)
        if isinstance(term, IRNatVal):
            return IRNat(), self.idx_demand(term.idx), {}
        if isinstance(term, IRBoolVal):
            return IRBool(), {}, {}
        if isinstance(term, IRTypeVal):
            lvl = term.ty.level + 1 if isinstance(term.ty, IRUniv) else 0
            return IRUniv(lvl), {}, self.ty_demand(term.ty)
        if isinstance(term, IRLam):
            a_dem = self.ty_demand(term.dom)
            old = self.env_types.get(term.uid)
            self.env_types[term.uid] = term.dom
            res_ty, u_b, v_b = self.infer(term.body)
            if old is None:
                self.env_types.pop(term.uid, None)
            else:
                self.env_types[term.uid] = old
            u_b.pop(term.uid, self.zero())
            actual_r = v_b.pop(term.uid, self.zero())
            r_eff = actual_r if term.r is None else term.r
            return (
                IRPi(term.uid, term.s, r_eff, term.dom, res_ty),
                u_b,
                self.add_maps(a_dem, v_b),
            )
        if isinstance(term, IRApp):
            fn_ty, u_fn, v_fn = self.infer(term.fn)
            arg_ty, u_arg, v_arg = self.infer(term.arg)
            if isinstance(fn_ty, IRPi):
                b_dem = self.ty_demand(fn_ty.cod)
                b_dem.pop(fn_ty.uid, None)
                res_ty = self._app_ty(fn_ty.dom, fn_ty.cod, term.arg, fn_ty.uid)
                r_eff = fn_ty.r if fn_ty.r is not None else self.zero()
                z_ty = v_arg if isinstance(fn_ty.dom, IRUniv) and isinstance(term.arg, IRTypeVal) else u_arg
                return (
                    res_ty,
                    self.add_maps(u_fn, self.scale_map(fn_ty.s, u_arg)),
                    self.add_maps(b_dem, self.scale_map(r_eff, z_ty)),
                )
            return arg_ty, self.add_maps(u_fn, u_arg), self.add_maps(v_fn, v_arg)
        if isinstance(term, IRLet):
            _, u_rhs, v_rhs = self.infer(term.rhs)
            old = self.env_types.get(term.uid)
            self.env_types[term.uid] = term.ann
            bod_ty, u_bod, v_bod = self.infer(term.body)
            if old is None:
                self.env_types.pop(term.uid, None)
            else:
                self.env_types[term.uid] = old
            u_bod.pop(term.uid, None)
            actual_r = v_bod.pop(term.uid, self.zero())
            r_eff = actual_r if term.r is None else term.r
            z_ty = v_rhs if isinstance(term.ann, IRUniv) and isinstance(term.rhs, IRTypeVal) else u_rhs
            out_ty = self._app_ty(term.ann, bod_ty, term.rhs, term.uid) if term.uid in self.ty_demand(bod_ty) else bod_ty
            return (
                out_ty,
                self.add_maps(u_bod, self.scale_map(term.s, u_rhs)),
                self.add_maps(v_bod, self.scale_map(r_eff, z_ty)),
            )
        if isinstance(term, IRPair):
            _, u_l, _ = self.infer(term.fst_val)
            _, u_r, _ = self.infer(term.snd_val)
            da = self.ty_demand(term.fst_ty)
            old = self.env_types.get(term.uid)
            self.env_types[term.uid] = term.fst_ty
            db = self.ty_demand(term.snd_ty)
            if old is None:
                self.env_types.pop(term.uid, None)
            else:
                self.env_types[term.uid] = old
            db.pop(term.uid, None)
            return (
                IRSigma(term.uid, term.r, term.fst_ty, term.snd_ty, term.nominal_name),
                self.add_maps(u_l, u_r),
                self.add_maps(da, db),
            )
        if isinstance(term, IRLetPair):
            p_ty, u_p, _ = self.infer(term.pair)
            v_mot = self.ty_demand(term.motive)
            v_mot.pop(term.motive_uid, None)
            fst_ty = p_ty.fst_ty if isinstance(p_ty, IRSigma) else IRNat()
            snd_ty = p_ty.snd_ty if isinstance(p_ty, IRSigma) else IRNat()
            if isinstance(p_ty, IRSigma):
                snd_ty = _subst_uid_ty(snd_ty, p_ty.uid, rep_idx=IRIdxVar(term.x_uid), rep_ty=IRTVar(term.x_uid))
            old_x, old_y = self.env_types.get(term.x_uid), self.env_types.get(term.y_uid)
            self.env_types[term.x_uid] = fst_ty
            self.env_types[term.y_uid] = snd_ty
            _, u_b, _ = self.infer(term.body)
            for uid, prev in ((term.x_uid, old_x), (term.y_uid, old_y)):
                if prev is None:
                    self.env_types.pop(uid, None)
                else:
                    self.env_types[uid] = prev
            u_b.pop(term.x_uid, None)
            u_b.pop(term.y_uid, None)
            res_ty = self._spec_pair_subj(term.pair, term.motive, term.motive_uid)
            return (
                res_ty,
                self.add_maps(u_b, self.scale_map(term.s, u_p)),
                self.add_maps(v_mot, self.scale_map(term.kappa, u_p)),
            )
        if isinstance(term, IRPromote):
            t_v, u_v, v_v = self.infer(term.val)
            return IRBox(term.grade, t_v), self.scale_map(term.grade, u_v), v_v
        if isinstance(term, IRLetBox):
            bx_ty, u_bx, v_bx = self.infer(term.box_term)
            v_mot = self.ty_demand(term.motive)
            v_mot.pop(term.motive_uid, None)
            inner_ty = bx_ty.inner if isinstance(bx_ty, IRBox) else IRNat()
            q = bx_ty.grade if isinstance(bx_ty, IRBox) else self.one()
            old = self.env_types.get(term.x_uid)
            self.env_types[term.x_uid] = inner_ty
            _, u_b, _ = self.infer(term.body)
            if old is None:
                self.env_types.pop(term.x_uid, None)
            else:
                self.env_types[term.x_uid] = old
            u_b.pop(term.x_uid, None)
            res_ty = self._spec_box_subj(term.box_term, term.motive, term.motive_uid)
            z_ty = self.scale_map(q, v_bx) if isinstance(term.box_term, IRPromote) and isinstance(term.box_term.val, IRTypeVal) else u_bx
            return (
                res_ty,
                self.add_maps(u_b, u_bx),
                self.add_maps(v_mot, self.scale_map(term.kappa, z_ty)),
            )
        if isinstance(term, IRInl):
            lhs_ty, u_v, v_v = self.infer(term.val)
            return IRSum(lhs_ty, term.rhs_ty, term.nominal_name), u_v, self.add_maps(v_v, self.ty_demand(term.rhs_ty))
        if isinstance(term, IRInr):
            rhs_ty, u_v, v_v = self.infer(term.val)
            return IRSum(term.lhs_ty, rhs_ty, term.nominal_name), u_v, self.add_maps(self.ty_demand(term.lhs_ty), v_v)
        if isinstance(term, IRMatchSum):
            s_ty, u_s, _ = self.infer(term.scrut)
            v_mot = self.ty_demand(term.motive)
            v_mot.pop(term.motive_uid, None)
            a_ty = s_ty.lhs if isinstance(s_ty, IRSum) else IRNat()
            b_ty = s_ty.rhs if isinstance(s_ty, IRSum) else IRNat()
            old_x, old_y = self.env_types.get(term.x_uid), self.env_types.get(term.y_uid)
            self.env_types[term.x_uid] = a_ty
            _, u_l, _ = self.infer(term.lbranch)
            self.env_types[term.y_uid] = b_ty
            _, u_r, _ = self.infer(term.rbranch)
            for uid, prev in ((term.x_uid, old_x), (term.y_uid, old_y)):
                if prev is None:
                    self.env_types.pop(uid, None)
                else:
                    self.env_types[uid] = prev
            u_l.pop(term.x_uid, None)
            u_r.pop(term.y_uid, None)
            return (
                self._spec_sum_subj(term.scrut, term.motive, term.motive_uid),
                self.add_maps(self.scale_map(term.s, u_s), self.branch_map(u_l, u_r)),
                self.add_maps(v_mot, self.scale_map(term.kappa, u_s)),
            )
        if isinstance(term, IRIf):
            _, u_c, _ = self.infer(term.cond)
            t_t, u_t, v_t = self.infer(term.then_br)
            _, u_e, v_e = self.infer(term.else_br)
            return t_t, self.add_maps(u_c, self.branch_map(u_t, u_e)), self.branch_map(v_t, v_e)
        if isinstance(term, IRRecordMk):
            u_all: dict[int, GExpr] = {}
            v_all: dict[int, GExpr] = {}
            fields_ty: list[tuple[int, GExpr, IRTy]] = []
            for fn, fg, ft, fv in term.fields:
                _, u_v, _ = self.infer(fv)
                u_all = self.add_maps(u_all, self.scale_map(fg, u_v))
                v_all = self.add_maps(v_all, self.ty_demand(ft))
                fields_ty.append((fn, fg, ft))
            return IRRecord(term.rec_id, tuple(fields_ty), term.nominal_name), u_all, v_all
        if isinstance(term, IRMatchRecord):
            r_ty, u_s, _ = self.infer(term.scrut)
            v_mot = self.ty_demand(term.motive)
            saved: dict[int, IRTy | None] = {}
            fields = r_ty.fields if isinstance(r_ty, IRRecord) else ()
            for (b_uid, _, _), (_, _, ft) in zip(term.binders, fields, strict=False):
                saved[b_uid] = self.env_types.get(b_uid)
                self.env_types[b_uid] = ft
            _, u_b, _ = self.infer(term.body)
            for b_uid, prev in saved.items():
                if prev is None:
                    self.env_types.pop(b_uid, None)
                else:
                    self.env_types[b_uid] = prev
                u_b.pop(b_uid, None)
            return term.motive, self.add_maps(self.scale_map(term.s, u_s), u_b), v_mot
        if isinstance(term, IRSubgrade):
            _, u_b, _ = self.infer(term.body)
            return term.target, u_b, self.ty_demand(term.target)
        if isinstance(term, IRFix):
            _, u_s, _ = self.infer(term.scrut)
            old_n = self.env_types.get(term.n_uid)
            self.env_types[term.n_uid] = IRNat()
            v_mot = self.ty_demand(term.motive)
            n_r = v_mot.pop(term.n_uid, self.zero())
            _, u_b, _ = self.infer(term.base)
            old_rec = self.env_types.get(term.rec_uid)
            self.env_types[term.rec_uid] = term.motive
            _, u_st, _ = self.infer(term.step)
            for uid, prev in ((term.n_uid, old_n), (term.rec_uid, old_rec)):
                if prev is None:
                    self.env_types.pop(uid, None)
                else:
                    self.env_types[uid] = prev
            u_st.pop(term.n_uid, None)
            u_st.pop(term.rec_uid, None)
            return (
                self._spec_fix_subj(term.scrut, term.motive, term.motive_uid),
                self.add_maps(u_s, self.add_maps(u_b, self.scale_map(term.s_rec, u_st))),
                self.add_maps(v_mot, self.scale_map(n_r, u_s)),
            )
        return IRNat(), {}, {}

    def _spec_pair_subj(self, pair: IRTerm, motive: IRTy, mot_uid: int) -> IRTy:
        if isinstance(pair, IRPair):
            fv = pair.fst_val.idx if isinstance(pair.fst_val, IRNatVal) else (
                IRIdxVar(pair.fst_val.uid) if isinstance(pair.fst_val, IRVar) else None
            )
            sv = pair.snd_val.idx if isinstance(pair.snd_val, IRNatVal) else (
                IRIdxVar(pair.snd_val.uid) if isinstance(pair.snd_val, IRVar) else None
            )
            if fv is not None and sv is not None:
                return self._subst_pair_ty(motive, mot_uid, fv, sv)
        elif isinstance(pair, IRVar):
            return _subst_uid_ty(motive, mot_uid, rep_idx=IRIdxVar(pair.uid), rep_ty=IRTVar(pair.uid))
        return motive

    def _subst_pair_ty(self, ty: IRTy, mot_uid: int, fst_i: IRIdx, snd_i: IRIdx) -> IRTy:
        # Replace Fst/Snd of mot_uid cleanly without string substitution.
        def subst_idx(i: IRIdx) -> IRIdx:
            if isinstance(i, IRIdxFst) and i.uid == mot_uid:
                return fst_i
            if isinstance(i, IRIdxSnd) and i.uid == mot_uid:
                return snd_i
            if isinstance(i, IRIdxAdd):
                return IRIdxAdd(subst_idx(i.lhs), subst_idx(i.rhs))
            if isinstance(i, IRIdxProm):
                return IRIdxProm(i.grade, subst_idx(i.inner))
            if isinstance(i, IRIdxCase):
                return IRIdxCase(i.uid, i.left_uid, i.right_uid, subst_idx(i.left), subst_idx(i.right))
            return i

        if isinstance(ty, IRVec):
            return IRVec(self._subst_pair_ty(ty.elem, mot_uid, fst_i, snd_i), subst_idx(ty.length))
        if isinstance(ty, IRPi):
            return IRPi(ty.uid, ty.s, ty.r,
                        self._subst_pair_ty(ty.dom, mot_uid, fst_i, snd_i),
                        self._subst_pair_ty(ty.cod, mot_uid, fst_i, snd_i))
        if isinstance(ty, IRSigma):
            return IRSigma(ty.uid, ty.r,
                           self._subst_pair_ty(ty.fst_ty, mot_uid, fst_i, snd_i),
                           self._subst_pair_ty(ty.snd_ty, mot_uid, fst_i, snd_i),
                           ty.nominal_name)
        if isinstance(ty, (IRBox, IRTProm)):
            return type(ty)(ty.grade, self._subst_pair_ty(ty.inner, mot_uid, fst_i, snd_i))
        if isinstance(ty, IRSum):
            return IRSum(self._subst_pair_ty(ty.lhs, mot_uid, fst_i, snd_i),
                         self._subst_pair_ty(ty.rhs, mot_uid, fst_i, snd_i), ty.nominal_name)
        if isinstance(ty, IRInd):
            return IRInd(ty.ind_id, tuple(subst_idx(i) for i in ty.indices), ty.nominal_name)
        return ty

    def _spec_box_subj(self, box_term: IRTerm, motive: IRTy, mot_uid: int) -> IRTy:
        if isinstance(box_term, IRPromote):
            if isinstance(box_term.val, IRNatVal):
                return self._subst_box_nat_ty(motive, mot_uid, box_term.grade, box_term.val.idx)
            if isinstance(box_term.val, IRTypeVal):
                return self._subst_box_ty_ty(motive, mot_uid, box_term.grade, box_term.val.ty)
            if isinstance(box_term.val, IRVar):
                return self._subst_box_nat_ty(motive, mot_uid, box_term.grade, IRIdxVar(box_term.val.uid))
        elif isinstance(box_term, IRVar):
            return _subst_uid_ty(motive, mot_uid, rep_idx=IRIdxVar(box_term.uid), rep_ty=IRTVar(box_term.uid))
        return motive

    def _subst_box_nat_ty(self, ty: IRTy, mot_uid: int, q: GExpr, val: IRIdx) -> IRTy:
        def subst_idx(i: IRIdx) -> IRIdx:
            if isinstance(i, IRIdxUnbox) and i.uid == mot_uid:
                return IRIdxProm(q, val)
            if isinstance(i, IRIdxAdd):
                return IRIdxAdd(subst_idx(i.lhs), subst_idx(i.rhs))
            if isinstance(i, IRIdxProm):
                return IRIdxProm(i.grade, subst_idx(i.inner))
            return i

        if isinstance(ty, IRVec):
            return IRVec(self._subst_box_nat_ty(ty.elem, mot_uid, q, val), subst_idx(ty.length))
        if isinstance(ty, IRPi):
            return IRPi(ty.uid, ty.s, ty.r,
                        self._subst_box_nat_ty(ty.dom, mot_uid, q, val),
                        self._subst_box_nat_ty(ty.cod, mot_uid, q, val))
        if isinstance(ty, IRSigma):
            return IRSigma(ty.uid, ty.r,
                           self._subst_box_nat_ty(ty.fst_ty, mot_uid, q, val),
                           self._subst_box_nat_ty(ty.snd_ty, mot_uid, q, val),
                           ty.nominal_name)
        if isinstance(ty, (IRBox, IRTProm)):
            return type(ty)(ty.grade, self._subst_box_nat_ty(ty.inner, mot_uid, q, val))
        if isinstance(ty, IRSum):
            return IRSum(self._subst_box_nat_ty(ty.lhs, mot_uid, q, val),
                         self._subst_box_nat_ty(ty.rhs, mot_uid, q, val), ty.nominal_name)
        if isinstance(ty, IRInd):
            return IRInd(ty.ind_id, tuple(subst_idx(i) for i in ty.indices), ty.nominal_name)
        return ty

    def _subst_box_ty_ty(self, ty: IRTy, mot_uid: int, q: GExpr, rep: IRTy) -> IRTy:
        if isinstance(ty, IRTUnbox) and ty.uid == mot_uid:
            return IRTProm(q, rep)
        if isinstance(ty, IRVec):
            return IRVec(self._subst_box_ty_ty(ty.elem, mot_uid, q, rep), ty.length)
        if isinstance(ty, IRPi):
            return IRPi(ty.uid, ty.s, ty.r,
                        self._subst_box_ty_ty(ty.dom, mot_uid, q, rep),
                        self._subst_box_ty_ty(ty.cod, mot_uid, q, rep))
        if isinstance(ty, IRSigma):
            return IRSigma(ty.uid, ty.r,
                           self._subst_box_ty_ty(ty.fst_ty, mot_uid, q, rep),
                           self._subst_box_ty_ty(ty.snd_ty, mot_uid, q, rep),
                           ty.nominal_name)
        if isinstance(ty, (IRBox, IRTProm)):
            return type(ty)(ty.grade, self._subst_box_ty_ty(ty.inner, mot_uid, q, rep))
        if isinstance(ty, IRSum):
            return IRSum(self._subst_box_ty_ty(ty.lhs, mot_uid, q, rep),
                         self._subst_box_ty_ty(ty.rhs, mot_uid, q, rep), ty.nominal_name)
        return ty

    def _spec_sum_subj(self, scrut: IRTerm, motive: IRTy, mot_uid: int) -> IRTy:
        def subst_idx(i: IRIdx) -> IRIdx:
            if isinstance(i, IRIdxCase) and i.uid == mot_uid:
                if isinstance(scrut, IRInl):
                    v = scrut.val.idx if isinstance(scrut.val, IRNatVal) else (
                        IRIdxVar(scrut.val.uid) if isinstance(scrut.val, IRVar) else None
                    )
                    if v is not None:
                        return _subst_uid_idx(i.left, i.left_uid, v)
                elif isinstance(scrut, IRInr):
                    v = scrut.val.idx if isinstance(scrut.val, IRNatVal) else (
                        IRIdxVar(scrut.val.uid) if isinstance(scrut.val, IRVar) else None
                    )
                    if v is not None:
                        return _subst_uid_idx(i.right, i.right_uid, v)
                elif isinstance(scrut, IRVar):
                    return IRIdxCase(scrut.uid, i.left_uid, i.right_uid, i.left, i.right)
            if isinstance(i, IRIdxAdd):
                return IRIdxAdd(subst_idx(i.lhs), subst_idx(i.rhs))
            if isinstance(i, IRIdxProm):
                return IRIdxProm(i.grade, subst_idx(i.inner))
            return i

        if isinstance(ty := motive, IRVec):
            return IRVec(self._spec_sum_subj(scrut, ty.elem, mot_uid), subst_idx(ty.length))
        if isinstance(ty, IRPi):
            return IRPi(ty.uid, ty.s, ty.r,
                        self._spec_sum_subj(scrut, ty.dom, mot_uid),
                        self._spec_sum_subj(scrut, ty.cod, mot_uid))
        if isinstance(ty, IRSum):
            return IRSum(self._spec_sum_subj(scrut, ty.lhs, mot_uid),
                         self._spec_sum_subj(scrut, ty.rhs, mot_uid), ty.nominal_name)
        if isinstance(ty, IRInd):
            return IRInd(ty.ind_id, tuple(subst_idx(i) for i in ty.indices), ty.nominal_name)
        return motive

    def _spec_fix_subj(self, scrut: IRTerm, motive: IRTy, mot_uid: int) -> IRTy:
        if isinstance(scrut, IRNatVal):
            return _subst_uid_ty(motive, mot_uid, rep_idx=scrut.idx)
        if isinstance(scrut, IRVar):
            return _subst_uid_ty(motive, mot_uid, rep_idx=IRIdxVar(scrut.uid))
        return motive


def _fill_omitted_r_and_pi(
    term: IRTerm,
    expected: IRTy,
    domain: GradeDomain | CustomDomainSpec,
) -> tuple[IRTerm, IRTy, dict[int, int]]:
    """Compute exact `r` for binders whose type-use grade `r` was omitted (`None`)."""
    analyzer = _IRAnalyzer(domain)
    uid_aliases: dict[int, int] = {}

    def walk_ty(ty: IRTy) -> IRTy:
        if isinstance(ty, (IRNat, IRBool, IRUniv, IRTVar, IRTUnbox)):
            return ty
        if isinstance(ty, IRVec):
            return IRVec(walk_ty(ty.elem), ty.length)
        if isinstance(ty, IRTProm):
            return IRTProm(ty.grade, walk_ty(ty.inner))
        if isinstance(ty, IRPi):
            dom_f = walk_ty(ty.dom)
            old = analyzer.env_types.get(ty.uid)
            analyzer.env_types[ty.uid] = dom_f
            cod_f = walk_ty(ty.cod)
            if ty.r is not None:
                r_val = ty.r
            else:
                dem = analyzer.ty_demand(cod_f)
                r_val = dem.get(ty.uid, _gzero(domain))
            if old is None:
                analyzer.env_types.pop(ty.uid, None)
            else:
                analyzer.env_types[ty.uid] = old
            return IRPi(ty.uid, ty.s, r_val, dom_f, cod_f)
        if isinstance(ty, IRSigma):
            fst_f = walk_ty(ty.fst_ty)
            old = analyzer.env_types.get(ty.uid)
            analyzer.env_types[ty.uid] = fst_f
            snd_f = walk_ty(ty.snd_ty)
            if old is None:
                analyzer.env_types.pop(ty.uid, None)
            else:
                analyzer.env_types[ty.uid] = old
            return IRSigma(ty.uid, ty.r, fst_f, snd_f, ty.nominal_name)
        if isinstance(ty, IRBox):
            return IRBox(ty.grade, walk_ty(ty.inner))
        if isinstance(ty, IRSum):
            return IRSum(walk_ty(ty.lhs), walk_ty(ty.rhs), ty.nominal_name)
        if isinstance(ty, IRRecord):
            return IRRecord(ty.rec_id, tuple((fn, fg, walk_ty(ft)) for fn, fg, ft in ty.fields), ty.nominal_name)
        return ty

    def walk_term(t: IRTerm) -> IRTerm:
        if isinstance(t, (IRVar, IRNatVal, IRBoolVal)):
            return t
        if isinstance(t, IRTypeVal):
            return IRTypeVal(walk_ty(t.ty))
        if isinstance(t, IRLam):
            dom_f = walk_ty(t.dom)
            old = analyzer.env_types.get(t.uid)
            analyzer.env_types[t.uid] = dom_f
            bod_f = walk_term(t.body)
            if t.r is not None:
                r_val = t.r
            else:
                _, _, v_b = analyzer.infer(bod_f)
                r_val = v_b.get(t.uid, _gzero(domain))
            if old is None:
                analyzer.env_types.pop(t.uid, None)
            else:
                analyzer.env_types[t.uid] = old
            return IRLam(t.uid, t.name, t.span, t.s, r_val, dom_f, bod_f, t.explicit_r)
        if isinstance(t, IRApp):
            return IRApp(walk_term(t.fn), walk_term(t.arg))
        if isinstance(t, IRLet):
            ann_f = walk_ty(t.ann)
            rhs_f = walk_term(t.rhs)
            old = analyzer.env_types.get(t.uid)
            analyzer.env_types[t.uid] = ann_f
            bod_f = walk_term(t.body)
            if t.r is not None:
                r_val = t.r
            else:
                _, _, v_b = analyzer.infer(bod_f)
                r_val = v_b.get(t.uid, _gzero(domain))
            if old is None:
                analyzer.env_types.pop(t.uid, None)
            else:
                analyzer.env_types[t.uid] = old
            return IRLet(t.uid, t.name, t.span, t.s, r_val, ann_f, rhs_f, bod_f, t.explicit_r)
        if isinstance(t, IRPair):
            return IRPair(t.uid, t.r, walk_ty(t.fst_ty), walk_ty(t.snd_ty),
                          walk_term(t.fst_val), walk_term(t.snd_val), t.nominal_name)
        if isinstance(t, IRLetPair):
            return IRLetPair(t.x_uid, t.y_uid, t.x_name, t.y_name, t.x_span, t.y_span,
                             t.s, t.kappa, t.motive_uid, walk_ty(t.motive),
                             walk_term(t.pair), walk_term(t.body))
        if isinstance(t, IRPromote):
            return IRPromote(t.grade, walk_term(t.val))
        if isinstance(t, IRLetBox):
            return IRLetBox(t.x_uid, t.x_name, t.x_span, t.kappa, t.motive_uid,
                            walk_ty(t.motive), walk_term(t.box_term), walk_term(t.body))
        if isinstance(t, IRInl):
            return IRInl(walk_ty(t.rhs_ty), walk_term(t.val), t.nominal_name)
        if isinstance(t, IRInr):
            return IRInr(walk_ty(t.lhs_ty), walk_term(t.val), t.nominal_name)
        if isinstance(t, IRMatchSum):
            return IRMatchSum(t.x_uid, t.y_uid, t.x_name, t.y_name, t.x_span, t.y_span,
                              t.s, t.kappa, t.motive_uid, walk_ty(t.motive),
                              walk_term(t.scrut), walk_term(t.lbranch), walk_term(t.rbranch))
        if isinstance(t, IRIf):
            return IRIf(walk_term(t.cond), walk_term(t.then_br), walk_term(t.else_br))
        if isinstance(t, IRRecordMk):
            return IRRecordMk(
                t.rec_id,
                tuple((fn, fg, walk_ty(ft), walk_term(fv)) for fn, fg, ft, fv in t.fields),
                t.nominal_name,
            )
        if isinstance(t, IRMatchRecord):
            return IRMatchRecord(t.rec_id, t.s, t.motive_uid, walk_ty(t.motive),
                                 walk_term(t.scrut), t.binders, walk_term(t.body))
        if isinstance(t, IRSubgrade):
            return IRSubgrade(walk_ty(t.target), walk_term(t.body))
        if isinstance(t, IRFix):
            return IRFix(t.n_uid, t.rec_uid, t.n_name, t.rec_name, t.n_span, t.rec_span,
                         t.s_rec, t.motive_uid, walk_ty(t.motive),
                         walk_term(t.scrut), walk_term(t.base), walk_term(t.step))
        return t

    def sync_lambda_r_to_expected(t: IRTerm, exp: IRTy) -> tuple[IRTerm, IRTy]:
        # When expected Pi omits r (e.g. from parameter annotation without explicit r),
        # match expected Pi's r to lambda's inferred r so closed check passes exact r!
        if isinstance(t, IRLam) and isinstance(exp, IRPi):
            dom_f = t.dom
            old = analyzer.env_types.get(t.uid)
            analyzer.env_types[t.uid] = dom_f
            bod_s, cod_s = sync_lambda_r_to_expected(t.body, _subst_uid_ty(exp.cod, exp.uid, rep_idx=IRIdxVar(t.uid), rep_ty=IRTVar(t.uid)) if exp.uid != t.uid else exp.cod)
            if old is None:
                analyzer.env_types.pop(t.uid, None)
            else:
                analyzer.env_types[t.uid] = old
            if exp.uid != t.uid:
                uid_aliases[t.uid] = exp.uid
            if not t.explicit_r:
                # r was inferred from body + cod; keep t.uid so cod_s stays well-scoped!
                if t.r is None:
                    raise RuntimeError("expected filled type-use grade on IRLam")
                return (
                    IRLam(t.uid, t.name, t.span, t.s, t.r, dom_f, bod_s, t.explicit_r),
                    IRPi(t.uid, exp.s, t.r, dom_f, cod_s),
                )
            return (
                IRLam(t.uid, t.name, t.span, t.s, t.r, dom_f, bod_s, t.explicit_r),
                IRPi(t.uid, exp.s, exp.r if exp.r is not None else t.r, dom_f, cod_s),
            )
        return t, exp

    filled_term = walk_term(term)
    filled_exp = walk_ty(expected)
    synced_term, synced_exp = sync_lambda_r_to_expected(filled_term, filled_exp)
    return synced_term, synced_exp, uid_aliases


# ---------------------------------------------------------------------------
# Serializer from Typed IR -> GradedCore Gallina strings
# ---------------------------------------------------------------------------


def _serialize_gexpr_rocq(expr: GExpr, domain: GradeDomain | CustomDomainSpec,
                          gvar_env: Mapping[int, str] | None) -> str:
    return _eval_gexpr(expr, domain, gvar_env)


def _to_rocq_cidx(idx: IRIdx, env_uids: list[int], domain: GradeDomain | CustomDomainSpec,
                  gvar_env: Mapping[int, str] | None) -> str:
    if isinstance(idx, IRIdxVar):
        return f"(@CIdxVar _D {_db_idx(env_uids, idx.uid)})"
    if isinstance(idx, IRIdxLit):
        return f"(@CIdxLit _D {idx.value})"
    if isinstance(idx, IRIdxAdd):
        return f"(@CIdxAdd _D {_to_rocq_cidx(idx.lhs, env_uids, domain, gvar_env)} {_to_rocq_cidx(idx.rhs, env_uids, domain, gvar_env)})"
    if isinstance(idx, IRIdxProm):
        q = _serialize_gexpr_rocq(idx.grade, domain, gvar_env)
        return f"(@CIdxProm _D {q} {_to_rocq_cidx(idx.inner, env_uids, domain, gvar_env)})"
    if isinstance(idx, IRIdxUnbox):
        return f"(@CIdxUnbox _D {_db_idx(env_uids, idx.uid)})"
    if isinstance(idx, IRIdxFst):
        return f"(@CIdxFst _D {_db_idx(env_uids, idx.uid)})"
    if isinstance(idx, IRIdxSnd):
        return f"(@CIdxSnd _D {_db_idx(env_uids, idx.uid)})"
    if isinstance(idx, IRIdxCase):
        s_idx = _db_idx(env_uids, idx.uid)
        l_str = _to_rocq_cidx(idx.left, [idx.left_uid, *env_uids], domain, gvar_env)
        r_str = _to_rocq_cidx(idx.right, [idx.right_uid, *env_uids], domain, gvar_env)
        return f"(@CIdxCase _D {s_idx} {l_str} {r_str})"
    raise TypeError(f"unknown IRIdx {idx!r}")


def _to_rocq_cty(ty: IRTy, env_uids: list[int], domain: GradeDomain | CustomDomainSpec,
                 gvar_env: Mapping[int, str] | None) -> str:
    if isinstance(ty, IRNat):
        return "(@CNat _D)"
    if isinstance(ty, IRBool):
        return "(@CBool _D)"
    if isinstance(ty, IRVec):
        return f"(@CVec _D {_to_rocq_cty(ty.elem, env_uids, domain, gvar_env)} {_to_rocq_cidx(ty.length, env_uids, domain, gvar_env)})"
    if isinstance(ty, IRUniv):
        return f"(@CUniv _D {ty.level})"
    if isinstance(ty, IRTVar):
        return f"(@CTVar _D {_db_idx(env_uids, ty.uid)})"
    if isinstance(ty, IRTProm):
        q = _serialize_gexpr_rocq(ty.grade, domain, gvar_env)
        return f"(@CTProm _D {q} {_to_rocq_cty(ty.inner, env_uids, domain, gvar_env)})"
    if isinstance(ty, IRTUnbox):
        return f"(@CTUnbox _D {_db_idx(env_uids, ty.uid)})"
    if isinstance(ty, IRPi):
        s = _serialize_gexpr_rocq(ty.s, domain, gvar_env)
        r = _serialize_gexpr_rocq(ty.r if ty.r is not None else _gzero(domain), domain, gvar_env)
        dom_s = _to_rocq_cty(ty.dom, env_uids, domain, gvar_env)
        cod_s = _to_rocq_cty(ty.cod, [ty.uid, *env_uids], domain, gvar_env)
        return f"(@CPi _D {ty.uid} {s} {r} {dom_s} {cod_s})"
    if isinstance(ty, IRSigma):
        r = _serialize_gexpr_rocq(ty.r, domain, gvar_env)
        fst_s = _to_rocq_cty(ty.fst_ty, env_uids, domain, gvar_env)
        snd_s = _to_rocq_cty(ty.snd_ty, [ty.uid, *env_uids], domain, gvar_env)
        return f"(@CSigma _D {ty.uid} {r} {fst_s} {snd_s})"
    if isinstance(ty, IRBox):
        q = _serialize_gexpr_rocq(ty.grade, domain, gvar_env)
        return f"(@CBox _D {q} {_to_rocq_cty(ty.inner, env_uids, domain, gvar_env)})"
    if isinstance(ty, IRSum):
        return f"(@CSum _D {_to_rocq_cty(ty.lhs, env_uids, domain, gvar_env)} {_to_rocq_cty(ty.rhs, env_uids, domain, gvar_env)})"
    if isinstance(ty, IRRecord):
        f_strs = [
            f"({fn}, {_serialize_gexpr_rocq(fg, domain, gvar_env)}, {_to_rocq_cty(ft, env_uids, domain, gvar_env)})"
            for fn, fg, ft in ty.fields
        ]
        return f"(@CRecord _D {ty.rec_id} [{'; '.join(f_strs)}])"
    if isinstance(ty, IRInd):
        i_strs = [_to_rocq_cidx(i, env_uids, domain, gvar_env) for i in ty.indices]
        return f"(@CInd _D {ty.ind_id} [{'; '.join(i_strs)}])"
    raise TypeError(f"unknown IRTy {ty!r}")


def _to_rocq_cterm(term: IRTerm, env_uids: list[int], domain: GradeDomain | CustomDomainSpec,
                   gvar_env: Mapping[int, str] | None) -> str:
    if isinstance(term, IRVar):
        return f"(@CVar _D {_db_idx(env_uids, term.uid)})"
    if isinstance(term, IRNatVal):
        return f"(@CNatVal _D {_to_rocq_cidx(term.idx, env_uids, domain, gvar_env)})"
    if isinstance(term, IRBoolVal):
        return f"(@CBoolVal _D {'true' if term.value else 'false'})"
    if isinstance(term, IRTypeVal):
        return f"(@CTypeVal _D {_to_rocq_cty(term.ty, env_uids, domain, gvar_env)})"
    if isinstance(term, IRLam):
        s = _serialize_gexpr_rocq(term.s, domain, gvar_env)
        r = _serialize_gexpr_rocq(term.r if term.r is not None else _gzero(domain), domain, gvar_env)
        dom_s = _to_rocq_cty(term.dom, env_uids, domain, gvar_env)
        bod_s = _to_rocq_cterm(term.body, [term.uid, *env_uids], domain, gvar_env)
        return f"(@CLam _D {term.uid} {s} {r} {dom_s} {bod_s})"
    if isinstance(term, IRApp):
        return f"(@CApp _D {_to_rocq_cterm(term.fn, env_uids, domain, gvar_env)} {_to_rocq_cterm(term.arg, env_uids, domain, gvar_env)})"
    if isinstance(term, IRLet):
        s = _serialize_gexpr_rocq(term.s, domain, gvar_env)
        r = _serialize_gexpr_rocq(term.r if term.r is not None else _gzero(domain), domain, gvar_env)
        ann_s = _to_rocq_cty(term.ann, env_uids, domain, gvar_env)
        rhs_s = _to_rocq_cterm(term.rhs, env_uids, domain, gvar_env)
        bod_s = _to_rocq_cterm(term.body, [term.uid, *env_uids], domain, gvar_env)
        an = _IRAnalyzer(domain)
        bod_ty, _, _ = an.infer(term.body)
        if term.uid in an.ty_demand(bod_ty):
            return f"(@CApp _D (@CLam _D {term.uid} {s} {r} {ann_s} {bod_s}) {rhs_s})"
        return f"(@CLet _D {term.uid} {s} {r} {ann_s} {rhs_s} {bod_s})"
    if isinstance(term, IRPair):
        r = _serialize_gexpr_rocq(term.r, domain, gvar_env)
        f_ty = _to_rocq_cty(term.fst_ty, env_uids, domain, gvar_env)
        s_ty = _to_rocq_cty(term.snd_ty, [term.uid, *env_uids], domain, gvar_env)
        fv = _to_rocq_cterm(term.fst_val, env_uids, domain, gvar_env)
        sv = _to_rocq_cterm(term.snd_val, env_uids, domain, gvar_env)
        return f"(@CPair _D {term.uid} {r} {f_ty} {s_ty} {fv} {sv})"
    if isinstance(term, IRLetPair):
        s = _serialize_gexpr_rocq(term.s, domain, gvar_env)
        k = _serialize_gexpr_rocq(term.kappa, domain, gvar_env)
        mot = _to_rocq_cty(term.motive, [term.motive_uid, *env_uids], domain, gvar_env)
        pr = _to_rocq_cterm(term.pair, env_uids, domain, gvar_env)
        # GradedCore extends env with y :: x :: env (so y at 0, x at 1).
        bod = _to_rocq_cterm(term.body, [term.y_uid, term.x_uid, *env_uids], domain, gvar_env)
        return f"(@CLetPair _D {term.x_uid} {term.y_uid} {s} {k} {mot} {pr} {bod})"
    if isinstance(term, IRPromote):
        q = _serialize_gexpr_rocq(term.grade, domain, gvar_env)
        return f"(@CPromote _D {q} {_to_rocq_cterm(term.val, env_uids, domain, gvar_env)})"
    if isinstance(term, IRLetBox):
        k = _serialize_gexpr_rocq(term.kappa, domain, gvar_env)
        mot = _to_rocq_cty(term.motive, [term.motive_uid, *env_uids], domain, gvar_env)
        bx = _to_rocq_cterm(term.box_term, env_uids, domain, gvar_env)
        bod = _to_rocq_cterm(term.body, [term.x_uid, *env_uids], domain, gvar_env)
        return f"(@CLetBox _D {term.x_uid} {k} {mot} {bx} {bod})"
    if isinstance(term, IRInl):
        return f"(@CInl _D {_to_rocq_cty(term.rhs_ty, env_uids, domain, gvar_env)} {_to_rocq_cterm(term.val, env_uids, domain, gvar_env)})"
    if isinstance(term, IRInr):
        return f"(@CInr _D {_to_rocq_cty(term.lhs_ty, env_uids, domain, gvar_env)} {_to_rocq_cterm(term.val, env_uids, domain, gvar_env)})"
    if isinstance(term, IRMatchSum):
        s = _serialize_gexpr_rocq(term.s, domain, gvar_env)
        k = _serialize_gexpr_rocq(term.kappa, domain, gvar_env)
        mot = _to_rocq_cty(term.motive, [term.motive_uid, *env_uids], domain, gvar_env)
        sc = _to_rocq_cterm(term.scrut, env_uids, domain, gvar_env)
        lb = _to_rocq_cterm(term.lbranch, [term.x_uid, *env_uids], domain, gvar_env)
        rb = _to_rocq_cterm(term.rbranch, [term.y_uid, *env_uids], domain, gvar_env)
        return f"(@CMatchSum _D {term.x_uid} {term.y_uid} {s} {k} {mot} {sc} {lb} {rb})"
    if isinstance(term, IRIf):
        return (
            f"(@CIf _D {_to_rocq_cterm(term.cond, env_uids, domain, gvar_env)} "
            f"{_to_rocq_cterm(term.then_br, env_uids, domain, gvar_env)} "
            f"{_to_rocq_cterm(term.else_br, env_uids, domain, gvar_env)})"
        )
    if isinstance(term, IRRecordMk):
        f_strs = [
            f"({fn}, {_serialize_gexpr_rocq(fg, domain, gvar_env)}, "
            f"{_to_rocq_cty(ft, env_uids, domain, gvar_env)}, "
            f"{_to_rocq_cterm(fv, env_uids, domain, gvar_env)})"
            for fn, fg, ft, fv in term.fields
        ]
        return f"(@CRecordMk _D {term.rec_id} [{'; '.join(f_strs)}])"
    if isinstance(term, IRMatchRecord):
        s = _serialize_gexpr_rocq(term.s, domain, gvar_env)
        mot = _to_rocq_cty(term.motive, env_uids, domain, gvar_env)
        sc = _to_rocq_cterm(term.scrut, env_uids, domain, gvar_env)
        bs = [b_uid for b_uid, _, _ in term.binders]
        ext_uids = [*reversed(bs), *env_uids]
        bod = _to_rocq_cterm(term.body, ext_uids, domain, gvar_env)
        bs_str = "[" + "; ".join(str(b) for b in bs) + "]"
        return f"(@CMatchRecord _D {term.rec_id} {s} {mot} {sc} {bs_str} {bod})"
    if isinstance(term, IRSubgrade):
        return f"(@CSubgrade _D {_to_rocq_cty(term.target, env_uids, domain, gvar_env)} {_to_rocq_cterm(term.body, env_uids, domain, gvar_env)})"
    if isinstance(term, IRFix):
        sr = _serialize_gexpr_rocq(term.s_rec, domain, gvar_env)
        mot = _to_rocq_cty(term.motive, [term.motive_uid, *env_uids], domain, gvar_env)
        sc = _to_rocq_cterm(term.scrut, env_uids, domain, gvar_env)
        bs = _to_rocq_cterm(term.base, env_uids, domain, gvar_env)
        st = _to_rocq_cterm(term.step, [term.rec_uid, term.n_uid, *env_uids], domain, gvar_env)
        return f"(@CFix _D {term.n_uid} {term.rec_uid} {sr} {mot} {sc} {bs} {st})"
    raise TypeError(f"unknown IRTerm {term!r}")


# ---------------------------------------------------------------------------
# Section 4: Local Grade Inference Integration (Q25bz / graded_inference.py)
# ---------------------------------------------------------------------------


def _to_gi_expr(g: GExpr, domain: GradeDomain | CustomDomainSpec, sec_is_presence: bool = False) -> gi.GradeExpr:
    if isinstance(g, GLit):
        val = g.value
        if isinstance(val, bool):
            return gi.GradeLit(1 if val else 0)
        if isinstance(val, int):
            return gi.GradeLit(val)
        s = val.lower()
        if s in {"0", "zero", "lzero", "azero", "lo", "false"}:
            return gi.GradeLit(0)
        if s in {"1", "one", "lone", "aone", "hi", "true"}:
            return gi.GradeLit(1)
        if s in {"many", "lmany", "amany"}:
            return gi.GradeLit(2)
        if val.isdigit():
            return gi.GradeLit(int(val))
        return gi.GradeLit(1)
    if isinstance(g, GVar):
        return gi.GradeVar(g.name)
    if isinstance(g, GAdd):
        return gi.GradeAdd(_to_gi_expr(g.lhs, domain, sec_is_presence),
                           _to_gi_expr(g.rhs, domain, sec_is_presence))
    if isinstance(g, GMul):
        return gi.GradeMul(_to_gi_expr(g.lhs, domain, sec_is_presence),
                           _to_gi_expr(g.rhs, domain, sec_is_presence))
    if isinstance(g, GHole):
        inf_dom = _to_inference_domain(domain)
        return gi.GradeVar(gi.GradeMeta(id=g.hole_id, domain=inf_dom, span=g.span))
    raise TypeError(f"cannot lower grade {g!r} to inference")


def _to_inference_domain(domain: GradeDomain | CustomDomainSpec) -> gi.InferenceDomain:
    if isinstance(domain, CustomDomainSpec):
        return gi.InferenceDomain.NAT_BOUND if domain.subgraded else gi.InferenceDomain.NAT_EXACT
    if domain == GradeDomain.SECURITY:
        return gi.InferenceDomain.PRESENCE
    return gi.coerce_domain(domain)


def _int_to_domain_lit(val: int, domain: GradeDomain | CustomDomainSpec) -> GLit:
    if isinstance(domain, CustomDomainSpec):
        return GLit(val)
    if domain == GradeDomain.PRESENCE:
        return GLit(val > 0)
    if domain == GradeDomain.LINEAR:
        return GLit("LZero" if val == 0 else ("LOne" if val == 1 else "LMany"))
    if domain == GradeDomain.AFFINE:
        return GLit("AZero" if val == 0 else ("AOne" if val == 1 else "AMany"))
    if domain == GradeDomain.SECURITY:
        return GLit("Lo" if val == 0 else "Hi")
    return GLit(val)


def _solve_ir_grade_holes(
    protocol: _Protocol,
    term: IRTerm,
    expected: IRTy,
    domain: GradeDomain | CustomDomainSpec,
) -> tuple[IRTerm, IRTy, dict[str, object]]:
    """Solve any `GHole` annotations in `(term, expected)` via `graded_inference`."""
    analyzer = _IRAnalyzer(domain)
    inf_dom = _to_inference_domain(domain)
    is_sub = isinstance(domain, CustomDomainSpec) or _domain_spec(domain).subgraded
    op_str: gi.ConstraintOp = "le" if is_sub else "eq"
    metas: dict[str, gi.GradeMeta] = {}
    constraints: list[gi.GradeConstraint] = []

    def reg_hole(g: GExpr | None) -> None:
        if isinstance(g, GHole):
            metas[g.hole_id] = gi.GradeMeta(id=g.hole_id, domain=inf_dom, span=g.span)
        elif isinstance(g, (GAdd, GMul)):
            reg_hole(g.lhs)
            reg_hole(g.rhs)

    def collect_ty(ty: IRTy) -> None:
        if isinstance(ty, IRPi):
            reg_hole(ty.s)
            reg_hole(ty.r)
            collect_ty(ty.dom)
            old = analyzer.env_types.get(ty.uid)
            analyzer.env_types[ty.uid] = ty.dom
            collect_ty(ty.cod)
            if ty.r is not None and isinstance(ty.r, GHole):
                dem = analyzer.ty_demand(ty.cod).get(ty.uid, _gzero(domain))
                constraints.append(gi.GradeConstraint(
                    lhs=_to_gi_expr(dem, domain),
                    op=op_str,
                    rhs=_to_gi_expr(ty.r, domain),
                    origin_span=ty.r.span,
                    reason=f"type-use binder {ty.uid}",
                ))
            if old is None:
                analyzer.env_types.pop(ty.uid, None)
            else:
                analyzer.env_types[ty.uid] = old
        elif isinstance(ty, IRSigma):
            reg_hole(ty.r)
            collect_ty(ty.fst_ty)
            collect_ty(ty.snd_ty)
        elif isinstance(ty, (IRBox, IRTProm)):
            reg_hole(ty.grade)
            collect_ty(ty.inner)
        elif isinstance(ty, IRSum):
            collect_ty(ty.lhs)
            collect_ty(ty.rhs)
        elif isinstance(ty, IRVec):
            collect_ty(ty.elem)

    def collect_term(t: IRTerm) -> tuple[dict[int, GExpr], dict[int, GExpr]]:
        if isinstance(t, IRLam):
            reg_hole(t.s)
            reg_hole(t.r)
            collect_ty(t.dom)
            old = analyzer.env_types.get(t.uid)
            analyzer.env_types[t.uid] = t.dom
            u_b, v_b = collect_term(t.body)
            if old is None:
                analyzer.env_types.pop(t.uid, None)
            else:
                analyzer.env_types[t.uid] = old
            u_actual = u_b.pop(t.uid, _gzero(domain))
            v_actual = v_b.pop(t.uid, _gzero(domain))
            if t.s.has_hole():
                constraints.append(gi.GradeConstraint(
                    lhs=_to_gi_expr(u_actual, domain),
                    op=op_str,
                    rhs=_to_gi_expr(t.s, domain),
                    origin_span=tuple(t.span),
                    reason=f"binder {t.name} computation",
                ))
            if t.r is not None and t.r.has_hole():
                constraints.append(gi.GradeConstraint(
                    lhs=_to_gi_expr(v_actual, domain),
                    op=op_str,
                    rhs=_to_gi_expr(t.r, domain),
                    origin_span=tuple(t.span),
                    reason=f"binder {t.name} type-use",
                ))
            return u_b, analyzer.add_maps(analyzer.ty_demand(t.dom), v_b)
        if isinstance(t, IRLet):
            reg_hole(t.s)
            reg_hole(t.r)
            collect_ty(t.ann)
            u_rhs, v_rhs = collect_term(t.rhs)
            old = analyzer.env_types.get(t.uid)
            analyzer.env_types[t.uid] = t.ann
            u_bod, v_bod = collect_term(t.body)
            if old is None:
                analyzer.env_types.pop(t.uid, None)
            else:
                analyzer.env_types[t.uid] = old
            u_actual = u_bod.pop(t.uid, _gzero(domain))
            v_actual = v_bod.pop(t.uid, _gzero(domain))
            if t.s.has_hole():
                constraints.append(gi.GradeConstraint(
                    lhs=_to_gi_expr(u_actual, domain),
                    op=op_str,
                    rhs=_to_gi_expr(t.s, domain),
                    origin_span=tuple(t.span),
                    reason=f"let {t.name} computation",
                ))
            if t.r is not None and t.r.has_hole():
                constraints.append(gi.GradeConstraint(
                    lhs=_to_gi_expr(v_actual, domain),
                    op=op_str,
                    rhs=_to_gi_expr(t.r, domain),
                    origin_span=tuple(t.span),
                    reason=f"let {t.name} type-use",
                ))
            z_ty = v_rhs if isinstance(t.ann, IRUniv) and isinstance(t.rhs, IRTypeVal) else u_rhs
            r_eff = t.r if t.r is not None else v_actual
            return (
                analyzer.add_maps(u_bod, analyzer.scale_map(t.s, u_rhs)),
                analyzer.add_maps(v_bod, analyzer.scale_map(r_eff, z_ty)),
            )
        u_res, v_res = analyzer.infer(t)[1:]
        return u_res, v_res

    collect_ty(expected)
    collect_term(term)
    if not metas:
        return term, expected, {}

    result = gi.solve_constraints(constraints, domain=inf_dom, metas=tuple(metas.values()), verify_rocq=True)
    if result.status != "solved":
        first = result.residuals[0] if result.residuals else None
        span_node: Node = {"span": list(first.origin_span) if first and first.origin_span else [0, 0]}
        reason = first.message if first else "grade inference left unsolved residual constraints"
        raise protocol.error("grade", f"grade inference failed: {reason}", span_node)

    mapping: dict[str, GExpr] = {
        str(meta_id): _int_to_domain_lit(val, domain)
        for meta_id, val in result.assignments.items()
    }
    solved_term = _subst_gexpr_term(term, mapping)
    solved_exp = _subst_gexpr_ty(expected, mapping)
    return solved_term, solved_exp, {
        "solution": {k: _rocq_grade_sort_value(domain, cast("GLit", v).value) for k, v in mapping.items()},
        "certificate_sha256": result.certificate.source_sha256 if result.certificate is not None else None,
        "certificate_gallina": result.certificate.gallina if result.certificate is not None else None,
    }


# ---------------------------------------------------------------------------
# Section 5: HoldFast Surface AST -> Typed Core IR Lowering
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _IRBinderMeta:
    uid: int
    name: str
    span: list[int]
    domain: GradeDomain | CustomDomainSpec
    s: GExpr
    r: GExpr | None
    explicit_r: bool
    role: str = "binder"


@dataclass(frozen=True)
class _Parameter:
    index: int
    uid: int
    name: str
    span: list[int]
    domain: str
    allowance: str
    expected_type_uses: str | None = None


@dataclass(frozen=True)
class _RecordSpec:
    name: str
    rec_id: int
    fields: tuple[tuple[str, str, str | None, GExpr, IRTy], ...]
    # (field_name, param_name, binder_type_name, grade, ir_type)
    is_dependent_pair: bool = False
    is_box: bool = False
    box_domain: GradeDomain | CustomDomainSpec | None = None


@dataclass(frozen=True)
class _UnionSpec:
    name: str
    generics: tuple[str, ...]
    ctors: tuple[tuple[str, tuple[tuple[str, Node], ...]], ...]


@dataclass(frozen=True)
class _InductiveSpec:
    name: str
    ind_id: int
    generics: tuple[tuple[str, str, str | None], ...]  # (mode, name, domain_or_type)
    ctors: tuple[tuple[str, list[Node], Node | None], ...]


@dataclass(frozen=True)
class _Definition:
    index: int
    name: str
    source: Node
    domain: GradeDomain | CustomDomainSpec
    ir_term: IRTerm
    ir_expected: IRTy
    closed_term_gallina: str
    closed_expected_gallina: str
    open_env_gallina: str
    open_body_gallina: str
    open_ret_gallina: str
    top_params: tuple[_Parameter, ...]
    binders: dict[int, _IRBinderMeta]
    zero_type_use_binders: tuple[tuple[int, str, list[int]], ...]
    records: tuple[str, ...] = ()
    symbolic_gvars: tuple[tuple[str, int], ...] = ()
    symbolic_obligations: tuple[tuple[GExpr, GExpr, str, int, str], ...] = ()
    inferred_grades: dict[str, object] = field(default_factory=dict)
    context: str | None = None
    open_uids_db: tuple[int, ...] = ()
    open_expected_s: tuple[str, ...] = ()
    open_expected_r: tuple[str | None, ...] = ()
    trailing_pi_params: tuple[tuple[_Parameter, tuple[int, object, list[int], object]], ...] = ()


@dataclass(frozen=True)
class GradeExport:
    protocol: _Protocol
    syntax: Node
    name: str
    domain: GradeDomain
    receipt: str
    imports: Mapping[str, tuple[str, GradeExport]]
    modal: bool = False
    box_imports: Mapping[str, GradeDomain] = MappingProxyType({})
    custom_domains: Mapping[str, CustomDomainSpec] = MappingProxyType({})


type GradeResolver = Callable[[str], tuple[str, GradeExport] | None]
type BoxResolver = Callable[[str], GradeDomain | None]


def _valid_box_record(declaration: Node, domain: GradeDomain) -> bool:
    generics = cast("list[Node]", declaration["generics"])
    parameters = cast("list[Node]", declaration["parameters"])
    if len(generics) != 2 or len(parameters) != 1 or declaration["declarations"] or declaration["contracts"]:
        return False
    first_generic, second_generic = generics
    field = parameters[0]
    if (first_generic["mode"] != "type" or first_generic["type"] is not None
            or second_generic["mode"] != "grade" or second_generic["type"] is None):
        return False
    grade_domain = cast("Node", second_generic["type"])
    field_type = cast("Node | None", field["type"])
    field_grade = cast("Node | None", field["grade"])
    qname = _name(second_generic["name"])
    grade_ok = False
    if field_grade is not None:
        if field_grade["kind"] == "name" and _name(field_grade["name"]) == qname:
            grade_ok = True
        elif field_grade["kind"] == "call":
            callee = cast("Node", field_grade["callee"])
            cargs = cast("list[Node]", field_grade["arguments"])
            arg0_val = cast("Node", cargs[0]["value"]) if len(cargs) == 1 else None
            if (callee["kind"] == "name" and _name(callee["name"]) == domain.value
                    and arg0_val is not None and arg0_val["kind"] == "name"
                    and _name(arg0_val["name"]) == qname):
                grade_ok = True
    return (
        grade_domain["kind"] == "type" and _name(grade_domain["name"]) == domain.value
        and field_type is not None and field_type["kind"] == "type"
        and _name(field_type["name"]) == _name(first_generic["name"])
        and grade_ok
    )


class _CoreLowerer:
    """Unified HoldFast-to-GradedCore typed IR lowerer."""

    reserved = _PRIMITIVES

    def __init__(
        self,
        protocol: _Protocol,
        syntax: Node,
        domain: GradeDomain | CustomDomainSpec,
        *,
        resolve_box: BoxResolver | None = None,
        infer_grades: bool = False,
        custom_domains: Mapping[str, CustomDomainSpec] | None = None,
        uid_counter: list[int] | None = None,
    ) -> None:
        self.protocol = protocol
        self.syntax = syntax
        self.domain = domain
        self.resolve_box = resolve_box
        self.infer_grades = infer_grades
        self.custom_domains = dict(custom_domains or {})
        self.declarations: dict[str, Node] = {}
        self.records: dict[str, Node] = {}
        self.unions: dict[str, Node] = {}
        self.inductives: dict[str, Node] = {}
        self.record_specs: dict[str, _RecordSpec] = {}
        self.union_specs: dict[str, _UnionSpec] = {}
        self.inductive_specs: dict[str, _InductiveSpec] = {}
        self.ctor_to_record: dict[str, str] = {}
        self.ctor_to_union: dict[str, tuple[str, int]] = {}
        self.ctor_to_inductive: dict[str, str] = {}
        self.box_names: set[str] = set()
        self.used_box_names: set[str] = set()
        self.annotations: set[int] = set()
        self.binders: dict[int, _IRBinderMeta] = {}
        self.definitions: list[_Definition] = []
        self.compiled_defs: dict[str, tuple[IRTerm, IRTy]] = {}
        self.seen_definitions: set[str] = set()
        self.imports: dict[str, tuple[str, GradeExport]] = {}
        self.box_imports: dict[str, GradeDomain] = {}
        self.provider_receipts: list[str] = []
        self.resolve_import: GradeResolver | None = None
        self._uid_counter = uid_counter if uid_counter is not None else [1]
        self._next_rec_id = 1
        self._next_ind_id = 1
        self._hole_count = 0

        for decl in cast("list[Node]", syntax["declarations"]):
            kind = decl["kind"]
            if kind in {"definition", "function", "theorem", "lemma"}:
                self.declarations[_name(decl["name"])] = decl
            elif kind == "record":
                rname = _name(decl["name"])
                self.records[rname] = decl
                for gd in GradeDomain:
                    if rname == "Box" and _valid_box_record(decl, gd):
                        self.box_names.add(rname)
            elif kind == "union":
                self.unions[_name(decl["name"])] = decl
            elif kind == "inductive":
                self.inductives[_name(decl["name"])] = decl
            elif kind == "domain":
                dname = _name(decl["name"])
                if dname not in self.custom_domains:
                    entries = {
                        cast("str", e["role"]): cast("Node", e["value"])
                        for e in cast("list[Node]", decl["entries"])
                    }
                    carrier_node = entries.get("carrier")
                    carrier_name = (
                        _name(carrier_node["name"])
                        if carrier_node is not None and carrier_node["kind"] == "type"
                        else "Nat"
                    )
                    if carrier_name == "bool":
                        self.custom_domains[dname] = CustomDomainSpec(
                            name=dname, rocq_name="PresenceJoin", carrier_key="bool",
                            zero_expr="false", one_expr="true", add_expr="orb", mul_expr="andb",
                            allows_expr="fun a b => implb a b = true", allowsb_expr="implb",
                            eqb_expr="Bool.eqb", subgraded=True,
                        )
                    else:
                        self.custom_domains[dname] = CustomDomainSpec(
                            name=dname, rocq_name="NatBoundJoin", carrier_key="nat",
                            zero_expr="0", one_expr="1", add_expr="Nat.add", mul_expr="Nat.mul",
                            allows_expr="Nat.le", allowsb_expr="Nat.leb",
                            eqb_expr="Nat.eqb", subgraded=True,
                        )

    def _fresh_uid(self) -> int:
        uid = self._uid_counter[0]
        self._uid_counter[0] += 1
        return uid

    def _fresh_hole(self, name: str, span: list[int]) -> GHole:
        self._hole_count += 1
        return GHole(f"g_{self._hole_count}", name, tuple(span))

    def _register_binder(self, name: str, span: list[int], s: GExpr, r: GExpr | None,
                         explicit_r: bool, role: str = "binder", uid: int | None = None) -> int:
        actual_uid = self._fresh_uid() if uid is None else uid
        self.binders[actual_uid] = _IRBinderMeta(
            uid=actual_uid,
            name=name,
            span=list(span),
            domain=self.domain,
            s=s,
            r=r,
            explicit_r=explicit_r,
            role=role,
        )
        return actual_uid

    def _parse_gexpr(self, node: Node, gvars: Mapping[str, int]) -> GExpr:
        kind = node["kind"]
        if kind == "hole":
            return self._fresh_hole("_", _span(node))
        if kind == "name":
            text = _name(node)
            if text == "_":
                return self._fresh_hole("_", _span(node))
            if text in gvars:
                return GVar(text, gvars[text])
            try:
                lit = _rocq_grade_sort_value(self.domain, text)
                return GLit(lit)
            except ValueError as err:
                raise self.protocol.error("grade", f"unknown grade expression '{text}'", node) from err
        if kind == "type" and not node["arguments"]:
            return self._parse_gexpr({"kind": "name", "span": node["span"], "name": node["name"]}, gvars)
        if kind == "nat":
            val = _nat_val(node)
            try:
                return GLit(_rocq_grade_sort_value(self.domain, val))
            except ValueError as err:
                raise self.protocol.error("grade", str(err), node) from err
        if kind == "bool":
            val = cast("bool", node["value"])
            return GLit(_rocq_grade_sort_value(self.domain, val))
        if kind in {"group", "computed_type"}:
            return self._parse_gexpr(cast("Node", node["value"]), gvars)
        if kind in {"group_type", "type_argument"}:
            return self._parse_gexpr(cast("Node", node["type"]), gvars)
        if kind == "binary":
            op = _name(node["operator"])
            lhs = self._parse_gexpr(cast("Node", node["left"]), gvars)
            rhs = self._parse_gexpr(cast("Node", node["right"]), gvars)
            if op == "+":
                return GAdd(lhs, rhs)
            if op == "*":
                return GMul(lhs, rhs)
            raise self.protocol.error("unsupported", f"unsupported grade operator '{op}'", node)
        raise self.protocol.error("grade", "unsupported grade expression form", node)

    def _parse_grade_ann(
        self,
        ann: Node | None,
        owner: Node,
        gvars: Mapping[str, int],
        *,
        allow_omitted: bool = False,
    ) -> tuple[GExpr, GExpr | None, bool]:
        """Parse `@ ...` annotation into `(s, r_or_none, explicit_r)`."""
        if ann is None:
            if self.infer_grades or allow_omitted:
                return self._fresh_hole(f"s_{_name(owner['name']) if owner.get('name') else 'local'}", _span(owner)), None, False
            raise self.protocol.error("grade", "graded definition requires grade annotations on all parameters", owner)
        self.annotations.add(id(owner))
        if ann["kind"] == "hole" or (ann["kind"] == "name" and _name(ann) == "_"):
            return self._fresh_hole("s_hole", _span(ann)), None, False
        if ann["kind"] == "tuple":
            vals = cast("list[Node]", ann["values"])
            if len(vals) != 2:
                raise self.protocol.error("grade", "grade pair requires exactly two components (computation, type)", ann)
            s = self._parse_gexpr(vals[0], gvars)
            r = self._parse_gexpr(vals[1], gvars)
            return s, r, True
        if ann["kind"] == "call":
            callee = cast("Node", ann["callee"])
            args = cast("list[Node]", ann["arguments"])
            if callee["kind"] != "name":
                raise self.protocol.error("grade", "grade annotation expects a domain name", ann)
            dname = _name(callee["name"])
            expected_name = self.domain.name if isinstance(self.domain, CustomDomainSpec) else self.domain.value
            if dname != expected_name and dname not in GradeDomain and dname not in self.custom_domains:
                raise self.protocol.error("unsupported", f"unknown grade domain '{dname}'", ann)
            if dname != expected_name:
                raise self.protocol.error(
                    "unsupported",
                    f"a graded definition requires a single grade domain (expected explicit @ {expected_name}(n) allowance)",
                    owner,
                )
            if not (1 <= len(args) <= 2):
                raise self.protocol.error("grade", "domain grade expects 1 or 2 arguments", ann)
            s = self._parse_gexpr(cast("Node", args[0]["value"]), gvars)
            if len(args) == 2:
                r = self._parse_gexpr(cast("Node", args[1]["value"]), gvars)
                return s, r, True
            return s, None, False
        # Symbolic bare expression such as `@ q` or `@ q + r`
        s = self._parse_gexpr(ann, gvars)
        return s, None, False

    def _callee_path(self, node: Node) -> str | None:
        if node["kind"] == "name":
            return _name(node)
        if node["kind"] == "member":
            return _IntrinsicsMixin._dotted_member_path(node)
        return None

    def _is_box_name(self, name: str) -> bool:
        short = name.rsplit(".", 1)[-1]
        if name in self.box_names or short in self.box_names:
            self.used_box_names.add(short)
            return True
        if self.resolve_box is not None:
            resolved = self.resolve_box(name) or self.resolve_box(short)
            if resolved is not None:
                self.box_imports[name] = resolved
                self.used_box_names.add(short)
                return True
        return False

    def _ensure_record(self, rname: str) -> _RecordSpec:
        if rname in self.record_specs:
            return self.record_specs[rname]
        decl = self.records[rname]
        params = cast("list[Node]", decl["parameters"])
        rec_id = self._next_rec_id
        self._next_rec_id += 1
        fields: list[tuple[str, str, str | None, GExpr, IRTy]] = []
        param_env: dict[str, tuple[int, str, IRTy]] = {}
        rec_gvars: dict[str, int] = {}
        for gnode in cast("list[Node]", decl["generics"]):
            gname = _name(gnode["name"])
            if gnode["mode"] == "grade":
                rec_gvars[gname] = len(rec_gvars)
            elif gnode["mode"] == "type":
                param_env[gname] = (self._fresh_uid(), "val", IRUniv(0))
        is_dep = False
        for param in params:
            pname = _name(param["name"])
            ptype_node = cast("Node | None", param["type"])
            if ptype_node is None:
                raise self.protocol.error("unsupported", f"record '{rname}' field '{pname}' requires a type", param)
            if param.get("grade") is not None:
                s_g, _, _ = self._parse_grade_ann(cast("Node", param["grade"]), param, rec_gvars)
            else:
                s_g = _gone(self.domain)
            # Check dependency on prior record fields
            try:
                ir_ft = self._lower_type(ptype_node, param_env, rec_gvars)
            except Exception as err:
                raise self.protocol.error("unsupported", f"record '{rname}' field '{pname}' has unsupported type: {err}", param) from err
            if any(uid in _IRAnalyzer(self.domain).ty_demand(ir_ft) for uid, _, _ in param_env.values()):
                is_dep = True
            fuid = self._fresh_uid()
            # Ensure nominal ordering in dependent records: only Nat/Type earlier fields can be depended upon cleanly.
            for dep_uid in _IRAnalyzer(self.domain).ty_demand(ir_ft):
                for p_uid, _, p_ty in param_env.values():
                    if p_uid == dep_uid and not isinstance(p_ty, (IRNat, IRUniv)):
                        raise self.protocol.error("unsupported", f"record '{rname}' depends on non-index field", param)
            param_env[pname] = (fuid, "val", ir_ft)
            fields.append((pname, pname, None, s_g, ir_ft))
        spec = _RecordSpec(
            name=rname,
            rec_id=rec_id,
            fields=tuple(fields),
            is_dependent_pair=(len(fields) == 2 and is_dep),
            is_box=(rname in self.box_names),
        )
        self.record_specs[rname] = spec
        self.ctor_to_record[rname] = rname
        return spec

    def _ensure_union(self, uname: str) -> _UnionSpec:
        if uname in self.union_specs:
            return self.union_specs[uname]
        decl = self.unions[uname]
        generics = tuple(_name(g["name"]) for g in cast("list[Node]", decl["generics"]) if g["mode"] == "type")
        ctors: list[tuple[str, tuple[tuple[str, Node], ...]]] = []
        for idx, cnode in enumerate(cast("list[Node]", decl["constructors"])):
            cname = _name(cnode["name"])
            cparams = [(_name(p["name"]), cast("Node", p["type"])) for p in cast("list[Node]", cnode["parameters"])]
            ctors.append((cname, tuple(cparams)))
            self.ctor_to_union[cname] = (uname, idx)
        spec = _UnionSpec(uname, generics, tuple(ctors))
        self.union_specs[uname] = spec
        return spec

    def _ensure_inductive(self, iname: str) -> _InductiveSpec:
        if iname in self.inductive_specs:
            return self.inductive_specs[iname]
        decl = self.inductives[iname]
        ind_id = self._next_ind_id
        self._next_ind_id += 1
        gens: list[tuple[str, str, str | None]] = []
        for g in cast("list[Node]", decl["generics"]):
            gtype = cast("Node | None", g.get("type"))
            tname = _name(gtype["name"]) if gtype is not None and isinstance(gtype.get("name"), dict) else None
            gens.append((cast("str", g["mode"]), _name(g["name"]), tname))
        ctors: list[tuple[str, list[Node], Node | None]] = []
        for cnode in cast("list[Node]", decl["constructors"]):
            cname = _name(cnode["name"])
            ctors.append((cname, cast("list[Node]", cnode["parameters"]), cast("Node | None", cnode.get("result"))))
            self.ctor_to_inductive[cname] = iname
        spec = _InductiveSpec(iname, ind_id, tuple(gens), tuple(ctors))
        self.inductive_specs[iname] = spec
        return spec

    def _lower_idx(self, node: Node, env: Mapping[str, tuple[int, str, IRTy]], gvars: Mapping[str, int]) -> IRIdx:
        kind = node["kind"]
        if kind == "nat":
            return IRIdxLit(_nat_val(node))
        if kind == "name":
            text = _name(node)
            if text not in env:
                raise self.protocol.error("grade", f"unknown index variable '{text}'", node)
            uid, role, _ = env[text]
            if role == "unbox":
                return IRIdxUnbox(uid)
            if role == "fst":
                return IRIdxFst(uid)
            if role == "snd":
                return IRIdxSnd(uid)
            return IRIdxVar(uid)
        if kind == "type":
            if node["arguments"]:
                raise self.protocol.error("grade", "type application cannot appear as a natural index", node)
            text = _name(node["name"])
            if text not in env:
                raise self.protocol.error("grade", f"unknown index variable '{text}'", node)
            uid, role, _ = env[text]
            return IRIdxUnbox(uid) if role == "unbox" else (
                IRIdxFst(uid) if role == "fst" else (IRIdxSnd(uid) if role == "snd" else IRIdxVar(uid))
            )
        if kind in {"group", "computed_type"}:
            return self._lower_idx(cast("Node", node["value"]), env, gvars)
        if kind == "group_type":
            return self._lower_idx(cast("Node", node["type"]), env, gvars)
        if kind == "binary":
            op = _name(node["operator"])
            if op != "+":
                raise self.protocol.error("unsupported", f"natural index operator '{op}' is outside GradedCore", node)
            return IRIdxAdd(
                self._lower_idx(cast("Node", node["left"]), env, gvars),
                self._lower_idx(cast("Node", node["right"]), env, gvars),
            )
        if kind == "member":
            target = cast("Node", node["value"])
            field = _name(node["name"])
            # Case: Box<Nat, q>(x).Value
            if target["kind"] == "call":
                callee = cast("Node", target["callee"])
                if callee["kind"] == "generic_application":
                    base = cast("Node", callee["value"])
                    if base["kind"] == "name" and self._is_box_name(_name(base["name"])) and field == "Value":
                        targs = cast("list[Node]", callee["arguments"])
                        q_g = self._parse_gexpr(_type_arg(targs[1]), gvars)
                        arg_val = cast("Node", cast("list[Node]", target["arguments"])[0]["value"])
                        return IRIdxProm(q_g, self._lower_idx(arg_val, env, gvars))
                elif callee["kind"] == "name" and _name(callee["name"]) in self.records:
                    spec = self._ensure_record(_name(callee["name"]))
                    fnames = [f[0] for f in spec.fields]
                    if field in fnames:
                        fidx = fnames.index(field)
                        arg_node = cast("Node", cast("list[Node]", target["arguments"])[fidx]["value"])
                        return self._lower_idx(arg_node, env, gvars)
            # Case: var.Field
            if target["kind"] == "name":
                vname = _name(target)
                if vname in env:
                    uid, _, ty = env[vname]
                    if isinstance(ty, IRBox) and field == "Value":
                        return IRIdxUnbox(uid)
                    if isinstance(ty, IRSigma) and ty.nominal_name in self.records:
                        spec = self._ensure_record(ty.nominal_name)
                        if spec.fields[0][0] == field:
                            return IRIdxFst(uid)
                        if spec.fields[1][0] == field:
                            return IRIdxSnd(uid)
                        raise self.protocol.error("grade", f"unknown field '{field}' on '{ty.nominal_name}'", node)
                    if field == "Length":
                        return IRIdxFst(uid)
                    if field == "Ticks":
                        return IRIdxFst(uid)
                    if field in {"Samples", "Values"}:
                        return IRIdxSnd(uid)
            raise self.protocol.error("grade", f"unsupported index member '{field}'", node)
        if kind == "match_expression":
            scrut_node = cast("Node", node["value"])
            if scrut_node["kind"] != "name" or _name(scrut_node) not in env:
                raise self.protocol.error("grade", "sum index case expects a scrutinee variable", node)
            uid, _, _ = env[_name(scrut_node)]
            cases = cast("list[Node]", node["cases"])
            if len(cases) != 2:
                raise self.protocol.error("grade", "sum index case expects 2 branches", node)
            l_uid = self._fresh_uid()
            r_uid = self._fresh_uid()
            l_env = dict(env)
            r_env = dict(env)
            l_pat = cast("Node", cases[0]["pattern"])
            r_pat = cast("Node", cases[1]["pattern"])
            l_args = cast("list[Node]", l_pat["arguments"]) if l_pat["kind"] == "constructor_pattern" else []
            if l_args:
                l_arg = l_args[0]
                l_name = _name(l_arg["name"]) if l_arg.get("name") else "l"
                l_env[l_name] = (l_uid, "val", IRNat())
            r_args = cast("list[Node]", r_pat["arguments"]) if r_pat["kind"] == "constructor_pattern" else []
            if r_args:
                r_arg = r_args[0]
                r_name = _name(r_arg["name"]) if r_arg.get("name") else "r"
                r_env[r_name] = (r_uid, "val", IRNat())
            return IRIdxCase(
                uid,
                l_uid,
                r_uid,
                self._lower_idx(cast("Node", cases[0]["value"]), l_env, gvars),
                self._lower_idx(cast("Node", cases[1]["value"]), r_env, gvars),
            )
        raise self.protocol.error("grade", f"unsupported index expression kind '{kind}'", node)

    def _lower_type(
        self,
        node: Node,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
    ) -> IRTy:
        kind = node["kind"]
        if kind == "group_type":
            return self._lower_type(cast("Node", node["type"]), env, gvars)
        if kind == "tuple_type":
            types = cast("list[Node]", node["types"])
            if len(types) < 2:
                raise self.protocol.error("unsupported", "tuple type requires at least 2 fields", node)
            cur = self._lower_type(types[-1], env, gvars)
            for item in reversed(types[:-1]):
                uid = self._fresh_uid()
                cur = IRSigma(uid, _gzero(self.domain), self._lower_type(item, env, gvars), cur)
            return cur
        if kind == "function_type":
            params = cast("list[Node]", node["parameters"])
            ret_node = cast("Node", node["result"])
            local_env = dict(env)
            binders: list[tuple[int, GExpr, GExpr | None, IRTy]] = []
            for p in params:
                pname = _name(p["name"]) if p.get("name") is not None else f"_arg{self._fresh_uid()}"
                ptype = cast("Node", p["type"])
                dom_ty = self._lower_type(ptype, local_env, gvars)
                s_g, r_g, explicit_r = self._parse_grade_ann(cast("Node | None", p.get("grade")), p, gvars)
                puid = self._register_binder(pname, _span(p), s_g, r_g, explicit_r, role="fn_param")
                local_env[pname] = (puid, "val", dom_ty)
                binders.append((puid, s_g, r_g, dom_ty))
            cur = self._lower_type(ret_node, local_env, gvars)
            for puid, s_g, r_g, dom_ty in reversed(binders):
                cur = IRPi(puid, s_g, r_g, dom_ty, cur)
            return cur
        if kind != "type":
            raise self.protocol.error("unsupported", f"type '{kind}' is outside GradedCore", node)
        tname = _name(node["name"])
        args = cast("list[Node]", node["arguments"])
        if tname == "Nat":
            if args:
                raise self.protocol.error("unsupported", "Nat takes no type arguments", node)
            return IRNat()
        if tname == "bool":
            if args:
                raise self.protocol.error("unsupported", "bool takes no type arguments", node)
            return IRBool()
        if tname == "Type":
            if not args:
                return IRUniv(0)
            if len(args) == 1:
                lvl_node = _type_arg(args[0])
                if lvl_node["kind"] == "nat":
                    return IRUniv(_nat_val(lvl_node))
            raise self.protocol.error("unsupported", "Type<n> requires a literal natural universe level", node)
        if tname == "Vec":
            if len(args) != 2:
                raise self.protocol.error("unsupported", "Vec requires element type and length index", node)
            elem = self._lower_type(_type_arg(args[0]), env, gvars)
            length = self._lower_idx(_type_arg(args[1]), env, gvars)
            return IRVec(elem, length)
        if self._is_box_name(tname):
            if len(args) != 2:
                raise self.protocol.error("unsupported", "Box requires payload type and grade", node)
            inner = self._lower_type(_type_arg(args[0]), env, gvars)
            q = self._parse_gexpr(_type_arg(args[1]), gvars)
            return IRBox(q, inner)
        if tname in env:
            uid, role, _ = env[tname]
            if role == "unbox":
                return IRTUnbox(uid)
            return IRTVar(uid)
        if tname in self.records:
            spec = self._ensure_record(tname)
            if spec.is_dependent_pair:
                puid = self._fresh_uid()
                f0_name, _, _, _, f0_ty = spec.fields[0]
                f1_param_node = cast("Node", cast("list[Node]", self.records[tname]["parameters"])[1]["type"])
                dep_env = dict(env)
                dep_env[f0_name] = (puid, "val", f0_ty)
                f1_ty = self._lower_type(f1_param_node, dep_env, gvars)
                r_dem = _IRAnalyzer(self.domain).ty_demand(f1_ty).get(puid, _gzero(self.domain))
                return IRSigma(puid, r_dem, f0_ty, f1_ty, nominal_name=tname)
            return IRRecord(
                spec.rec_id,
                tuple((idx, fg, ft) for idx, (_, _, _, fg, ft) in enumerate(spec.fields)),
                nominal_name=tname,
            )
        if tname in self.unions:
            uspec = self._ensure_union(tname)
            if len(uspec.ctors) != 2:
                raise self.protocol.error("unsupported", f"union '{tname}' must have 2 constructors for Sum projection", node)
            subst_map = {gname: _type_arg(arg) for gname, arg in zip(uspec.generics, args, strict=True)}
            c0 = uspec.ctors[0][1]
            c1 = uspec.ctors[1][1]
            t0 = self._lower_type_subst(c0[0][1], subst_map, env, gvars) if c0 else IRNat()
            t1 = self._lower_type_subst(c1[0][1], subst_map, env, gvars) if c1 else IRNat()
            return IRSum(t0, t1, nominal_name=tname)
        if tname in self.inductives:
            ispec = self._ensure_inductive(tname)
            idx_vals: list[IRIdx] = []
            for (gmode, _, _), arg in zip(ispec.generics, args, strict=False):
                arg_node = _type_arg(arg)
                if ((gmode in ("value", "ghost") or arg_node["kind"] in ("nat", "name", "binary"))
                        and (arg_node["kind"] != "type" or _name(arg_node["name"]) in env)):
                    with contextlib.suppress(Exception):
                        idx_vals.append(self._lower_idx(arg_node, env, gvars))
            return IRInd(ispec.ind_id, tuple(idx_vals), nominal_name=tname)
        raise self.protocol.error("unsupported", f"unknown type '{tname}' in graded declaration", node)

    def _lower_type_subst(
        self,
        node: Node,
        subst_map: Mapping[str, Node],
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
    ) -> IRTy:
        if node["kind"] == "type" and not node["arguments"] and _name(node["name"]) in subst_map:
            return self._lower_type(subst_map[_name(node["name"])], env, gvars)
        return self._lower_type(node, env, gvars)

    def _resolve_callable_import(self, name: str, node: Node) -> tuple[IRTerm, IRTy] | None:
        if name in self.compiled_defs:
            return self.compiled_defs[name]
        if name in self.declarations:
            self.definition(name)
            return self.compiled_defs[name]
        if self.resolve_import is not None:
            resolved = self.resolve_import(name)
            if resolved is not None:
                mod_name, exp = resolved
                if exp.domain != self.domain:
                    raise self.protocol.error(
                        "unsupported",
                        f"imported declaration '{name}' requires the {exp.domain.value} grade domain",
                        node,
                    )
                self.imports[name] = (mod_name, exp)
                self.provider_receipts.append(f"(* Import {mod_name}.{exp.name}: SHA256 {exp.receipt} *)")
                imp_lower = _CoreLowerer(
                    exp.protocol,
                    exp.syntax,
                    self.domain,
                    resolve_box=lambda bn: exp.box_imports.get(bn) or (self.resolve_box(bn) if self.resolve_box else None),
                    infer_grades=self.infer_grades,
                    custom_domains={**self.custom_domains, **exp.custom_domains},
                    uid_counter=self._uid_counter,
                )
                imp_lower.resolve_import = lambda dep_name, exp_imps=exp.imports: exp_imps.get(dep_name)
                imp_lower.definition(exp.name)
                return imp_lower.compiled_defs[exp.name]
        return None

    def _lower_expr(
        self,
        node: Node,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
        *,
        expected_ty: IRTy | None = None,
    ) -> IRTerm:
        kind = node["kind"]
        if kind == "group":
            return self._lower_expr(cast("Node", node["value"]), env, gvars, expected_ty=expected_ty)
        if kind == "nat":
            return IRNatVal(IRIdxLit(_nat_val(node)))
        if kind == "bool":
            return IRBoolVal(cast("bool", node["value"]))
        if kind == "type_expression":
            return IRTypeVal(self._lower_type(cast("Node", node["type"]), env, gvars))
        if kind == "name":
            vname = _name(node)
            if vname in env:
                uid, _, _ = env[vname]
                return IRVar(uid)
            resolved = self._resolve_callable_import(vname, node)
            if resolved is not None:
                return resolved[0]
            raise self.protocol.error("grade", f"unknown variable '{vname}' in graded expression", node)
        if kind == "binary":
            op = _name(node["operator"])
            if op != "+":
                raise self.protocol.error("unsupported", f"operator '{op}' is outside GradedCore", node)
            try:
                return IRNatVal(IRIdxAdd(
                    self._lower_idx(cast("Node", node["left"]), env, gvars),
                    self._lower_idx(cast("Node", node["right"]), env, gvars),
                ))
            except HoldFastError:
                lhs_ir = self._lower_expr(cast("Node", node["left"]), env, gvars, expected_ty=IRNat())
                rhs_ir = self._lower_expr(cast("Node", node["right"]), env, gvars, expected_ty=IRNat())
                luid = self._fresh_uid()
                ruid = self._fresh_uid()
                return IRLet(
                    luid, f"_add_l{luid}", tuple(_span(cast("Node", node["left"]))),
                    _gone(self.domain), _gzero(self.domain), IRNat(), lhs_ir,
                    IRLet(
                        ruid, f"_add_r{ruid}", tuple(_span(cast("Node", node["right"]))),
                        _gone(self.domain), _gzero(self.domain), IRNat(), rhs_ir,
                        IRNatVal(IRIdxAdd(IRIdxVar(luid), IRIdxVar(ruid))),
                        False,
                    ),
                    False,
                )
        if kind == "tuple":
            vals = cast("list[Node]", node["values"])
            if len(vals) < 2:
                raise self.protocol.error("unsupported", "tuple requires at least 2 elements", node)
            sub_exp = expected_ty
            cur_val = self._lower_expr(vals[-1], env, gvars)
            an = _IRAnalyzer(self.domain)
            for uid, _, ty in env.values():
                an.env_types[uid] = ty
            for vnode in reversed(vals[:-1]):
                fst_term = self._lower_expr(vnode, env, gvars)
                fst_ty, _, _ = an.infer(fst_term)
                snd_ty, _, _ = an.infer(cur_val)
                uid = self._fresh_uid()
                r_g = sub_exp.r if isinstance(sub_exp, IRSigma) else _gzero(self.domain)
                cur_val = IRPair(uid, r_g, fst_ty, snd_ty, fst_term, cur_val)
            return cur_val
        if kind == "if_expression":
            return IRIf(
                self._lower_expr(cast("Node", node["condition"]), env, gvars),
                self._lower_expr(cast("Node", node["then"]), env, gvars, expected_ty=expected_ty),
                self._lower_expr(cast("Node", node["else"]), env, gvars, expected_ty=expected_ty),
            )
        if kind == "let_expression":
            binding = cast("Node", node["binding"])
            bkind = binding["kind"]
            body_node = cast("Node", node["body"])
            if bkind == "let_pattern":
                pat = cast("Node", binding["pattern"])
                rhs_term = self._lower_expr(cast("Node", binding["value"]), env, gvars)
                rhs_ty, _, _ = _IRAnalyzer(self.domain).infer(rhs_term)
                if pat["kind"] == "constructor_pattern":
                    return self._lower_single_constructor_unpack(
                        pat, rhs_term, rhs_ty, body_node, expected_ty, env, gvars,
                    )
                if pat["kind"] == "tuple_pattern":
                    return self._lower_tuple_unpack(pat, rhs_term, rhs_ty, body_node, expected_ty, env, gvars)
                raise self.protocol.error("unsupported", f"unsupported let pattern '{pat['kind']}'", pat)
            bname = _name(binding["name"])
            if bname == "_" or bname in env:
                raise self.protocol.error("grade", f"duplicate or invalid graded binder '{bname}'", binding)
            rhs_term = self._lower_expr(cast("Node", binding["value"]), env, gvars)
            rhs_ty, _, _ = _IRAnalyzer(self.domain).infer(rhs_term)
            ann_ty = (
                self._lower_type(cast("Node", binding["type"]), env, gvars)
                if binding.get("type") is not None else rhs_ty
            )
            s_g, r_g, explicit_r = self._parse_grade_ann(
                cast("Node | None", binding.get("grade")), binding, gvars, allow_omitted=False,
            )
            luid = self._register_binder(bname, _span(binding), s_g, r_g, explicit_r, role="let")
            local_env = dict(env)
            local_env[bname] = (luid, "val", ann_ty)
            bod_term = self._lower_expr(body_node, local_env, gvars, expected_ty=expected_ty)
            return IRLet(luid, bname, tuple(_span(binding)), s_g, r_g, ann_ty, rhs_term, bod_term, explicit_r)
        if kind == "lambda":
            params = cast("list[Node]", node["parameters"])
            body_node = cast("Node", node["body"])
            return self._lower_lambda_chain(params, body_node, env, gvars, expected_ty=expected_ty)
        if kind == "typed_lambda":
            sig = cast("Node", node["signature"])
            params = cast("list[Node]", sig["parameters"])
            body_node = cast("Node", node["body"])
            return self._lower_lambda_chain(params, body_node, env, gvars, expected_ty=expected_ty)
        if kind == "member":
            target = cast("Node", node["value"])
            fname = _name(node["name"])
            if target["kind"] == "call":
                callee = cast("Node", target["callee"])
                if callee["kind"] == "generic_application":
                    base = cast("Node", callee["value"])
                    if base["kind"] == "name" and self._is_box_name(_name(base["name"])) and fname == "Value":
                        targs = cast("list[Node]", callee["arguments"])
                        q_g = self._parse_gexpr(_type_arg(targs[1]), gvars)
                        inner_val = cast("Node", cast("list[Node]", target["arguments"])[0]["value"])
                        promoted = IRPromote(q_g, self._lower_expr(inner_val, env, gvars))
                        xuid = self._fresh_uid()
                        mot = expected_ty if expected_ty is not None else IRNat()
                        muid = self._fresh_uid()
                        return IRLetBox(xuid, "unboxed", tuple(_span(node)), _gzero(self.domain), muid, mot, promoted, IRVar(xuid))
                elif callee["kind"] == "name" and _name(callee["name"]) in self.records:
                    spec = self._ensure_record(_name(callee["name"]))
                    fnames = [f[0] for f in spec.fields]
                    if fname in fnames:
                        return self._lower_expr(cast("Node", cast("list[Node]", target["arguments"])[fnames.index(fname)]["value"]), env, gvars)
            if target["kind"] == "name" and _name(target) in env:
                uid, _, ty = env[_name(target)]
                if isinstance(ty, IRBox) and fname == "Value":
                    xuid = self._fresh_uid()
                    mot = expected_ty if expected_ty is not None else ty.inner
                    muid = self._fresh_uid()
                    return IRLetBox(xuid, "unboxed", tuple(_span(node)), _gzero(self.domain), muid, mot, IRVar(uid), IRVar(xuid))
            dotted = _IntrinsicsMixin._dotted_member_path(node)
            if dotted is not None:
                resolved = self._resolve_callable_import(dotted, node)
                if resolved is not None:
                    return resolved[0]
            raise self.protocol.error("grade", f"unsupported member projection '.{fname}'", node)
        if kind == "match_expression":
            return self._lower_match_expr(node, env, gvars, expected_ty=expected_ty)
        if kind == "call":
            return self._lower_call_expr(node, env, gvars, expected_ty=expected_ty)
        raise self.protocol.error("unsupported", f"expression '{kind}' is outside GradedCore", node)

    def _lower_lambda_chain(
        self,
        params: list[Node],
        body_node: Node,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
        *,
        expected_ty: IRTy | None,
    ) -> IRTerm:
        if not params:
            return self._lower_expr(body_node, env, gvars, expected_ty=expected_ty)
        p = params[0]
        pname = _name(p["name"])
        if pname == "_" or pname in env:
            raise self.protocol.error("grade", f"duplicate or invalid graded binder '{pname}'", p)
        dom_ty = self._lower_type(cast("Node", p["type"]), env, gvars) if p.get("type") is not None else (
            expected_ty.dom if isinstance(expected_ty, IRPi) else IRNat()
        )
        s_g, r_g, explicit_r = self._parse_grade_ann(cast("Node | None", p.get("grade")), p, gvars)
        puid = self._register_binder(pname, _span(p), s_g, r_g, explicit_r, role="lambda")
        local_env = dict(env)
        local_env[pname] = (puid, "val", dom_ty)
        next_exp = expected_ty.cod if isinstance(expected_ty, IRPi) else None
        if isinstance(expected_ty, IRPi) and expected_ty.uid != puid:
            next_exp = _subst_uid_ty(expected_ty.cod, expected_ty.uid, rep_idx=IRIdxVar(puid), rep_ty=IRTVar(puid))
        bod = self._lower_lambda_chain(params[1:], body_node, local_env, gvars, expected_ty=next_exp)
        return IRLam(puid, pname, tuple(_span(p)), s_g, r_g, dom_ty, bod, explicit_r)

    def _lower_call_expr(
        self,
        node: Node,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
        *,
        expected_ty: IRTy | None,
    ) -> IRTerm:
        callee = cast("Node", node["callee"])
        args: list[Node] = []
        for a in cast("list[Node]", node["arguments"]):
            if a.get("label") is not None:
                raise self.protocol.error("unsupported", "labeled call arguments are not supported in graded checking", a)
            args.append(cast("Node", a["value"]))
        if callee["kind"] == "generic_application":
            base = cast("Node", callee["value"])
            bname = self._callee_path(base)
            if bname is not None and self._is_box_name(bname):
                targs = cast("list[Node]", callee["arguments"])
                q_g = self._parse_gexpr(_type_arg(targs[1]), gvars)
                inner_t = self._lower_type(_type_arg(targs[0]), env, gvars)
                return IRPromote(q_g, self._lower_expr(args[0], env, gvars, expected_ty=inner_t))
            if bname is not None and (bname in self.ctor_to_union or bname.rsplit(".", 1)[-1] in self.ctor_to_union):
                targs = cast("list[Node]", callee["arguments"])
                cname_short = bname if bname in self.ctor_to_union else bname.rsplit(".", 1)[-1]
                uname, cidx = self.ctor_to_union[cname_short]
                uspec = self._ensure_union(uname)
                subst_map = {gn: _type_arg(ta) for gn, ta in zip(uspec.generics, targs, strict=True)}
                lhs_t = self._lower_type_subst(uspec.ctors[0][1][0][1], subst_map, env, gvars) if uspec.ctors[0][1] else IRNat()
                rhs_t = self._lower_type_subst(uspec.ctors[1][1][0][1], subst_map, env, gvars) if uspec.ctors[1][1] else IRNat()
                val = self._lower_expr(args[0], env, gvars, expected_ty=lhs_t if cidx == 0 else rhs_t)
                return IRInl(rhs_t, val, uname) if cidx == 0 else IRInr(lhs_t, val, uname)
            if bname is not None and (
                bname in self.declarations or bname in self.compiled_defs
                or (self.resolve_import is not None and self.resolve_import(bname) is not None)
            ):
                targs = cast("list[Node]", callee["arguments"])
                resolved = self._resolve_callable_import(bname, node)
                if resolved is None:
                    raise self.protocol.error("grade", f"unknown callable '{bname}'", node)
                fn_term, fn_ty = resolved
                cur_term = fn_term
                cur_ty = fn_ty
                for ta in targs:
                    ta_ty = self._lower_type(_type_arg(ta), env, gvars)
                    cur_term = IRApp(cur_term, IRTypeVal(ta_ty))
                    if isinstance(cur_ty, IRPi):
                        cur_ty = _subst_uid_ty(cur_ty.cod, cur_ty.uid, rep_ty=ta_ty)
                for a_node in args:
                    a_val = self._lower_expr(a_node, env, gvars, expected_ty=cur_ty.dom if isinstance(cur_ty, IRPi) else None)
                    cur_term = IRApp(cur_term, a_val)
                    if isinstance(cur_ty, IRPi):
                        cur_ty = _IRAnalyzer(self.domain)._app_ty(cur_ty.dom, cur_ty.cod, a_val, cur_ty.uid)
                return cur_term
        cname = self._callee_path(callee)
        if cname is not None:
            short_c = cname.rsplit(".", 1)[-1]
            if cname in self.records or short_c in self.records:
                rkey = cname if cname in self.records else short_c
                spec = self._ensure_record(rkey)
                if len(args) != len(spec.fields):
                    raise self.protocol.error("grade", f"record '{rkey}' expects {len(spec.fields)} arguments", node)
                if spec.is_dependent_pair:
                    f0_val = self._lower_expr(args[0], env, gvars, expected_ty=spec.fields[0][4])
                    fuid = self._fresh_uid()
                    f1_pnode = cast("Node", cast("list[Node]", self.records[rkey]["parameters"])[1]["type"])
                    dep_env = dict(env)
                    dep_env[spec.fields[0][0]] = (fuid, "val", spec.fields[0][4])
                    f1_ty = self._lower_type(f1_pnode, dep_env, gvars)
                    r_dem = _IRAnalyzer(self.domain).ty_demand(f1_ty).get(fuid, _gzero(self.domain))
                    snd_expected = _IRAnalyzer(self.domain)._app_ty(spec.fields[0][4], f1_ty, f0_val, fuid)
                    f1_val = self._lower_expr(args[1], env, gvars, expected_ty=snd_expected)
                    return IRPair(fuid, r_dem, spec.fields[0][4], f1_ty, f0_val, f1_val, nominal_name=rkey)
                rec_fields = tuple(
                    (idx, fg, ft, self._lower_expr(arg, env, gvars, expected_ty=ft))
                    for idx, ((_, _, _, fg, ft), arg) in enumerate(zip(spec.fields, args, strict=True))
                )
                return IRRecordMk(spec.rec_id, rec_fields, nominal_name=rkey)
            if cname in self.ctor_to_union or short_c in self.ctor_to_union:
                ukey = cname if cname in self.ctor_to_union else short_c
                uname, cidx = self.ctor_to_union[ukey]
                uspec = self._ensure_union(uname)
                if isinstance(expected_ty, IRSum):
                    lhs_t, rhs_t = expected_ty.lhs, expected_ty.rhs
                else:
                    lhs_t = self._lower_type(uspec.ctors[0][1][0][1], env, gvars) if uspec.ctors[0][1] else IRNat()
                    rhs_t = self._lower_type(uspec.ctors[1][1][0][1], env, gvars) if uspec.ctors[1][1] else IRNat()
                val = self._lower_expr(args[0], env, gvars, expected_ty=lhs_t if cidx == 0 else rhs_t)
                return IRInl(rhs_t, val, uname) if cidx == 0 else IRInr(lhs_t, val, uname)
            if cname in env:
                uid, _, ty = env[cname]
                cur: IRTerm = IRVar(uid)
                cur_t = ty
                for a_node in args:
                    a_val = self._lower_expr(a_node, env, gvars, expected_ty=cur_t.dom if isinstance(cur_t, IRPi) else None)
                    cur = IRApp(cur, a_val)
                    if isinstance(cur_t, IRPi):
                        cur_t = _IRAnalyzer(self.domain)._app_ty(cur_t.dom, cur_t.cod, a_val, cur_t.uid)
                return cur
            resolved = self._resolve_callable_import(cname, node)
            if resolved is not None:
                fn_term, fn_ty = resolved
                cur = fn_term
                cur_t = fn_ty
                for a_node in args:
                    a_val = self._lower_expr(a_node, env, gvars, expected_ty=cur_t.dom if isinstance(cur_t, IRPi) else None)
                    cur = IRApp(cur, a_val)
                    if isinstance(cur_t, IRPi):
                        cur_t = _IRAnalyzer(self.domain)._app_ty(cur_t.dom, cur_t.cod, a_val, cur_t.uid)
                return cur
        # General lambda application `(params => body)(arg1, ...)`
        fn_term = self._lower_expr(callee, env, gvars)
        cur = fn_term
        for a_node in args:
            cur = IRApp(cur, self._lower_expr(a_node, env, gvars))
        return cur

    def _lower_single_constructor_unpack(
        self,
        pat: Node,
        rhs_term: IRTerm,
        rhs_ty: IRTy,
        body_node: Node,
        expected_ty: IRTy | None,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
    ) -> IRLetBox:
        cname = _name(pat["name"])
        pargs = cast("list[Node]", pat["arguments"])
        if not self._is_box_name(cname) or len(pargs) != 1 or not isinstance(rhs_ty, IRBox):
            raise self.protocol.error("unsupported", f"let-pattern '{cname}' requires Box<T, q>", pat)
        bpat = pargs[0]
        bname = _name(bpat["name"])
        kappa = _gzero(self.domain)
        xuid = self._fresh_uid()
        muid = self._fresh_uid()
        local_env = dict(env)
        local_env[bname] = (xuid, "val", rhs_ty.inner)
        bod = self._lower_expr(body_node, local_env, gvars, expected_ty=expected_ty)
        bod_ty, _, _ = _IRAnalyzer(self.domain, infer_holes=self.infer_grades).infer(bod)
        return IRLetBox(xuid, bname, tuple(_span(bpat)), kappa, muid, expected_ty or bod_ty, rhs_term, bod)

    def _lower_tuple_unpack(
        self,
        pat: Node,
        rhs_term: IRTerm,
        rhs_ty: IRTy,
        body_node: Node,
        expected_ty: IRTy | None,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
    ) -> IRLetPair:
        sub_pats = cast("list[Node]", pat["patterns"])
        if len(sub_pats) != 2 or not isinstance(rhs_ty, IRSigma):
            raise self.protocol.error("unsupported", "tuple unpack requires a binary dependent or product pair", pat)
        xname = _name(sub_pats[0]["name"])
        yname = _name(sub_pats[1]["name"])
        xuid = self._fresh_uid()
        yuid = self._fresh_uid()
        local_env = dict(env)
        local_env[xname] = (xuid, "val", rhs_ty.fst_ty)
        snd_ty = _subst_uid_ty(rhs_ty.snd_ty, rhs_ty.uid, rep_idx=IRIdxVar(xuid), rep_ty=IRTVar(xuid))
        local_env[yname] = (yuid, "val", snd_ty)
        bod = self._lower_expr(body_node, local_env, gvars, expected_ty=expected_ty)
        an = _IRAnalyzer(self.domain)
        an.env_types.update({xuid: rhs_ty.fst_ty, yuid: snd_ty})
        bod_ty, u_b, _ = an.infer(bod)
        ux = u_b.get(xuid, _gzero(self.domain))
        uy = u_b.get(yuid, _gzero(self.domain))
        s = _gexpr_join(ux, uy, self.domain)
        muid = self._fresh_uid()
        return IRLetPair(xuid, yuid, xname, yname, tuple(_span(sub_pats[0])), tuple(_span(sub_pats[1])),
                         s, _gzero(self.domain), muid, expected_ty or bod_ty, rhs_term, bod)

    def _lower_match_expr(
        self,
        node: Node,
        env: Mapping[str, tuple[int, str, IRTy]],
        gvars: Mapping[str, int],
        *,
        expected_ty: IRTy | None,
    ) -> IRTerm:
        scrut_node = cast("Node", node["value"])
        scrut_term = self._lower_expr(scrut_node, env, gvars)
        an = _IRAnalyzer(self.domain)
        for uid, _, ty in env.values():
            an.env_types[uid] = ty
        scrut_ty, _, _ = an.infer(scrut_term)
        motive_node = cast("Node | None", node.get("motive"))
        cases = cast("list[Node]", node["cases"])
        muid = self._fresh_uid()
        mot_var = _name(motive_node["name"]) if motive_node is not None else f"_whole_{muid}"
        kappa_g = _gzero(self.domain)
        explicit_kappa = False
        if motive_node is not None and motive_node.get("grade") is not None:
            kappa_g, _, _ = self._parse_grade_ann(cast("Node", motive_node["grade"]), motive_node, gvars)
            explicit_kappa = True

        # Lower Box match
        if isinstance(scrut_ty, IRBox):
            if len(cases) != 1:
                raise self.protocol.error("grade", "Box match requires exactly 1 Box(...) branch", node)
            pat = cast("Node", cases[0]["pattern"])
            if pat["kind"] != "constructor_pattern" or not self._is_box_name(_name(pat["name"])):
                raise self.protocol.error("grade", "Box scrutinee must match a Box constructor pattern", pat)
            pargs = cast("list[Node]", pat["arguments"])
            bpat = pargs[0]
            bname = _name(bpat["name"]) if bpat.get("name") else "v"
            xuid = self._fresh_uid()
            mot_env = dict(env)
            mot_env[mot_var] = (muid, "unbox", scrut_ty)
            if motive_node is not None:
                motive_ty = self._lower_type(cast("Node", motive_node["type"]), mot_env, gvars)
            else:
                motive_ty = expected_ty if expected_ty is not None else IRNat()
            if not explicit_kappa:
                kappa_g = an.ty_demand(motive_ty).get(muid, _gzero(self.domain))
            else:
                self._register_binder(f"{mot_var}(motive)", _span(motive_node or node), kappa_g, kappa_g, True, role="motive", uid=0)
            bod_env = dict(env)
            bod_env[bname] = (xuid, "val", scrut_ty.inner)
            bod_exp = an._subst_box_nat_ty(motive_ty, muid, scrut_ty.grade, IRIdxVar(xuid)) if isinstance(scrut_ty.inner, IRNat) else motive_ty
            bod_term = self._lower_expr(cast("Node", cases[0]["value"]), bod_env, gvars, expected_ty=bod_exp)
            return IRLetBox(xuid, bname, tuple(_span(bpat)), kappa_g, muid, motive_ty, scrut_term, bod_term)

        # Lower dependent pair / Sigma match
        if isinstance(scrut_ty, IRSigma):
            if len(cases) != 1:
                raise self.protocol.error("grade", "dependent record match requires 1 branch", node)
            pat = cast("Node", cases[0]["pattern"])
            if pat["kind"] == "constructor_pattern":
                pat_cname = _name(pat["name"])
                if scrut_ty.nominal_name is not None and pat_cname != scrut_ty.nominal_name:
                    raise self.protocol.error(
                        "grade",
                        f"inferred graded type differs from the declared dependent type ('{pat_cname}' vs '{scrut_ty.nominal_name}')",
                        pat,
                    )
                pargs = cast("list[Node]", pat["arguments"])
            elif pat["kind"] == "tuple_pattern":
                pargs = cast("list[Node]", pat["patterns"])
            else:
                raise self.protocol.error("grade", "expected constructor or tuple pattern for pair", pat)
            if len(pargs) != 2:
                raise self.protocol.error("grade", "pair pattern requires 2 binders", pat)
            xname = _name(pargs[0]["name"])
            yname = _name(pargs[1]["name"])
            xuid = self._fresh_uid()
            yuid = self._fresh_uid()
            mot_env = dict(env)
            mot_env[mot_var] = (muid, "record_scrut", scrut_ty)
            motive_ty = (
                self._lower_type(cast("Node", motive_node["type"]), mot_env, gvars)
                if motive_node is not None else (expected_ty if expected_ty is not None else IRNat())
            )
            if not explicit_kappa:
                kappa_g = an.ty_demand(motive_ty).get(muid, _gzero(self.domain))
            bod_env = dict(env)
            bod_env[xname] = (xuid, "val", scrut_ty.fst_ty)
            snd_ty = _subst_uid_ty(scrut_ty.snd_ty, scrut_ty.uid, rep_idx=IRIdxVar(xuid), rep_ty=IRTVar(xuid))
            bod_env[yname] = (yuid, "val", snd_ty)
            bod_exp = an._subst_pair_ty(motive_ty, muid, IRIdxVar(xuid), IRIdxVar(yuid))
            bod_term = self._lower_expr(cast("Node", cases[0]["value"]), bod_env, gvars, expected_ty=bod_exp)
            # Determine s from x and y uses in bod_term
            bod_an = _IRAnalyzer(self.domain)
            bod_an.env_types.update(an.env_types)
            bod_an.env_types[xuid] = scrut_ty.fst_ty
            bod_an.env_types[yuid] = snd_ty
            _, u_b, _ = bod_an.infer(bod_term)
            ux = u_b.get(xuid, _gzero(self.domain))
            uy = u_b.get(yuid, _gzero(self.domain))
            s_g = _gexpr_join(ux, uy, self.domain)
            if pargs[0].get("grade") is not None:
                s_g, _, _ = self._parse_grade_ann(cast("Node", pargs[0]["grade"]), pargs[0], gvars)
            return IRLetPair(xuid, yuid, xname, yname, tuple(_span(pargs[0])), tuple(_span(pargs[1])),
                             s_g, kappa_g, muid, motive_ty, scrut_term, bod_term)

        # Lower Sum match (2 constructors)
        if isinstance(scrut_ty, IRSum):
            if len(cases) != 2:
                raise self.protocol.error("grade", "sum match requires 2 branches", node)
            uspec = self.union_specs.get(scrut_ty.nominal_name or "")
            lcase, rcase = cases[0], cases[1]
            if uspec is not None:
                c0_name = uspec.ctors[0][0]
                p0 = cast("Node", lcase["pattern"])
                if p0["kind"] == "constructor_pattern" and _name(p0["name"]) != c0_name:
                    lcase, rcase = rcase, lcase
            lp, rp = cast("Node", lcase["pattern"]), cast("Node", rcase["pattern"])
            lp_args = cast("list[Node]", lp["arguments"]) if lp.get("arguments") else []
            rp_args = cast("list[Node]", rp["arguments"]) if rp.get("arguments") else []
            xpat = lp_args[0] if lp_args else lp
            ypat = rp_args[0] if rp_args else rp
            xname = _name(xpat["name"]) if xpat.get("name") else "l"
            yname = _name(ypat["name"]) if ypat.get("name") else "r"
            xuid = self._fresh_uid()
            yuid = self._fresh_uid()
            mot_env = dict(env)
            mot_env[mot_var] = (muid, "sum_scrut", scrut_ty)
            motive_ty = (
                self._lower_type(cast("Node", motive_node["type"]), mot_env, gvars)
                if motive_node is not None else (expected_ty if expected_ty is not None else IRNat())
            )
            if not explicit_kappa:
                kappa_g = an.ty_demand(motive_ty).get(muid, _gzero(self.domain))
            l_env = dict(env)
            l_env[xname] = (xuid, "val", scrut_ty.lhs)
            r_env = dict(env)
            r_env[yname] = (yuid, "val", scrut_ty.rhs)
            lb = self._lower_expr(cast("Node", lcase["value"]), l_env, gvars, expected_ty=expected_ty)
            rb = self._lower_expr(cast("Node", rcase["value"]), r_env, gvars, expected_ty=expected_ty)
            bod_an = _IRAnalyzer(self.domain)
            bod_an.env_types.update(an.env_types)
            bod_an.env_types[xuid] = scrut_ty.lhs
            _, u_l, _ = bod_an.infer(lb)
            bod_an.env_types[yuid] = scrut_ty.rhs
            _, u_r, _ = bod_an.infer(rb)
            ux = u_l.get(xuid, _gzero(self.domain))
            uy = u_r.get(yuid, _gzero(self.domain))
            s_g = _gexpr_join(ux, uy, self.domain)
            if _is_gzero(s_g, self.domain):
                s_g = _gone(self.domain)
            return IRMatchSum(xuid, yuid, xname, yname, tuple(_span(xpat)), tuple(_span(ypat)),
                              s_g, kappa_g, muid, motive_ty, scrut_term, lb, rb)

        # Lower general non-dependent record match
        if isinstance(scrut_ty, IRRecord):
            if len(cases) != 1:
                raise self.protocol.error("grade", "record match requires 1 branch", node)
            pat = cast("Node", cases[0]["pattern"])
            pargs = cast("list[Node]", pat["arguments"])
            binders: list[tuple[int, str, tuple[int, ...]]] = []
            bod_env = dict(env)
            for parg, (_, _, ft) in zip(pargs, scrut_ty.fields, strict=True):
                bname = _name(parg["name"])
                buid = self._fresh_uid()
                binders.append((buid, bname, tuple(_span(parg))))
                bod_env[bname] = (buid, "val", ft)
            mot_ty = (
                self._lower_type(cast("Node", motive_node["type"]), env, gvars)
                if motive_node is not None else (expected_ty if expected_ty is not None else IRNat())
            )
            bod = self._lower_expr(cast("Node", cases[0]["value"]), bod_env, gvars, expected_ty=mot_ty)
            return IRMatchRecord(scrut_ty.rec_id, _gone(self.domain), muid, mot_ty, scrut_term, tuple(binders), bod)

        # Lower bool match `match (flag) { true => ..., false => ... }` to IRIf
        if isinstance(scrut_ty, IRBool) and len(cases) == 2:
            p0 = cast("Node", cases[0]["pattern"])
            p1 = cast("Node", cases[1]["pattern"])
            if p0["kind"] == "bool_pattern" and p1["kind"] == "bool_pattern" and p0["value"] != p1["value"]:
                th_case, el_case = (cases[0], cases[1]) if p0["value"] else (cases[1], cases[0])
                th = self._lower_expr(cast("Node", th_case["value"]), env, gvars, expected_ty=expected_ty)
                el = self._lower_expr(cast("Node", el_case["value"]), env, gvars, expected_ty=expected_ty)
                return IRIf(scrut_term, th, el)

        raise self.protocol.error("unsupported", "unsupported match scrutinee in GradedCore", node)

    def _extract_callable_body(self, decl: Node) -> Node:
        kind = decl["kind"]
        if kind == "definition":
            return cast("Node", decl["value"])
        if kind == "function":
            body = cast("Node | None", decl.get("body"))
            if body is None:
                raise self.protocol.error("unsupported", "abstract function cannot be grade-replayed", decl)
            if body["kind"] == "expression_body":
                return cast("Node", body["value"])
            if body["kind"] == "block":
                stmts = cast("list[Node]", body["statements"])
                if not stmts:
                    raise self.protocol.error("unsupported", "empty function block has no graded return", body)
                return self._block_to_let_expr(stmts, body)
        raise self.protocol.error("unsupported", f"declaration kind '{kind}' has no pure expression body", decl)

    def _block_to_let_expr(self, stmts: list[Node], owner: Node) -> Node:
        if len(stmts) == 1:
            last = stmts[0]
            if last["kind"] == "return" and last.get("value") is not None:
                return cast("Node", last["value"])
            if last["kind"] == "expression_statement":
                return cast("Node", last["value"])
            raise self.protocol.error("unsupported", "graded function block must end in a return expression", last)
        head = stmts[0]
        if head["kind"] not in {"let", "var", "typed_local"}:
            raise self.protocol.error("unsupported", f"statement '{head['kind']}' in graded function is unsupported", head)
        return {
            "kind": "let_expression",
            "span": head["span"],
            "binding": head,
            "body": self._block_to_let_expr(stmts[1:], owner),
        }

    def definition(self, name: str) -> _Definition:
        if name in self.seen_definitions:
            for d in self.definitions:
                if d.name == name:
                    return d
        decl = self.declarations.get(name)
        if decl is None:
            raise self.protocol.error("unsupported", f"unknown graded declaration '{name}'", self.syntax)

        # Parse generic parameters: Type/Type<n> generics -> outer Pi binders; <grade q : D> -> symbolic gvars!
        generics = cast("list[Node]", decl["generics"])
        gvars: dict[str, int] = {}
        env: dict[str, tuple[int, str, IRTy]] = {}
        type_param_binders: list[tuple[int, str, list[int], GExpr, GExpr | None, bool, IRTy]] = []
        next_gv = 0
        for gp in generics:
            gname = _name(gp["name"])
            gmode = cast("str", gp["mode"])
            if gmode == "grade":
                gvars[gname] = next_gv
                next_gv += 1
                self.annotations.add(id(gp))
            elif gmode == "type":
                lvl = 0
                if gp.get("type") is not None:
                    tnode = cast("Node", gp["type"])
                    if tnode["kind"] == "type" and _name(tnode["name"]) == "Type":
                        targs = cast("list[Node]", tnode["arguments"])
                        if targs:
                            lvl_arg = _type_arg(targs[0])
                            if lvl_arg["kind"] == "nat":
                                lvl = _nat_val(lvl_arg)
                dom_ty: IRTy = IRUniv(lvl)
                uid = self._register_binder(gname, _span(gp), _gzero(self.domain), None, False, role="type_generic")
                env[gname] = (uid, "val", dom_ty)
                type_param_binders.append((uid, gname, _span(gp), _gzero(self.domain), None, False, dom_ty))
            elif gmode == "ghost":
                dom_ty = self._lower_type(cast("Node", gp["type"]), env, gvars)
                uid = self._register_binder(gname, _span(gp), _gzero(self.domain), None, False, role="ghost_generic")
                env[gname] = (uid, "val", dom_ty)
                type_param_binders.append((uid, gname, _span(gp), _gzero(self.domain), None, False, dom_ty))

        val_params = cast("list[Node]", decl["parameters"])
        param_binders: list[tuple[int, str, list[int], GExpr, GExpr | None, bool, IRTy]] = []
        top_params: list[_Parameter] = []
        for p in val_params:
            if p.get("const"):
                raise self.protocol.error("unsupported", "const parameters are not supported in graded checking", p)
            pname = _name(p["name"])
            if pname == "_" or pname in env:
                raise self.protocol.error("grade", f"duplicate or invalid graded binder '{pname}'", p)
            dom_ty = self._lower_type(cast("Node", p["type"]), env, gvars)
            s_g, r_g, explicit_r = self._parse_grade_ann(cast("Node | None", p.get("grade")), p, gvars)
            puid = self._register_binder(pname, _span(p), s_g, r_g, explicit_r, role="param")
            env[pname] = (puid, "val", dom_ty)
            param_binders.append((puid, pname, _span(p), s_g, r_g, explicit_r, dom_ty))

        all_binders = [*type_param_binders, *param_binders]
        ret_node = cast("Node", decl["result"])
        ret_ty = self._lower_type(ret_node, env, gvars)
        body_node = self._extract_callable_body(decl)
        open_body = self._lower_expr(body_node, env, gvars, expected_ty=ret_ty)

        # Build closed term and closed expected Pi
        closed_term: IRTerm = open_body
        closed_expected: IRTy = ret_ty
        for uid, pname, pspan, s_g, r_g, explicit_r, dom_ty in reversed(all_binders):
            closed_term = IRLam(uid, pname, tuple(pspan), s_g, r_g, dom_ty, closed_term, explicit_r)
            closed_expected = IRPi(uid, s_g, r_g, dom_ty, closed_expected)

        # Solve any GHole grade inference targets via graded_inference.py
        solved_term, solved_exp, inferred_info = _solve_ir_grade_holes(self.protocol, closed_term, closed_expected, self.domain)
        # Fill omitted r values inside the IR so Rocq source_check_core verifies exact (s, r) everywhere
        filled_term, filled_exp, uid_aliases = _fill_omitted_r_and_pi(solved_term, solved_exp, self.domain)

        # Extract updated open_body / open_ret / open_params from filled_term
        # Peel BOTH declaration binders AND leading top-level curried lambdas!
        cur_t: IRTerm = filled_term
        cur_e: IRTy = filled_exp
        open_env_entries: list[tuple[int, IRTy, str]] = []
        param_meta_by_uid: dict[int, tuple[GExpr, GExpr, IRTy]] = {}
        peeled_binders: list[tuple[int, str, list[int], GExpr, GExpr | None, bool, IRTy]] = list(all_binders)
        for uid, pname, _pspan, _, _, _, _ in all_binders:
            if not isinstance(cur_t, IRLam) or not isinstance(cur_e, IRPi) or cur_t.r is None:
                raise RuntimeError("expected lambda/pi telescope matching binders")
            open_env_entries.append((uid, cur_t.dom, pname))
            param_meta_by_uid[uid] = (cur_t.s, cur_t.r, cur_t.dom)
            cur_t = cur_t.body
            cur_e = cur_e.cod
        # Peel leading IRLam binders matched against Fn(...) -> ... codomain
        while isinstance(cur_t, IRLam) and isinstance(cur_e, IRPi):
            lam_r = cur_t.r if cur_t.r is not None else _gzero(self.domain)
            sig_uid = uid_aliases.get(cur_t.uid, cur_e.uid)
            sig_meta = self.binders.get(sig_uid)
            exposed_name = (
                sig_meta.name
                if sig_meta is not None and sig_meta.role == "fn_param" and not sig_meta.name.startswith("_arg")
                else cur_t.name
            )
            open_env_entries.append((cur_t.uid, cur_t.dom, exposed_name))
            param_meta_by_uid[cur_t.uid] = (cur_t.s, lam_r, cur_t.dom)
            peeled_binders.append((cur_t.uid, exposed_name, list(cur_t.span), cur_t.s, lam_r, cur_t.explicit_r, cur_t.dom))
            if cur_e.uid != cur_t.uid:
                cur_e = _subst_uid_ty(cur_e.cod, cur_e.uid, rep_idx=IRIdxVar(cur_t.uid), rep_ty=IRTVar(cur_t.uid))
            else:
                cur_e = cur_e.cod
            cur_t = cur_t.body
        open_body_filled = cur_t
        open_ret_filled = cur_e

        # Record any extra trailing Pi params behind non-modal-elim bodies (e.g. `Specialize`, `StereoRoute`, `Shape`),
        # leaving LetBox/LetPair dependent motives unpeeled for result_type_uses.
        trailing_pi_params: list[tuple[int, str, list[int], GExpr, GExpr | None, bool, IRTy]] = []
        if not isinstance(open_body_filled, (IRLetBox, IRLetPair)):
            probe_e = open_ret_filled
            while isinstance(probe_e, IRPi):
                p_meta = self.binders.get(probe_e.uid)
                pname = p_meta.name if p_meta is not None else f"_p{probe_e.uid}"
                pspan = list(p_meta.span) if p_meta is not None else [0, 0]
                pr = probe_e.r if probe_e.r is not None else _gzero(self.domain)
                trailing_pi_params.append((probe_e.uid, pname, pspan, probe_e.s, pr, False, probe_e.dom))
                param_meta_by_uid[probe_e.uid] = (probe_e.s, pr, probe_e.dom)
                probe_e = probe_e.cod

        # Compute symbolic sample valuation (for <grade q : D> polymorphism) + symbolic gexpr obligations
        gvar_env: dict[int, str] | None = None
        symbolic_obs: list[tuple[GExpr, GExpr, str, int, str]] = []
        if gvars:
            default_sample = (
                self.domain.one_expr
                if isinstance(self.domain, CustomDomainSpec)
                else _domain_spec(self.domain).one
            )
            gvar_env = dict.fromkeys(gvars.values(), default_sample)
            an = _IRAnalyzer(self.domain)
            _, u_closed, v_closed = an.infer(filled_term)
            # Check symbolic computation & type demands on all binders in filled_term
            def _collect_sym(t: IRTerm) -> tuple[dict[int, GExpr], dict[int, GExpr]]:
                if isinstance(t, IRLam):
                    old = an.env_types.get(t.uid)
                    an.env_types[t.uid] = t.dom
                    u_b, v_b = _collect_sym(t.body)
                    if old is None:
                        an.env_types.pop(t.uid, None)
                    else:
                        an.env_types[t.uid] = old
                    u_act = u_b.pop(t.uid, _gzero(self.domain))
                    v_act = v_b.pop(t.uid, _gzero(self.domain))
                    if t.s.has_var() or u_act.has_var():
                        symbolic_obs.append((u_act, t.s, t.name, t.uid, "computation"))
                    if t.r is not None and (t.r.has_var() or v_act.has_var()):
                        symbolic_obs.append((v_act, t.r, t.name, t.uid, "type"))
                    return u_b, an.add_maps(an.ty_demand(t.dom), v_b)
                if isinstance(t, IRLet):
                    u_r, v_r = _collect_sym(t.rhs)
                    old = an.env_types.get(t.uid)
                    an.env_types[t.uid] = t.ann
                    u_b, v_b = _collect_sym(t.body)
                    if old is None:
                        an.env_types.pop(t.uid, None)
                    else:
                        an.env_types[t.uid] = old
                    u_act = u_b.pop(t.uid, _gzero(self.domain))
                    v_act = v_b.pop(t.uid, _gzero(self.domain))
                    if t.s.has_var() or u_act.has_var():
                        symbolic_obs.append((u_act, t.s, t.name, t.uid, "computation"))
                    if t.r is not None and (t.r.has_var() or v_act.has_var()):
                        symbolic_obs.append((v_act, t.r, t.name, t.uid, "type"))
                    z_t = v_r if isinstance(t.ann, IRUniv) and isinstance(t.rhs, IRTypeVal) else u_r
                    return an.add_maps(u_b, an.scale_map(t.s, u_r)), an.add_maps(v_b, an.scale_map(t.r or v_act, z_t))
                return an.infer(t)[1:]
            _ = (u_closed, v_closed)
            _collect_sym(filled_term)

        # Build parameter list for JSON report (peeled params + trailing Pi params in declaration order!)
        report_binders = [*peeled_binders, *trailing_pi_params]
        for idx, (uid, pname, pspan, _, _, explicit_r, _) in enumerate(report_binders):
            s_val, r_val, _ = param_meta_by_uid[uid]
            s_str = _serialize_gexpr_rocq(s_val, self.domain, gvar_env)
            r_str = _serialize_gexpr_rocq(r_val, self.domain, gvar_env)
            top_params.append(_Parameter(
                index=idx,
                uid=uid,
                name=pname,
                span=pspan,
                domain=self.domain.name if isinstance(self.domain, CustomDomainSpec) else self.domain.value,
                allowance=s_str,
                expected_type_uses=r_str if explicit_r else None,
            ))

        # Build zero-type-use binders list from filled IR (parameters with total r == 0)
        an_zero = _IRAnalyzer(self.domain)
        _, _, _ = an_zero.infer(filled_term)
        zero_binders: list[tuple[int, str, list[int]]] = []
        for uid, pname, pspan, _, _, _, _ in peeled_binders:
            _, r_val, _ = param_meta_by_uid[uid]
            r_lit = _serialize_gexpr_rocq(r_val, self.domain, gvar_env)
            # Note: also require not appearing in any subsequent parameter's annotation!
            in_later_ann = any(
                uid in an_zero.ty_demand(later_dom)
                for later_uid, later_dom, _ in open_env_entries
                if later_uid > uid
            )
            if r_lit in _BOUND_ZERO_VALUES and not in_later_ann:
                zero_binders.append((uid, pname, pspan))

        # Detect if closed check has omitted-r elimination divergence (`r_body != r_cod` in exact domain).
        is_sub = isinstance(self.domain, CustomDomainSpec) or _domain_spec(self.domain).subgraded
        closed_compatible = True
        if not is_sub and open_env_entries:
            an_compat = _IRAnalyzer(self.domain)
            for u, dt, _ in open_env_entries:
                an_compat.env_types[u] = dt
            _, _, v_bod = an_compat.infer(open_body_filled)
            dem_ret = an_compat.ty_demand(open_ret_filled)
            for uid, _, _pspan, _, _, explicit_r, _ in peeled_binders:
                if not explicit_r:
                    rb = _serialize_gexpr_rocq(v_bod.get(uid, _gzero(self.domain)), self.domain, gvar_env)
                    rc = _serialize_gexpr_rocq(dem_ret.get(uid, _gzero(self.domain)), self.domain, gvar_env)
                    if rb != rc:
                        closed_compatible = False
                        break

        # Serialize closed and open forms for Rocq GradedCoreSource
        closed_term_g = _to_rocq_cterm(filled_term, [], self.domain, gvar_env)
        closed_exp_g = _to_rocq_cty(filled_exp, [], self.domain, gvar_env)

        # Build open_env in De Bruijn order (newest innermost at index 0)
        open_env_items: list[str] = []
        open_uids_prefix: list[int] = []
        an_open = _IRAnalyzer(self.domain)
        for uid, dom_ty, _ in open_env_entries:
            # Prior binders are in open_uids_prefix (already innermost-first)
            dom_s = _to_rocq_cty(dom_ty, open_uids_prefix, self.domain, gvar_env)
            dem = an_open.ty_demand(dom_ty)
            t_uses = [
                _serialize_gexpr_rocq(dem.get(prev_uid, _gzero(self.domain)), self.domain, gvar_env)
                for prev_uid in open_uids_prefix
            ]
            entry = (
                f"{{| cbinder := {uid}; cannotation := {dom_s}; "
                f"ctype_uses := [{'; '.join(t_uses)}] |}}"
            )
            open_env_items.insert(0, entry)
            open_uids_prefix.insert(0, uid)

        open_env_g = "[" + "; ".join(open_env_entries_g := open_env_items) + "]"
        _ = open_env_entries_g
        open_body_g = _to_rocq_cterm(open_body_filled, open_uids_prefix, self.domain, gvar_env)
        open_ret_g = _to_rocq_cty(open_ret_filled, open_uids_prefix, self.domain, gvar_env)

        used_records = tuple(sorted(set(self.record_specs) | set(self.union_specs) | set(self.inductive_specs) | self.used_box_names))
        # Build top-level binder allowances in De Bruijn order (`None` when omitted for open-check)
        open_expected_s: list[str] = []
        open_expected_r: list[str | None] = []
        open_uids_db: list[int] = [uid for uid, _, _ in reversed(open_env_entries)]
        meta_by_uid = {uid: (s_g, r_g, exp_r) for uid, _, _, s_g, r_g, exp_r, _ in peeled_binders}
        for uid in open_uids_db:
            s_g, r_g, exp_r = meta_by_uid[uid]
            open_expected_s.append(_serialize_gexpr_rocq(s_g, self.domain, gvar_env))
            open_expected_r.append(
                _serialize_gexpr_rocq(r_g, self.domain, gvar_env) if exp_r and r_g is not None else None
            )

        # Build trailing Pi param metadata when IRLet precedes inner lambdas (e.g. Shape)
        trailing_meta: list[tuple[_Parameter, tuple[int, object, list[int], object]]] = []
        base_idx = len(peeled_binders)
        an_trail = _IRAnalyzer(self.domain)
        trail_env_params: list[_Parameter] = list(reversed(top_params[:base_idx]))
        for t_offset, (t_uid, _t_name, t_span, t_s, t_r, _, t_dom) in enumerate(trailing_pi_params):
            t_param = top_params[base_idx + t_offset]
            t_dem = an_trail.ty_demand(t_dom)
            t_ann = [
                {
                    "name": ep.name,
                    "span": ep.span,
                    "uses": _format_grade_atom(_serialize_gexpr_rocq(t_dem.get(ep.uid, _gzero(self.domain)), self.domain, gvar_env)),
                }
                for ep in trail_env_params
                if ep.uid in t_dem and not _is_gzero(t_dem[ep.uid], self.domain)
            ]
            t_s_atom = _format_grade_atom(_serialize_gexpr_rocq(t_s, self.domain, gvar_env))
            t_r_atom = _format_grade_atom(_serialize_gexpr_rocq(t_r or _gzero(self.domain), self.domain, gvar_env))
            trailing_meta.append((t_param, (t_uid, t_s_atom, t_span, cast("object", (t_r_atom, t_ann)))))
            trail_env_params.insert(0, t_param)

        defn = _Definition(
            index=len(self.definitions) + 1,
            name=name,
            source=decl,
            domain=self.domain,
            ir_term=filled_term,
            ir_expected=filled_exp,
            closed_term_gallina=closed_term_g,
            closed_expected_gallina=closed_exp_g,
            open_env_gallina=open_env_g,
            open_body_gallina=open_body_g,
            open_ret_gallina=open_ret_g,
            top_params=tuple(top_params[:base_idx]),
            binders=dict(self.binders),
            zero_type_use_binders=tuple(zero_binders),
            records=used_records,
            symbolic_gvars=tuple(gvars.items()),
            symbolic_obligations=tuple(symbolic_obs),
            inferred_grades=inferred_info,
            context="core" if closed_compatible else "core-open",
            open_uids_db=tuple(open_uids_db),
            open_expected_s=tuple(open_expected_s),
            open_expected_r=tuple(open_expected_r),
            trailing_pi_params=tuple(trailing_meta),
        )
        self.compiled_defs[name] = (filled_term, filled_exp)
        self.seen_definitions.add(name)
        self.definitions.append(defn)
        return defn


# ---------------------------------------------------------------------------
# Section 6: Certificate Emission, Rocq Execution & Error Decoding
# ---------------------------------------------------------------------------


def _certificate(
    definitions: list[_Definition],
    source_hash: str,
    domain: GradeDomain | CustomDomainSpec,
    provider_receipts: list[str] | None = None,
) -> str:
    if isinstance(domain, CustomDomainSpec):
        d_name = domain.rocq_name
        check_fn = "source_check_core_sub" if domain.subgraded else "source_check_core"
        grade_ty = domain.carrier_key
        base_dom = domain.rocq_name
        subgraded = domain.subgraded
    else:
        spec = _domain_spec(domain)
        d_name = spec.rocq_domain
        check_fn = spec.check_fn
        grade_ty = spec.grade_type
        base_dom = spec.base_domain
        subgraded = spec.subgraded

    lines = [
        "From Corelib Require Import Init.Datatypes.",
        "From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool.",
        "Require Import graded_pure graded_domains graded_core graded_core_source.",
        "Import ListNotations GradedDomains GradedCore GradedCoreSource.",
        f"(* Source SHA256: {source_hash} *)",
    ]
    if provider_receipts is not None and provider_receipts:
        lines.extend(provider_receipts)
    if isinstance(domain, CustomDomainSpec) and domain.gallina_prelude:
        lines.append(domain.gallina_prelude)

    lines.extend([
        f"Definition _D : JoinDomain := {d_name}.",
        f"Definition accepted (r : result (list (list (grade {d_name}))) (grade_error {d_name})) : bool :=",
        "  match r with Ok _ => true | Err _ => false end.",
        f"Fixpoint _vec_add_opt (xs ys : list (grade {d_name})) : list (grade {d_name}) :=",
        "  match xs, ys with",
        "  | [], _ => ys",
        "  | _, [] => xs",
        f"  | x :: xs', y :: ys' => (@add {d_name} x y) :: _vec_add_opt xs' ys'",
        "  end.",
        f"Fixpoint _check_top_comp (uids : list nat) (acts exps : list (grade {d_name})) : result unit (grade_error {d_name}) :=",
        "  match uids, acts, exps with",
        "  | [], _, _ => Ok tt",
        "  | u :: us, a :: acs, e :: exs =>",
        f"      if (@allowsb {d_name} a e) then _check_top_comp us acs exs",
        "      else Err (ErrBinderCompMismatch u a e)",
        "  | _, _, _ => Ok tt",
        "  end.",
        f"Fixpoint _check_top_type (uids : list nat) (acts : list (grade {d_name})) (ann_rows : list (list (grade {d_name})))",
        f"    (acc : list (grade {d_name})) (exps : list (option (grade {d_name}))) : result unit (grade_error {d_name}) :=",
        "  match uids, acts, exps with",
        "  | [], _, _ => Ok tt",
        "  | u :: us, a :: acs, Some e :: exs =>",
        f"      let tot := @add {d_name} a (hd (@zero {d_name}) acc) in",
        "      let next_acc := _vec_add_opt (tl acc) (hd [] ann_rows) in",
        f"      if (@allowsb {d_name} tot e) then _check_top_type us acs (tl ann_rows) next_acc exs",
        "      else Err (ErrBinderTypeMismatch u tot e)",
        "  | _ :: us, _ :: acs, None :: exs =>",
        "      let next_acc := _vec_add_opt (tl acc) (hd [] ann_rows) in",
        "      _check_top_type us acs (tl ann_rows) next_acc exs",
        "  | _, _, _ => Ok tt",
        "  end.",
        f"Definition _check_open_with_top (uids : list nat) (exps_s : list (grade {d_name})) (exps_r : list (option (grade {d_name})))",
        f"    (res : result (list (list (grade {d_name}))) (grade_error {d_name})) : result (list (list (grade {d_name}))) (grade_error {d_name}) :=",
        "  match res with",
        "  | Err e => Err e",
        "  | Ok rows =>",
        "      let comp := hd [] rows in",
        "      let typ := hd [] (tl rows) in",
        "      let anns := tl (tl (tl rows)) in",
        "      match _check_top_comp uids comp exps_s with",
        "      | Err e => Err e",
        "      | Ok tt =>",
        "          match _check_top_type uids typ anns [] exps_r with",
        "          | Err e => Err e",
        "          | Ok tt => Ok [[]; []; []]",
        "          end",
        "      end",
        "  end.",
    ])

    closed_reports: list[str] = []
    open_reports: list[str] = []
    symbolic_checks: list[str] = []

    for defn in definitions:
        num = defn.index
        lines.append(f"Definition source_closed_term_{num} : cterm {d_name} := {defn.closed_term_gallina}.")
        lines.append(f"Definition source_closed_type_{num} : cty {d_name} := {defn.closed_expected_gallina}.")
        lines.append(f"Definition source_open_env_{num} : cenv {d_name} := {defn.open_env_gallina}.")
        lines.append(f"Definition source_open_term_{num} : cterm {d_name} := {defn.open_body_gallina}.")
        lines.append(f"Definition source_open_type_{num} : cty {d_name} := {defn.open_ret_gallina}.")
        open_call = f"({check_fn} (D := {d_name}) source_open_env_{num} source_open_term_{num} source_open_type_{num})"
        open_reports.append(open_call)
        if defn.context == "core":
            closed_reports.append(
                f"({check_fn} (D := {d_name}) [] source_closed_term_{num} source_closed_type_{num})"
            )
        else:
            uids_str = "[" + "; ".join(str(u) for u in defn.open_uids_db) + "]"
            es_str = "[" + "; ".join(defn.open_expected_s) + "]"
            er_str = "[" + "; ".join(
                f"Some ({er})" if er is not None else "None"
                for er in defn.open_expected_r
            ) + "]"
            closed_reports.append(
                f"(_check_open_with_top {uids_str} {es_str} {er_str} {open_call})"
            )
        for s_idx, (act_g, exp_g, _, _, _) in enumerate(defn.symbolic_obligations):
            g_dom = base_dom if (subgraded and not isinstance(domain, CustomDomainSpec)) else d_name
            g_act = _to_rocq_gexpr(act_g, domain, g_dom)
            g_exp = _to_rocq_gexpr(exp_g, domain, g_dom)
            if subgraded and not isinstance(domain, CustomDomainSpec):
                symbolic_checks.append(f"(@gexpr_allowsb {base_dom} {g_act} {g_exp})")
            elif not isinstance(domain, CustomDomainSpec):
                symbolic_checks.append(f"(@gexpr_eqb {d_name} {g_act} {g_exp})")
            _ = s_idx

    _ = grade_ty
    lines.extend([
        f"Definition source_checks : list (result (list (list (grade {d_name}))) (grade_error {d_name})) :=",
        f"  [{'; '.join(closed_reports)}].",
        f"Definition source_reports : list (result (list (list (grade {d_name}))) (grade_error {d_name})) :=",
        f"  [{'; '.join(open_reports)}].",
        f"Definition source_symbolic : list bool := [{'; '.join(symbolic_checks)}].",
        "Set Printing Width 100000.",
        "Set Printing Depth 100000.",
        "Eval vm_compute in source_checks.",
        "Eval vm_compute in source_reports.",
        "Eval vm_compute in source_symbolic.",
        "Example source_checks_ok : forallb accepted source_checks = true.",
        "Proof. vm_compute. reflexivity. Qed.",
        "Example source_replays : forallb accepted source_reports = true.",
        "Proof. vm_compute. reflexivity. Qed.",
        "Example source_symbolic_ok : forallb (fun b => b) source_symbolic = true.",
        "Proof. vm_compute. reflexivity. Qed.",
    ])
    return "\n".join(lines) + "\n"


def _run_rocq(compiler: list[str], directory: Path, unit: str) -> subprocess.CompletedProcess[str]:
    command = [*compiler, "-q", unit]
    deadline = REPLAY_DEADLINE.get()
    budget = 30.0 if deadline is None else min(30.0, deadline - time.monotonic())
    if budget <= 0:
        raise subprocess.TimeoutExpired(command, 0)
    return subprocess.run(command, cwd=directory, capture_output=True,
                          text=True, encoding="utf-8", check=False, timeout=budget)


def _tokenize_coq(text: str) -> list[str]:
    tokens: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
        elif ch in "()[];":
            tokens.append(ch)
            i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "()[];":
                j += 1
            tokens.append(text[i:j])
            i = j
    return tokens


def _parse_coq_value(tokens: list[str], pos: int) -> tuple[object, int]:
    tok = tokens[pos]
    if tok == "[":
        items: list[object] = []
        pos += 1
        while pos < len(tokens) and tokens[pos] != "]":
            if tokens[pos] == ";":
                pos += 1
                continue
            elems: list[object] = []
            while pos < len(tokens) and tokens[pos] not in (";", "]"):
                elem, pos = _parse_coq_value(tokens, pos)
                elems.append(elem)
            items.append(elems[0] if len(elems) == 1 else tuple(elems))
        return items, pos + 1
    if tok == "(":
        parts: list[object] = []
        pos += 1
        while pos < len(tokens) and tokens[pos] != ")":
            item, pos = _parse_coq_value(tokens, pos)
            parts.append(item)
        return tuple(parts), pos + 1
    if tok.isdigit():
        return int(tok), pos + 1
    if tok == "true":
        return True, pos + 1
    if tok == "false":
        return False, pos + 1
    return tok, pos + 1


def _extract_vm_evals(stdout: str) -> list[object]:
    """Parse each `= <value> : <type>` block printed by `Eval vm_compute in ...`."""
    results: list[object] = []
    pattern = re.compile(r"(?m)^\s*=\s*(.*?)\s*:\s*list\s+", re.DOTALL)
    for match in pattern.finditer(stdout):
        tokens = _tokenize_coq(match.group(1))
        if tokens:
            parsed, _ = _parse_coq_value(tokens, 0)
            results.append(parsed)
    return results


def _format_grade_atom(val: object) -> object:
    if isinstance(val, bool):
        return 1 if val else 0
    if isinstance(val, int):
        return val
    s = str(val)
    if s.isdigit():
        return int(s)
    return s


def _format_grade_display(val: object, domain: GradeDomain | CustomDomainSpec) -> str:
    if isinstance(val, bool):
        if domain == GradeDomain.PRESENCE:
            return "1" if val else "0"
        return "true" if val else "false"
    return str(val)


def _unwrap_result_item(item: object) -> tuple[str, object]:
    # item can be ('Ok', rows) or ('Err', err_tuple)
    if isinstance(item, tuple) and len(item) >= 2:
        tag = item[0]
        if tag in ("Ok", "Err"):
            return str(tag), item[1]
    raise RuntimeError(f"unexpected Rocq result shape: {item!r}")


def _raise_decoded_grade_error(
    protocol: _Protocol,
    defn: _Definition,
    err_obj: object,
    domain: GradeDomain | CustomDomainSpec,
) -> None:
    order = domain.name if isinstance(domain, CustomDomainSpec) else _domain_spec(domain).label
    err_tuple = err_obj if isinstance(err_obj, tuple) else (err_obj,)
    ctor = str(err_tuple[0])

    if ctor == "ErrBinderCompMismatch" and len(err_tuple) >= 4:
        binder_uid = cast("int", err_tuple[1])
        actual_s = _format_grade_display(err_tuple[2], domain)
        expected_s = _format_grade_display(err_tuple[3], domain)
        meta = defn.binders.get(binder_uid)
        if meta is not None:
            raise protocol.error(
                "grade",
                f"binder '{meta.name}' fails {order} computation demand (expected {expected_s}, got {actual_s})",
                {"span": meta.span},
            )
        raise protocol.error(
            "grade",
            f"term fails {order} computation demand (expected {expected_s}, got {actual_s})",
            defn.source,
        )

    if ctor == "ErrBinderTypeMismatch" and len(err_tuple) >= 4:
        binder_uid = cast("int", err_tuple[1])
        actual_r = _format_grade_display(err_tuple[2], domain)
        expected_r = _format_grade_display(err_tuple[3], domain)
        meta = defn.binders.get(binder_uid)
        if meta is not None:
            raise protocol.error(
                "grade",
                f"binder '{meta.name}' fails {order} type-use demand (expected {expected_r}, got {actual_r})",
                {"span": meta.span},
            )
        raise protocol.error(
            "grade",
            f"term fails {order} type-use demand (expected {expected_r}, got {actual_r})",
            defn.source,
        )

    if ctor == "ErrMotiveMismatch":
        raise protocol.error(
            "grade",
            f"term fails {order} computation demand, modal motive specialization mismatch ({err_obj})",
            defn.source,
        )
    if ctor == "ErrTypeMismatch":
        if isinstance(err_obj, tuple) and len(err_obj) >= 3:
            act_t, exp_t = err_obj[1], err_obj[2]
            if (isinstance(act_t, tuple) and isinstance(exp_t, tuple)
                    and act_t and exp_t and act_t[0] == "CPi" and exp_t[0] == "CPi"
                    and len(act_t) >= 4 and len(exp_t) >= 4 and act_t[2] != exp_t[2]):
                raise protocol.error(
                    "grade",
                    f"callback fails {order} computation demand (expected {exp_t[2]}, got {act_t[2]}) / differs from the declared dependent type ({err_obj})",
                    defn.source,
                )
            if (isinstance(act_t, tuple) and isinstance(exp_t, tuple)
                    and act_t and exp_t and act_t[0] == "CBox" and exp_t[0] == "CBox"
                    and len(act_t) >= 2 and len(exp_t) >= 2 and act_t[1] != exp_t[1]):
                raise protocol.error(
                    "grade",
                    f"box grade fails {order} computation demand and differs from the declared dependent type (expected {exp_t[1]}, got {act_t[1]})",
                    defn.source,
                )
            if (isinstance(act_t, tuple) and isinstance(exp_t, tuple)
                    and act_t and exp_t and act_t[0] == "CUniv" and exp_t[0] == "CUniv"):
                raise protocol.error(
                    "grade",
                    f"inferred graded type differs from the declared dependent type / fails {order} computation demand or natural-index checking ({err_obj})",
                    defn.source,
                )
            if (isinstance(act_t, tuple) and isinstance(exp_t, tuple)
                    and act_t and exp_t and act_t[0] == "CVec" and exp_t[0] == "CVec"):
                raise protocol.error(
                    "grade",
                    f"inferred graded type differs from the declared dependent type / fails {order} computation demand or natural-index checking ({err_obj})",
                    defn.source,
                )
        raise protocol.error(
            "grade",
            f"inferred graded type differs from the declared dependent type ({err_obj})",
            defn.source,
        )
    if ctor == "ErrSubgradeFailed":
        raise protocol.error(
            "grade",
            f"inferred graded type differs from the declared dependent type (subgrade failed: {err_obj})",
            defn.source,
        )
    if ctor == "ErrUniverseLevel" and len(err_tuple) >= 3:
        raise protocol.error(
            "grade",
            f"universe level mismatch in polymorphic application (expected Type<{err_tuple[2]}>, got Type<{err_tuple[1]}>)",
            defn.source,
        )
    if ctor == "ErrBranchMismatch":
        raise protocol.error(
            "grade",
            f"term fails {order} computation demand in branch checking ({err_obj})",
            defn.source,
        )
    raise protocol.error(
        "grade",
        f"term fails {order} computation demand or natural-index checking ({err_obj})",
        defn.source,
    )


def _verdict(lowerer: _CoreLowerer, replay: subprocess.CompletedProcess[str]) -> list[list[list[object]]]:
    evals = _extract_vm_evals(replay.stdout)
    if len(evals) < 2:
        raise RuntimeError(f"graded core replay gave incomplete verdict: {replay.stderr.strip()}")
    closed_eval = cast("list[object]", evals[0])
    open_eval = cast("list[object]", evals[1])
    symbolic_eval = cast("list[object]", evals[2]) if len(evals) >= 3 else []

    for defn, closed_item in zip(lowerer.definitions, closed_eval, strict=True):
        tag, payload = _unwrap_result_item(closed_item)
        if tag == "Err":
            _raise_decoded_grade_error(lowerer.protocol, defn, payload, defn.domain)

    parsed_rows: list[list[list[object]]] = []
    for defn, open_item in zip(lowerer.definitions, open_eval, strict=True):
        tag, payload = _unwrap_result_item(open_item)
        if tag == "Err":
            _raise_decoded_grade_error(lowerer.protocol, defn, payload, defn.domain)
        raw_rows = cast("list[list[object]]", payload)
        parsed_rows.append([[_format_grade_atom(v) for v in row] for row in raw_rows])

    for sym_ok in symbolic_eval:
        if sym_ok is False:
            defn = lowerer.definitions[-1]
            order = defn.domain.name if isinstance(defn.domain, CustomDomainSpec) else _domain_spec(defn.domain).label
            raise lowerer.protocol.error(
                "grade",
                f"polymorphic symbolic grade constraint failed {order} verification",
                defn.source,
            )

    if replay.returncode:
        raise RuntimeError(f"graded core certificate failed: {replay.stderr.strip()}")
    return parsed_rows


def _compile_support(compiler: list[str], directory: Path, sources: dict[str, bytes]) -> None:
    rocq_cache._compile_all(compiler, directory, sources, _run_rocq)


def _support_cache_root() -> Path | None:
    return rocq_cache.support_cache_root()


def _compiler_sha256(compiler: list[str]) -> str | None:
    return rocq_cache.compiler_sha256(compiler)


def _support(root: Path, compiler: list[str], directory: Path, files: tuple[str, ...]) -> dict[str, str]:
    if not files:
        return {}
    units = [(name, (root / "tools" / "rocq" / name).read_bytes()) for name in files]
    cache_root = _support_cache_root()
    compiler_digest = _compiler_sha256(compiler) if cache_root is not None else None
    return rocq_cache.materialize_units(
        directory,
        units,
        compiler=compiler,
        cache_dir=cache_root,
        compiler_digest=compiler_digest,
        compile_fn=_run_rocq,
        use_default_cache=False,
    )


def _rocq_top_command(compiler: list[str]) -> list[str] | None:
    if len(compiler) >= 2 and Path(compiler[-2]).name == "rocq" and compiler[-1] == "c":
        return [*compiler[:-1], "top", "-q"]
    if compiler and Path(compiler[-1]).name == "coqc":
        return [*compiler[:-1], "coqtop", "-q"]
    return None


def _drain_stream(stream: TextIO, lines: list[str], sentinel: str | None = None,
                  event: threading.Event | None = None) -> None:
    try:
        while line := stream.readline():
            lines.append(line)
            if sentinel is not None and event is not None and sentinel in line:
                event.set()
    finally:
        if event is not None:
            event.set()


def _format_rocq_row_literal(row: list[object], domain: GradeDomain | CustomDomainSpec) -> str:
    def fmt(val: object) -> str:
        if isinstance(val, int) and domain == GradeDomain.PRESENCE:
            return "true" if val > 0 else "false"
        if isinstance(val, bool):
            return "true" if val else "false"
        return str(val)
    return "[" + "; ".join(fmt(v) for v in row) + "]"


def _pinned_theorems(lowerer: _CoreLowerer, rows: list[list[list[object]]]) -> str:
    domain = lowerer.domain
    d_name = domain.rocq_name if isinstance(domain, CustomDomainSpec) else _domain_spec(domain).rocq_domain
    sound_thm = (
        ("source_check_core_sub_sound" if domain.subgraded else "source_check_core_sound")
        if isinstance(domain, CustomDomainSpec)
        else _domain_spec(domain).sound_thm
    )
    pinned_items = [
        "Ok [" + "; ".join(_format_rocq_row_literal(subrow, domain) for subrow in defn_rows) + "]"
        for defn_rows in rows
    ]
    pinned_open = "; ".join(pinned_items)
    pinned_closed = "; ".join("Ok [[]; []; []]" for _ in rows)
    pinned_theorems = (
        f"Example source_checks_match : source_checks = [{pinned_closed}].\n"
        "Proof. vm_compute. reflexivity. Qed.\n"
        f"Example source_rows_match : source_reports = [{pinned_open}].\n"
        "Proof. vm_compute. reflexivity. Qed.\n"
    )
    last_defn = lowerer.definitions[-1]
    last_idx = last_defn.index
    if last_defn.context == "core":
        is_sub = domain.subgraded if isinstance(domain, CustomDomainSpec) else _domain_spec(domain).subgraded
        pinned_theorems += (
            f"Theorem source_closed_sound : exists j exp_row,\n"
            f"  CEnvWf (D := {d_name}) [] /\\\n"
            f"  CoreDerives [] source_closed_term_{last_idx} j /\\\n"
            f"  CTypeDemand [] source_closed_type_{last_idx} exp_row /\\\n"
            f"  {'Subty [] (cresult_type j) source_closed_type_' + str(last_idx) if is_sub else 'cty_alpha_eq (cresult_type j) source_closed_type_' + str(last_idx)} /\\\n"
            f"  [[]; []; []] = ccomp_demand j :: ctype_demand_row j :: exp_row :: map (@ctype_uses {d_name}) [].\n"
            f"Proof. apply {sound_thm}. vm_compute. reflexivity. Qed.\n"
        )
    else:
        pinned_theorems += (
            f"Theorem source_closed_sound : exists j exp_row,\n"
            f"  CEnvWf (D := {d_name}) source_open_env_{last_idx} /\\\n"
            f"  CoreDerives source_open_env_{last_idx} source_open_term_{last_idx} j /\\\n"
            f"  CTypeDemand source_open_env_{last_idx} source_open_type_{last_idx} exp_row.\n"
            f"Proof.\n"
            f"  destruct ({sound_thm} {d_name} source_open_env_{last_idx} source_open_term_{last_idx} source_open_type_{last_idx}\n"
            f"    {pinned_items[-1].replace('Ok ', '', 1)}) as [j [exp_row [Hwf [Hd [Ht _]]]]].\n"
            f"  - vm_compute. reflexivity.\n"
            f"  - exists j, exp_row. repeat split; assumption.\n"
            f"Qed.\n"
        )
    return pinned_theorems


def _replay_single_session(compiler: list[str], directory: Path, lowerer: _CoreLowerer,
                           certificate: str) -> tuple[list[list[object]], str] | None:
    top_cmd = _rocq_top_command(compiler)
    if top_cmd is None:
        return None
    deadline = REPLAY_DEADLINE.get()

    def remaining() -> float:
        budget = 30.0 if deadline is None else min(30.0, deadline - time.monotonic())
        if budget <= 0:
            raise subprocess.TimeoutExpired(top_cmd, 0)
        return budget

    sentinel = "     = (tt, false)"
    out_lines: list[str] = []
    err_lines: list[str] = []
    phase1_done = threading.Event()
    proc = subprocess.Popen(
        top_cmd,
        cwd=directory,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
    )
    if proc.stdin is None or proc.stdout is None or proc.stderr is None:
        raise RuntimeError("failed to open rocq top stdio pipes")
    stdin_pipe = proc.stdin
    stdout_pipe = proc.stdout
    stderr_pipe = proc.stderr
    out_thread = threading.Thread(
        target=_drain_stream, args=(stdout_pipe, out_lines, sentinel, phase1_done), daemon=True)
    err_thread = threading.Thread(
        target=_drain_stream, args=(stderr_pipe, err_lines), daemon=True)
    out_thread.start()
    err_thread.start()

    def run_session() -> tuple[list[list[object]], str]:
        stdin_pipe.write(certificate + "Check source_replays.\nEval vm_compute in (tt, false).\n")
        stdin_pipe.flush()
        budget = remaining()
        if not phase1_done.wait(timeout=budget):
            proc.kill()
            out_thread.join(timeout=2)
            err_thread.join(timeout=2)
            proc.wait(timeout=2)
            raise subprocess.TimeoutExpired(top_cmd, budget)
        rc = 0 if proc.poll() is None else int(proc.returncode)
        partial_err = "".join(err_lines)
        if rc == 0 and "Error:" in partial_err:
            rc = 1
        rows = _verdict(lowerer, subprocess.CompletedProcess(
            top_cmd, rc, "".join(out_lines), partial_err))
        if proc.poll() is not None:
            raise RuntimeError("graded source prover exited before row pin")
        pinned = _pinned_theorems(lowerer, rows)
        stdin_pipe.write(pinned + "Check source_rows_match.\nQuit.\n")
        stdin_pipe.flush()
        stdin_pipe.close()
        budget = remaining()
        rc = proc.wait(timeout=budget)
        out_thread.join(timeout=budget)
        err_thread.join(timeout=budget)
        full_out = "".join(out_lines)
        full_err = "".join(err_lines)
        if rc != 0 or "Error:" in full_err or "source_rows_match\n     : source_reports =" not in full_out:
            raise RuntimeError(f"graded demand certificate failed: {full_err.strip()}")
        return rows[-1], certificate + pinned

    try:
        return run_session()
    except BaseException:
        if proc.poll() is None:
            with suppress(OSError):
                proc.kill()
            with suppress(OSError, subprocess.SubprocessError):
                proc.wait(timeout=2)
        raise
    finally:
        with suppress(OSError):
            stdin_pipe.close()
        with suppress(OSError):
            stdout_pipe.close()
        with suppress(OSError):
            stderr_pipe.close()


def _replay(compiler: list[str], directory: Path, lowerer: _CoreLowerer,
            certificate: str) -> tuple[list[list[object]], str]:
    single = _replay_single_session(compiler, directory, lowerer, certificate)
    if single is not None:
        return single
    (directory / "SourceReplay.v").write_text(certificate, encoding="utf-8", newline="\n")
    rows = _verdict(lowerer, _run_rocq(compiler, directory, "SourceReplay.v"))
    pinned_theorems = _pinned_theorems(lowerer, rows)
    report = directory / "SourceReport.v"
    report.write_text(
        "From Stdlib Require Import Lists.List.\n"
        "Require Import graded_domains graded_core graded_core_source SourceReplay.\n"
        "Import ListNotations GradedDomains GradedCore GradedCoreSource.\n"
        + pinned_theorems,
        encoding="utf-8",
        newline="\n",
    )
    verified = _run_rocq(compiler, directory, report.name)
    if verified.returncode:
        raise RuntimeError(f"graded demand certificate failed: {verified.stderr.strip()}")
    return rows[-1], certificate + pinned_theorems


def _core_dependency_row(env_params: list[_Parameter], counts: list[object]) -> list[dict[str, object]]:
    # env_params is in De Bruijn order (innermost first), matching GradedCore rows.
    out: list[dict[str, object]] = []
    for param, val in zip(env_params, counts, strict=True):
        if isinstance(val, str) and val in {"LZero", "AZero", "Lo", "false", "0"}:
            continue
        if isinstance(val, (int, bool)) and int(val) == 0:
            continue
        out.append({"name": param.name, "span": param.span, "uses": val})
    return out


def _domain(protocol: _Protocol, node: Node, custom_domains: Mapping[str, CustomDomainSpec] | None = None) -> GradeDomain | CustomDomainSpec:
    annotation = cast("Node | None", node.get("grade"))
    if annotation is None:
        raise protocol.error("unsupported", "graded checking requires a grade domain annotation", node)
    if annotation["kind"] == "call":
        callee = cast("Node", annotation["callee"])
        if callee["kind"] == "name":
            name = _name(callee["name"])
            if name in GradeDomain:
                return GradeDomain(name)
            if custom_domains is not None and name in custom_domains:
                return custom_domains[name]
    raise protocol.error("unsupported", "graded checking requires a supported grade domain allowance", annotation)


def _local_box(protocol: _Protocol, declarations: list[Node]) -> tuple[Node, GradeDomain] | None:
    for declaration in declarations:
        if declaration["kind"] != "record" or _name(declaration["name"]) != "Box":
            continue
        generics = cast("list[Node]", declaration["generics"])
        if not any(node["mode"] == "grade" for node in generics):
            continue
        for domain in GradeDomain:
            if _valid_box_record(declaration, domain):
                return declaration, domain
        raise protocol.error("unsupported", "graded Box requires a canonical declaration", declaration)
    return None


class ModuleReplay:
    """Replay each graded declaration in its resolved import context via GradedCore."""

    def __init__(
        self,
        root: Path,
        protocol: _Protocol,
        syntax: Node,
        stack: ExitStack,
        *,
        resolve_box: BoxResolver | None = None,
        infer_grades: bool = False,
        custom_domains: Mapping[str, CustomDomainSpec] | None = None,
        uid_counter: list[int] | None = None,
    ) -> None:
        self.root = root
        self.protocol = protocol
        self.syntax = syntax
        self.stack = stack
        self.resolve_box = resolve_box
        self.infer_grades = infer_grades
        self._uid_counter = uid_counter
        self.custom_domains: dict[str, CustomDomainSpec] = dict(custom_domains or {})
        declarations = cast("list[Node]", syntax["declarations"])
        self.record_names = {_name(node["name"]) for node in declarations if node["kind"] == "record"}
        self.union_names = {_name(node["name"]) for node in declarations if node["kind"] == "union"}
        self.inductive_names = {_name(node["name"]) for node in declarations if node["kind"] == "inductive"}
        self.union_ctor_names = {
            _name(ctor["name"])
            for node in declarations if node["kind"] == "union"
            for ctor in cast("list[Node]", node["constructors"])
        }
        box_info = _local_box(protocol, declarations)
        self.box = None if box_info is None else box_info[0]
        self.box_domain = None if box_info is None else box_info[1]
        self.compiler: list[str] = []
        self.directory: Path | None = None
        self.hashes: dict[str, str] = {}
        self.receipts: list[str] = []
        self.exports: dict[str, GradeExport] = {}
        self.modal_definitions: set[str] = set()
        self.zero_type_use_binders: dict[str, tuple[tuple[int, str, list[int]], ...]] = {}
        self.definition_certificates: dict[str, str] = {}
        self.last_definition: _Definition | None = None

    def _lookup_box_domain(self, name: str | None) -> GradeDomain | None:
        if name is None:
            return None
        if name == "Box" and self.box_domain is not None:
            return self.box_domain
        if self.resolve_box is not None:
            return self.resolve_box(name)
        return None

    def check(self, declaration: Node, resolve_import: GradeResolver) -> tuple[set[int], str | None]:
        protocol = self.protocol
        if declaration is self.box:
            return ({id(cast("list[Node]", declaration["generics"])[1]),
                     id(cast("list[Node]", declaration["parameters"])[0])}, None)
        if declaration["kind"] == "domain":
            return set(), None
        if declaration["kind"] in {"record", "union", "inductive"}:
            # Lift Box-only restriction: allow `<grade q : D>` and graded fields/constructors.
            ann_ids: set[int] = set()
            for node in syntax_nodes(declaration):
                if (node["kind"] == "generic_parameter" and node["mode"] == "grade") or node.get("grade") is not None:
                    ann_ids.add(id(node))
            return ann_ids, None

        modal = False
        annotations: list[Node] = []
        grade_generics: list[Node] = []
        box_uses: list[Node] = []
        signature = (
            [*cast("list[Node]", declaration["parameters"]), cast("Node", declaration["result"])]
            if declaration["kind"] in {"definition", "function"} else []
        )
        interface_nodes = {id(node) for part in signature for node in syntax_nodes(part)}
        box_interface = False
        for node in syntax_nodes(declaration):
            if node["kind"] == "generic_parameter" and node["mode"] == "grade":
                grade_generics.append(node)
                annotations.append(node)
            elif node.get("grade") is not None:
                annotations.append(node)
            if node["kind"] in {"type", "name", "member", "constructor_pattern"}:
                path = _IntrinsicsMixin._dotted_member_path(node) or (
                    _name(node["name"]) if isinstance(node.get("name"), dict) else None
                )
                if path is not None:
                    if self._lookup_box_domain(path) is not None:
                        box_uses.append(node)
                        modal = True
                        if id(node) in interface_nodes:
                            box_interface = True
                    elif (path in self.modal_definitions
                          or path in self.union_ctor_names
                          or ((imported := resolve_import(path)) is not None and imported[1].modal)):
                        modal = True
            if (node["kind"] in {"if_expression", "bool", "match_expression", "tuple", "tuple_type"}
                    or (node["kind"] == "type" and _name(node["name"]) in (self.record_names | self.union_names | self.inductive_names | {"bool"}))):
                modal = True

        if not annotations:
            if box_uses:
                raise protocol.error("unsupported", "graded Box operations require an annotated pure definition", box_uses[0])
            return set(), None
        if declaration["kind"] not in {"definition", "function", "theorem", "lemma"}:
            raise protocol.error("unsupported", "graded checking supports definitions, functions, theorems, and data declarations", annotations[0])

        # Determine domain from explicit parameter/local annotations or <grade q : D> generic!
        domain: GradeDomain | CustomDomainSpec | None = None
        callable_input = False
        for gg in grade_generics:
            dtype = cast("Node", gg["type"])
            dname = _name(dtype["name"])
            gg_dom: GradeDomain | CustomDomainSpec = (
                GradeDomain(dname) if dname in GradeDomain else self.custom_domains[dname]
            )
            if domain is None:
                domain = gg_dom
            elif gg_dom != domain:
                raise protocol.error("unsupported", "a graded definition requires a single grade domain", gg)

        for annotation in annotations:
            if annotation in grade_generics:
                continue
            ann_node = cast("Node", annotation["grade"])
            if ann_node["kind"] == "call":
                ann_dom = _domain(protocol, annotation, self.custom_domains)
                if domain is None:
                    domain = ann_dom
                elif ann_dom != domain:
                    raise protocol.error("unsupported", "a graded definition requires a single grade domain", annotation)
            if (id(annotation) in interface_nodes and annotation["kind"] == "parameter"
                    and annotation["type"] is not None and any(
                        node["kind"] == "function_type" for node in syntax_nodes(cast("Node", annotation["type"]))
                    )):
                callable_input = True
        if domain is None:
            domain = GradeDomain.EXACT

        lowerer = _CoreLowerer(
            protocol,
            self.syntax,
            domain,
            resolve_box=self.resolve_box,
            infer_grades=self.infer_grades,
            custom_domains=self.custom_domains,
        )
        lowerer.resolve_import = resolve_import
        selected = lowerer.definition(_name(declaration["name"]))
        if "Box" in lowerer.used_box_names and self.box_domain is not None and self.box_domain != domain:
            dom_label = domain.name if isinstance(domain, CustomDomainSpec) else domain.value
            raise protocol.error(
                "unsupported",
                f"Box domain {self.box_domain.value} disagrees with {dom_label}",
                declaration,
            )
        self.last_definition = selected
        self.zero_type_use_binders[selected.name] = selected.zero_type_use_binders
        for annotation in annotations:
            if id(annotation) not in lowerer.annotations and annotation not in grade_generics:
                raise protocol.error("unsupported", "grade annotation has no checked projection", annotation)
        self._check_lowerer(lowerer, selected)
        if modal:
            self.modal_definitions.add(selected.name)
        caller_requirement = "callback" if callable_input else ("box" if box_interface else None)
        return lowerer.annotations, caller_requirement

    def _check_lowerer(self, lowerer: _CoreLowerer, definition: _Definition) -> None:
        if self.directory is None:
            try:
                self.compiler = proofenv.rocq_command()
            except SystemExit as error:
                raise self.protocol.error("unsupported", "graded checking requires an available Rocq prover",
                                          definition.source) from error
            self.directory = Path(self.stack.enter_context(tempfile.TemporaryDirectory(prefix="holdfast-graded-module-")))
        dependencies = _CORE_FILES
        if any(name not in self.hashes for name in dependencies):
            self.hashes.update(_support(self.root, self.compiler, self.directory, dependencies))
        source_hash = hashlib.sha256(self.protocol.source).hexdigest()
        certificate = _certificate(lowerer.definitions, source_hash, lowerer.domain, lowerer.provider_receipts)
        _, checked = _replay(self.compiler, self.directory, lowerer, certificate)
        self.definition_certificates[definition.name] = checked
        evidence = json.dumps({"certificate": checked, "support": {name: self.hashes[name] for name in dependencies}},
                              sort_keys=True, separators=(",", ":"))
        receipt = hashlib.sha256(evidence.encode()).hexdigest()
        dom_label = lowerer.domain.name if isinstance(lowerer.domain, CustomDomainSpec) else lowerer.domain.value
        self.receipts.append(f"(* Graded replay {definition.name} {dom_label}: SHA256 {receipt} *)\n")
        if definition.source["modifiers"] == ["public"] and isinstance(lowerer.domain, GradeDomain):
            box_imports = lowerer.box_imports.copy()
            if self.box is not None and self.box_domain is not None and self.box["modifiers"] == ["public"]:
                box_imports.setdefault("Box", self.box_domain)
            self.exports[definition.name] = GradeExport(
                self.protocol, self.syntax, definition.name,
                lowerer.domain, receipt,
                MappingProxyType(lowerer.imports.copy()),
                modal=bool(definition.records),
                box_imports=MappingProxyType(box_imports),
                custom_domains=MappingProxyType(self.custom_domains),
            )


def check(
    root: Path,
    path: Path,
    declaration: str,
    *,
    modal: bool = False,
    domain: GradeDomain = GradeDomain.EXACT,
    infer_grades: bool = False,
) -> dict[str, object]:
    """Check one graded HoldFast declaration via GradedCoreSource in Rocq."""
    snapshot = read_source(path)
    with parser.cached_build(root) as compiled:
        parsed = parser.parse_source(compiled, snapshot.data, surface=True)
    protocol = _Protocol(snapshot.data)
    decoded = protocol.decode(parsed)
    probe_lowerer = _CoreLowerer(protocol, decoded, domain, infer_grades=infer_grades)
    effective_domain: GradeDomain | CustomDomainSpec = domain
    if domain == GradeDomain.EXACT and declaration in probe_lowerer.declarations:
        decl_node = probe_lowerer.declarations[declaration]
        for s_node in syntax_nodes(decl_node):
            if s_node.get("kind") in {"parameter", "lambda_parameter", "let", "var", "typed_local", "match_motive", "binding_pattern"}:
                g_node = cast("Node | None", s_node.get("grade"))
                if g_node is not None and g_node.get("kind") == "call":
                    callee = cast("Node", g_node["callee"])
                    if callee.get("kind") == "name":
                        matched_custom = probe_lowerer.custom_domains.get(_name(callee["name"]))
                        if isinstance(matched_custom, CustomDomainSpec):
                            effective_domain = matched_custom
                            break
    box_info = _local_box(protocol, cast("list[Node]", decoded["declarations"]))
    lowerer = _CoreLowerer(
        protocol, decoded, effective_domain, infer_grades=infer_grades, custom_domains=probe_lowerer.custom_domains
    )
    selected = lowerer.definition(declaration)
    if "Box" in lowerer.used_box_names and box_info is not None and box_info[1] != effective_domain:
        raise protocol.error(
            "unsupported",
            f"Box domain {box_info[1].value} disagrees with {domain.value}",
            selected.source,
        )
    definitions = lowerer.definitions
    source_hash = hashlib.sha256(snapshot.data).hexdigest()
    certificate = _certificate(definitions, source_hash, effective_domain)
    compiler = proofenv.rocq_command()
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-source-") as temporary:
        directory = Path(temporary)
        kernel_hashes = _support(root, compiler, directory, _CORE_FILES)
        demand, certificate = _replay(compiler, directory, lowerer, certificate)
    ensure_unchanged(snapshot)

    params_decl = list(selected.top_params)
    n_params = len(params_decl)
    comp_row = demand[0] if len(demand) >= 1 else []
    type_row = demand[1] if len(demand) >= 2 else []
    exp_row = demand[2] if len(demand) >= 3 else []
    ann_rows = demand[3:]

    # GradedCore returns open_env in De Bruijn order (innermost first), reverse back to decl order for binders!
    comp_decl = list(reversed(comp_row))
    type_decl = list(reversed(type_row))
    ann_decl = list(reversed(ann_rows))
    env_db_params = list(reversed(params_decl))

    binders_out: list[dict[str, object]] = []
    for idx in range(n_params):
        param = params_decl[idx]
        # param at declaration index `idx` has `idx` older params (De Bruijn slice `env_db_params[n_params - idx :]`)
        older_db_params = env_db_params[n_params - idx:]
        older_ann_counts = ann_decl[idx] if idx < len(ann_decl) else []
        base_type = type_decl[idx] if idx < len(type_decl) else 0
        # Total type-use of param[idx] includes uses in subsequent parameter annotations (ann_decl[j][j - 1 - idx])!
        total_type = base_type
        for j in range(idx + 1, n_params):
            pos_in_j = j - 1 - idx
            if j < len(ann_decl) and pos_in_j < len(ann_decl[j]):
                use_val = ann_decl[j][pos_in_j]
                if isinstance(total_type, int) and isinstance(use_val, int):
                    total_type = total_type + use_val
                else:
                    total_type = _add_grades(domain, str(total_type), str(use_val))
        binders_out.append({
            "name": param.name,
            "span": param.span,
            "computation": comp_decl[idx] if idx < len(comp_decl) else 0,
            "type": total_type,
            "annotation_type_uses": _core_dependency_row(older_db_params, older_ann_counts),
        })

    for t_param, (_, t_s_atom, t_span, t_r_pair) in selected.trailing_pi_params:
        t_r_atom, t_ann = cast("tuple[object, list[dict[str, object]]]", t_r_pair)
        binders_out.append({
            "name": t_param.name,
            "span": list(t_span),
            "computation": t_s_atom,
            "type": t_r_atom,
            "annotation_type_uses": t_ann,
        })

    # If `result` had trailing Pi params (e.g., `Shape` returns `Fn(Vec<Nat, n+n>) -> Vec<Nat, n+n>`),
    # report `result_type_uses` on the innermost return codomain matching old projection conventions!
    if selected.trailing_pi_params:
        an_res = _IRAnalyzer(effective_domain)
        cod_ir = selected.ir_expected
        for _ in selected.top_params:
            if isinstance(cod_ir, IRPi):
                cod_ir = cod_ir.cod
        while isinstance(cod_ir, IRPi):
            cod_ir = cod_ir.cod
        cod_dem = an_res.ty_demand(cod_ir)
        result_deps = [
            {
                "name": p.name,
                "span": p.span,
                "uses": _format_grade_atom(_eval_gexpr(cod_dem[p.uid], effective_domain)),
            }
            for p in env_db_params
            if p.uid in cod_dem and not _is_gzero(cod_dem[p.uid], effective_domain)
        ]
    else:
        result_deps = _core_dependency_row(env_db_params, exp_row)
    scope = "pure-natural-modal-source-trial" if (modal or selected.records) else "pure-natural-graded-source-trial"
    dom_out = effective_domain.name if isinstance(effective_domain, CustomDomainSpec) else effective_domain.value
    output: dict[str, object] = {
        "status": "checked",
        "scope": scope,
        "domain": dom_out,
        "source_sha256": source_hash,
        "declaration": declaration,
        "span": _span(selected.source),
        "dependencies": list(selected.records) if (modal or selected.records) else [d.name for d in definitions[:-1]],
        "kernel_sha256": kernel_hashes,
        "gallina": certificate,
        "binders": binders_out,
        "result_type_uses": result_deps,
        "zero_type_use_binders": [
            {"uid": uid, "name": bname, "span": bspan}
            for uid, bname, bspan in selected.zero_type_use_binders
        ],
    }
    if selected.inferred_grades:
        output["inferred_grades"] = selected.inferred_grades
    return output
