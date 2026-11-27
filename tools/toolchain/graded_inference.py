# SPDX-License-Identifier: Apache-2.0
"""Symbolic grade constraint solver and Rocq certificate generator.

Supports ``NatExact``, ``NatBound``, ``Presence``, ``Linear``, and ``Affine``
domains, canonical polynomial normalization, equality/inequality propagation,
minimal satisfying assignments for bounded domains, explicit residual goals for
ambiguous/non-linear/underconstrained/inconsistent/budget-exhausted cases, and
zero-axiom Rocq replay audited via :mod:`toolchain.solver_ledger`.
"""

from __future__ import annotations

import hashlib
import math
import re
import subprocess
import tempfile
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Literal

from toolchain import graded_source, proofenv, solver_ledger

_ROCQ_SUPPORT = ("graded_pure.v", "graded_domains.v", "graded_semiring.v")
_DEFAULT_SPAN: tuple[int, ...] = ()


class InferenceDomain(StrEnum):
    """Supported grade domains for symbolic inference and kernel certificates."""

    NAT_EXACT = "NatExact"
    NAT_BOUND = "NatBound"
    PRESENCE = "Presence"
    LINEAR = "Linear"
    AFFINE = "Affine"


def coerce_domain(domain: str | InferenceDomain | graded_source.GradeDomain) -> InferenceDomain:
    """Validate and normalize a grade domain name."""
    if isinstance(domain, InferenceDomain):
        return domain
    value = domain.value if isinstance(domain, graded_source.GradeDomain) else str(domain)
    try:
        return InferenceDomain(value)
    except ValueError as err:
        supported = ", ".join(item.value for item in InferenceDomain)
        raise ValueError(f"unsupported grade domain {value!r}; expected one of {supported}") from err


def domain_is_exact(domain: InferenceDomain) -> bool:
    """Return True when admission requires exact equality (never weakening to <=)."""
    return domain in {InferenceDomain.NAT_EXACT, InferenceDomain.LINEAR}


@dataclass(frozen=True)
class GradeMeta:
    """Grade metavariable bound to a domain and optional source span."""

    id: int | str
    domain: InferenceDomain | str = InferenceDomain.NAT_EXACT
    span: tuple[int, ...] = _DEFAULT_SPAN

    def __post_init__(self) -> None:
        object.__setattr__(self, "domain", coerce_domain(self.domain))
        if not isinstance(self.span, tuple):
            object.__setattr__(self, "span", tuple(self.span))


@dataclass(frozen=True)
class GradeLit:
    """Concrete grade literal."""

    value: int

    def __init__(self, value: int | bool) -> None:
        normalized = (1 if value else 0) if isinstance(value, bool) else int(value)
        if normalized < 0:
            raise ValueError(f"grade literals must be non-negative naturals, got {value!r}")
        object.__setattr__(self, "value", normalized)


@dataclass(frozen=True)
class GradeVar:
    """Symbolic grade variable referencing a :class:`GradeMeta` or variable identifier."""

    meta: GradeMeta | int | str

    @property
    def var_id(self) -> int | str:
        """Return the underlying variable identifier."""
        return self.meta.id if isinstance(self.meta, GradeMeta) else self.meta


@dataclass(frozen=True)
class GradeAdd:
    """Semiring addition of two grade expressions."""

    lhs: GradeExpr
    rhs: GradeExpr


@dataclass(frozen=True)
class GradeMul:
    """Semiring multiplication of two grade expressions."""

    lhs: GradeExpr
    rhs: GradeExpr


@dataclass(frozen=True)
class GradeJoin:
    """Branch join / least-upper-bound of two grade expressions."""

    lhs: GradeExpr
    rhs: GradeExpr


type GradeExpr = GradeLit | GradeVar | GradeAdd | GradeMul | GradeJoin
type ConstraintOp = Literal["eq", "le"]


@dataclass(frozen=True)
class GradeConstraint:
    """Grade equality or admission constraint with origin metadata."""

    lhs: GradeExpr
    op: ConstraintOp
    rhs: GradeExpr
    origin_span: tuple[int, ...] = _DEFAULT_SPAN
    reason: str = ""

    def __post_init__(self) -> None:
        if self.op not in {"eq", "le"}:
            raise ValueError(f"unsupported constraint operator {self.op!r}; expected 'eq' or 'le'")
        if not isinstance(self.origin_span, tuple):
            object.__setattr__(self, "origin_span", tuple(self.origin_span))


type ResidualKind = Literal[
    "ambiguous",
    "non_linear",
    "underconstrained",
    "inconsistent",
    "budget_exhausted",
    "unsupported",
]


@dataclass(frozen=True)
class ResidualGoal:
    """Explicit unresolved constraint goal returned rather than guessing without proof."""

    constraint: GradeConstraint | None
    kind: ResidualKind
    message: str
    remaining_variables: tuple[int | str, ...] = ()
    origin_span: tuple[int, ...] = _DEFAULT_SPAN


@dataclass(frozen=True)
class GradeCertificate:
    """Replayable Rocq proof certificate for solved grade constraints."""

    domain: InferenceDomain
    assignments: Mapping[int | str, int]
    constraints: tuple[GradeConstraint, ...]
    gallina: str
    module_name: str
    theorem_names: tuple[str, ...]
    source_sha256: str


@dataclass(frozen=True)
class InferenceResult:
    """Outcome of bounded deterministic grade constraint inference."""

    status: Literal["solved", "residual", "inconsistent", "budget_exhausted"]
    domain: InferenceDomain
    assignments: dict[int | str, int]
    residuals: tuple[ResidualGoal, ...]
    certificate: GradeCertificate | None
    steps_used: int

    @property
    def ok(self) -> bool:
        """Return True iff every constraint was proved with zero residuals."""
        return self.status == "solved" and not self.residuals and self.certificate is not None


type Monomial = tuple[int | str, ...]
type Poly = dict[Monomial, int]


def _var_sort_key(var_id: int | str) -> tuple[int, int | str]:
    return (0, var_id) if isinstance(var_id, int) else (1, var_id)


def _mono_sort_key(mono: Monomial) -> tuple[int, tuple[tuple[int, int | str], ...]]:
    return (len(mono), tuple(_var_sort_key(v) for v in mono))


def _poly_clean(poly: Mapping[Monomial, int]) -> Poly:
    return {m: c for m, c in poly.items() if c > 0}


def _poly_lit(value: int) -> Poly:
    return {(): value} if value > 0 else {}


def _poly_var(var_id: int | str) -> Poly:
    return {(var_id,): 1}


def _poly_add(p1: Poly, p2: Poly) -> Poly:
    out = dict(p1)
    for mono, coeff in p2.items():
        out[mono] = out.get(mono, 0) + coeff
    return _poly_clean(out)


def _poly_mul(p1: Poly, p2: Poly) -> Poly:
    out: Poly = {}
    for m1, c1 in p1.items():
        for m2, c2 in p2.items():
            merged = tuple(sorted((*m1, *m2), key=_var_sort_key))
            out[merged] = out.get(merged, 0) + c1 * c2
    return _poly_clean(out)


def _poly_vars(poly: Poly) -> set[int | str]:
    return {v for mono in poly for v in mono}


def _poly_is_const(poly: Poly) -> int | None:
    if not poly:
        return 0
    if list(poly.keys()) == [()]:
        return poly[()]
    return None


def _poly_linear(poly: Poly) -> tuple[int, dict[int | str, int]] | None:
    const = poly.get((), 0)
    coeffs: dict[int | str, int] = {}
    for mono, coeff in poly.items():
        if len(mono) == 0:
            continue
        if len(mono) > 1:
            return None
        coeffs[mono[0]] = coeff
    return const, coeffs


def _poly_eq(p1: Poly, p2: Poly) -> bool:
    return p1 == p2


def _poly_le(p1: Poly, p2: Poly) -> bool:
    return all(coeff <= p2.get(mono, 0) for mono, coeff in p1.items())


def _poly_to_expr(poly: Poly) -> GradeExpr:
    if not poly:
        return GradeLit(0)
    terms: list[GradeExpr] = []
    for mono in sorted(poly, key=_mono_sort_key):
        coeff = poly[mono]
        if not mono:
            terms.append(GradeLit(coeff))
            continue
        factors: list[GradeExpr] = [GradeVar(v) for v in mono]
        prod = factors[0]
        for factor in factors[1:]:
            prod = GradeMul(prod, factor)
        if coeff != 1:
            prod = GradeMul(GradeLit(coeff), prod)
        terms.append(prod)
    acc = terms[0]
    for term in terms[1:]:
        acc = GradeAdd(acc, term)
    return acc


def _expr_vars(expr: GradeExpr) -> set[int | str]:
    if isinstance(expr, GradeLit):
        return set()
    if isinstance(expr, GradeVar):
        return {expr.var_id}
    return _expr_vars(expr.lhs) | _expr_vars(expr.rhs)


def _subst_expr(expr: GradeExpr, assignments: Mapping[int | str, GradeExpr]) -> GradeExpr:
    if isinstance(expr, GradeLit):
        return expr
    if isinstance(expr, GradeVar):
        return assignments.get(expr.var_id, expr)
    if isinstance(expr, GradeAdd):
        return GradeAdd(_subst_expr(expr.lhs, assignments), _subst_expr(expr.rhs, assignments))
    if isinstance(expr, GradeMul):
        return GradeMul(_subst_expr(expr.lhs, assignments), _subst_expr(expr.rhs, assignments))
    return GradeJoin(_subst_expr(expr.lhs, assignments), _subst_expr(expr.rhs, assignments))


def _expr_to_poly(expr: GradeExpr, domain: InferenceDomain) -> Poly | None:
    """Convert a join-free expression into canonical polynomial form, or None if join remains."""
    if isinstance(expr, GradeLit):
        val = (1 if expr.value > 0 else 0) if domain == InferenceDomain.PRESENCE else expr.value
        return _poly_lit(val)
    if isinstance(expr, GradeVar):
        return _poly_var(expr.var_id)
    if isinstance(expr, GradeAdd):
        pl = _expr_to_poly(expr.lhs, domain)
        pr = _expr_to_poly(expr.rhs, domain)
        if pl is None or pr is None:
            return None
        added = _poly_add(pl, pr)
        return _presence_poly(added) if domain == InferenceDomain.PRESENCE else added
    if isinstance(expr, GradeMul):
        pl = _expr_to_poly(expr.lhs, domain)
        pr = _expr_to_poly(expr.rhs, domain)
        if pl is None or pr is None:
            return None
        mulled = _poly_mul(pl, pr)
        return _presence_poly(mulled) if domain == InferenceDomain.PRESENCE else mulled
    return None


def _presence_poly(poly: Poly) -> Poly:
    """Normalize a polynomial over Boolean Presence ({0, 1}, idempotent + and *)."""
    out: Poly = {}
    for mono in poly:
        dedup = tuple(sorted(set(mono), key=_var_sort_key))
        out[dedup] = 1
    # Absorption: if constant 1 is present, whole sum is 1.
    if () in out:
        return {(): 1}
    return out


def _eval_concrete(expr: GradeExpr, env: Mapping[int | str, int], domain: InferenceDomain) -> int | None:
    if isinstance(expr, GradeLit):
        return (1 if expr.value > 0 else 0) if domain == InferenceDomain.PRESENCE else expr.value
    if isinstance(expr, GradeVar):
        return env.get(expr.var_id)
    lv = _eval_concrete(expr.lhs, env, domain)
    rv = _eval_concrete(expr.rhs, env, domain)
    if lv is None or rv is None:
        return None
    if isinstance(expr, GradeAdd):
        return (1 if (lv > 0 or rv > 0) else 0) if domain == InferenceDomain.PRESENCE else (lv + rv)
    if isinstance(expr, GradeMul):
        return (1 if (lv > 0 and rv > 0) else 0) if domain == InferenceDomain.PRESENCE else (lv * rv)
    # GradeJoin
    if domain == InferenceDomain.PRESENCE:
        return 1 if (lv > 0 or rv > 0) else 0
    if domain in {InferenceDomain.NAT_BOUND, InferenceDomain.AFFINE}:
        return max(lv, rv)
    # Exact domains require equal branches for a join.
    return lv if lv == rv else None


def _allows_concrete(domain: InferenceDomain, op: ConstraintOp, lhs: int, rhs: int) -> bool:
    if domain == InferenceDomain.NAT_EXACT:
        return lhs == rhs
    if domain == InferenceDomain.LINEAR:
        return lhs == rhs
    if domain == InferenceDomain.NAT_BOUND:
        return lhs == rhs if op == "eq" else lhs <= rhs
    if domain == InferenceDomain.AFFINE:
        if lhs > 1 or rhs > 1:
            return False
        return lhs == rhs if op == "eq" else lhs <= rhs
    # Presence
    lb, rb = (lhs > 0), (rhs > 0)
    return (lb == rb) if op == "eq" else ((not lb) or rb)


def _simplify_joins(
    expr: GradeExpr,
    domain: InferenceDomain,
) -> tuple[GradeExpr, str | None]:
    """Simplify GradeJoin nodes when branches agree or order is decidable."""
    if isinstance(expr, (GradeLit, GradeVar)):
        return expr, None
    if isinstance(expr, GradeAdd):
        lhs, err1 = _simplify_joins(expr.lhs, domain)
        if err1 is not None:
            return expr, err1
        rhs, err2 = _simplify_joins(expr.rhs, domain)
        if err2 is not None:
            return expr, err2
        return GradeAdd(lhs, rhs), None
    if isinstance(expr, GradeMul):
        lhs, err1 = _simplify_joins(expr.lhs, domain)
        if err1 is not None:
            return expr, err1
        rhs, err2 = _simplify_joins(expr.rhs, domain)
        if err2 is not None:
            return expr, err2
        return GradeMul(lhs, rhs), None

    lhs, err1 = _simplify_joins(expr.lhs, domain)
    if err1 is not None:
        return expr, err1
    rhs, err2 = _simplify_joins(expr.rhs, domain)
    if err2 is not None:
        return expr, err2
    pl = _expr_to_poly(lhs, domain)
    pr = _expr_to_poly(rhs, domain)
    if pl is not None and pr is not None:
        cl = _poly_is_const(pl)
        cr = _poly_is_const(pr)
        if cl is not None and cr is not None:
            if domain_is_exact(domain):
                if cl != cr:
                    return expr, f"exact domain {domain.value} forbids joining {cl} and {cr}"
                return GradeLit(cl), None
            if domain == InferenceDomain.PRESENCE:
                return GradeLit(1 if (cl > 0 or cr > 0) else 0), None
            return GradeLit(max(cl, cr)), None
        if _poly_eq(pl, pr):
            return lhs, None
        if not domain_is_exact(domain):
            if _poly_le(pl, pr):
                return rhs, None
            if _poly_le(pr, pl):
                return lhs, None
    return GradeJoin(lhs, rhs), None


def _constraint_domain_check(
    constraints: Sequence[GradeConstraint],
    metas: Sequence[GradeMeta],
    domain: InferenceDomain,
) -> ResidualGoal | None:
    for meta in metas:
        meta_domain = coerce_domain(meta.domain)
        if meta_domain != domain:
            return ResidualGoal(
                constraint=None,
                kind="inconsistent",
                message=f"metavariable {meta.id!r} belongs to domain {meta_domain.value}, expected {domain.value}",
                remaining_variables=(meta.id,),
                origin_span=meta.span,
            )
    for c in constraints:
        for expr in (c.lhs, c.rhs):
            stack: list[GradeExpr] = [expr]
            while stack:
                node = stack.pop()
                if isinstance(node, GradeVar) and isinstance(node.meta, GradeMeta):
                    node_domain = coerce_domain(node.meta.domain)
                    if node_domain != domain:
                        return ResidualGoal(
                            constraint=c,
                            kind="inconsistent",
                            message=(
                                f"metavariable {node.meta.id!r} belongs to domain "
                                f"{node_domain.value}, expected {domain.value}"
                            ),
                            remaining_variables=(node.meta.id,),
                            origin_span=c.origin_span or node.meta.span,
                        )
                elif isinstance(node, (GradeAdd, GradeMul, GradeJoin)):
                    stack.extend((node.lhs, node.rhs))
    return None


@dataclass
class _ActiveConstraint:
    original: GradeConstraint
    lhs: GradeExpr
    op: ConstraintOp
    rhs: GradeExpr


def _effective_op(op: ConstraintOp, domain: InferenceDomain) -> ConstraintOp:
    """Enforce exact equality for NatExact and Linear (never weaken exact into bound)."""
    return "eq" if domain_is_exact(domain) else op


def _resolve_linear_equality(
    pl: Poly,
    pr: Poly,
    domain: InferenceDomain,
) -> tuple[bool, dict[int | str, int], tuple[int | str, GradeExpr] | None, str | None]:
    """Try to solve or refute a linear equality ``pl == pr``.

    Returns ``(resolved, new_concrete, new_symbolic, inconsistency_msg)``.
    """
    lin_l = _poly_linear(pl)
    lin_r = _poly_linear(pr)
    if lin_l is None or lin_r is None:
        return False, {}, None, None
    c_l, vars_l = lin_l
    c_r, vars_r = lin_r
    # Cancel common terms on both sides.
    common_const = min(c_l, c_r)
    rem_cl = c_l - common_const
    rem_cr = c_r - common_const
    net_l: dict[int | str, int] = {}
    net_r: dict[int | str, int] = {}
    for v in set(vars_l) | set(vars_r):
        al = vars_l.get(v, 0)
        ar = vars_r.get(v, 0)
        if al > ar:
            net_l[v] = al - ar
        elif ar > al:
            net_r[v] = ar - al

    if not net_l and not net_r:
        if rem_cl != rem_cr:
            return False, {}, None, f"unsatisfiable equality {c_l} == {c_r}"
        return True, {}, None, None

    # All variables on one side equal a constant on the other side.
    if net_l and not net_r:
        if rem_cl > rem_cr:
            return False, {}, None, f"unsatisfiable equality: left side >= {rem_cl} > {rem_cr}"
        rhs_const = rem_cr - rem_cl
        if rhs_const == 0:
            # Sum of positive-coefficient naturals == 0 -> all 0.
            return True, dict.fromkeys(net_l, 0), None, None
        if len(net_l) == 1:
            (v, coeff) = next(iter(net_l.items()))
            if rhs_const % coeff != 0:
                return False, {}, None, f"unsatisfiable divisibility: {coeff} * {v} == {rhs_const}"
            val = rhs_const // coeff
            if domain == InferenceDomain.AFFINE and val > 1:
                return False, {}, None, f"affine variable {v!r} cannot take value {val} > 1"
            return True, {v: val}, None, None
        return False, {}, None, None

    if net_r and not net_l:
        if rem_cr > rem_cl:
            return False, {}, None, f"unsatisfiable equality: right side >= {rem_cr} > {rem_cl}"
        lhs_const = rem_cl - rem_cr
        if lhs_const == 0:
            return True, dict.fromkeys(net_r, 0), None, None
        if len(net_r) == 1:
            (v, coeff) = next(iter(net_r.items()))
            if lhs_const % coeff != 0:
                return False, {}, None, f"unsatisfiable divisibility: {coeff} * {v} == {lhs_const}"
            val = lhs_const // coeff
            if domain == InferenceDomain.AFFINE and val > 1:
                return False, {}, None, f"affine variable {v!r} cannot take value {val} > 1"
            return True, {v: val}, None, None
        return False, {}, None, None

    # Variable isolation: 1*x == expr (with x not in expr).
    if rem_cl == 0 and len(net_l) == 1:
        (v, coeff) = next(iter(net_l.items()))
        if coeff == 1 and v not in net_r:
            rhs_poly: Poly = {**({(): rem_cr} if rem_cr > 0 else {}), **{(k,): c for k, c in net_r.items()}}
            return True, {}, (v, _poly_to_expr(rhs_poly)), None
    if rem_cr == 0 and len(net_r) == 1:
        (v, coeff) = next(iter(net_r.items()))
        if coeff == 1 and v not in net_l:
            lhs_poly: Poly = {**({(): rem_cl} if rem_cl > 0 else {}), **{(k,): c for k, c in net_l.items()}}
            return True, {}, (v, _poly_to_expr(lhs_poly)), None

    return False, {}, None, None


def _presence_propagate(
    active: list[_ActiveConstraint],
) -> tuple[list[_ActiveConstraint], dict[int | str, int], str | None]:
    """Propagate unit constraints for Boolean Presence."""
    new_vals: dict[int | str, int] = {}
    remaining: list[_ActiveConstraint] = []
    for item in active:
        pl = _expr_to_poly(item.lhs, InferenceDomain.PRESENCE)
        pr = _expr_to_poly(item.rhs, InferenceDomain.PRESENCE)
        if pl is None or pr is None:
            remaining.append(item)
            continue
        cl = _poly_is_const(pl)
        cr = _poly_is_const(pr)
        if cl is not None and cr is not None:
            if not _allows_concrete(InferenceDomain.PRESENCE, item.op, cl, cr):
                return remaining, new_vals, f"unsatisfiable Presence constraint {cl} {item.op} {cr}"
            continue
        if _poly_eq(pl, pr) or (item.op == "le" and _poly_le(pl, pr)):
            continue
        if item.op == "le":
            # lhs <= 0 -> every monomial of lhs must be 0; single-var monomials force var=0.
            if cr == 0:
                forced = False
                for mono in pl:
                    if len(mono) == 1:
                        new_vals[mono[0]] = 0
                        forced = True
                if forced:
                    continue
            # 1 <= rhs -> if rhs is single monomial (v1 * ... * vk), all vi = 1.
            if cl == 1 and len(pr) == 1:
                mono = next(iter(pr))
                if mono:
                    for v in mono:
                        new_vals[v] = 1
                    continue
        else:
            if cr == 0:
                forced = False
                for mono in pl:
                    if len(mono) == 1:
                        new_vals[mono[0]] = 0
                        forced = True
                if forced:
                    continue
            if cl == 0:
                forced = False
                for mono in pr:
                    if len(mono) == 1:
                        new_vals[mono[0]] = 0
                        forced = True
                if forced:
                    continue
            if cr == 1 and len(pl) == 1:
                mono = next(iter(pl))
                if mono:
                    for v in mono:
                        new_vals[v] = 1
                    continue
            if cl == 1 and len(pr) == 1:
                mono = next(iter(pr))
                if mono:
                    for v in mono:
                        new_vals[v] = 1
                    continue
        remaining.append(item)
    return remaining, new_vals, None


def _solve_bounded_inequalities(
    active: list[_ActiveConstraint],
    domain: InferenceDomain,
    meta_ids: set[int | str],
    concrete: dict[int | str, int],
) -> tuple[list[_ActiveConstraint], dict[int | str, int], ResidualGoal | None]:
    """Compute minimal satisfying assignments for bounded domains (NatBound / Affine / Presence)."""
    lowers: dict[int | str, list[int]] = {}
    uppers: dict[int | str, list[int]] = {}
    unhandled: list[_ActiveConstraint] = []
    pair_le_edges: list[tuple[int | str, int | str]] = []

    if domain == InferenceDomain.AFFINE:
        for v in meta_ids:
            if v not in concrete:
                uppers.setdefault(v, []).append(1)

    for item in active:
        pl = _expr_to_poly(item.lhs, domain)
        pr = _expr_to_poly(item.rhs, domain)
        if pl is None or pr is None or item.op != "le":
            unhandled.append(item)
            continue
        lin_l = _poly_linear(pl)
        lin_r = _poly_linear(pr)
        if lin_l is None or lin_r is None:
            unhandled.append(item)
            continue
        c_l, vars_l = lin_l
        c_r, vars_r = lin_r
        common_c = min(c_l, c_r)
        rem_cl, rem_cr = c_l - common_c, c_r - common_c
        net_l: dict[int | str, int] = {}
        net_r: dict[int | str, int] = {}
        for v in set(vars_l) | set(vars_r):
            al, ar = vars_l.get(v, 0), vars_r.get(v, 0)
            if al > ar:
                net_l[v] = al - ar
            elif ar > al:
                net_r[v] = ar - al

        if not net_l and not net_r:
            if rem_cl > rem_cr:
                return active, {}, ResidualGoal(
                    item.original,
                    "inconsistent",
                    f"unsatisfiable inequality {c_l} <= {c_r}",
                    (),
                    item.original.origin_span,
                )
            continue

        # sum(c_i * x_i) + rem_cl <= rem_cr (upper bounds)
        if net_l and not net_r:
            if rem_cl > rem_cr:
                return active, {}, ResidualGoal(
                    item.original,
                    "inconsistent",
                    f"unsatisfiable inequality: left side >= {rem_cl} > {rem_cr}",
                    tuple(sorted(net_l, key=_var_sort_key)),
                    item.original.origin_span,
                )
            slack = rem_cr - rem_cl
            for v, coeff in net_l.items():
                uppers.setdefault(v, []).append(slack // coeff)
            continue

        # rem_cl <= sum(c_i * x_i) + rem_cr (lower bounds)
        if net_r and not net_l:
            if len(net_r) == 1:
                (v, coeff) = next(iter(net_r.items()))
                need = max(0, rem_cl - rem_cr)
                lb = math.ceil(need / coeff) if need > 0 else 0
                lowers.setdefault(v, []).append(lb)
                continue
            if rem_cl <= rem_cr:
                # 0 <= sum(c_i * x_i) + (rem_cr - rem_cl) always holds!
                continue
            unhandled.append(item)
            continue

        # Single variable on each side: c1 * x + rem_cl <= c2 * y + rem_cr
        if rem_cl == 0 and rem_cr == 0 and len(net_l) == 1 and len(net_r) == 1:
            (vx, cx) = next(iter(net_l.items()))
            (vy, cy) = next(iter(net_r.items()))
            if cx == 1 and cy == 1:
                pair_le_edges.append((vx, vy))
                continue
        unhandled.append(item)

    if unhandled:
        return unhandled, {}, None

    candidate_vars = (set(lowers) | set(uppers) | {u for edge in pair_le_edges for u in edge}) - set(concrete)
    solved = dict(concrete)
    for v in sorted(candidate_vars, key=_var_sort_key):
        # If a variable only appears in x <= y without any concrete bound, treat as underconstrained.
        if v not in lowers and v not in uppers:
            return active, {}, ResidualGoal(
                None,
                "underconstrained",
                f"bounded variable {v!r} has no concrete lower or upper bound",
                (v,),
                (),
            )
        solved[v] = max(lowers.get(v, [0]))

    # Propagate x <= y edges minimally (raise y to max(y, x)).
    for _ in range(len(pair_le_edges) + 1):
        changed = False
        for vx, vy in pair_le_edges:
            if solved[vx] > solved[vy]:
                solved[vy] = solved[vx]
                changed = True
        if not changed:
            break

    # Validate all upper bounds and domain limits.
    for v, bound_list in uppers.items():
        val = solved[v]
        for ub in bound_list:
            if val > ub:
                return active, {}, ResidualGoal(
                    None,
                    "inconsistent",
                    f"variable {v!r} requires >= {val} but upper bound is {ub}",
                    (v,),
                    (),
                )
    # Re-verify every original active constraint concretely under `solved`.
    for item in active:
        lv = _eval_concrete(item.lhs, solved, domain)
        rv = _eval_concrete(item.rhs, solved, domain)
        if lv is None or rv is None or not _allows_concrete(domain, item.op, lv, rv):
            return active, {}, ResidualGoal(
                item.original,
                "inconsistent",
                f"bounded assignment violates constraint {item.original.reason or ''}".strip(),
                tuple(sorted(_expr_vars(item.lhs) | _expr_vars(item.rhs), key=_var_sort_key)),
                item.original.origin_span,
            )

    return [], solved, None


def _classify_residual(
    item: _ActiveConstraint,
    domain: InferenceDomain,
) -> ResidualGoal:
    pl = _expr_to_poly(item.lhs, domain)
    pr = _expr_to_poly(item.rhs, domain)
    vars_left = sorted(_expr_vars(item.lhs) | _expr_vars(item.rhs), key=_var_sort_key)
    span = item.original.origin_span
    if pl is None or pr is None:
        return ResidualGoal(
            item.original,
            "ambiguous",
            f"unresolved branch join in {domain.value}",
            tuple(vars_left),
            span,
        )
    if _poly_linear(pl) is None or _poly_linear(pr) is None:
        return ResidualGoal(
            item.original,
            "non_linear",
            f"unresolved non-linear grade constraint in {domain.value}",
            tuple(vars_left),
            span,
        )
    if len(vars_left) > 1:
        return ResidualGoal(
            item.original,
            "ambiguous",
            f"ambiguous multi-variable grade constraint in {domain.value}",
            tuple(vars_left),
            span,
        )
    return ResidualGoal(
        item.original,
        "underconstrained",
        f"underconstrained grade constraint in {domain.value}",
        tuple(vars_left),
        span,
    )


def _var_index_map(
    constraints: Sequence[GradeConstraint],
    assignments: Mapping[int | str, int],
    metas: Sequence[GradeMeta],
) -> dict[int | str, int]:
    all_vars: set[int | str] = set(assignments) | {m.id for m in metas}
    for c in constraints:
        all_vars |= _expr_vars(c.lhs) | _expr_vars(c.rhs)
    ordered = sorted(all_vars, key=_var_sort_key)
    return {v: idx for idx, v in enumerate(ordered)}


def _emit_grade_expr(expr: GradeExpr, var_idx: Mapping[int | str, int]) -> str:
    if isinstance(expr, GradeLit):
        return f"(GLit {expr.value})"
    if isinstance(expr, GradeVar):
        return f"(GVar {var_idx[expr.var_id]})"
    if isinstance(expr, GradeAdd):
        return f"(GAdd {_emit_grade_expr(expr.lhs, var_idx)} {_emit_grade_expr(expr.rhs, var_idx)})"
    if isinstance(expr, GradeMul):
        return f"(GMul {_emit_grade_expr(expr.lhs, var_idx)} {_emit_grade_expr(expr.rhs, var_idx)})"
    raise ValueError("GradeJoin cannot be emitted directly as GradedSemiring.grade_expr")


def _emit_nat_expr(
    expr: GradeExpr,
    var_idx: Mapping[int | str, int],
    domain: InferenceDomain,
) -> str:
    if isinstance(expr, GradeLit):
        val = (1 if expr.value > 0 else 0) if domain == InferenceDomain.PRESENCE else expr.value
        return str(val)
    if isinstance(expr, GradeVar):
        return f"(rho_witness {var_idx[expr.var_id]})"
    lhs = _emit_nat_expr(expr.lhs, var_idx, domain)
    rhs = _emit_nat_expr(expr.rhs, var_idx, domain)
    if isinstance(expr, GradeAdd):
        if domain == InferenceDomain.PRESENCE:
            return f"(if (Nat.ltb 0 ({lhs} + {rhs})) then 1 else 0)"
        return f"({lhs} + {rhs})"
    if isinstance(expr, GradeMul):
        if domain == InferenceDomain.PRESENCE:
            return f"(if (Nat.ltb 0 ({lhs} * {rhs})) then 1 else 0)"
        return f"({lhs} * {rhs})"
    # GradeJoin
    if domain in {InferenceDomain.NAT_BOUND, InferenceDomain.AFFINE}:
        return f"(Nat.max ({lhs}) ({rhs}))"
    if domain == InferenceDomain.PRESENCE:
        return f"(if (Nat.ltb 0 ({lhs} + {rhs})) then 1 else 0)"
    return f"({lhs})"


def _has_join(expr: GradeExpr) -> bool:
    if isinstance(expr, GradeJoin):
        return True
    if isinstance(expr, (GradeAdd, GradeMul)):
        return _has_join(expr.lhs) or _has_join(expr.rhs)
    return False


def _emit_certificate(
    domain: InferenceDomain,
    constraints: tuple[GradeConstraint, ...],
    assignments: dict[int | str, int],
    metas: Sequence[GradeMeta],
) -> GradeCertificate:
    var_idx = _var_index_map(constraints, assignments, metas)
    module_name = "GradedInferenceCert"
    rho_arms = "".join(
        f"  | {idx} => {assignments[v]}\n"
        for v, idx in sorted(var_idx.items(), key=lambda item: item[1])
        if v in assignments
    )
    lines = [
        "(* SPDX-License-Identifier: Apache-2.0 *)",
        "From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.",
        "Require Import graded_pure graded_domains graded_semiring.",
        "Import ListNotations GradedDomains GradedSemiring.",
        "",
        f"Module {module_name}.",
        "",
        "Definition rho_witness (x : nat) : nat :=",
        "  match x with",
        f"{rho_arms}  | _ => 0",
        "  end.",
        "",
    ]
    theorem_names: list[str] = []
    for idx, c in enumerate(constraints):
        eff_op = _effective_op(c.op, domain)
        thm_name = f"constraint_{idx}"
        theorem_names.append(thm_name)
        can_universal = (
            not _has_join(c.lhs)
            and not _has_join(c.rhs)
            and domain in {InferenceDomain.NAT_EXACT, InferenceDomain.LINEAR, InferenceDomain.NAT_BOUND}
        )
        pl = _expr_to_poly(c.lhs, domain)
        pr = _expr_to_poly(c.rhs, domain)
        universal_eq = can_universal and pl is not None and pr is not None and _poly_eq(pl, pr)
        universal_le = (
            can_universal
            and eff_op == "le"
            and pl is not None
            and pr is not None
            and _poly_le(pl, pr)
        )
        if universal_eq:
            gl = _emit_grade_expr(c.lhs, var_idx)
            gr = _emit_grade_expr(c.rhs, var_idx)
            lines.extend([
                f"Theorem {thm_name} : forall rho,",
                f"  eval_grade rho {gl} = eval_grade rho {gr}.",
                "Proof.",
                "  intro rho. apply grade_eqb_sound. vm_compute. reflexivity.",
                "Qed.",
                "",
            ])
        elif universal_le:
            gl = _emit_grade_expr(c.lhs, var_idx)
            gr = _emit_grade_expr(c.rhs, var_idx)
            lines.extend([
                f"Theorem {thm_name} : forall rho,",
                f"  eval_grade rho {gl} <= eval_grade rho {gr}.",
                "Proof.",
                "  intro rho. apply grade_leb_sound. vm_compute. reflexivity.",
                "Qed.",
                "",
            ])
        else:
            nl = _emit_nat_expr(c.lhs, var_idx, domain)
            nr = _emit_nat_expr(c.rhs, var_idx, domain)
            if domain == InferenceDomain.NAT_EXACT:
                lines.extend([
                    f"Theorem {thm_name} : @allows NatExact ({nl}) ({nr}).",
                    "Proof.",
                    "  cbn. vm_compute. reflexivity.",
                    "Qed.",
                    "",
                ])
            elif domain == InferenceDomain.LINEAR:
                lines.extend([
                    f"Theorem {thm_name} : ({nl}) = ({nr}).",
                    "Proof.",
                    "  vm_compute. reflexivity.",
                    "Qed.",
                    "",
                ])
            elif domain == InferenceDomain.NAT_BOUND:
                if eff_op == "eq":
                    lines.extend([
                        f"Theorem {thm_name} : ({nl}) = ({nr}).",
                        "Proof.",
                        "  vm_compute. reflexivity.",
                        "Qed.",
                        "",
                    ])
                else:
                    lines.extend([
                        f"Theorem {thm_name} : @allows NatBound ({nl}) ({nr}).",
                        "Proof.",
                        "  cbn. apply Nat.leb_le. vm_compute. reflexivity.",
                        "Qed.",
                        "",
                    ])
            elif domain == InferenceDomain.AFFINE:
                if eff_op == "eq":
                    lines.extend([
                        f"Theorem {thm_name} : ({nl}) = ({nr}) /\\ ({nr}) <= 1.",
                        "Proof.",
                        "  split; [vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity].",
                        "Qed.",
                        "",
                    ])
                else:
                    lines.extend([
                        f"Theorem {thm_name} : ({nl}) <= ({nr}) /\\ ({nr}) <= 1.",
                        "Proof.",
                        "  split; apply Nat.leb_le; vm_compute; reflexivity.",
                        "Qed.",
                        "",
                    ])
            else:
                # Presence
                bl = f"(negb (Nat.eqb ({nl}) 0))"
                br = f"(negb (Nat.eqb ({nr}) 0))"
                if eff_op == "eq":
                    lines.extend([
                        f"Theorem {thm_name} : ({bl}) = ({br}).",
                        "Proof.",
                        "  vm_compute. reflexivity.",
                        "Qed.",
                        "",
                    ])
                else:
                    lines.extend([
                        f"Theorem {thm_name} : @allows Presence ({bl}) ({br}).",
                        "Proof.",
                        f"  apply (proj2 (reflect_iff _ _ (allows_reflect Presence ({bl}) ({br})))).",
                        "  vm_compute. reflexivity.",
                        "Qed.",
                        "",
                    ])

    lines.append(f"End {module_name}.")
    gallina = "\n".join(lines) + "\n"
    digest = hashlib.sha256(gallina.encode("utf-8")).hexdigest()
    return GradeCertificate(
        domain=domain,
        assignments=dict(assignments),
        constraints=constraints,
        gallina=gallina,
        module_name=module_name,
        theorem_names=tuple(theorem_names),
        source_sha256=digest,
    )


def replay_semiring_proof(
    gallina: str,
    unit_name: str,
    theorem_count: int,
    module_name: str,
    error_context: str,
    *,
    theorem_names: Sequence[str] = (),
    prefix: str = "holdfast-semiring-",
    timeout: int = 60,
) -> list[str]:
    """Replay a semiring-based Rocq module and audit ``Print Assumptions`` for zero axioms."""
    root = Path(__file__).resolve().parents[2]
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory(prefix=prefix) as tmp:
        directory = Path(tmp)
        graded_source._support(root, compiler, directory, _ROCQ_SUPPORT)
        unit = directory / unit_name
        audit_lines = [f"Print Assumptions {module_name}.{name}." for name in theorem_names]
        unit.write_text(
            gallina + ("\n".join(audit_lines) + "\n" if audit_lines else ""),
            encoding="utf-8",
            newline="\n",
        )
        compiled = subprocess.run(
            [*compiler, unit.name],
            cwd=directory,
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            timeout=timeout,
        )
        if compiled.returncode != 0:
            raise ValueError(f"{error_context}: {compiled.stderr.strip()}")
        return solver_ledger.audit(compiled.stdout, theorem_count, module_name, ())


def verify_certificate(certificate: GradeCertificate) -> list[str]:
    """Replay a :class:`GradeCertificate` through Rocq and audit for zero axioms."""
    if not certificate.theorem_names:
        return []
    return replay_semiring_proof(
        certificate.gallina,
        "InferenceCertificate.v",
        len(certificate.theorem_names),
        certificate.module_name,
        "Rocq rejected grade inference certificate",
        theorem_names=certificate.theorem_names,
        prefix="holdfast-grade-infer-",
    )


def solve_constraints(
    constraints: Sequence[GradeConstraint],
    domain: str | InferenceDomain | graded_source.GradeDomain,
    *,
    metas: Sequence[GradeMeta] = (),
    max_steps: int = 256,
    verify_rocq: bool = False,
) -> InferenceResult:
    """Deterministically solve grade constraints and emit a replayable Rocq certificate."""
    if max_steps < 1:
        raise ValueError(f"max_steps must be positive, got {max_steps}")
    resolved_domain = coerce_domain(domain)
    constraint_tuple = tuple(constraints)

    domain_err = _constraint_domain_check(constraint_tuple, metas, resolved_domain)
    if domain_err is not None:
        return InferenceResult(
            status="inconsistent",
            domain=resolved_domain,
            assignments={},
            residuals=(domain_err,),
            certificate=None,
            steps_used=0,
        )

    all_meta_ids: set[int | str] = {m.id for m in metas}
    for c in constraint_tuple:
        all_meta_ids |= _expr_vars(c.lhs) | _expr_vars(c.rhs)

    active = [
        _ActiveConstraint(c, c.lhs, _effective_op(c.op, resolved_domain), c.rhs)
        for c in constraint_tuple
    ]
    concrete: dict[int | str, int] = {}
    symbolic: dict[int | str, GradeExpr] = {}
    steps = 0

    def _apply_subst(expr: GradeExpr) -> GradeExpr:
        env: dict[int | str, GradeExpr] = dict(symbolic)
        for k, val in concrete.items():
            env[k] = GradeLit(val)
        return _subst_expr(expr, env)

    while active:
        progress = False
        next_active: list[_ActiveConstraint] = []

        for idx, item in enumerate(active):
            steps += 1
            if steps > max_steps:
                remaining_items = active[idx:]
                residuals = tuple(
                    ResidualGoal(
                        rem.original,
                        "budget_exhausted",
                        f"solver exceeded max_steps={max_steps}",
                        tuple(sorted(_expr_vars(rem.lhs) | _expr_vars(rem.rhs), key=_var_sort_key)),
                        rem.original.origin_span,
                    )
                    for rem in remaining_items
                )
                return InferenceResult(
                    status="budget_exhausted",
                    domain=resolved_domain,
                    assignments=dict(concrete),
                    residuals=residuals,
                    certificate=None,
                    steps_used=steps - 1,
                )
            lhs = _apply_subst(item.lhs)
            rhs = _apply_subst(item.rhs)
            lhs, j_err_l = _simplify_joins(lhs, resolved_domain)
            rhs, j_err_r = _simplify_joins(rhs, resolved_domain)
            if j_err_l is not None or j_err_r is not None:
                return InferenceResult(
                    status="inconsistent",
                    domain=resolved_domain,
                    assignments=dict(concrete),
                    residuals=(
                        ResidualGoal(
                            item.original,
                            "inconsistent",
                            j_err_l or j_err_r or "inconsistent branch join",
                            tuple(sorted(_expr_vars(lhs) | _expr_vars(rhs), key=_var_sort_key)),
                            item.original.origin_span,
                        ),
                    ),
                    certificate=None,
                    steps_used=steps,
                )
            # Split GradeJoin(a, b) <= rhs into (a <= rhs) and (b <= rhs) for bounded domains.
            if (
                not domain_is_exact(resolved_domain)
                and item.op == "le"
                and isinstance(lhs, GradeJoin)
            ):
                next_active.append(_ActiveConstraint(item.original, lhs.lhs, "le", rhs))
                next_active.append(_ActiveConstraint(item.original, lhs.rhs, "le", rhs))
                progress = True
                continue

            if lhs != item.lhs or rhs != item.rhs:
                progress = True

            # Concrete evaluation check when all variables are resolved.
            lv = _eval_concrete(lhs, concrete, resolved_domain)
            rv = _eval_concrete(rhs, concrete, resolved_domain)
            if lv is not None and rv is not None:
                if not _allows_concrete(resolved_domain, item.op, lv, rv):
                    return InferenceResult(
                        status="inconsistent",
                        domain=resolved_domain,
                        assignments=dict(concrete),
                        residuals=(
                            ResidualGoal(
                                item.original,
                                "inconsistent",
                                f"constraint {lv} {item.op} {rv} fails in {resolved_domain.value}",
                                tuple(sorted(_expr_vars(lhs) | _expr_vars(rhs), key=_var_sort_key)),
                                item.original.origin_span,
                            ),
                        ),
                        certificate=None,
                        steps_used=steps,
                    )
                progress = True
                continue

            pl = _expr_to_poly(lhs, resolved_domain)
            pr = _expr_to_poly(rhs, resolved_domain)
            if pl is not None and pr is not None:
                if (item.op == "eq" and _poly_eq(pl, pr)) or (
                    item.op == "le"
                    and not domain_is_exact(resolved_domain)
                    and _poly_le(pl, pr)
                ):
                    progress = True
                    continue

                if item.op == "eq" and resolved_domain != InferenceDomain.PRESENCE:
                    resolved, new_c, new_s, err = _resolve_linear_equality(pl, pr, resolved_domain)
                    if err is not None:
                        return InferenceResult(
                            status="inconsistent",
                            domain=resolved_domain,
                            assignments=dict(concrete),
                            residuals=(
                                ResidualGoal(
                                    item.original,
                                    "inconsistent",
                                    err,
                                    tuple(sorted(_expr_vars(lhs) | _expr_vars(rhs), key=_var_sort_key)),
                                    item.original.origin_span,
                                ),
                            ),
                            certificate=None,
                            steps_used=steps,
                        )
                    if resolved:
                        for v, val in new_c.items():
                            if v in concrete and concrete[v] != val:
                                return InferenceResult(
                                    status="inconsistent",
                                    domain=resolved_domain,
                                    assignments=dict(concrete),
                                    residuals=(
                                        ResidualGoal(
                                            item.original,
                                            "inconsistent",
                                            f"conflicting values for {v!r}: {concrete[v]} vs {val}",
                                            (v,),
                                            item.original.origin_span,
                                        ),
                                    ),
                                    certificate=None,
                                    steps_used=steps,
                                )
                            concrete[v] = val
                        if new_s is not None:
                            sv, sexpr = new_s
                            if sv not in symbolic and sv not in concrete:
                                symbolic[sv] = sexpr
                        progress = True
                        continue

                # In bounded domains, sum(c_i * x_i) + const_l <= const_r with const_l == const_r forces x_i = 0.
                if (
                    item.op == "le"
                    and resolved_domain in {InferenceDomain.NAT_BOUND, InferenceDomain.AFFINE}
                ):
                    lin_l = _poly_linear(pl)
                    lin_r = _poly_linear(pr)
                    if lin_l is not None and lin_r is not None:
                        cl, vl = lin_l
                        cr, vr = lin_r
                        if vl and not vr:
                            if cl > cr:
                                return InferenceResult(
                                    status="inconsistent",
                                    domain=resolved_domain,
                                    assignments=dict(concrete),
                                    residuals=(
                                        ResidualGoal(
                                            item.original,
                                            "inconsistent",
                                            f"unsatisfiable inequality: left side >= {cl} > {cr}",
                                            tuple(sorted(vl, key=_var_sort_key)),
                                            item.original.origin_span,
                                        ),
                                    ),
                                    certificate=None,
                                    steps_used=steps,
                                )
                            if cl == cr:
                                for v in vl:
                                    if v in concrete and concrete[v] != 0:
                                        return InferenceResult(
                                            status="inconsistent",
                                            domain=resolved_domain,
                                            assignments=dict(concrete),
                                            residuals=(
                                                ResidualGoal(
                                                    item.original,
                                                    "inconsistent",
                                                    f"conflicting values for {v!r}: {concrete[v]} vs 0",
                                                    (v,),
                                                    item.original.origin_span,
                                                ),
                                            ),
                                            certificate=None,
                                            steps_used=steps,
                                        )
                                    concrete[v] = 0
                                progress = True
                                continue

            next_active.append(_ActiveConstraint(item.original, lhs, item.op, rhs))

        if resolved_domain == InferenceDomain.PRESENCE and next_active:
            next_active, pres_vals, pres_err = _presence_propagate(next_active)
            if pres_err is not None:
                return InferenceResult(
                    status="inconsistent",
                    domain=resolved_domain,
                    assignments=dict(concrete),
                    residuals=(
                        ResidualGoal(None, "inconsistent", pres_err, (), ()),
                    ),
                    certificate=None,
                    steps_used=steps,
                )
            for v, val in pres_vals.items():
                if v in concrete and concrete[v] != val:
                    return InferenceResult(
                        status="inconsistent",
                        domain=resolved_domain,
                        assignments=dict(concrete),
                        residuals=(
                            ResidualGoal(
                                None,
                                "inconsistent",
                                f"conflicting Presence values for {v!r}: {concrete[v]} vs {val}",
                                (v,),
                                (),
                            ),
                        ),
                        certificate=None,
                        steps_used=steps,
                    )
                if v not in concrete:
                    concrete[v] = val
                    progress = True

        # Resolve symbolic substitutions whose RHS variables became concrete.
        for sv in list(symbolic):
            rhs_val = _eval_concrete(symbolic[sv], concrete, resolved_domain)
            if rhs_val is not None:
                if resolved_domain == InferenceDomain.AFFINE and rhs_val > 1:
                    return InferenceResult(
                        status="inconsistent",
                        domain=resolved_domain,
                        assignments=dict(concrete),
                        residuals=(
                            ResidualGoal(
                                None,
                                "inconsistent",
                                f"affine variable {sv!r} resolved to {rhs_val} > 1",
                                (sv,),
                                (),
                            ),
                        ),
                        certificate=None,
                        steps_used=steps,
                    )
                concrete[sv] = rhs_val
                del symbolic[sv]
                progress = True

        active = next_active
        if not progress:
            break

    # Resolve any remaining bounded inequalities when domain admits minimal satisfying assignments.
    if active and not domain_is_exact(resolved_domain):
        if resolved_domain == InferenceDomain.PRESENCE:
            # In Presence, remaining bounded le constraints `x <= y` or `x <= 1` can take minimal 0.
            bounded_ok = True
            trial = dict(concrete)
            for v in sorted(all_meta_ids, key=_var_sort_key):
                if v not in trial and v not in symbolic:
                    trial[v] = 0
            # Only accept minimal 0 assignment if NO variable appears in an unresolved `eq` or lower-bound `1 <= ...`.
            if any(item.op == "eq" for item in active):
                bounded_ok = False
            else:
                for item in active:
                    lv = _eval_concrete(item.lhs, trial, resolved_domain)
                    rv = _eval_concrete(item.rhs, trial, resolved_domain)
                    if lv is None or rv is None or not _allows_concrete(resolved_domain, item.op, lv, rv):
                        bounded_ok = False
                        break
            if bounded_ok and not any(
                isinstance(item.lhs, GradeLit) and item.lhs.value > 0 for item in active
            ):
                # Ensure variables in active `x <= y` have an explicit upper bound rather than free `x <= y`.
                has_free_var_pair = any(
                    isinstance(item.lhs, GradeVar) and isinstance(item.rhs, GradeVar)
                    for item in active
                )
                if not has_free_var_pair:
                    concrete = trial
                    active = []
        else:
            rem_active, solved_bounds, bound_err = _solve_bounded_inequalities(
                active, resolved_domain, all_meta_ids, concrete
            )
            if bound_err is not None:
                return InferenceResult(
                    status="inconsistent" if bound_err.kind == "inconsistent" else "residual",
                    domain=resolved_domain,
                    assignments=dict(concrete),
                    residuals=(bound_err,),
                    certificate=None,
                    steps_used=steps,
                )
            if not rem_active:
                concrete = solved_bounds
                active = []

    if active:
        residuals = tuple(_classify_residual(item, resolved_domain) for item in active)
        return InferenceResult(
            status="residual",
            domain=resolved_domain,
            assignments=dict(concrete),
            residuals=residuals,
            certificate=None,
            steps_used=steps,
        )

    # Check if declared metas remain completely unconstrained by any constraint.
    unconstrained = [
        m for m in metas
        if m.id not in concrete and m.id not in symbolic
        and all(m.id not in (_expr_vars(c.lhs) | _expr_vars(c.rhs)) for c in constraint_tuple)
    ]
    if unconstrained:
        residuals = tuple(
            ResidualGoal(
                None,
                "underconstrained",
                f"metavariable {m.id!r} has no constraints",
                (m.id,),
                m.span,
            )
            for m in unconstrained
        )
        return InferenceResult(
            status="residual",
            domain=resolved_domain,
            assignments=dict(concrete),
            residuals=residuals,
            certificate=None,
            steps_used=steps,
        )

    # Final check on symbolic substitutions whose RHS still contains unsolved metavariables.
    if symbolic:
        unresolved_vars = tuple(sorted(symbolic, key=_var_sort_key))
        return InferenceResult(
            status="residual",
            domain=resolved_domain,
            assignments=dict(concrete),
            residuals=(
                ResidualGoal(
                    None,
                    "underconstrained",
                    f"underconstrained metavariables: {unresolved_vars}",
                    unresolved_vars,
                    (),
                ),
            ),
            certificate=None,
            steps_used=steps,
        )

    # For bounded domains, any declared meta whose constraints were all universally
    # satisfied (e.g. `0 <= m`) receives its minimal satisfying assignment `0`.
    if not domain_is_exact(resolved_domain):
        for m in metas:
            if m.id not in concrete and m.id not in symbolic:
                concrete[m.id] = 0

    # Verify all constraints concretely when assignments exist, and universally otherwise.
    for c in constraint_tuple:
        lv = _eval_concrete(c.lhs, concrete, resolved_domain)
        rv = _eval_concrete(c.rhs, concrete, resolved_domain)
        eff_op = _effective_op(c.op, resolved_domain)
        if lv is not None and rv is not None and not _allows_concrete(resolved_domain, eff_op, lv, rv):
            return InferenceResult(
                status="inconsistent",
                domain=resolved_domain,
                assignments=dict(concrete),
                residuals=(
                    ResidualGoal(
                        c,
                        "inconsistent",
                        f"final verification failed: {lv} {eff_op} {rv} in {resolved_domain.value}",
                        tuple(sorted(_expr_vars(c.lhs) | _expr_vars(c.rhs), key=_var_sort_key)),
                        c.origin_span,
                    ),
                ),
                certificate=None,
                steps_used=steps,
            )

    certificate = _emit_certificate(resolved_domain, constraint_tuple, concrete, metas)
    if verify_rocq:
        verify_certificate(certificate)

    return InferenceResult(
        status="solved",
        domain=resolved_domain,
        assignments=dict(concrete),
        residuals=(),
        certificate=certificate,
        steps_used=steps,
    )


def parse_rocq_assumptions_count(gallina: str) -> int:
    """Count declared axioms in emitted Gallina using :mod:`toolchain.solver_ledger`."""
    return len(solver_ledger.ledger(gallina))


_SANITY_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
