# SPDX-License-Identifier: Apache-2.0
"""Bounded grade-directed program synthesis with Rocq verification (Q25ca).

Synthesizes graded programs over a typed component library and graded context
under a finite :class:`SynthesisBudget`, pruning resource-invalid branches
immediately, rejecting well-typed but behaviorally wrong candidates against an
optional specification/oracle, replaying accepted candidates through Rocq (zero
axioms), and returning explicit :class:`SynthesisResidual` results on failure
or budget exhaustion.
"""

import hashlib
import subprocess
import tempfile
import time
from collections.abc import Callable, Iterator, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from toolchain import graded_combinators as gc
from toolchain import graded_inference as gi
from toolchain import graded_source, proofenv, solver_ledger

_ROCQ_SUPPORT = ("graded_pure.v", "graded_domains.v", "graded_semiring.v")


@dataclass(frozen=True)
class SynthesisBudget:
    """Finite search bounds for grade-directed synthesis."""

    max_nodes: int = 250
    max_depth: int = 6
    timeout_ms: int = 2000

    def __post_init__(self) -> None:
        if self.max_nodes < 1:
            raise ValueError(f"max_nodes must be >= 1, got {self.max_nodes}")
        if self.max_depth < 1:
            raise ValueError(f"max_depth must be >= 1, got {self.max_depth}")
        if self.timeout_ms < 1:
            raise ValueError(f"timeout_ms must be >= 1, got {self.timeout_ms}")


@dataclass(frozen=True)
class ContextVar:
    """Graded input variable in the synthesis context."""

    name: str
    ty: gc.CombinatorType
    allowance: int
    duplicable: bool = True
    disposable: bool = True

    def __post_init__(self) -> None:
        if self.allowance < 0:
            raise ValueError(f"allowance for {self.name!r} must be >= 0, got {self.allowance}")


@dataclass(frozen=True)
class Component:
    """Typed graded component available during synthesis."""

    name: str
    ty: gc.CombinatorType
    semantics: Callable[..., object] | None = None
    cost: int = 1
    duplicable: bool = True
    rocq_expr: str | None = None


@dataclass(frozen=True)
class SVar:
    name: str


@dataclass(frozen=True)
class SConst:
    name: str


@dataclass(frozen=True)
class SUnit:
    pass


@dataclass(frozen=True)
class SPair:
    left: STerm
    right: STerm


@dataclass(frozen=True)
class SLetPair:
    left_var: str
    right_var: str
    scale: int
    scrutinee: STerm
    body: STerm


@dataclass(frozen=True)
class SPromote:
    grade: int
    body: STerm


@dataclass(frozen=True)
class SLetBox:
    var_name: str
    scale: int
    scrutinee: STerm
    body: STerm


@dataclass(frozen=True)
class SInl:
    right_ty: gc.CombinatorType
    body: STerm


@dataclass(frozen=True)
class SInr:
    left_ty: gc.CombinatorType
    body: STerm


@dataclass(frozen=True)
class SMatchSum:
    left_var: str
    right_var: str
    scale: int
    scrutinee: STerm
    left_body: STerm
    right_body: STerm


@dataclass(frozen=True)
class SLam:
    param: str
    allowance: int
    domain: gc.CombinatorType
    body: STerm


@dataclass(frozen=True)
class SApp:
    callee: STerm
    arg: STerm


type STerm = (
    SVar
    | SConst
    | SUnit
    | SPair
    | SLetPair
    | SPromote
    | SLetBox
    | SInl
    | SInr
    | SMatchSum
    | SLam
    | SApp
)


@dataclass(frozen=True)
class SynthesisSuccess:
    """Accepted, behaviorally validated, and kernel-replayable synthesis outcome."""

    status: Literal["synthesized"]
    domain: gi.InferenceDomain
    term: STerm
    goal_type: gc.CombinatorType
    used_grades: Mapping[str, int]
    holdfast_source: str
    gallina: str
    module_name: str
    theorem_name: str
    explored_nodes: int
    pruned_branches: int
    behavioral_rejections: int
    source_sha256: str


@dataclass(frozen=True)
class SynthesisResidual:
    """Explicit failure/exhaustion verdict with zero accepted partial results."""

    status: Literal["exhausted", "unsatisfiable"]
    domain: gi.InferenceDomain
    explored_nodes: int
    pruned_branches: int
    behavioral_rejections: int
    remaining_goals: tuple[str, ...]
    reason: str = ""


type SynthesisOutcome = SynthesisSuccess | SynthesisResidual


class _BudgetExhausted(Exception):
    def __init__(self, reason: str) -> None:
        super().__init__(reason)
        self.reason = reason


@dataclass(frozen=True)
class _BoxedTag:
    value: object


@dataclass(frozen=True)
class _SumTag:
    side: Literal["left", "right"]
    value: object


def _eval_sterm(
    term: STerm,
    env: Mapping[str, object],
    components: Mapping[str, Component],
) -> object:
    if isinstance(term, SVar):
        return env[term.name]
    if isinstance(term, SConst):
        comp = components[term.name]
        if comp.semantics is None:
            raise ValueError(f"component {term.name!r} has no Python semantics for behavioral oracle")
        return comp.semantics
    if isinstance(term, SUnit):
        return ()
    if isinstance(term, SPair):
        return (_eval_sterm(term.left, env, components), _eval_sterm(term.right, env, components))
    if isinstance(term, SLetPair):
        pair_val = _eval_sterm(term.scrutinee, env, components)
        if not isinstance(pair_val, tuple) or len(pair_val) != 2:
            raise TypeError(f"expected pair value, got {pair_val!r}")
        extended = {**env, term.left_var: pair_val[0], term.right_var: pair_val[1]}
        return _eval_sterm(term.body, extended, components)
    if isinstance(term, SPromote):
        return _BoxedTag(_eval_sterm(term.body, env, components))
    if isinstance(term, SLetBox):
        boxed = _eval_sterm(term.scrutinee, env, components)
        if not isinstance(boxed, _BoxedTag):
            raise TypeError(f"expected Box value, got {boxed!r}")
        extended = {**env, term.var_name: boxed.value}
        return _eval_sterm(term.body, extended, components)
    if isinstance(term, SInl):
        return _SumTag("left", _eval_sterm(term.body, env, components))
    if isinstance(term, SInr):
        return _SumTag("right", _eval_sterm(term.body, env, components))
    if isinstance(term, SMatchSum):
        scrut = _eval_sterm(term.scrutinee, env, components)
        if not isinstance(scrut, _SumTag):
            raise TypeError(f"expected Sum value, got {scrut!r}")
        if scrut.side == "left":
            return _eval_sterm(term.left_body, {**env, term.left_var: scrut.value}, components)
        return _eval_sterm(term.right_body, {**env, term.right_var: scrut.value}, components)
    if isinstance(term, SLam):
        return lambda arg: _eval_sterm(term.body, {**env, term.param: arg}, components)
    # SApp
    callee_val = _eval_sterm(term.callee, env, components)
    arg_val = _eval_sterm(term.arg, env, components)
    if not callable(callee_val):
        raise TypeError(f"expected callable in application, got {callee_val!r}")
    return callee_val(arg_val)


def _build_evaluator(
    term: STerm,
    context: Sequence[ContextVar],
    components: Mapping[str, Component],
) -> Callable[..., object]:
    def _run(*args: object) -> object:
        if len(args) != len(context):
            raise TypeError(f"expected {len(context)} arguments, got {len(args)}")
        env = {var.name: val for var, val in zip(context, args, strict=True)}
        return _eval_sterm(term, env, components)

    return _run


def _unwrap_arrows(ty: gc.CombinatorType) -> tuple[list[tuple[int, gc.CombinatorType]], gc.CombinatorType]:
    args: list[tuple[int, gc.CombinatorType]] = []
    cur = ty
    while isinstance(cur, gc.ArrowType):
        if not isinstance(cur.allowance, gi.GradeLit):
            break
        args.append((cur.allowance.value, cur.domain))
        cur = cur.codomain
    return args, cur


def _format_sterm_hf(term: STerm, domain: gi.InferenceDomain) -> str:
    if isinstance(term, SVar):
        return term.name
    if isinstance(term, SConst):
        return term.name
    if isinstance(term, SUnit):
        return "()"
    if isinstance(term, SPair):
        return f"({_format_sterm_hf(term.left, domain)}, {_format_sterm_hf(term.right, domain)})"
    if isinstance(term, SLetPair):
        return (
            f"(match ({_format_sterm_hf(term.scrutinee, domain)}) "
            f"{{ Pair({term.left_var}, {term.right_var}) => {_format_sterm_hf(term.body, domain)}, }})"
        )
    if isinstance(term, SPromote):
        return f"Box<_, {term.grade}>({_format_sterm_hf(term.body, domain)})"
    if isinstance(term, SLetBox):
        return (
            f"(match ({_format_sterm_hf(term.scrutinee, domain)}) "
            f"{{ Box({term.var_name}) => {_format_sterm_hf(term.body, domain)}, }})"
        )
    if isinstance(term, SInl):
        return f"Left({_format_sterm_hf(term.body, domain)})"
    if isinstance(term, SInr):
        return f"Right({_format_sterm_hf(term.body, domain)})"
    if isinstance(term, SMatchSum):
        return (
            f"(match ({_format_sterm_hf(term.scrutinee, domain)}) "
            f"{{ Left({term.left_var}) => {_format_sterm_hf(term.left_body, domain)}, "
            f"Right({term.right_var}) => {_format_sterm_hf(term.right_body, domain)}, }})"
        )
    if isinstance(term, SLam):
        return (
            f"(({gc._format_type_hf(term.domain)} {term.param} @ {domain.value}({term.allowance})) => "
            f"{_format_sterm_hf(term.body, domain)})"
        )
    # Collapse curried SApp(SApp(f, a), b) -> f(a, b)
    args: list[STerm] = []
    head: STerm = term
    while isinstance(head, SApp):
        args.append(head.arg)
        head = head.callee
    args.reverse()
    arg_str = ", ".join(_format_sterm_hf(arg, domain) for arg in args)
    return f"{_format_sterm_hf(head, domain)}({arg_str})"


def _collect_sterm_types(term: STerm) -> set[str]:
    names: set[str] = set()
    if isinstance(term, (SPair, SApp)):
        names |= _collect_sterm_types(term.left if isinstance(term, SPair) else term.callee)
        names |= _collect_sterm_types(term.right if isinstance(term, SPair) else term.arg)
    elif isinstance(term, SLetPair):
        names |= _collect_sterm_types(term.scrutinee) | _collect_sterm_types(term.body)
    elif isinstance(term, SPromote):
        names |= _collect_sterm_types(term.body)
    elif isinstance(term, SLetBox):
        names |= _collect_sterm_types(term.scrutinee) | _collect_sterm_types(term.body)
    elif isinstance(term, SInl):
        names |= gc._collect_base_names(term.right_ty) | _collect_sterm_types(term.body)
    elif isinstance(term, SInr):
        names |= gc._collect_base_names(term.left_ty) | _collect_sterm_types(term.body)
    elif isinstance(term, SMatchSum):
        names |= (
            _collect_sterm_types(term.scrutinee)
            | _collect_sterm_types(term.left_body)
            | _collect_sterm_types(term.right_body)
        )
    elif isinstance(term, SLam):
        names |= gc._collect_base_names(term.domain) | _collect_sterm_types(term.body)
    return names


def _emit_sterm_coq(
    term: STerm,
    var_ids: Mapping[str, int],
    base_map: Mapping[str, int],
    next_id: list[int],
) -> str:
    if isinstance(term, SVar):
        return f"(CVar {var_ids[term.name]})"
    if isinstance(term, SConst):
        return f"(CVar {var_ids[f'__comp_{term.name}']})"
    if isinstance(term, SUnit):
        return "CUnit"
    if isinstance(term, SPair):
        return f"(CPair {_emit_sterm_coq(term.left, var_ids, base_map, next_id)} {_emit_sterm_coq(term.right, var_ids, base_map, next_id)})"
    if isinstance(term, SLetPair):
        scrut = _emit_sterm_coq(term.scrutinee, var_ids, base_map, next_id)
        lx = next_id[0]
        rx = next_id[0] + 1
        next_id[0] += 2
        body = _emit_sterm_coq(
            term.body,
            {**var_ids, term.left_var: lx, term.right_var: rx},
            base_map,
            next_id,
        )
        return f"(CLetPair {lx} {rx} (GLit {term.scale}) {scrut} {body})"
    if isinstance(term, SPromote):
        return f"(CPromote (GLit {term.grade}) {_emit_sterm_coq(term.body, var_ids, base_map, next_id)})"
    if isinstance(term, SLetBox):
        scrut = _emit_sterm_coq(term.scrutinee, var_ids, base_map, next_id)
        bx = next_id[0]
        next_id[0] += 1
        body = _emit_sterm_coq(term.body, {**var_ids, term.var_name: bx}, base_map, next_id)
        return f"(CLetBox {bx} (GLit {term.scale}) {scrut} {body})"
    if isinstance(term, SInl):
        return f"(CInl {gc._emit_type_coq(term.right_ty, base_map, {})} {_emit_sterm_coq(term.body, var_ids, base_map, next_id)})"
    if isinstance(term, SInr):
        return f"(CInr {gc._emit_type_coq(term.left_ty, base_map, {})} {_emit_sterm_coq(term.body, var_ids, base_map, next_id)})"
    if isinstance(term, SMatchSum):
        scrut = _emit_sterm_coq(term.scrutinee, var_ids, base_map, next_id)
        lx = next_id[0]
        rx = next_id[0] + 1
        next_id[0] += 2
        lbody = _emit_sterm_coq(term.left_body, {**var_ids, term.left_var: lx}, base_map, next_id)
        rbody = _emit_sterm_coq(term.right_body, {**var_ids, term.right_var: rx}, base_map, next_id)
        return f"(CMatchSum {lx} {rx} (GLit {term.scale}) {scrut} {lbody} {rbody})"
    if isinstance(term, SLam):
        px = next_id[0]
        next_id[0] += 1
        dom_c = gc._emit_type_coq(term.domain, base_map, {})
        body = _emit_sterm_coq(term.body, {**var_ids, term.param: px}, base_map, next_id)
        return f"(CLam {px} (GLit {term.allowance}) {dom_c} {body})"
    # SApp
    return f"(CApp {_emit_sterm_coq(term.callee, var_ids, base_map, next_id)} {_emit_sterm_coq(term.arg, var_ids, base_map, next_id)})"


def _collect_used_components(term: STerm) -> list[str]:
    seen: list[str] = []

    def _walk(node: STerm) -> None:
        if isinstance(node, SConst):
            if node.name not in seen:
                seen.append(node.name)
        elif isinstance(node, SPair):
            _walk(node.left)
            _walk(node.right)
        elif isinstance(node, SApp):
            _walk(node.callee)
            _walk(node.arg)
        elif isinstance(node, SLetPair):
            _walk(node.scrutinee)
            _walk(node.body)
        elif isinstance(node, (SPromote, SInl, SInr, SLam)):
            _walk(node.body)
        elif isinstance(node, SLetBox):
            _walk(node.scrutinee)
            _walk(node.body)
        elif isinstance(node, SMatchSum):
            _walk(node.scrutinee)
            _walk(node.left_body)
            _walk(node.right_body)

    _walk(term)
    return seen


def _count_component_uses(term: STerm, comp_name: str, scale: int = 1) -> int:
    if isinstance(term, SConst):
        return scale if term.name == comp_name else 0
    if isinstance(term, (SVar, SUnit)):
        return 0
    if isinstance(term, SPair):
        return _count_component_uses(term.left, comp_name, scale) + _count_component_uses(term.right, comp_name, scale)
    if isinstance(term, SLetPair):
        return (
            _count_component_uses(term.scrutinee, comp_name, scale * term.scale)
            + _count_component_uses(term.body, comp_name, scale)
        )
    if isinstance(term, SPromote):
        return _count_component_uses(term.body, comp_name, scale * term.grade)
    if isinstance(term, SLetBox):
        return (
            _count_component_uses(term.scrutinee, comp_name, scale * term.scale)
            + _count_component_uses(term.body, comp_name, scale)
        )
    if isinstance(term, (SInl, SInr, SLam)):
        return _count_component_uses(term.body, comp_name, scale)
    if isinstance(term, SMatchSum):
        return (
            _count_component_uses(term.scrutinee, comp_name, scale * term.scale)
            + _count_component_uses(term.left_body, comp_name, scale)
        )
    # SApp
    return _count_component_uses(term.callee, comp_name, scale) + _count_component_uses(term.arg, comp_name, scale)


def _emit_synthesis_gallina(
    term: STerm,
    domain: gi.InferenceDomain,
    context: Sequence[ContextVar],
    goal_type: gc.CombinatorType,
    components: Mapping[str, Component],
) -> tuple[str, str, str]:
    module_name = "SynthesizedProgram"
    theorem_name = "synthesized_sound"
    allows_prop, allowsb_fn, sound_lemma, zero_lemma = gc.rocq_domain_config(domain)

    used_comps = _collect_used_components(term)
    all_base_names = gc._collect_base_names(goal_type) | _collect_sterm_types(term)
    for var in context:
        all_base_names |= gc._collect_base_names(var.ty)
    for cname in used_comps:
        all_base_names |= gc._collect_base_names(components[cname].ty)
    base_map = {name: idx for idx, name in enumerate(sorted(all_base_names))}

    var_ids: dict[str, int] = {}
    next_id = [1]
    for cname in used_comps:
        var_ids[f"__comp_{cname}"] = next_id[0]
        next_id[0] += 1
    for var in context:
        var_ids[var.name] = next_id[0]
        next_id[0] += 1

    body_coq = _emit_sterm_coq(term, var_ids, base_map, next_id)
    wrapped_term = body_coq
    wrapped_ty = gc._emit_type_coq(goal_type, base_map, {})

    for var in reversed(context):
        vid = var_ids[var.name]
        vty = gc._emit_type_coq(var.ty, base_map, {})
        wrapped_term = f"(CLam {vid} (GLit {var.allowance}) {vty} {wrapped_term})"
        wrapped_ty = f"(CArr (GLit {var.allowance}) {vty} {wrapped_ty})"

    for cname in reversed(used_comps):
        cid = var_ids[f"__comp_{cname}"]
        cty = gc._emit_type_coq(components[cname].ty, base_map, {})
        c_uses = _count_component_uses(term, cname)
        wrapped_term = f"(CLam {cid} (GLit {c_uses}) {cty} {wrapped_term})"
        wrapped_ty = f"(CArr (GLit {c_uses}) {cty} {wrapped_ty})"

    lines = [
        "(* SPDX-License-Identifier: Apache-2.0 *)",
        "From Stdlib Require Import List Arith.PeanoNat Bool.Bool Lia.",
        "Require Import graded_pure graded_domains graded_semiring.",
        "Import ListNotations GradedDomains GradedSemiring.",
        gc.COMBINATOR_KERNEL_GALLINA,
        f"Module {module_name}.",
        "Import CombinatorKernel.",
        "",
        f"Definition candidate_term : cterm := {wrapped_term}.",
        f"Definition candidate_type : cty := {wrapped_ty}.",
        "",
        "Theorem synthesized_checked :",
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
        "  exact synthesized_checked.",
        "Qed.",
        "",
        f"End {module_name}.",
    ]
    return "\n".join(lines) + "\n", module_name, theorem_name


def verify_synthesis(outcome: SynthesisSuccess) -> list[str]:
    """Replay an accepted synthesis candidate through Rocq and audit for zero axioms."""
    root = Path(__file__).resolve().parents[2]
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-synth-") as tmp:
        directory = Path(tmp)
        graded_source._support(root, compiler, directory, _ROCQ_SUPPORT)
        unit = directory / "SynthProof.v"
        unit.write_text(outcome.gallina, encoding="utf-8", newline="\n")
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
            raise ValueError(f"Rocq rejected synthesized program: {compiled.stderr.strip()}")
        audit = directory / "SynthAudit.v"
        audit.write_text(
            f"Require Import SynthProof.\nPrint Assumptions {outcome.module_name}.{outcome.theorem_name}.\n",
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
            raise ValueError(f"Rocq audit failed on synthesized program: {audited.stderr.strip()}")
        return solver_ledger.audit(audited.stdout, 1, outcome.module_name, ())


def synthesize(
    goal_type: gc.CombinatorType,
    *,
    domain: str | gi.InferenceDomain | graded_source.GradeDomain = gi.InferenceDomain.NAT_EXACT,
    context: Sequence[ContextVar] = (),
    components: Sequence[Component] = (),
    budget: SynthesisBudget | None = None,
    examples: Sequence[tuple[tuple[object, ...], object]] = (),
    oracle: Callable[[Callable[..., object]], bool] | None = None,
    verify_rocq: bool = False,
) -> SynthesisOutcome:
    """Run bounded grade-directed synthesis over ``components`` and ``context``."""
    resolved_domain = gi.coerce_domain(domain)
    active_budget = budget if budget is not None else SynthesisBudget()
    comp_map = {comp.name: comp for comp in components}
    if len(comp_map) != len(components):
        raise ValueError("duplicate component name in synthesis library")
    if len({v.name for v in context}) != len(context):
        raise ValueError("duplicate variable name in synthesis context")

    if resolved_domain == gi.InferenceDomain.AFFINE:
        for var in context:
            if var.allowance > 1:
                return SynthesisResidual(
                    status="unsatisfiable",
                    domain=resolved_domain,
                    explored_nodes=0,
                    pruned_branches=1,
                    behavioral_rejections=0,
                    remaining_goals=(f"affine binder {var.name!r} allowance {var.allowance} > 1",),
                    reason="affine context allowance cannot exceed 1",
                )

    explored_nodes = 0
    pruned_branches = 0
    behavioral_rejections = 0
    fresh_counter = 0
    start_ns = time.monotonic_ns()

    def _fresh(prefix: str) -> str:
        nonlocal fresh_counter
        fresh_counter += 1
        return f"{prefix}_{fresh_counter}"

    def _tick() -> None:
        nonlocal explored_nodes
        elapsed_ms = (time.monotonic_ns() - start_ns) / 1_000_000.0
        if elapsed_ms > active_budget.timeout_ms:
            raise _BudgetExhausted(f"timeout after {elapsed_ms:.1f}ms > {active_budget.timeout_ms}ms")
        if explored_nodes >= active_budget.max_nodes:
            raise _BudgetExhausted(f"explored {explored_nodes} >= max_nodes={active_budget.max_nodes}")
        explored_nodes += 1

    def _can_consume(var: ContextVar, current_used: int, added: int) -> int | None:
        nonlocal pruned_branches
        if not var.duplicable and ((current_used > 0 and added > 0) or added > 1):
            pruned_branches += 1
            return None
        if resolved_domain == gi.InferenceDomain.PRESENCE:
            new_u = 1 if (current_used > 0 or added > 0) else 0
            if var.allowance == 0 and new_u > 0:
                pruned_branches += 1
                return None
            return new_u
        new_u = current_used + added
        if new_u > var.allowance:
            pruned_branches += 1
            return None
        return new_u

    def _final_grade_ok(var: ContextVar, actual: int) -> bool:
        if resolved_domain in {gi.InferenceDomain.NAT_EXACT, gi.InferenceDomain.LINEAR}:
            return actual == var.allowance
        if resolved_domain in {gi.InferenceDomain.NAT_BOUND, gi.InferenceDomain.AFFINE}:
            if not var.disposable and actual == 0 and var.allowance > 0:
                return False
            return actual <= var.allowance
        # Presence
        return actual == 0 or var.allowance > 0

    def _check_all_final(env: tuple[ContextVar, ...], used: Mapping[str, int]) -> bool:
        return all(_final_grade_ok(v, used[v.name]) for v in env)

    def _search(
        target: gc.CombinatorType,
        env: tuple[ContextVar, ...],
        used: dict[str, int],
        comp_used: dict[str, int],
        scale: int,
        depth: int,
        unpacked: frozenset[str],
    ) -> Iterator[tuple[STerm, dict[str, int], dict[str, int]]]:
        nonlocal pruned_branches
        if depth > active_budget.max_depth:
            return
        _tick()

        # 1. Exact variable match (immediate grade pruning)
        for var in env:
            if var.ty == target:
                next_val = _can_consume(var, used[var.name], scale)
                if next_val is not None:
                    yield (SVar(var.name), {**used, var.name: next_val}, comp_used)

        # 2. Direct nullary component match
        for comp in components:
            if comp.ty == target:
                if not comp.duplicable and comp_used.get(comp.name, 0) > 0:
                    pruned_branches += 1
                    continue
                if scale > 1 and not comp.duplicable:
                    pruned_branches += 1
                    continue
                yield (
                    SConst(comp.name),
                    used,
                    {**comp_used, comp.name: comp_used.get(comp.name, 0) + scale},
                )

        # 3. Structural introduction rules
        if target == gc.UNIT_TYPE:
            yield (SUnit(), used, comp_used)

        if isinstance(target, gc.BoxType) and isinstance(target.grade, gi.GradeLit):
            q = target.grade.value
            for body, u1, cu1 in _search(
                target.payload, env, used, comp_used, scale * q, depth + 1, unpacked
            ):
                yield (SPromote(q, body), u1, cu1)

        if isinstance(target, gc.PairType):
            for left_term, u1, cu1 in _search(
                target.left, env, used, comp_used, scale, depth + 1, unpacked
            ):
                for right_term, u2, cu2 in _search(
                    target.right, env, u1, cu1, scale, depth + 1, unpacked
                ):
                    yield (SPair(left_term, right_term), u2, cu2)

        if isinstance(target, gc.SumType):
            for inner, u1, cu1 in _search(
                target.left, env, used, comp_used, scale, depth + 1, unpacked
            ):
                yield (SInl(target.right, inner), u1, cu1)
            for inner, u1, cu1 in _search(
                target.right, env, used, comp_used, scale, depth + 1, unpacked
            ):
                yield (SInr(target.left, inner), u1, cu1)

        if isinstance(target, gc.ArrowType) and isinstance(target.allowance, gi.GradeLit):
            p_name = _fresh("p")
            p_var = ContextVar(p_name, target.domain, target.allowance.value)
            for body, u1, cu1 in _search(
                target.codomain,
                (*env, p_var),
                {**used, p_name: 0},
                comp_used,
                scale,
                depth + 1,
                unpacked,
            ):
                if _final_grade_ok(p_var, u1[p_name]):
                    trimmed = {k: v for k, v in u1.items() if k != p_name}
                    yield (SLam(p_name, target.allowance.value, target.domain, body), trimmed, cu1)
                else:
                    pruned_branches += 1

        # 4. Component & context function applications
        if depth < active_budget.max_depth:
            for comp in components:
                arg_specs, ret_ty = _unwrap_arrows(comp.ty)
                if not arg_specs or ret_ty != target:
                    continue
                if not comp.duplicable and comp_used.get(comp.name, 0) > 0:
                    pruned_branches += 1
                    continue
                yield from _apply_chain(
                    SConst(comp.name),
                    arg_specs,
                    env,
                    used,
                    {**comp_used, comp.name: comp_used.get(comp.name, 0) + scale},
                    scale,
                    depth + 1,
                    unpacked,
                )

            for var in env:
                arg_specs, ret_ty = _unwrap_arrows(var.ty)
                if not arg_specs or ret_ty != target:
                    continue
                next_val = _can_consume(var, used[var.name], scale)
                if next_val is None:
                    continue
                yield from _apply_chain(
                    SVar(var.name),
                    arg_specs,
                    env,
                    {**used, var.name: next_val},
                    comp_used,
                    scale,
                    depth + 1,
                    unpacked,
                )

        # 5. Box and Pair eliminations from context
        if depth + 1 < active_budget.max_depth:
            for var in env:
                if var.name in unpacked:
                    continue
                if isinstance(var.ty, gc.BoxType) and isinstance(var.ty.grade, gi.GradeLit):
                    next_val = _can_consume(var, used[var.name], scale)
                    if next_val is None:
                        continue
                    inner_name = _fresh("unbox")
                    inner_allow = var.ty.grade.value * scale
                    inner_var = ContextVar(
                        inner_name,
                        var.ty.payload,
                        inner_allow,
                        duplicable=var.duplicable and gc._is_duplicable(var.ty.payload),
                        disposable=var.disposable and gc._is_disposable(var.ty.payload),
                    )
                    for body, u1, cu1 in _search(
                        target,
                        (*env, inner_var),
                        {**used, var.name: next_val, inner_name: 0},
                        comp_used,
                        1,
                        depth + 1,
                        unpacked | {var.name, inner_name},
                    ):
                        if _final_grade_ok(inner_var, u1[inner_name]):
                            trimmed = {k: v for k, v in u1.items() if k != inner_name}
                            yield (SLetBox(inner_name, scale, SVar(var.name), body), trimmed, cu1)
                        else:
                            pruned_branches += 1

    def _apply_chain(
        callee_term: STerm,
        arg_specs: list[tuple[int, gc.CombinatorType]],
        env: tuple[ContextVar, ...],
        used: dict[str, int],
        comp_used: dict[str, int],
        scale: int,
        depth: int,
        unpacked: frozenset[str],
    ) -> Iterator[tuple[STerm, dict[str, int], dict[str, int]]]:
        if not arg_specs:
            yield (callee_term, used, comp_used)
            return
        arg_grade, arg_ty = arg_specs[0]
        rest = arg_specs[1:]
        for arg_term, u1, cu1 in _search(
            arg_ty, env, used, comp_used, scale * arg_grade, depth, unpacked
        ):
            yield from _apply_chain(
                SApp(callee_term, arg_term),
                rest,
                env,
                u1,
                cu1,
                scale,
                depth,
                unpacked,
            )

    def _behavioral_ok(term: STerm) -> bool:
        if not examples and oracle is None:
            return True
        fn = _build_evaluator(term, context, comp_map)
        try:
            for args, expected in examples:
                if fn(*args) != expected:
                    return False
            if oracle is not None and not oracle(fn):
                return False
        except Exception:
            return False
        return True

    init_used = {var.name: 0 for var in context}
    env_tuple = tuple(context)
    try:
        for candidate, final_used, _ in _search(
            goal_type, env_tuple, init_used, {}, 1, 0, frozenset()
        ):
            if not _check_all_final(env_tuple, final_used):
                pruned_branches += 1
                continue
            if not _behavioral_ok(candidate):
                behavioral_rejections += 1
                continue

            params_hf = ", ".join(
                f"{gc._format_type_hf(v.ty)} {v.name} @ {resolved_domain.value}({v.allowance})"
                for v in context
            )
            holdfast_source = "\n".join([
                "// SPDX-License-Identifier: Apache-2.0",
                "module Synthesized;",
                f"public definition {gc._format_type_hf(goal_type)} Synth({params_hf}) =>",
                f"    {_format_sterm_hf(candidate, resolved_domain)};",
            ]) + "\n"
            gallina, module_name, theorem_name = _emit_synthesis_gallina(
                candidate, resolved_domain, context, goal_type, comp_map
            )
            success = SynthesisSuccess(
                status="synthesized",
                domain=resolved_domain,
                term=candidate,
                goal_type=goal_type,
                used_grades=dict(final_used),
                holdfast_source=holdfast_source,
                gallina=gallina,
                module_name=module_name,
                theorem_name=theorem_name,
                explored_nodes=explored_nodes,
                pruned_branches=pruned_branches,
                behavioral_rejections=behavioral_rejections,
                source_sha256=hashlib.sha256(holdfast_source.encode("utf-8")).hexdigest(),
            )
            if verify_rocq:
                verify_synthesis(success)
            return success
    except _BudgetExhausted as exc:
        return SynthesisResidual(
            status="exhausted",
            domain=resolved_domain,
            explored_nodes=explored_nodes,
            pruned_branches=pruned_branches,
            behavioral_rejections=behavioral_rejections,
            remaining_goals=(f"{gc._format_type_hf(goal_type)} under {resolved_domain.value}",),
            reason=exc.reason,
        )

    return SynthesisResidual(
        status="unsatisfiable",
        domain=resolved_domain,
        explored_nodes=explored_nodes,
        pruned_branches=pruned_branches,
        behavioral_rejections=behavioral_rejections,
        remaining_goals=(f"{gc._format_type_hf(goal_type)} under {resolved_domain.value}",),
        reason="search space exhausted with no grade-valid, behaviorally matching candidate",
    )
