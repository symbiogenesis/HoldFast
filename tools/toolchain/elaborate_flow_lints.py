# SPDX-License-Identifier: Apache-2.0
"""Advisories backed by checked expression, proof and loop facts."""

from collections.abc import Generator
from contextlib import contextmanager
from typing import TYPE_CHECKING, cast

from toolchain.ast import HoldFastError
from toolchain.elaborate_types import Node, _apps, _Binding, _constant, _IntSpec, _Meta, _Term
from toolchain.surface import nodes

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator
    from toolchain.parser import Json


def report(compiler: _Elaborator, code: str, node: Node, message: str) -> None:
    compiler.semantic_lints[code, cast("list[int]", node["span"])[0]] = message


def observe(compiler: _Elaborator, code: str, node: Node, message: str | None) -> None:
    key = code, cast("list[int]", node["span"])[0]
    # One source site can be checked at several iterations or branch states.
    # Require agreement before reporting a finding for the source site.
    previous = compiler.flow_lint_observations.setdefault(key, message)
    if previous != message:
        compiler.flow_lint_observations[key] = None


@contextmanager
def _probe(compiler: _Elaborator) -> Generator[None]:
    work, reductions, site = compiler.work, compiler.reductions, compiler.site
    serial = compiler.serial
    metas, first_meta, cache = compiler.metas, compiler.decl_first_meta, compiler.whnf_cache
    freezes, freeze_bytes = compiler.freeze_checks, compiler.freeze_check_bytes
    compiler.metas = [_Meta(meta.type, meta.scope, meta.solution) for meta in metas]
    compiler.whnf_cache = {}
    compiler.freeze_checks = {}
    compiler.work = min(work, 3000)
    compiler.reductions = min(reductions, 1000)
    try:
        yield
    except (HoldFastError, RecursionError):
        pass
    finally:
        for binder in range(serial, compiler.serial, compiler.binder_stride):
            compiler.types.pop(binder, None)
        compiler.serial = serial
        compiler.work, compiler.reductions, compiler.site = work, reductions, site
        compiler.metas, compiler.decl_first_meta, compiler.whnf_cache = metas, first_meta, cache
        compiler.freeze_checks, compiler.freeze_check_bytes = freezes, freeze_bytes


def _truth(compiler: _Elaborator, condition: _Term, environment: dict[str, _Binding]) -> bool | None:
    with _probe(compiler):
        yes = compiler._prove_bool_precondition(condition, environment)
        no = compiler._prove_bool_precondition(compiler._negate_bool_term(condition), environment)
        if yes != no:
            return yes
    return None


def branch(compiler: _Elaborator, node: Node, condition: _Term, environment: dict[str, _Binding]) -> None:
    if compiler.in_executable_function:
        truth = _truth(compiler, condition, environment)
        message = None if truth is None else f"conditional is always {'true' if truth else 'false'} on this path"
        observe(compiler, "HOLDFAST125", node, message)


def short_circuit(
    compiler: _Elaborator, node: Node, operator: str, left: _Term, environment: dict[str, _Binding],
) -> None:
    if compiler.in_executable_function and operator in {"&&", "||"}:
        truth = _truth(compiler, left, environment)
        unreachable = truth is not None and truth == (operator == "||")
        message = "short-circuit right operand is never evaluated" if unreachable else None
        observe(compiler, "HOLDFAST125", node, message)


def while_entry(compiler: _Elaborator, node: Node, condition: _Term, environment: dict[str, _Binding]) -> None:
    if compiler.in_executable_function:
        truth = _truth(compiler, condition, environment)
        observe(compiler, "HOLDFAST125", node, "while loop has no iterations" if truth is False else None)


def checked_operation(
    compiler: _Elaborator, node: Node, environment: dict[str, _Binding],
    operands: tuple[tuple[_Term, _IntSpec | None], ...], target: _IntSpec, name: str,
) -> None:
    if not compiler.in_executable_function:
        return
    message = None
    with _probe(compiler):
        facts = compiler._expand_bool_facts([*compiler.active_facts, *compiler._fact_bool_terms((), environment)])
        bounds = [compiler._term_bounds(term, spec, facts)[:2] for term, spec in operands]
        if all(hi is not None and lo <= hi for lo, hi in bounds):
            low = sum(lo for lo, _ in bounds)
            high = sum(cast("int", hi) for _, hi in bounds)
            if target.min_val <= low <= high <= target.max_val:
                message = f"{name} always succeeds within {target.name} bounds"
    observe(compiler, "HOLDFAST127", node, message)


def range_loop(
    compiler: _Elaborator, node: Node, contracts: list[Node], environment: dict[str, _Binding],
    start: _Term, end: _Term, spec: _IntSpec | None,
) -> None:
    le = _constant("<=" if spec is None else f"int_le_{spec.name}")
    if compiler.in_executable_function:
        truth = _truth(compiler, _apps(le, end, start), environment)
        observe(compiler, "HOLDFAST125", node, "range loop has no iterations" if truth is True else None)
    bound = compiler._unwrap_group(compiler.node(compiler.node(node["range"])["end"]))
    index_name = compiler.name(node["name"])
    if bound["kind"] == "name":
        bound_name = compiler.name(bound["name"])
        if bound_name == index_name or bound_name in compiler.mutable_locals:
            return
    elif bound["kind"] != "nat":
        return
    for clause in contracts:
        value = compiler._unwrap_group(compiler.node(clause["value"]))
        if value["kind"] != "binary":
            continue
        operator = compiler.operator(value["operator"])
        left = compiler._unwrap_group(compiler.node(value["left"]))
        right = compiler._unwrap_group(compiler.node(value["right"]))
        if clause["role"] == "decreases" and operator == "-":
            index, limit = right, left
        elif clause["role"] == "invariant" and operator in {"<=", ">="}:
            index, limit = (left, right) if operator == "<=" else (right, left)
        else:
            continue
        if index["kind"] != "name" or compiler.name(index["name"]) != index_name or limit["kind"] != bound["kind"]:
            continue
        if bound["kind"] == "name":
            same = compiler.name(limit["name"]) == compiler.name(bound["name"])
        else:
            same = compiler.protocol.source[slice(*cast("list[int]", limit["span"]))] == (
                compiler.protocol.source[slice(*cast("list[int]", bound["span"]))]
            )
        if not same:
            continue
        ordered = _truth(compiler, _apps(le, start, end), environment)
        if clause["role"] == "decreases":
            message = "range loop already supplies this decreasing distance"
        else:
            message = "range loop already supplies this index bound"
        observe(compiler, "HOLDFAST131", clause, message if ordered is True else None)


def stable_loop_fact(compiler: _Elaborator, node: Node, fact: _Term, inherited: list[_Term]) -> None:
    value = compiler.node(node["value"])
    if any(item["kind"] == "name" and compiler.name(item["name"]) in compiler.mutable_locals
           for item in nodes(cast("Json", cast("object", value)))):
        return
    observe(compiler, "HOLDFAST131", value,
            "loop invariant repeats an available enclosing fact" if fact in inherited else None)


def ghost_parameters(
    compiler: _Elaborator, declaration: Node, binders: list[Node], variables: list[_Term], dependencies: set[int],
) -> None:
    uses = {compiler.name(item["name"]) for item in nodes(cast("Json", cast("object", declaration)))
            if item["kind"] in {"name", "type_ref"}}
    for binder, variable in zip(binders, variables, strict=True):
        ghost = binder.get("mode") == "ghost" or variable.value in compiler.ghost_parameters
        if ghost and binder["name"] is not None and cast("int", variable.value) not in dependencies:
            name = compiler.name(binder["name"])
            if name not in uses:
                report(compiler, "HOLDFAST132", cast("Node", binder["name"]), f"ghost parameter '{name}' is unused")


def forwards_case(
    compiler: _Elaborator, node: Node, value: _Term, pattern: _Term, arm_environment: dict[str, _Binding],
    ctor: str, fields: tuple[str, ...],
) -> bool:
    expr = compiler._unwrap_group(node)
    callee = compiler.node(expr["callee"]) if expr["kind"] == "call" else expr
    if callee["kind"] == "generic_application":
        callee = compiler._unwrap_group(compiler.node(callee["value"]))
    if callee["kind"] != "name" or compiler.name(callee["name"]) != ctor or ctor in arm_environment:
        return False
    args = compiler.nodes(expr["arguments"]) if expr["kind"] == "call" else []
    if len(args) != len(fields):
        return False
    for arg, field in zip(args, fields, strict=True):
        argument = compiler._unwrap_group(compiler.node(arg["value"]))
        if arg["label"] is not None or argument["kind"] != "name" or compiler.name(argument["name"]) != field:
            return False
    with _probe(compiler):
        return compiler.convertible(value, pattern)
    return False
