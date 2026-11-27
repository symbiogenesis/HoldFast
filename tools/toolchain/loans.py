# SPDX-License-Identifier: Apache-2.0
"""Infer loan ends and report conflicts and obligations over supplied flow facts.

See the [loan diagnostic contract](../../docs/language/loan-analysis.md) for
the graph inputs, abstract interpretation, and limits of the result.
"""

import re
from collections import Counter, deque
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from typing import Literal, cast

from toolchain import regions

type Mode = Literal["shared", "exclusive", "shared_mut"]
type AccessKind = Literal["read", "write", "move"]
type Stability = Literal["stable", "unstable"]
type Overlap = Literal["yes", "no", "unknown"]

_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")


def base_loan_name(name: str) -> str:
    """Strip any loop-step ``#suffix`` from a canonical loan identity."""
    return name.partition("#")[0]


class AnalysisRefusalError(ValueError):
    """Malformed or incompletely explored input; no partial report is returned."""


@dataclass(frozen=True)
class Place:
    owner: str
    fields: tuple[str, ...] = ()


@dataclass(frozen=True)
class Owner:
    name: str
    borrowed: bool = False
    # A projection prefix is a declared field; distinct siblings may be split.
    fields: tuple[tuple[str, ...], ...] = ()
    invariants: tuple[str, ...] = ()
    origin: str | None = None
    mode: Mode | None = None


@dataclass(frozen=True)
class Loan:
    name: str
    parent: str
    place: Place
    mode: Mode = "shared"
    scoped: bool = False
    invariant: str | None = None
    origin: str | None = None


@dataclass(frozen=True)
class Borrow:
    loan: Loan


@dataclass(frozen=True)
class Reserve:
    """Reserve an exclusive receiver without making its loan available."""

    loan: Loan


@dataclass(frozen=True)
class Activate:
    """Grant the reserved receiver while the call's arguments remain live."""

    name: str
    captures: tuple[str, ...] = ()
    # Results of branch expressions may carry different handles on each path.
    possible_captures: tuple[str, ...] = ()


@dataclass(frozen=True)
class Access:
    place: Place
    kind: AccessKind = "read"
    via: str | None = None
    stability: Stability = "stable"


@dataclass(frozen=True)
class Bind:
    """A wrapper/environment retaining its inputs' complete loan captures."""

    name: str
    captures: tuple[str, ...]


@dataclass(frozen=True)
class Use:
    """Read through retained loans, or read an owner root; not just a name mention.

    Binding, moving and returning descriptors retain their demands without this
    implicit read. This distinction makes suspended-parent diagnostics explicit.
    """

    name: str


@dataclass(frozen=True)
class Drop:
    """End a handle's availability; this never disposes a protocol resource."""

    name: str


@dataclass(frozen=True)
class Move:
    source: str
    target: str


@dataclass(frozen=True)
class Return:
    outcome: str = "return"
    captures: tuple[str, ...] = ()
    origin: str | None = None


@dataclass(frozen=True)
class Checkpoint:
    kind: str = "await"


@dataclass(frozen=True)
class OpenInvariant:
    name: str
    clauses: tuple[str, ...] = ()


@dataclass(frozen=True)
class CloseInvariant:
    name: str
    clauses: tuple[str, ...] = ()


@dataclass(frozen=True)
class AssumeDisjoint:
    """Assume two places are spatially disjoint until an index symbol is invalidated."""

    left: Place
    right: Place


@dataclass(frozen=True)
class AssumeIndexNe:
    """Assume two symbolic indices are distinct until either symbol is invalidated."""

    left: str
    right: str


@dataclass(frozen=True)
class InvalidateSymbol:
    """Invalidate symbolic-index disjointness facts and symbol-dependent refinements."""

    symbol: str


@dataclass(frozen=True)
class AssumeRefinement:
    """Record a current-content refinement fact tied to a place."""

    name: str
    place: Place


@dataclass(frozen=True)
class UseRefinement:
    """Require that a current-content refinement remains valid at this point."""

    name: str


@dataclass(frozen=True)
class DropRefinement:
    """Discard a current-content refinement without requiring it to remain valid."""

    name: str


@dataclass(frozen=True)
class AssumeTagPreserved:
    """Assume a tagged union's discriminant/tag is preserved for ``place``."""

    place: Place


@dataclass(frozen=True)
class AssumeNoRealloc:
    """Assume a container has spare capacity and will not reallocate on append/push."""

    place: Place


@dataclass(frozen=True)
class Nop:
    pass


type Event = (Borrow | Reserve | Activate | Access | Bind | Use | Drop | Move | Return | Checkpoint
              | OpenInvariant | CloseInvariant | AssumeDisjoint | AssumeIndexNe | InvalidateSymbol
              | AssumeRefinement | UseRefinement | DropRefinement
              | AssumeTagPreserved | AssumeNoRealloc | Nop)


@dataclass(frozen=True)
class Node:
    name: str
    event: Event = Nop()
    successors: tuple[str, ...] = ()


@dataclass(frozen=True)
class Graph:
    entry: str
    nodes: tuple[Node, ...]
    return_origin: str | None = None
    declared_outlives: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True)
class Limits:
    owners: int = 64
    nodes: int = 256
    paths: int = 128
    captures: int = 2048
    work: int = 100_000


@dataclass(frozen=True)
class Issue:
    node: str
    kind: str
    resources: tuple[str, ...] = ()
    origin_node: str | None = None
    conflict_node: str | None = None
    live_use_node: str | None = None
    proposed_end_node: str | None = None


@dataclass(frozen=True)
class Obligation:
    node: str
    kind: str
    resources: tuple[str, ...] = ()
    status: Literal["unresolved"] = field(default="unresolved", init=False)


@dataclass(frozen=True)
class Restoration:
    node: str
    loan: str
    parent: str
    place: Place
    # This is a proposed proof step, with no concrete memory predicate supplied.
    status: Literal["unresolved"] = field(default="unresolved", init=False)


@dataclass(frozen=True)
class PathReport:
    nodes: tuple[str, ...]
    outcome: str
    issues: tuple[Issue, ...]
    obligations: tuple[Obligation, ...]
    restorations: tuple[Restoration, ...]
    returned_loans: tuple[str, ...]
    retained_loans: tuple[str, ...]
    suspended: tuple[Place, ...]
    moved_owners: tuple[str, ...]
    active_invariants: tuple[tuple[str, str], ...] = ()
    open_invariants: tuple[tuple[str, str], ...] = ()
    moved_places: tuple[Place, ...] = ()


@dataclass(frozen=True)
class Report:
    paths: tuple[PathReport, ...]
    status: Literal["diagnostic-only"] = field(default="diagnostic-only", init=False)


@dataclass(frozen=True)
class LoweredFunction:
    name: str
    owners: tuple[Owner, ...]
    graph: Graph
    node_sites: Mapping[str, dict[str, object]] = field(default_factory=dict)


class _Budget:
    def __init__(self, limit: int) -> None:
        self.remaining = limit

    def spend(self, amount: int = 1) -> None:
        self.remaining -= amount
        if self.remaining < 0:
            raise AnalysisRefusalError("analysis work budget exhausted; no complete report")


def _name(value: object) -> None:
    if not isinstance(value, str) or len(value) > 128 or not _NAME.fullmatch(value):
        raise AnalysisRefusalError("identities must be nonempty normalized identifiers")


def _symbol_name(value: object) -> str:
    if not isinstance(value, str) or len(value) > 129:
        raise AnalysisRefusalError("identities must be nonempty normalized identifiers")
    if value.startswith("@"):
        _name(value[1:])
        return value
    _name(value)
    return f"@{value}"


def _origin_name(value: object) -> str:
    if not isinstance(value, str) or not value or len(value) > 129:
        raise AnalysisRefusalError("region origins must be nonempty normalized identifiers")
    ident = value.removeprefix("'")
    _name(ident)
    return value


def _is_symbolic(part: object) -> bool:
    return isinstance(part, str) and part.startswith("@")


def _projection(value: tuple[str, ...]) -> None:
    if not isinstance(value, tuple) or len(value) > 32:
        raise AnalysisRefusalError("projection must be an immutable path of at most 32 fields")
    for part in value:
        if part == "*":
            continue
        if _is_symbolic(part):
            _name(part[1:])
        else:
            _name(part)


def _validate_place(
    place: object, owner_map: Mapping[str, Owner], *, allow_wildcard: bool = True
) -> Place:
    if not isinstance(place, Place):
        raise AnalysisRefusalError("footprint must be an immutable Place record")
    _name(place.owner)
    _projection(place.fields)
    if place.owner not in owner_map:
        raise AnalysisRefusalError("missing place owner")
    if not allow_wildcard and "*" in place.fields:
        raise AnalysisRefusalError("disjointness assumption cannot contain unknown '*' projections")
    return place


def _references(event: Event) -> tuple[str, ...]:
    match event:
        case Borrow(loan) | Reserve(loan):
            return (loan.parent,)
        case Activate(name, captures, possible_captures):
            return (name, *captures, *possible_captures)
        case Access(via=via) if via is not None:
            return (via,)
        case Bind(captures=names) | Return(captures=names):
            return names
        case Use(name) | Drop(name):
            return (name,)
        case Move(source, _):
            return (source,)
        case _:
            return ()


def _binder(event: Event) -> str | None:
    match event:
        case Borrow(loan) | Reserve(loan):
            return loan.name
        case Bind(name, _) | Move(_, name):
            return name
        case _:
            return None


def _invariant_conjuncts(
    owners: Mapping[str, Owner], name: str, clauses: tuple[str, ...]
) -> tuple[tuple[tuple[str, str], ...], bool]:
    if clauses:
        return tuple((name, clause) for clause in clauses), True
    owner = owners.get(name)
    if owner is not None and owner.invariants:
        return tuple((name, clause) for clause in owner.invariants), True
    return ((name, name),), False


def _validate(
    owners: tuple[Owner, ...], graph: Graph, limits: Limits, budget: _Budget
) -> tuple[dict[str, Node], dict[str, frozenset[str]]]:
    for bound in (limits.owners, limits.nodes, limits.paths, limits.captures, limits.work):
        if type(bound) is not int or bound < 1:
            raise AnalysisRefusalError("analysis limits must be positive integers")
    if not isinstance(graph, Graph):
        raise AnalysisRefusalError("graph must be an immutable Graph record")
    if not isinstance(owners, tuple) or not isinstance(graph.nodes, tuple):
        raise AnalysisRefusalError("owners and nodes must be immutable tuples")
    if not owners or len(owners) > limits.owners or not graph.nodes or len(graph.nodes) > limits.nodes:
        raise AnalysisRefusalError("owner or node budget exhausted, or empty input")
    owner_map: dict[str, Owner] = {}
    capture_count = 0
    for owner in owners:
        budget.spend()
        if not isinstance(owner, Owner):
            raise AnalysisRefusalError("owner must be an immutable Owner record")
        _name(owner.name)
        if owner.name in owner_map or type(owner.borrowed) is not bool:
            raise AnalysisRefusalError("duplicate owner identity or malformed owner mode")
        if not isinstance(owner.fields, tuple) or len(owner.fields) > limits.captures:
            raise AnalysisRefusalError("field declarations must be immutable")
        for path in owner.fields:
            _projection(path)
            budget.spend(len(path) + 1)
            if not path or "*" in path:
                raise AnalysisRefusalError("declared field projections cannot be empty or unknown")
        if len(set(owner.fields)) != len(owner.fields):
            raise AnalysisRefusalError("duplicate field declaration")
        if not isinstance(owner.invariants, tuple) or len(owner.invariants) > limits.captures:
            raise AnalysisRefusalError("invariant declarations must be immutable")
        for clause in owner.invariants:
            _name(clause)
            budget.spend()
        if len(set(owner.invariants)) != len(owner.invariants):
            raise AnalysisRefusalError("duplicate invariant declaration")
        if owner.origin is not None:
            _origin_name(owner.origin)
        if owner.mode is not None and owner.mode not in ("shared", "exclusive", "shared_mut"):
            raise AnalysisRefusalError("malformed owner mode")
        owner_map[owner.name] = owner
    if graph.return_origin is not None:
        _origin_name(graph.return_origin)
    for sup, sub in graph.declared_outlives:
        _origin_name(sup)
        _origin_name(sub)

    nodes: dict[str, Node] = {}
    known = set(owner_map)
    known_refinements: set[str] = set()
    reservations: set[str] = set()
    invariants: set[str] = set()
    opened_conjuncts: set[tuple[str, str]] = set()
    for owner in owners:
        for clause in owner.invariants:
            invariants.add(clause)
            invariants.add(owner.name)
    for node in graph.nodes:
        budget.spend()
        if not isinstance(node, Node):
            raise AnalysisRefusalError("node must be an immutable Node record")
        _name(node.name)
        if node.name in nodes:
            raise AnalysisRefusalError("duplicate graph identity")
        nodes[node.name] = node
        if not isinstance(node.event, (Borrow, Reserve, Activate, Access, Bind, Use, Drop, Move, Return,
                                       Checkpoint, OpenInvariant, CloseInvariant,
                                       AssumeDisjoint, AssumeIndexNe, InvalidateSymbol,
                                       AssumeRefinement, UseRefinement, DropRefinement,
                                       AssumeTagPreserved, AssumeNoRealloc, Nop)):
            raise AnalysisRefusalError("unknown event")
        if isinstance(node.event, (Borrow, Reserve)) and not isinstance(node.event.loan, Loan):
            raise AnalysisRefusalError("borrow must contain an immutable Loan record")
        if isinstance(node.event, Activate) and (
            not isinstance(node.event.captures, tuple) or not isinstance(node.event.possible_captures, tuple)
        ):
            raise AnalysisRefusalError("activation captures must be immutable")
        binder = _binder(node.event)
        if isinstance(node.event, (Borrow, Reserve, Bind, Move)):
            _name(binder)
            if binder is not None:
                known.add(binder)
        if isinstance(node.event, AssumeRefinement):
            _name(node.event.name)
            known_refinements.add(node.event.name)
        if isinstance(node.event, Reserve):
            if node.event.loan.name in reservations:
                raise AnalysisRefusalError("duplicate receiver reservation identity")
            reservations.add(node.event.loan.name)
        if isinstance(node.event, (OpenInvariant, CloseInvariant)):
            _name(node.event.name)
            if not isinstance(node.event.clauses, tuple) or len(node.event.clauses) > limits.captures:
                raise AnalysisRefusalError("invariant clauses must be an immutable tuple")
            for clause in node.event.clauses:
                _name(clause)
                budget.spend()
            if len(set(node.event.clauses)) != len(node.event.clauses):
                raise AnalysisRefusalError("duplicate invariant clause")
            target_owner = owner_map.get(node.event.name)
            if target_owner is not None and target_owner.invariants:
                for clause in node.event.clauses:
                    if clause not in target_owner.invariants:
                        raise AnalysisRefusalError("missing invariant reference")
            if isinstance(node.event, OpenInvariant):
                conjuncts, _ = _invariant_conjuncts(owner_map, node.event.name, node.event.clauses)
                opened_conjuncts.update(conjuncts)
                invariants.add(node.event.name)
                for owner_name, clause in conjuncts:
                    invariants.add(owner_name)
                    invariants.add(clause)

    _name(graph.entry)
    if graph.entry not in nodes:
        raise AnalysisRefusalError("missing entry node")
    for node in graph.nodes:
        budget.spend()
        if not isinstance(node.successors, tuple) or len(node.successors) > limits.nodes:
            raise AnalysisRefusalError("malformed or duplicate edges")
        for successor in node.successors:
            budget.spend()
            _name(successor)
            if successor not in nodes:
                raise AnalysisRefusalError("missing successor")
        if len(set(node.successors)) != len(node.successors):
            raise AnalysisRefusalError("malformed or duplicate edges")
        if isinstance(node.event, Return) and node.successors:
            raise AnalysisRefusalError("return node has successors")
        references = _references(node.event)
        if not isinstance(references, tuple):
            raise AnalysisRefusalError("capture references must be immutable")
        capture_count += len(references)
        if capture_count > limits.captures:
            raise AnalysisRefusalError("capture/reference budget exhausted")
        for reference in references:
            budget.spend()
            _name(reference)
            if reference not in known:
                raise AnalysisRefusalError(f"missing resource reference: {reference}")
        event = node.event
        if isinstance(event, (Borrow, Reserve, Access)):
            place = event.place if isinstance(event, Access) else event.loan.place
            _validate_place(place, owner_map)
        if isinstance(event, (AssumeTagPreserved, AssumeNoRealloc)):
            _validate_place(event.place, owner_map)
            budget.spend(len(event.place.fields) + 1)
        if isinstance(event, AssumeDisjoint):
            _validate_place(event.left, owner_map, allow_wildcard=False)
            _validate_place(event.right, owner_map, allow_wildcard=False)
            budget.spend(len(event.left.fields) + len(event.right.fields) + 1)
        if isinstance(event, AssumeIndexNe):
            _symbol_name(event.left)
            _symbol_name(event.right)
            budget.spend()
        if isinstance(event, InvalidateSymbol):
            _symbol_name(event.symbol)
            budget.spend()
        if isinstance(event, AssumeRefinement):
            _validate_place(event.place, owner_map)
            budget.spend(len(event.place.fields) + 1)
        if isinstance(event, (UseRefinement, DropRefinement)):
            _name(event.name)
            if event.name not in known_refinements:
                raise AnalysisRefusalError(f"missing refinement reference: {event.name}")
            budget.spend()
        if isinstance(event, (Borrow, Reserve)):
            if event.loan.mode not in ("shared", "exclusive", "shared_mut") or type(event.loan.scoped) is not bool:
                raise AnalysisRefusalError("malformed loan mode")
            if event.loan.origin is not None:
                _origin_name(event.loan.origin)
            if isinstance(event, Reserve) and event.loan.mode != "exclusive":
                raise AnalysisRefusalError("receiver reservation requires an exclusive loan")
            if event.loan.invariant is not None:
                _name(event.loan.invariant)
                if event.loan.invariant not in invariants:
                    raise AnalysisRefusalError("missing invariant reference")
        if isinstance(event, Activate) and event.name not in reservations:
            raise AnalysisRefusalError("missing receiver reservation reference")
        if isinstance(event, Access):
            if event.kind not in ("read", "write", "move"):
                raise AnalysisRefusalError("unknown access kind")
            if event.stability not in ("stable", "unstable"):
                raise AnalysisRefusalError("unknown access stability")
        if isinstance(event, CloseInvariant):
            conjuncts, _ = _invariant_conjuncts(owner_map, event.name, event.clauses)
            if not all(pair in opened_conjuncts for pair in conjuncts):
                raise AnalysisRefusalError("missing invariant reference")
        if isinstance(event, (Return, Checkpoint)):
            label = event.outcome if isinstance(event, Return) else event.kind
            _name(label)
            if isinstance(event, Return) and event.origin is not None:
                _origin_name(event.origin)

    # Check forward reachability from entry and record reverse postorder for dominators.
    reached: set[str] = set()
    postorder: list[str] = []
    dfs_stack: list[tuple[str, bool]] = [(graph.entry, False)]
    while dfs_stack:
        current, expanded = dfs_stack.pop()
        if expanded:
            postorder.append(current)
            continue
        if current in reached:
            continue
        budget.spend()
        reached.add(current)
        dfs_stack.append((current, True))
        dfs_stack.extend(
            (successor, False)
            for successor in reversed(nodes[current].successors)
            if successor not in reached
        )
    if reached != set(nodes):
        raise AnalysisRefusalError("unreachable graph nodes")
    rpo_order = [name for name in reversed(postorder) if name != graph.entry]

    # Reject self-edges and require a graph path from every node to a terminal.
    predecessors: dict[str, list[str]] = {name: [] for name in nodes}
    for node in graph.nodes:
        if node.name in node.successors:
            raise AnalysisRefusalError("cyclic control flow requires an invariant interpretation")
        for successor in node.successors:
            predecessors[successor].append(node.name)

    can_terminate = {name for name, node in nodes.items() if not node.successors}
    rev_stack = list(can_terminate)
    while rev_stack:
        budget.spend()
        current = rev_stack.pop()
        for pred in predecessors[current]:
            if pred not in can_terminate:
                can_terminate.add(pred)
                rev_stack.append(pred)
    if can_terminate != set(nodes):
        raise AnalysisRefusalError("cyclic control flow requires an invariant interpretation")

    # A successor that dominates its predecessor identifies a natural-loop header.
    all_names = frozenset(nodes)
    dominators: dict[str, frozenset[str]] = {
        name: frozenset({graph.entry}) if name == graph.entry else all_names
        for name in nodes
    }
    changed = True
    while changed:
        changed = False
        for node_name in rpo_order:
            budget.spend()
            preds = predecessors[node_name]
            if not preds:
                continue
            intersected = set(dominators[preds[0]])
            for pred in preds[1:]:
                intersected &= dominators[pred]
            intersected.add(node_name)
            updated = frozenset(intersected)
            if updated != dominators[node_name]:
                dominators[node_name] = updated
                changed = True

    for node in graph.nodes:
        for successor in node.successors:
            # Require a branch at each loop header.
            if successor in dominators[node.name] and len(nodes[successor].successors) < 2:
                raise AnalysisRefusalError(
                    "cyclic control flow requires an invariant interpretation"
                )

    # Check that removing natural-loop back-edges leaves a DAG (no irreducible cycle).
    incoming = dict.fromkeys(nodes, 0)
    for node in graph.nodes:
        for successor in node.successors:
            if successor not in dominators[node.name]:
                incoming[successor] += 1
    ready = [name for name, count in incoming.items() if count == 0]
    visited = 0
    while ready:
        budget.spend()
        name = ready.pop()
        visited += 1
        for successor in nodes[name].successors:
            if successor not in dominators[name]:
                incoming[successor] -= 1
                if incoming[successor] == 0:
                    ready.append(successor)
    if visited != len(nodes):
        raise AnalysisRefusalError("cyclic control flow requires an invariant interpretation")

    _capture_cycles(graph.nodes, budget)
    return nodes, dominators


def _capture_cycles(nodes: tuple[Node, ...], budget: _Budget) -> None:
    """Refuse cyclic supplied retention facts, without conflating shadowed names."""
    counts: dict[str, int] = {}
    for node in nodes:
        budget.spend()
        name = _binder(node.event)
        if name is not None:
            counts[name] = counts.get(name, 0) + 1
    dependencies: dict[str, set[str]] = {}
    for node in nodes:
        budget.spend()
        name = _binder(node.event)
        if name is not None and counts[name] == 1:
            references = _references(node.event)
            budget.spend(len(references))
            dependencies[name] = set(references)
    pending = set(dependencies)
    while pending:
        ready: set[str] = set()
        for name in pending:
            budget.spend(len(dependencies[name]) + 1)
            if not dependencies[name] & pending:
                ready.add(name)
        if not ready:
            raise AnalysisRefusalError("cyclic loan/capture dependencies")
        pending.difference_update(ready)


def _within(child: Place, parent: Place) -> bool:
    return child.owner == parent.owner and child.fields[:len(parent.fields)] == parent.fields


def _canonical_place_pair(left: Place, right: Place) -> tuple[Place, Place]:
    if (left.owner, left.fields) <= (right.owner, right.fields):
        return left, right
    return right, left


def _canonical_symbol_pair(left: str, right: str) -> tuple[str, str]:
    return (left, right) if left <= right else (right, left)


def _replace_symbol_in_place(place: Place, symbol: str) -> Place:
    if symbol not in place.fields:
        return place
    return Place(place.owner, tuple("*" if part == symbol else part for part in place.fields))


def _containment(
    child: Place,
    parent: Place,
    disjoint_places: frozenset[tuple[Place, Place]] | set[tuple[Place, Place]] = frozenset(),
    disjoint_symbols: frozenset[tuple[str, str]] | set[tuple[str, str]] = frozenset(),
) -> Overlap:
    """A repeated unknown index spelling establishes no index identity."""
    if child.owner != parent.owner:
        return "no"
    for left_p, right_p in disjoint_places:
        if (_within(child, left_p) and _within(parent, right_p)) or (
            _within(child, right_p) and _within(parent, left_p)
        ):
            return "no"
    unknown = False
    for child_field, parent_field in zip(child.fields, parent.fields, strict=False):
        if child_field == parent_field:
            if child_field == "*":
                unknown = True
            continue
        if child_field == "*" or parent_field == "*":
            unknown = True
            continue
        if _is_symbolic(child_field) and _is_symbolic(parent_field):
            if _canonical_symbol_pair(child_field, parent_field) in disjoint_symbols:
                return "no"
            unknown = True
            continue
        if _is_symbolic(child_field) or _is_symbolic(parent_field):
            unknown = True
            continue
        return "no"
    if len(child.fields) < len(parent.fields):
        return "unknown" if unknown else "no"
    return "unknown" if unknown else "yes"


def _overlap(
    left: Place,
    right: Place,
    fields_by_owner: dict[str, frozenset[tuple[str, ...]]],
    disjoint_places: frozenset[tuple[Place, Place]] | set[tuple[Place, Place]] = frozenset(),
    disjoint_symbols: frozenset[tuple[str, str]] | set[tuple[str, str]] = frozenset(),
) -> Overlap:
    if left.owner != right.owner:
        return "no"
    for left_p, right_p in disjoint_places:
        if (_within(left, left_p) and _within(right, right_p)) or (
            _within(left, right_p) and _within(right, left_p)
        ):
            return "no"
    if _within(left, right):
        return "unknown" if "*" in right.fields else "yes"
    if _within(right, left):
        return "unknown" if "*" in left.fields else "yes"
    saw_unknown = False
    for index, (first, second) in enumerate(zip(left.fields, right.fields, strict=False)):
        if first == second:
            if first == "*":
                saw_unknown = True
            continue
        if first == "*" or second == "*":
            saw_unknown = True
            continue
        if _is_symbolic(first) and _is_symbolic(second):
            if _canonical_symbol_pair(first, second) in disjoint_symbols:
                return "no"
            left_prefix = Place(left.owner, left.fields[:index + 1])
            right_prefix = Place(right.owner, right.fields[:index + 1])
            if _canonical_place_pair(left_prefix, right_prefix) in disjoint_places:
                return "no"
            saw_unknown = True
            continue
        if _is_symbolic(first) or _is_symbolic(second):
            left_prefix = Place(left.owner, left.fields[:index + 1])
            right_prefix = Place(right.owner, right.fields[:index + 1])
            if _canonical_place_pair(left_prefix, right_prefix) in disjoint_places:
                return "no"
            saw_unknown = True
            continue
        if not saw_unknown:
            fields = fields_by_owner[left.owner]
            if left.fields[:index + 1] in fields and right.fields[:index + 1] in fields:
                return "no"
        saw_unknown = True
    return "unknown"


@dataclass(frozen=True)
class _Value:
    captures: frozenset[str]
    # Only a direct handle (or its move) grants a route for an access/reborrow.
    handle: str | None = None


def _transfer_demand_backward(node: Node, demanded_after: frozenset[str]) -> frozenset[str]:
    before = set(demanded_after)
    match node.event:
        case Drop(name):
            before.discard(name)
        case Move(source, target):
            before.discard(target)
            before.add(source)
        case Bind(name, captures):
            before.discard(name)
            before.update(captures)
        case Borrow(loan) | Reserve(loan):
            before.discard(loan.name)
            before.add(loan.parent)
        case Activate(name, captures, possible_captures):
            before.add(name)
            before.update(captures)
            before.update(possible_captures)
        case Use(name):
            before.add(name)
        case Access(via=via) if via is not None:
            before.add(via)
        case Return(captures=names):
            before.update(names)
        case _:
            pass
    return frozenset(before)


def _compute_cfg_liveness(
    graph: Graph, nodes: dict[str, Node], budget: _Budget
) -> tuple[dict[str, frozenset[str]], dict[str, frozenset[str]], dict[str, frozenset[str]]]:
    demanded_before: dict[str, frozenset[str]] = dict.fromkeys(nodes, frozenset())
    demanded_after: dict[str, frozenset[str]] = dict.fromkeys(nodes, frozenset())
    local_names = {}
    for name, node in nodes.items():
        references = frozenset(_references(node.event))
        binder = _binder(node.event)
        local_names[name] = references if binder is None else references | {binder}
    reachable_names = local_names.copy()
    ordered = tuple(reversed(graph.nodes))
    changed = True
    while changed:
        changed = False
        for node in ordered:
            budget.spend()
            after = frozenset().union(*(demanded_before[succ] for succ in node.successors))
            before = _transfer_demand_backward(node, after)
            names = local_names[node.name].union(
                *(reachable_names[succ] for succ in node.successors)
            )
            if (after != demanded_after[node.name]
                    or before != demanded_before[node.name]
                    or names != reachable_names[node.name]):
                demanded_after[node.name] = after
                demanded_before[node.name] = before
                reachable_names[node.name] = names
                changed = True
    return demanded_before, demanded_after, reachable_names


def _compute_cfg_demand_sites(
    graph: Graph, nodes: dict[str, Node], budget: _Budget
) -> tuple[
    dict[str, frozenset[str]],
    dict[str, frozenset[str]],
    dict[str, dict[str, str]],
    dict[str, dict[str, str]],
]:
    ordered = tuple(reversed(graph.nodes))
    future_nodes: dict[str, frozenset[str]] = {name: frozenset({name}) for name in nodes}
    must_before: dict[str, frozenset[str]] = dict.fromkeys(nodes, frozenset())
    direct_uses: dict[str, frozenset[str]] = {}
    for name, node in nodes.items():
        match node.event:
            case Use(rname) | Access(via=rname) if rname is not None:
                direct_uses[name] = frozenset({rname})
            case Return(captures=names):
                direct_uses[name] = frozenset(names)
            case Activate(rname, captures, possible_captures):
                direct_uses[name] = frozenset({rname, *captures, *possible_captures})
            case _:
                direct_uses[name] = frozenset()

    first_demand: dict[str, dict[str, str]] = {name: {} for name in nodes}
    last_demand: dict[str, dict[str, str]] = {name: {} for name in nodes}
    changed = True
    while changed:
        changed = False
        for node in ordered:
            budget.spend()
            fut = frozenset({node.name}).union(*(future_nodes[succ] for succ in node.successors))
            if fut != future_nodes[node.name]:
                future_nodes[node.name] = fut
                changed = True
            if node.successors:
                after = frozenset.intersection(
                    *(must_before[succ] for succ in node.successors)
                )
            else:
                after = frozenset()
            before = _transfer_demand_backward(node, after)
            if before != must_before[node.name]:
                must_before[node.name] = before
                changed = True
            new_first: dict[str, str] = {}
            new_last: dict[str, str] = {}
            for succ in node.successors:
                for res, target_node in first_demand[succ].items():
                    new_first.setdefault(res, target_node)
                new_last.update(last_demand[succ])
            for res in direct_uses[node.name]:
                new_first[res] = node.name
                new_last.setdefault(res, node.name)
            if new_first != first_demand[node.name] or new_last != last_demand[node.name]:
                first_demand[node.name] = new_first
                last_demand[node.name] = new_last
                changed = True
    return must_before, future_nodes, first_demand, last_demand


def _compute_cfg_relevance(
    graph: Graph, nodes: dict[str, Node], budget: _Budget
) -> tuple[
    dict[str, frozenset[str]],
    dict[str, frozenset[str]],
    dict[str, frozenset[str]],
]:
    local_owners: dict[str, set[str]] = {name: set() for name in nodes}
    local_symbols: dict[str, set[str]] = {name: set() for name in nodes}
    local_refinements: dict[str, set[str]] = {name: set() for name in nodes}
    for name, node in nodes.items():
        budget.spend()
        places: list[Place] = []
        match node.event:
            case Borrow(loan) | Reserve(loan):
                places.append(loan.place)
            case Access(place=place):
                places.append(place)
            case AssumeDisjoint(left, right):
                places.extend((left, right))
            case AssumeTagPreserved(place) | AssumeNoRealloc(place):
                places.append(place)
            case AssumeIndexNe(left, right):
                local_symbols[name].update((_symbol_name(left), _symbol_name(right)))
            case InvalidateSymbol(symbol):
                local_symbols[name].add(_symbol_name(symbol))
            case AssumeRefinement(rname, place):
                local_refinements[name].add(rname)
                places.append(place)
            case UseRefinement(rname) | DropRefinement(rname):
                local_refinements[name].add(rname)
            case _:
                pass
        for place in places:
            local_owners[name].add(place.owner)
            for part in place.fields:
                if _is_symbolic(part):
                    local_symbols[name].add(part)
    reachable_owners = {name: frozenset(vals) for name, vals in local_owners.items()}
    reachable_symbols = {name: frozenset(vals) for name, vals in local_symbols.items()}
    reachable_refinements = {name: frozenset(vals) for name, vals in local_refinements.items()}
    ordered = tuple(reversed(graph.nodes))
    changed = True
    while changed:
        changed = False
        for node in ordered:
            budget.spend()
            owners_u = frozenset(local_owners[node.name]).union(
                *(reachable_owners[succ] for succ in node.successors)
            )
            symbols_u = frozenset(local_symbols[node.name]).union(
                *(reachable_symbols[succ] for succ in node.successors)
            )
            refs_u = frozenset(local_refinements[node.name]).union(
                *(reachable_refinements[succ] for succ in node.successors)
            )
            if (
                owners_u != reachable_owners[node.name]
                or symbols_u != reachable_symbols[node.name]
                or refs_u != reachable_refinements[node.name]
            ):
                reachable_owners[node.name] = owners_u
                reachable_symbols[node.name] = symbols_u
                reachable_refinements[node.name] = refs_u
                changed = True
    return reachable_owners, reachable_symbols, reachable_refinements


class _State:
    def __init__(
        self,
        owners: dict[str, Owner],
        fields: dict[str, frozenset[tuple[str, ...]]],
        budget: _Budget,
        entry_name: str,
        *,
        graph_return_origin: str | None = None,
        region_solution: regions.RegionSolution | None = None,
        first_demand: dict[str, dict[str, str]] | None = None,
        last_demand: dict[str, dict[str, str]] | None = None,
    ) -> None:
        self.owners = owners
        self.fields = fields
        self.budget = budget
        self.graph_return_origin = graph_return_origin
        self.region_solution = region_solution
        self.first_demand = first_demand or {}
        self.last_demand = last_demand or {}
        self.nodes: tuple[str, ...] = ()
        self.outcome = "fallthrough"
        self.issues: list[Issue] = []
        self.issues_emitted = 0
        self.obligations: list[Obligation] = [
            Obligation(entry_name, "supplied-interpretation", tuple(owners)),
            Obligation(entry_name, "supplied-separation", tuple(owners)),
        ]
        self.restorations: list[Restoration] = []
        self.values: dict[str, _Value] = {}
        self.loans: dict[str, Loan] = {}
        self.parents: dict[str, str] = {}
        self.loan_origin_node: dict[str, str] = {}
        self.last_demand_node: dict[str, str] = {}
        self.seen_binders: dict[str, str] = {}
        self.active: set[str] = set()
        self.reserved: set[str] = set()
        self.opened: set[tuple[str, str]] = set()
        self.active_invariants: set[tuple[str, str]] = {
            (owner.name, clause)
            for owner in owners.values()
            for clause in owner.invariants
        }
        self.explicit_invariants: dict[tuple[str, str], bool] = {
            (owner.name, clause): True
            for owner in owners.values()
            for clause in owner.invariants
        }
        self.returned: frozenset[str] = frozenset()
        self.moved: set[str] = set()
        self.moved_places: set[Place] = set()
        self.invalid: set[str] = set()
        self.disjoint_places: set[tuple[Place, Place]] = set()
        self.disjoint_symbols: set[tuple[str, str]] = set()
        self.tag_preserved: set[Place] = set()
        self.no_realloc: set[Place] = set()
        self.refinements: dict[str, Place] = {}
        self.refinement_origin_node: dict[str, str] = {}
        self.refinement_invalidated_node: dict[str, str] = {}
        self.stale_refinements: set[str] = set()
        self.unstable_invalidated: set[str] = set()
        self.frozen_places: dict[str, Place] = {}
        self.step_bases: dict[str, str] = {}

    def clone(self) -> _State:
        self.budget.spend()
        copy = _State.__new__(_State)
        copy.owners = self.owners
        copy.fields = self.fields
        copy.budget = self.budget
        copy.graph_return_origin = self.graph_return_origin
        copy.region_solution = self.region_solution
        copy.first_demand = self.first_demand
        copy.last_demand = self.last_demand
        copy.nodes = self.nodes
        copy.outcome = self.outcome
        copy.issues = list(self.issues)
        copy.issues_emitted = self.issues_emitted
        copy.obligations = list(self.obligations)
        copy.restorations = list(self.restorations)
        copy.values = dict(self.values)
        copy.loans = dict(self.loans)
        copy.parents = dict(self.parents)
        copy.loan_origin_node = dict(self.loan_origin_node)
        copy.last_demand_node = dict(self.last_demand_node)
        copy.seen_binders = dict(self.seen_binders)
        copy.active = set(self.active)
        copy.reserved = set(self.reserved)
        copy.opened = set(self.opened)
        copy.active_invariants = set(self.active_invariants)
        copy.explicit_invariants = dict(self.explicit_invariants)
        copy.returned = self.returned
        copy.moved = set(self.moved)
        copy.moved_places = set(self.moved_places)
        copy.invalid = set(self.invalid)
        copy.disjoint_places = set(self.disjoint_places)
        copy.disjoint_symbols = set(self.disjoint_symbols)
        copy.tag_preserved = set(self.tag_preserved)
        copy.no_realloc = set(self.no_realloc)
        copy.refinements = dict(self.refinements)
        copy.refinement_origin_node = dict(self.refinement_origin_node)
        copy.refinement_invalidated_node = dict(self.refinement_invalidated_node)
        copy.stale_refinements = set(self.stale_refinements)
        copy.unstable_invalidated = set(self.unstable_invalidated)
        copy.frozen_places = dict(self.frozen_places)
        copy.step_bases = dict(self.step_bases)
        return copy

    def _effective_place(self, loan_name: str) -> Place:
        return self.frozen_places.get(loan_name, self.loans[loan_name].place)

    def join_key(
        self,
        relevant_names: frozenset[str],
        history_names: set[str],
        relevant_owners: frozenset[str] | None = None,
        relevant_symbols: frozenset[str] | None = None,
        relevant_refinements: frozenset[str] | None = None,
        must_demanded: frozenset[str] | None = None,
        future_nodes: frozenset[str] | None = None,
    ) -> tuple[object, ...]:
        self.budget.spend(len(relevant_names) + len(self.active) + len(self.reserved))
        relevant_values = {name: self.values[name] for name in relevant_names if name in self.values}
        relevant_loans = self.ancestors(self.active | self.reserved | {
            loan for value in relevant_values.values() for loan in value.captures
        })
        must_demanded_loans: set[str] = set()
        if must_demanded is not None:
            for dname in must_demanded:
                if (val := self.values.get(dname)) is not None:
                    must_demanded_loans.update(val.captures)
                elif dname in self.reserved:
                    must_demanded_loans.add(dname)
            must_demanded_loans = set(self.ancestors(must_demanded_loans))
        relevant_binders = (relevant_names & history_names) | self.reserved
        live_places = [self._effective_place(name) for name in relevant_loans]
        for rname, rplace in self.refinements.items():
            if relevant_refinements is None or rname in relevant_refinements:
                live_places.append(rplace)
        active_owners = set(relevant_owners or ()) | {p.owner for p in live_places}
        active_symbols = set(relevant_symbols or ()) | {
            part for p in live_places for part in p.fields if _is_symbolic(part)
        }
        return (
            frozenset(relevant_values.items()),
            frozenset(
                (
                    name,
                    self.loans[name],
                    self.parents[name],
                    None if name in must_demanded_loans else self.last_demand_node.get(name),
                )
                for name in relevant_loans
            ),
            frozenset(
                (
                    name,
                    self.seen_binders[name]
                    if future_nodes is None or self.seen_binders[name] in future_nodes
                    else "__past__",
                )
                for name in relevant_binders
                if name in self.seen_binders
            ),
            frozenset(self.active),
            frozenset(self.reserved),
            frozenset(self.opened),
            frozenset(self.active_invariants),
            frozenset(self.explicit_invariants.items()),
            frozenset(self.moved),
            frozenset(mp for mp in self.moved_places if mp.owner in active_owners),
            frozenset(self.invalid & relevant_loans),
            frozenset(self.unstable_invalidated & relevant_loans),
            frozenset((name, self.frozen_places[name]) for name in relevant_loans if name in self.frozen_places),
            frozenset(
                pair for pair in self.disjoint_places
                if pair[0].owner in active_owners
                or pair[1].owner in active_owners
                or any(part in active_symbols for part in (*pair[0].fields, *pair[1].fields))
            ),
            frozenset(
                pair for pair in self.disjoint_symbols
                if pair[0] in active_symbols or pair[1] in active_symbols
            ),
            frozenset(p for p in self.tag_preserved if p.owner in active_owners),
            frozenset(p for p in self.no_realloc if p.owner in active_owners),
            frozenset(
                (rname, rplace) for rname, rplace in self.refinements.items()
                if relevant_refinements is None or rname in relevant_refinements
            ),
            frozenset(
                rname for rname in self.stale_refinements
                if relevant_refinements is None or rname in relevant_refinements
            ),
        )

    def merge_evidence(self, other: _State) -> bool:
        # The join key already fixes every retained input to the remaining CFG.
        # Combine the reports from earlier paths without combining grants.
        self.budget.spend(len(other.nodes) + len(other.issues)
                          + len(other.obligations) + len(other.restorations))
        before = (len(self.nodes), len(self.issues), len(self.obligations), len(self.restorations))
        self.nodes = tuple(dict.fromkeys((*self.nodes, *other.nodes)))
        seen_issues = set(self.issues)
        for issue in other.issues:
            if issue not in seen_issues:
                self.issues.append(issue)
                seen_issues.add(issue)
        seen_obligations = set(self.obligations)
        for obligation in other.obligations:
            if obligation not in seen_obligations:
                self.obligations.append(obligation)
                seen_obligations.add(obligation)
        seen_restorations = set(self.restorations)
        for restoration in other.restorations:
            if restoration not in seen_restorations:
                self.restorations.append(restoration)
                seen_restorations.add(restoration)
        return before != (len(self.nodes), len(self.issues), len(self.obligations), len(self.restorations))

    def _resolve_loan_spans(
        self, node: Node, canonical_loan: str
    ) -> tuple[str | None, str | None, str | None]:
        origin_node = self.loan_origin_node.get(canonical_loan)
        live_use: str | None = None
        last_use: str | None = None
        demand_map = self.first_demand.get(node.name, {})
        last_map = self.last_demand.get(node.name, {})
        candidates = [
            vname for vname, val in self.values.items() if canonical_loan in val.captures
        ]
        if canonical_loan in self.reserved:
            candidates.append(canonical_loan)
        base = base_loan_name(canonical_loan)
        if base != canonical_loan:
            candidates.append(base)
        for cand in candidates:
            if live_use is None and cand in demand_map:
                live_use = demand_map[cand]
            if cand in last_map:
                last_use = last_map[cand]
        if live_use is None and self.region_solution is not None:
            for diag in self.region_solution.conflicts:
                if diag.loan in {canonical_loan, base} and diag.witness.conflict_point == node.name:
                    origin_node = origin_node or diag.witness.origin_point
                    live_use = diag.witness.live_use_point
                    break
        proposed_end = last_use or live_use or self.last_demand_node.get(canonical_loan)
        return origin_node, live_use, proposed_end

    def _issue_loan(self, node: Node, kind: str, *loans_or_resources: str) -> None:
        normalized = tuple(base_loan_name(res) for res in loans_or_resources)
        target_canon = loans_or_resources[-1] if loans_or_resources else None
        origin_node: str | None = None
        live_use_node: str | None = None
        proposed_end_node: str | None = None
        if target_canon is not None and (
            target_canon in self.loans or target_canon in self.loan_origin_node
        ):
            origin_node, live_use_node, proposed_end_node = self._resolve_loan_spans(
                node, target_canon
            )
        self.issue(
            node,
            kind,
            *normalized,
            origin_node=origin_node,
            conflict_node=node.name,
            live_use_node=live_use_node,
            proposed_end_node=proposed_end_node,
        )

    def issue(
        self,
        node: Node,
        kind: str,
        *resources: str,
        origin_node: str | None = None,
        conflict_node: str | None = None,
        live_use_node: str | None = None,
        proposed_end_node: str | None = None,
    ) -> None:
        # Repeated rejection at a loop site still rejects the current grant.
        self.issues_emitted += 1
        item = Issue(
            node.name,
            kind,
            resources,
            origin_node=origin_node,
            conflict_node=conflict_node,
            live_use_node=live_use_node,
            proposed_end_node=proposed_end_node,
        )
        if item not in self.issues:
            self.issues.append(item)

    def obligation(self, node: Node, kind: str, *resources: str) -> None:
        item = Obligation(node.name, kind, resources)
        if item not in self.obligations:
            self.obligations.append(item)

    def _invariant_res(self, pair: tuple[str, str]) -> tuple[str, ...]:
        if self.explicit_invariants.get(pair, pair[0] != pair[1]):
            return pair
        return (pair[0],)

    def _loan_invariant(self, loan: Loan) -> tuple[str, str] | None:
        clause = loan.invariant
        if clause is None:
            return None
        if clause in self.owners[loan.place.owner].invariants:
            return loan.place.owner, clause
        # A standalone invariant has its own identity and can guard a separate place.
        return clause, clause

    def ancestors(self, names: frozenset[str] | set[str]) -> frozenset[str]:
        result = set(names)
        pending = list(names)
        while pending:
            self.budget.spend()
            parent = self.parents.get(pending.pop())
            if parent in self.loans and parent not in result:
                result.add(parent)
                pending.append(parent)
        return frozenset(result)

    def live_loans(self, demanded_names: frozenset[str]) -> frozenset[str]:
        seeds = set(self.reserved)
        for name in demanded_names:
            value = self.values.get(name)
            if value is not None:
                seeds.update(value.captures)
        return self.ancestors(seeds)

    def compare(self, node: Node, place: Place, other: str) -> Overlap:
        self.budget.spend()
        overlap = _overlap(
            place,
            self._effective_place(other),
            self.fields,
            self.disjoint_places,
            self.disjoint_symbols,
        )
        if overlap == "unknown":
            self.obligation(node, "overlap", place.owner, *place.fields, other)
        return overlap

    def containment(self, node: Node, child: Place, parent: Place, grant: str) -> Overlap:
        self.budget.spend()
        relation = _containment(child, parent, self.disjoint_places, self.disjoint_symbols)
        if relation == "unknown":
            self.obligation(node, "footprint-containment", grant, child.owner, *child.fields)
        return relation

    def check_reserved(self, node: Node, place: Place, *resources: str) -> None:
        for other in sorted(self.reserved):
            if self.compare(node, place, other) == "yes":
                self._issue_loan(node, "conflicting-receiver-reservation", *resources, other)

    def check_reserved_transfer(self, node: Node, captures: frozenset[str]) -> None:
        if self.reserved:
            for name in sorted(captures):
                self.budget.spend()
                loan = self.loans[name]
                if loan.mode == "exclusive":
                    self.check_reserved(node, loan.place)

    def cancel_reservations(self, node: Node, names: set[str]) -> None:
        for ancestor in self.ancestors(names) & self.active:
            self.last_demand_node[ancestor] = node.name
        self.reserved -= names

    def _place_touches_moved(self, place: Place, moved_place: Place) -> bool:
        if place.owner != moved_place.owner:
            return False
        if _within(place, moved_place) or _within(moved_place, place):
            return True
        if "*" in place.fields or any(_is_symbolic(part) for part in place.fields):
            return (
                _overlap(
                    place,
                    moved_place,
                    self.fields,
                    self.disjoint_places,
                    self.disjoint_symbols,
                )
                != "no"
            )
        return False

    def _has_stability_proof(self, place: Place) -> bool:
        if any(_within(place, p) or _within(p, place) for p in self.tag_preserved):
            return True
        if any(_within(place, p) or _within(p, place) for p in self.no_realloc):
            return True
        for left_p, right_p in self.disjoint_places:
            if _within(place, left_p) or _within(place, right_p):
                return True
        place_syms = {part for part in place.fields if _is_symbolic(part)}
        return bool(
            place_syms
            and any(s1 in place_syms or s2 in place_syms for s1, s2 in self.disjoint_symbols)
        )

    def borrow(self, node: Node, name: str, *, reserve: bool = False) -> None:
        loan = self.loans[name]
        parent = self.parents[name]
        prior_issues = self.issues_emitted
        self.loan_origin_node[name] = node.name
        self.obligation(
            node, "receiver-reservation-interpretation" if reserve else "loan-interpretation", name, parent
        )
        if "*" in loan.place.fields:
            self.obligation(node, "unknown-footprint", name, loan.place.owner, *loan.place.fields)
        if loan.place.owner in self.moved or any(
            self._place_touches_moved(loan.place, mp) for mp in self.moved_places
        ):
            self.issue(node, "use-after-owner-move", loan.place.owner)
        if parent in self.owners:
            parent_place = Place(parent)
            parent_owner = self.owners[parent]
            if parent_owner.mode == "shared" and loan.mode != "shared":
                self._issue_loan(node, "exclusive-from-shared", name, parent)
        else:
            parent_loan = self.loans[parent]
            parent_place = self._effective_place(parent)
            if parent not in self.active:
                self._issue_loan(node, "borrow-parent-has-no-grant", name, parent)
            if parent in self.unstable_invalidated:
                self._issue_loan(node, "invalidated-by-unstable-mutation", parent)
            if (parent_loan.mode == "shared" and loan.mode != "shared") or (
                parent_loan.mode == "shared_mut" and loan.mode == "exclusive"
            ):
                self._issue_loan(node, "exclusive-from-shared", name, parent)
        if self.containment(node, loan.place, parent_place, parent) == "no":
            self._issue_loan(node, "reborrow-outside-parent", name, parent)
        if loan.invariant is not None and self._loan_invariant(loan) not in self.opened:
            self.issue(node, "loan-invariant-not-open", base_loan_name(name), loan.invariant)
        ancestors = self.ancestors({name}) - {name}
        for other in sorted(self.active - ancestors):
            if (loan.mode == "exclusive" and not reserve) or self.loans[other].mode == "exclusive":
                overlap = self.compare(node, loan.place, other)
                if overlap == "yes":
                    self._issue_loan(node, "competing-loans", name, other)
        if loan.mode == "exclusive":
            self.check_reserved(node, loan.place, name)
        if self.issues_emitted == prior_issues:
            self.invalid.discard(name)
            (self.reserved if reserve else self.active).add(name)
        else:
            self.invalid.add(name)

    def access(self, node: Node, event: Access, route: str | None) -> None:
        self.obligation(node, "access-interpretation", event.place.owner, event.kind)
        self.obligation(node, "effect-interpretation", event.place.owner, event.kind)
        if "*" in event.place.fields:
            self.obligation(node, "unknown-footprint", event.place.owner, *event.place.fields)
        if event.kind != "read":
            self.obligation(node, "content-refinement-invalidation", event.place.owner)
            self.check_reserved(node, event.place)
            for rname, rplace in list(self.refinements.items()):
                overlap = _overlap(
                    event.place,
                    rplace,
                    self.fields,
                    self.disjoint_places,
                    self.disjoint_symbols,
                )
                if overlap == "unknown":
                    self.obligation(node, "overlap", event.place.owner, *event.place.fields, rname)
                if overlap != "no":
                    del self.refinements[rname]
                    self.stale_refinements.add(rname)
                    self.refinement_invalidated_node[rname] = node.name
        if event.kind == "write" and event.via is None:
            if not event.place.fields:
                self.moved.discard(event.place.owner)
                self.moved_places = {
                    mp for mp in self.moved_places if mp.owner != event.place.owner
                }
            elif event.place.owner in self.moved or any(
                _within(event.place, mp) and event.place != mp for mp in self.moved_places
            ):
                self.issue(node, "use-after-owner-move", event.place.owner)
            else:
                self.moved_places = {
                    mp for mp in self.moved_places if not _within(mp, event.place)
                }
        elif event.place.owner in self.moved or any(
            self._place_touches_moved(event.place, mp) for mp in self.moved_places
        ):
            self.issue(node, "use-after-owner-move", event.place.owner)
        if not event.place.fields:
            for pair in sorted(self.opened):
                if pair[0] == event.place.owner and self.explicit_invariants.get(pair, False):
                    self.issue(node, "open-invariant-whole-receiver", *self._invariant_res(pair))
        if event.via is not None:
            if route is None:
                return
            if route not in self.active:
                self._issue_loan(node, "access-route-has-no-grant", route)
                return
            if route in self.unstable_invalidated:
                self._issue_loan(node, "invalidated-by-unstable-mutation", route)
            loan = self.loans[route]
            if self.containment(node, event.place, self._effective_place(route), route) == "no":
                self._issue_loan(node, "access-outside-loan", route)
            if event.kind != "read" and loan.mode == "shared":
                self._issue_loan(node, "write-through-shared", route)
            if (
                event.kind != "read"
                and loan.mode == "shared_mut"
                and event.stability == "unstable"
                and not self._has_stability_proof(event.place)
            ):
                self._issue_loan(node, "unstable-shared-mut-write", route)
            if event.kind == "move":
                self._issue_loan(node, "move-through-loan-unsupported", route)
        ancestors = self.ancestors({route}) if route is not None else frozenset()
        route_mode = self.loans[route].mode if route is not None and route in self.loans else None
        for other in sorted(self.active - ancestors):
            overlap = self.compare(node, event.place, other)
            if overlap == "no":
                continue
            other_loan = self.loans[other]
            other_place = self._effective_place(other)
            protected_tag = any(
                _within(event.place, p) and _within(other_place, p) for p in self.tag_preserved
            )
            protected_norealloc = any(
                _within(event.place, p)
                and _within(other_place, p)
                and len(other_place.fields) > len(p.fields)
                for p in self.no_realloc
            )
            stability_protected = (
                protected_tag
                or protected_norealloc
                or (other_loan.mode == "shared_mut" and self._has_stability_proof(event.place))
            )
            if (
                event.kind != "read"
                and event.stability == "unstable"
                and not stability_protected
                and len(other_place.fields) >= len(event.place.fields)
            ):
                self.unstable_invalidated.add(other)
                self.invalid.add(other)
            # An owner/ancestor route cannot bypass a live descendant permission.
            descendant = route is None or route in self.ancestors({other})
            exclusive_ancestor = (
                descendant and route is not None and self.loans[route].mode == "exclusive"
            )
            # Aliased shared_mut stable writes (and proof-justified unstable writes) do not conflict.
            if (
                other_loan.mode == "shared_mut"
                and (route is None or route_mode == "shared_mut")
                and (event.kind == "read" or event.stability == "stable" or stability_protected)
            ):
                continue
            if (
                other_loan.mode == "shared"
                and event.kind != "read"
                and protected_norealloc
            ):
                continue
            if overlap == "yes" and (
                exclusive_ancestor
                or event.kind != "read"
                or other_loan.mode == "exclusive"
            ):
                self._issue_loan(
                    node, "suspended-parent" if descendant else "conflicting-access", other
                )
        if event.kind == "move" and event.via is None:
            self.tag_preserved = {
                p
                for p in self.tag_preserved
                if _overlap(event.place, p, self.fields, self.disjoint_places, self.disjoint_symbols) == "no"
            }
            self.no_realloc = {
                p
                for p in self.no_realloc
                if _overlap(event.place, p, self.fields, self.disjoint_places, self.disjoint_symbols) == "no"
            }
            if event.place.fields:
                if "*" in event.place.fields or any(_is_symbolic(f) for f in event.place.fields):
                    self.issue(node, "partial-owner-move-unsupported", event.place.owner)
                else:
                    self.moved_places.add(event.place)
                    for rname, rplace in list(self.refinements.items()):
                        if (
                            _overlap(
                                event.place,
                                rplace,
                                self.fields,
                                self.disjoint_places,
                                self.disjoint_symbols,
                            )
                            != "no"
                        ):
                            del self.refinements[rname]
                            self.stale_refinements.add(rname)
                            self.refinement_invalidated_node[rname] = node.name
            elif any(mp.owner == event.place.owner for mp in self.moved_places):
                self.issue(node, "use-after-owner-move", event.place.owner)
            else:
                self.moved.add(event.place.owner)
                for rname, rplace in list(self.refinements.items()):
                    if rplace.owner == event.place.owner:
                        del self.refinements[rname]
                        self.stale_refinements.add(rname)
                        self.refinement_invalidated_node[rname] = node.name

    def end_dead(self, fallback_node: str, live: frozenset[str]) -> None:
        # Every child is deeper than its ancestor. Lexical names only break ties.
        ending = sorted(
            self.active - live,
            key=lambda name: (-len(self.ancestors({name})), name),
        )
        for name in ending:
            self.budget.spend()
            loan = self.loans[name]
            at_node = self.last_demand_node.get(name, fallback_node)
            restoration = Restoration(at_node, name, self.parents[name], loan.place)
            if restoration not in self.restorations:
                self.restorations.append(restoration)
            obligation = Obligation(at_node, "restoration", (name, self.parents[name]))
            if obligation not in self.obligations:
                self.obligations.append(obligation)
            self.active.remove(name)
            self.unstable_invalidated.discard(name)
            self.frozen_places.pop(name, None)
            self.step_bases.pop(name, None)
            self.loan_origin_node.pop(name, None)

    def fold_loop_cursor(self) -> None:
        if not self.step_bases:
            return
        changed = True
        while changed:
            changed = False
            self.budget.spend()
            children_map: dict[str, set[str]] = {}
            for lname in self.active | self.reserved:
                parent = self.parents.get(lname)
                if parent in self.loans:
                    children_map.setdefault(parent, set()).add(lname)
            leaves = sorted(name for name in self.active if name not in children_map)
            for leaf in leaves:
                chain_rev: list[str] = []
                curr: str | None = leaf
                while curr is not None and curr in self.active and curr not in chain_rev:
                    chain_rev.append(curr)
                    parent = self.parents.get(curr)
                    curr = parent if parent in self.loans else None
                chain = list(reversed(chain_rev))
                max_k = len(chain) // 2
                for k in range(1, max_k + 1):
                    suffix = chain[-k:]
                    prefix = chain[-2 * k:-k]
                    if not any(s in self.step_bases for s in suffix):
                        continue
                    compatible = True
                    for idx in range(k):
                        s = suffix[idx]
                        p = prefix[idx]
                        s_loan = self.loans[s]
                        p_loan = self.loans[p]
                        expected_child = chain[-2 * k + idx + 1]
                        s_place = self._effective_place(s)
                        p_place = self._effective_place(p)
                        place_compatible = s_place == p_place or (
                            _within(s_place, p_place) and "*" not in p_place.fields
                        )
                        if (
                            self.step_bases.get(s, s) != self.step_bases.get(p, p)
                            or not place_compatible
                            or s_loan.mode != p_loan.mode
                            or s_loan.scoped != p_loan.scoped
                            or s_loan.invariant != p_loan.invariant
                            or p in self.reserved
                            or any(p in v.captures for v in self.values.values())
                            or not (children_map.get(p, set()) <= {expected_child})
                        ):
                            compatible = False
                            break
                    if not compatible:
                        continue
                    remap = {suffix[idx]: prefix[idx] for idx in range(k)}
                    for vname, val in list(self.values.items()):
                        if any(s in val.captures or val.handle == s for s in remap):
                            new_caps = frozenset(remap.get(c, c) for c in val.captures)
                            new_handle = remap.get(val.handle, val.handle) if val.handle is not None else None
                            self.values[vname] = _Value(new_caps, new_handle)
                    for cname in list(self.parents):
                        if self.parents[cname] in remap and cname not in remap:
                            self.parents[cname] = remap[self.parents[cname]]
                    for s, p in remap.items():
                        if s in self.last_demand_node:
                            self.last_demand_node[p] = self.last_demand_node.pop(s)
                        if s in self.invalid:
                            self.invalid.add(p)
                            self.invalid.discard(s)
                        if s in self.unstable_invalidated:
                            self.unstable_invalidated.add(p)
                            self.unstable_invalidated.discard(s)
                        self.active.discard(s)
                        self.loans.pop(s, None)
                        self.parents.pop(s, None)
                        self.frozen_places.pop(s, None)
                        self.step_bases.pop(s, None)
                        self.loan_origin_node.pop(s, None)
                    changed = True
                    break
                if changed:
                    break

    def step(self, node: Node, demanded_after: frozenset[str]) -> None:
        self.budget.spend()
        if not self.nodes or self.nodes[-1] != node.name:
            self.nodes = (*self.nodes, node.name)
        event = node.event
        used: set[str] = set()
        references = (
            (*event.captures, *(name for name in event.possible_captures if name in self.seen_binders))
            if isinstance(event, Activate) else _references(event)
        )
        for name in references:
            self.budget.spend()
            if name in self.owners:
                continue
            if name not in self.values:
                self.issue(node, "unavailable-name", name)
            elif not isinstance(event, Drop):
                self.budget.spend(len(self.values[name].captures))
                used.update(self.values[name].captures)
        binder = _binder(event)
        fresh = True
        if binder is not None:
            prior = self.seen_binders.get(binder)
            if binder in self.owners or (
                prior is not None and prior != node.name and not isinstance(event, Move)
            ):
                fresh = False
                self.issue(node, "ambiguous-name", binder)
            else:
                self.seen_binders[binder] = node.name
        creates: str | None = None
        route: str | None = None
        match event:
            case Borrow(loan) | Reserve(loan):
                if fresh:
                    parent = self.values.get(loan.parent)
                    if loan.parent in self.owners:
                        route = loan.parent
                    elif parent is not None and parent.handle is not None:
                        route = parent.handle
                    else:
                        self.issue(node, "borrow-parent-has-no-grant", loan.parent)
                    if route is not None:
                        canonical = loan.name
                        if canonical in self.active or canonical in self.reserved:
                            suffix = 1
                            while (
                                f"{loan.name}#{suffix}" in self.loans
                                or f"{loan.name}#{suffix}" in self.active
                                or f"{loan.name}#{suffix}" in self.reserved
                            ):
                                self.budget.spend()
                                suffix += 1
                            canonical = f"{loan.name}#{suffix}"
                            self.step_bases[canonical] = loan.name
                        actual_loan = (
                            loan if canonical == loan.name
                            else Loan(
                                canonical,
                                loan.parent,
                                loan.place,
                                loan.mode,
                                loan.scoped,
                                loan.invariant,
                                loan.origin,
                            )
                        )
                        self.loans[canonical] = actual_loan
                        self.parents[canonical] = route
                        if isinstance(event, Borrow):
                            self.values[loan.name] = _Value(frozenset({canonical}), canonical)
                        creates = canonical
            case Activate(name):
                if name not in self.reserved:
                    self.issue(node, "receiver-reservation-unavailable", name)
                else:
                    self.reserved.remove(name)
                    self.values[name] = _Value(frozenset({name}), name)
                    creates = name
            case Access(via=via) if via is not None:
                value = self.values.get(via)
                if value is not None:
                    route = value.handle
                if route is None:
                    self.issue(node, "access-route-has-no-grant", via)
            case Bind(name, captures):
                if fresh:
                    if set(captures) & self.owners.keys():
                        self.issue(node, "owner-capture-unsupported", name)
                    self.values[name] = _Value(frozenset(used))
                    self.obligation(node, "capture-interpretation", name, *sorted(used))
            case Move(source, target):
                if source in self.owners:
                    self.issue(node, "owner-handle-move-unsupported", source)
                elif fresh and source in self.values:
                    value = self.values.pop(source)
                    self.check_reserved_transfer(node, value.captures)
                    self.values[target] = value
            case Drop(name):
                if name in self.owners:
                    self.issue(node, "owner-drop-unsupported", name)
                elif (value := self.values.pop(name, None)) is not None and value.handle is not None:
                    self.check_reserved_transfer(node, value.captures)
            case Return(captures=names):
                if set(names) & self.owners.keys():
                    self.issue(
                        node,
                        "owner-return-unsupported",
                        *sorted(set(names) & self.owners.keys()),
                    )
                self.returned = frozenset(used)
            case _:
                pass

        if creates is not None:
            for anc in self.ancestors({creates}):
                self.last_demand_node[anc] = node.name
        if used and not isinstance(event, Drop):
            for anc in self.ancestors(used):
                self.last_demand_node[anc] = node.name

        if isinstance(event, Reserve) and creates is not None:
            self.borrow(node, creates, reserve=True)
        live_after = (
            self.ancestors(self.returned)
            if not node.successors
            else self.live_loans(demanded_after)
        )
        match event:
            case (Borrow() | Activate()) if creates is not None:
                self.borrow(node, creates)
            case Access():
                self.access(node, event, route)
            case Use(name):
                if name in self.owners:
                    self.access(node, Access(Place(name)), None)
                else:
                    for captured in sorted(used):
                        if captured in self.unstable_invalidated:
                            self._issue_loan(node, "invalidated-by-unstable-mutation", captured)
                        self.access(node, Access(self._effective_place(captured), via=name), captured)
            case AssumeDisjoint(left, right):
                self.disjoint_places.add(_canonical_place_pair(left, right))
                self.obligation(node, "disjointness-assumption", left.owner, right.owner)
            case AssumeIndexNe(left, right):
                left_sym = _symbol_name(left)
                right_sym = _symbol_name(right)
                if left_sym != right_sym:
                    self.disjoint_symbols.add(_canonical_symbol_pair(left_sym, right_sym))
                self.obligation(node, "disjointness-assumption", left_sym, right_sym)
            case AssumeTagPreserved(place):
                self.tag_preserved.add(place)
                self.obligation(node, "tag-preservation-assumption", place.owner, *place.fields)
            case AssumeNoRealloc(place):
                self.no_realloc.add(place)
                self.obligation(node, "no-realloc-assumption", place.owner, *place.fields)
            case InvalidateSymbol(symbol):
                sym = _symbol_name(symbol)
                self.disjoint_symbols = {pair for pair in self.disjoint_symbols if sym not in pair}
                self.disjoint_places = {
                    pair for pair in self.disjoint_places
                    if sym not in pair[0].fields and sym not in pair[1].fields
                }
                self.tag_preserved = {
                    _replace_symbol_in_place(p, sym) for p in self.tag_preserved
                }
                self.no_realloc = {
                    _replace_symbol_in_place(p, sym) for p in self.no_realloc
                }
                for lname in self.active | self.reserved:
                    eplace = self._effective_place(lname)
                    if sym in eplace.fields:
                        self.frozen_places[lname] = _replace_symbol_in_place(eplace, sym)
                for rname, rplace in list(self.refinements.items()):
                    if sym in rplace.fields:
                        del self.refinements[rname]
                        self.stale_refinements.add(rname)
                        self.refinement_invalidated_node[rname] = node.name
            case AssumeRefinement(name, place):
                self.refinements[name] = place
                self.refinement_origin_node[name] = node.name
                self.refinement_invalidated_node.pop(name, None)
                self.stale_refinements.discard(name)
                self.obligation(node, "refinement-interpretation", name, place.owner, *place.fields)
            case UseRefinement(name):
                if name in self.stale_refinements:
                    self.issue(
                        node,
                        "stale-refinement",
                        name,
                        origin_node=self.refinement_origin_node.get(name),
                        conflict_node=self.refinement_invalidated_node.get(name, node.name),
                        live_use_node=node.name,
                    )
                elif name not in self.refinements:
                    self.issue(node, "unavailable-refinement", name)
                elif self.refinements[name].owner in self.moved or any(
                    self._place_touches_moved(self.refinements[name], mp)
                    for mp in self.moved_places
                ):
                    self.issue(
                        node,
                        "stale-refinement",
                        name,
                        origin_node=self.refinement_origin_node.get(name),
                        conflict_node=node.name,
                        live_use_node=node.name,
                    )
            case DropRefinement(name):
                if name not in self.refinements and name not in self.stale_refinements:
                    self.issue(node, "unavailable-refinement", name)
                else:
                    self.refinements.pop(name, None)
                    self.refinement_origin_node.pop(name, None)
                    self.refinement_invalidated_node.pop(name, None)
                    self.stale_refinements.discard(name)
            case OpenInvariant(name, clauses):
                conjuncts, is_explicit = _invariant_conjuncts(self.owners, name, clauses)
                for pair in conjuncts:
                    self.explicit_invariants[pair] = is_explicit
                    res = self._invariant_res(pair)
                    if pair in self.opened:
                        self.issue(node, "invariant-already-open", *res)
                    self.opened.add(pair)
                    self.active_invariants.discard(pair)
                    self.obligation(node, "invariant-open", *res)
                owner = self.owners.get(name)
                if owner is not None and owner.invariants:
                    for clause in owner.invariants:
                        if (name, clause) in self.active_invariants:
                            self.obligation(node, "invariant-active", name, clause)
            case CloseInvariant(name, clauses):
                conjuncts, is_explicit = _invariant_conjuncts(self.owners, name, clauses)
                for pair in conjuncts:
                    if pair not in self.explicit_invariants:
                        self.explicit_invariants[pair] = is_explicit
                    res = self._invariant_res(pair)
                    if pair not in self.opened:
                        self.issue(node, "invariant-not-open", *res)
                    for loan in sorted(self.active):
                        if loan in live_after and self._loan_invariant(self.loans[loan]) == pair:
                            self.issue(node, "invariant-closed-with-live-loan", *res, loan)
                    self.opened.discard(pair)
                    owner = self.owners.get(pair[0])
                    if owner is not None and pair[1] in owner.invariants:
                        self.active_invariants.add(pair)
                    self.obligation(node, "invariant-close", *res)
            case Checkpoint(kind):
                self.issue(node, "unsupported-boundary", kind)
                self.obligation(node, "boundary-interpretation", kind, *sorted(self.active))
                for name in sorted(self.reserved):
                    self.issue(node, "receiver-reservation-at-boundary", name)
                for pair in sorted(self.opened):
                    self.issue(node, "open-invariant-at-boundary", *self._invariant_res(pair))
                for loan in sorted(self.active & live_after):
                    if self.loans[loan].scoped:
                        self.issue(node, "scoped-loan-at-boundary", loan)
            case Return(tag, _):
                self.outcome = tag
            case _:
                pass

        if not node.successors and self.reserved:
            self.cancel_reservations(node, self.reserved)
        self.end_dead(node.name, live_after)

    def _effective_loan_origin(self, name: str) -> str | None:
        curr: str | None = name
        visited: set[str] = set()
        while curr is not None and curr in self.loans and curr not in visited:
            visited.add(curr)
            loan = self.loans[curr]
            if loan.origin is not None:
                return loan.origin
            parent = self.parents.get(curr)
            if parent in self.owners:
                return self.owners[parent].origin
            curr = parent
        return None

    def finalize(self, terminal: Node) -> PathReport:
        for pair in sorted(self.opened):
            self.issue(terminal, "unclosed-invariant", *self._invariant_res(pair))
        # Retaining a descendant retains every ancestor's restoration duty and
        # scope. An unscoped descriptor cannot launder a scoped parent grant.
        for name in sorted(self.ancestors(self.returned)):
            if self.loans[name].scoped:
                self._issue_loan(terminal, "scoped-loan-escape", name)

        returned_list = sorted(self.returned)
        for idx, left_name in enumerate(returned_list):
            left_loan = self.loans[left_name]
            for right_name in returned_list[idx + 1:]:
                right_loan = self.loans[right_name]
                if right_name in self.ancestors({left_name}) or left_name in self.ancestors(
                    {right_name}
                ):
                    continue
                if left_loan.mode == "exclusive" or right_loan.mode == "exclusive":
                    overlap = _overlap(
                        self._effective_place(left_name),
                        self._effective_place(right_name),
                        self.fields,
                        self.disjoint_places,
                        self.disjoint_symbols,
                    )
                    if overlap != "no":
                        self._issue_loan(terminal, "competing-loans", left_name, right_name)

        ret_origin = terminal.event.origin if isinstance(terminal.event, Return) else None
        for name in returned_list:
            loan = self.loans[name]
            root_owner = self.owners[loan.place.owner]
            if name in self.invalid:
                self._issue_loan(terminal, "invalid-loan-escape", name)
            if not root_owner.borrowed:
                self._issue_loan(terminal, "local-loan-escape", name)
            if loan.mode == "exclusive":
                target_origin = ret_origin or self.graph_return_origin or root_owner.origin
                eff_loan_origin = self._effective_loan_origin(name)
                owner_origin = root_owner.origin
                origin_matches = (
                    root_owner.borrowed
                    and root_owner.mode != "shared"
                    and target_origin is not None
                    and owner_origin is not None
                    and (
                        owner_origin == target_origin
                        or (
                            self.region_solution is not None
                            and self.region_solution.can_outlive(
                                owner_origin, target_origin, terminal.name
                            )
                        )
                    )
                    and (
                        eff_loan_origin == target_origin
                        or (
                            self.region_solution is not None
                            and eff_loan_origin is not None
                            and self.region_solution.can_outlive(
                                eff_loan_origin, target_origin, terminal.name
                            )
                        )
                    )
                )
                region_ok = True
                if self.region_solution is not None:
                    for diag in (
                        *self.region_solution.hrtb_escapes,
                        *self.region_solution.outlives_errors,
                    ):
                        chain = diag.witness.origin_chain
                        if chain and (
                            chain[0] in {eff_loan_origin, owner_origin}
                            or chain[-1] == target_origin
                        ):
                            region_ok = False
                            break
                anc = self.ancestors({name})
                has_sibling_conflict = any(
                    other != name
                    and other not in anc
                    and _overlap(
                        self._effective_place(name),
                        self._effective_place(other),
                        self.fields,
                        self.disjoint_places,
                        self.disjoint_symbols,
                    )
                    != "no"
                    for other in sorted(self.active | self.returned)
                )
                if not origin_matches or not region_ok or has_sibling_conflict:
                    self._issue_loan(terminal, "exclusive-loan-escape", name)
                else:
                    self.obligation(terminal, "returned-loan-restoration", name, self.parents[name])
            self.obligation(terminal, "returned-loan-lifetime", name, loan.place.owner)
        suspended = tuple(
            sorted(
                {self.loans[name].place for name in self.active},
                key=lambda place: (place.owner, place.fields),
            )
        )
        moved_places = tuple(
            sorted(self.moved_places, key=lambda place: (place.owner, place.fields))
        )
        return PathReport(
            self.nodes,
            self.outcome,
            tuple(self.issues),
            tuple(self.obligations),
            tuple(self.restorations),
            tuple(sorted(self.returned)),
            tuple(sorted(self.active)),
            suspended,
            tuple(sorted(self.moved)),
            tuple(sorted(self.active_invariants)),
            tuple(sorted(self.opened)),
            moved_places,
        )


def _build_region_solution(
    owners: tuple[Owner, ...],
    graph: Graph,
    budget: _Budget,
) -> regions.RegionSolution:
    budget.spend()
    solver = regions.RegionSolver(
        entry=graph.entry,
        successors={node.name: node.successors for node in graph.nodes},
        declared_outlives=graph.declared_outlives,
    )
    owner_origins: dict[str, str] = {}
    param_origins: set[str] = set()
    for owner in owners:
        if owner.origin is not None:
            kind: regions.OriginKind = "param" if owner.borrowed else "local"
            solver.add_origin(regions.Origin(owner.origin, kind=kind))
            owner_origins[owner.name] = owner.origin
            if kind == "param":
                param_origins.add(owner.origin)
    if graph.return_origin is not None:
        solver.add_origin(regions.Origin(graph.return_origin, kind="param"))
        param_origins.add(graph.return_origin)

    loan_origins: dict[str, str] = {}
    handle_origins: dict[str, set[str]] = {}
    for node in graph.nodes:
        budget.spend()
        ev = node.event
        if isinstance(ev, (Borrow, Reserve)):
            loan = ev.loan
            orig = loan.origin or f"__loan_{loan.name}"
            kind = "param" if orig in param_origins else "local"
            if orig not in solver.origins:
                solver.add_origin(regions.Origin(orig, kind=kind))
            loan_origins[loan.name] = orig
            handle_origins.setdefault(loan.name, set()).add(orig)
            solver.add_origin_loan(regions.OriginLoan(node.name, orig, loan.name))
            parent_orig = owner_origins.get(loan.parent) or loan_origins.get(loan.parent)
            if parent_orig is not None:
                solver.add_outlives(regions.OutlivesConstraint(parent_orig, orig, node.name))
        elif isinstance(ev, Bind):
            caps: set[str] = set()
            for cap in ev.captures:
                caps.update(handle_origins.get(cap, ()))
            if caps:
                handle_origins[ev.name] = caps
        elif isinstance(ev, Move):
            if ev.source in handle_origins:
                handle_origins[ev.target] = set(handle_origins[ev.source])
        elif isinstance(ev, Use):
            for orig in handle_origins.get(ev.name, ()):
                solver.add_origin_use(node.name, orig)
        elif isinstance(ev, Access) and ev.via is not None:
            for orig in handle_origins.get(ev.via, ()):
                solver.add_origin_use(node.name, orig)
        elif isinstance(ev, Return):
            target = ev.origin or graph.return_origin
            for cap in ev.captures:
                for orig in handle_origins.get(cap, ()):
                    solver.add_origin_use(node.name, orig)
                    if target is not None:
                        if target not in solver.origins:
                            solver.add_origin(regions.Origin(target, kind="param"))
                        solver.add_outlives(regions.OutlivesConstraint(orig, target, node.name))
    return solver.solve()


def export_loan_certificate(report: Report) -> dict[str, object]:
    """Export a ``Report`` into a JSON-serializable schema matching ``loan_soundness.v``."""
    if not isinstance(report, Report):
        raise AnalysisRefusalError("certificate export requires an immutable Report record")
    return {
        "schema": "holdfast-loan-certificate-v1",
        "status": report.status,
        "valid": all(not path.issues for path in report.paths),
        "path_count": len(report.paths),
        "paths": [
            {
                "index": idx,
                "nodes": list(path.nodes),
                "outcome": path.outcome,
                "valid": not path.issues,
                "issues": [
                    {
                        "node": issue.node,
                        "kind": issue.kind,
                        "resources": list(issue.resources),
                        "origin_node": issue.origin_node,
                        "conflict_node": issue.conflict_node,
                        "live_use_node": issue.live_use_node,
                        "proposed_end_node": issue.proposed_end_node,
                    }
                    for issue in path.issues
                ],
                "obligations": [
                    {
                        "node": ob.node,
                        "kind": ob.kind,
                        "resources": list(ob.resources),
                        "status": ob.status,
                    }
                    for ob in path.obligations
                ],
                "restorations": [
                    {
                        "node": rest.node,
                        "loan": rest.loan,
                        "parent": rest.parent,
                        "place": {"owner": rest.place.owner, "fields": list(rest.place.fields)},
                        "status": rest.status,
                    }
                    for rest in path.restorations
                ],
                "returned_loans": list(path.returned_loans),
                "retained_loans": list(path.retained_loans),
                "suspended": [
                    {"owner": p.owner, "fields": list(p.fields)} for p in path.suspended
                ],
                "moved_owners": list(path.moved_owners),
                "moved_places": [
                    {"owner": p.owner, "fields": list(p.fields)} for p in path.moved_places
                ],
                "active_invariants": [list(pair) for pair in path.active_invariants],
                "open_invariants": [list(pair) for pair in path.open_invariants],
            }
            for idx, path in enumerate(report.paths)
        ],
    }


def analyze(owners: tuple[Owner, ...], graph: Graph, limits: Limits | None = None) -> Report:
    """Return a deterministic diagnostic over supplied abstract inputs without I/O, or raise `AnalysisRefusalError`.

    Leaves source-interpretation and restoration obligations unresolved even on empty issue sets,
    and discards all path results on budget exhaustion instead of returning a partial prefix.

    Example: ``analyze((Owner("input", borrowed=True),), Graph("lend", (
    Node("lend", Borrow(Loan("view", "input", Place("input"))), ("read",)),
    Node("read", Use("view")),)))`` proposes ending ``view`` after ``read``.
    """
    if limits is None:
        limits = Limits()
    if not isinstance(limits, Limits):
        raise AnalysisRefusalError("limits must be an immutable Limits record")
    budget = _Budget(limits.work)
    nodes, dominators = _validate(owners, graph, limits, budget)
    demanded_before, demanded_after, reachable_names = _compute_cfg_liveness(graph, nodes, budget)
    must_demand_before, future_nodes, first_demand, last_demand = _compute_cfg_demand_sites(
        graph, nodes, budget
    )
    reachable_owners, reachable_symbols, reachable_refinements = _compute_cfg_relevance(
        graph, nodes, budget
    )
    region_solution = _build_region_solution(owners, graph, budget)
    binder_counts = Counter(_binder(node.event) for node in graph.nodes)
    # Binder history matters for ambiguous identities and conditional captures.
    history_names = {name for name, count in binder_counts.items() if name is not None and count > 1}
    history_names.update(name for node in graph.nodes if isinstance(node.event, Activate)
                         for name in node.event.possible_captures)
    owner_map = {owner.name: owner for owner in owners}
    budget.spend(sum(len(owner.fields) for owner in owners))
    fields = {owner.name: frozenset(owner.fields) for owner in owners}

    in_degree = dict.fromkeys(nodes, 0)
    # The initial state is an incoming edge when the entry is a loop header.
    in_degree[graph.entry] = 1
    for node in graph.nodes:
        for successor in node.successors:
            in_degree[successor] += 1

    # Topological order of the forward DAG (excluding natural-loop back-edges).
    postorder: list[str] = []
    visited_rpo: set[str] = set()

    def _dfs_rpo(curr: str) -> None:
        visited_rpo.add(curr)
        for succ in nodes[curr].successors:
            if succ not in dominators[curr] and succ not in visited_rpo:
                _dfs_rpo(succ)
        postorder.append(curr)

    _dfs_rpo(graph.entry)
    rpo_index = {name: idx for idx, name in enumerate(reversed(postorder))}

    # Retain distinct incoming grants and routes at joins, including loop headers.
    join_states: dict[str, dict[tuple[object, ...], _State]] = {
        name: {} for name, deg in in_degree.items() if deg > 1
    }
    pending_joins: dict[str, deque[tuple[object, ...]]] = {
        name: deque() for name in join_states
    }
    initial = _State(
        owner_map,
        fields,
        budget,
        graph.entry,
        graph_return_origin=graph.return_origin,
        region_solution=region_solution,
        first_demand=first_demand,
        last_demand=last_demand,
    )
    entry_key = ()
    if graph.entry in join_states:
        entry_key = initial.join_key(
            reachable_names[graph.entry],
            history_names,
            reachable_owners[graph.entry],
            reachable_symbols[graph.entry],
            reachable_refinements[graph.entry],
            must_demand_before[graph.entry],
            future_nodes[graph.entry],
        )
        join_states[graph.entry][entry_key] = initial.clone()
    branch_worklist: list[tuple[str, _State, tuple[object, ...]]] = [(graph.entry, initial, entry_key)]
    terminal_reports: dict[tuple[str, tuple[object, ...]], PathReport] = {}

    while branch_worklist or any(pending_joins.values()):
        budget.spend()
        if branch_worklist:
            node_name, state, join_env = branch_worklist.pop()
        else:
            next_join = min(
                (name for name, keys in pending_joins.items() if keys),
                key=lambda name: rpo_index.get(name, 0),
            )
            join_env = pending_joins[next_join].popleft()
            node_name = next_join
            state = join_states[next_join][join_env].clone()

        node = nodes[node_name]
        state.step(node, demanded_after[node_name])
        if not node.successors:
            # Each terminal has a unique nearest upstream join (or the entry).
            # A fixpoint revisit updates only that join environment's prior report.
            terminal_reports[node_name, join_env] = state.finalize(node)
            if len(terminal_reports) > limits.paths:
                raise AnalysisRefusalError("complete path budget exhausted")
            continue

        for index, successor in enumerate(reversed(node.successors)):
            branch = state if index == len(node.successors) - 1 else state.clone()
            is_backedge = successor in dominators[node.name]
            if branch.reserved and is_backedge:
                enclosing = dominators[successor] - {successor}
                local_reservations = {
                    name
                    for name in branch.reserved
                    if branch.seen_binders[branch.step_bases.get(name, name)] not in enclosing
                }
                if local_reservations:
                    branch.issue(node, "receiver-reservation-at-loop-backedge", *sorted(local_reservations))
                    branch.cancel_reservations(node, local_reservations)
            branch.end_dead(node.name, branch.live_loans(demanded_before[successor]))
            if is_backedge:
                branch.fold_loop_cursor()
            if in_degree[successor] > 1:
                env_key = branch.join_key(
                    reachable_names[successor],
                    history_names,
                    reachable_owners[successor],
                    reachable_symbols[successor],
                    reachable_refinements[successor],
                    must_demand_before[successor],
                    future_nodes[successor],
                )
                buckets = join_states[successor]
                if env_key in buckets:
                    if not buckets[env_key].merge_evidence(branch):
                        continue
                elif len(buckets) < limits.paths:
                    buckets[env_key] = branch.clone()
                else:
                    raise AnalysisRefusalError("complete path budget exhausted at control-flow join")
                if env_key not in pending_joins[successor]:
                    pending_joins[successor].append(env_key)
            else:
                branch_worklist.append((successor, branch, join_env))

    return Report(tuple(terminal_reports.values()))


# ---------------------------------------------------------------------------
# Loan graph lowering from the schema-2 surface AST
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class _Receiver:
    mode: Mode
    view: str | None
    retained: bool
    two_phase: bool = False
    scalar_result: bool = False


@dataclass
class _StructInfo:
    fields: tuple[tuple[str, ...], ...]
    views: dict[str, tuple[str, ...]]
    invariants: tuple[str, ...]
    methods: dict[str, _Receiver | None] = field(default_factory=dict)
    field_types: dict[str, str | None] = field(default_factory=dict)


@dataclass(frozen=True)
class ProvedFacts:
    """Optional semantic facts injected into ``_FunctionLowerer`` / ``lower_function``."""

    disjoint_places: tuple[tuple[Place, Place], ...] = ()
    arithmetic_disequalities: tuple[tuple[str, str], ...] = ()
    tag_preserved: tuple[Place, ...] = ()
    no_realloc: tuple[Place, ...] = ()
    refinements: Mapping[str, Place] = field(default_factory=dict)
    use_refinements: tuple[str, ...] = ()
    record_views: Mapping[str, Mapping[str, tuple[str, ...]]] = field(default_factory=dict)
    methods: Mapping[str, Mapping[str, _Receiver | None]] = field(default_factory=dict)
    function_returns: Mapping[str, str | None] = field(default_factory=dict)
    return_summaries: Mapping[str, str] = field(default_factory=dict)


def _normalize_proved_facts(
    proved_facts: ProvedFacts | Mapping[str, object] | None,
) -> ProvedFacts | None:
    if proved_facts is None or isinstance(proved_facts, ProvedFacts):
        return proved_facts
    if not isinstance(proved_facts, Mapping):
        raise AnalysisRefusalError("proved_facts must be a ProvedFacts record or mapping")

    def _places_seq(key: str) -> tuple[Place, ...]:
        raw = proved_facts.get(key, ())
        if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
            raise AnalysisRefusalError(f"proved_facts[{key!r}] must be a sequence of Places")
        return tuple(cast("Sequence[Place]", raw))

    raw_disjoint = proved_facts.get("disjoint_places", ())
    disjoint_pairs = (
        tuple((pair[0], pair[1]) for pair in cast("Sequence[tuple[Place, Place]]", raw_disjoint))
        if isinstance(raw_disjoint, Sequence) and not isinstance(raw_disjoint, (str, bytes))
        else ()
    )
    raw_arith = proved_facts.get("arithmetic_disequalities", ())
    arith_pairs = (
        tuple((pair[0], pair[1]) for pair in cast("Sequence[tuple[str, str]]", raw_arith))
        if isinstance(raw_arith, Sequence) and not isinstance(raw_arith, (str, bytes))
        else ()
    )
    raw_refs = proved_facts.get("refinements", {})
    refs = (
        dict(cast("Mapping[str, Place]", raw_refs))
        if isinstance(raw_refs, Mapping)
        else {}
    )
    raw_use_refs = proved_facts.get("use_refinements", ())
    use_refs = (
        tuple(cast("Sequence[str]", raw_use_refs))
        if isinstance(raw_use_refs, Sequence) and not isinstance(raw_use_refs, (str, bytes))
        else ()
    )
    raw_views = proved_facts.get("record_views", {})
    views = (
        {
            str(k): {str(vk): tuple(vv) for vk, vv in v.items()}
            for k, v in cast("Mapping[str, Mapping[str, Sequence[str]]]", raw_views).items()
        }
        if isinstance(raw_views, Mapping)
        else {}
    )
    raw_methods = proved_facts.get("methods", {})
    methods = (
        dict(cast("Mapping[str, Mapping[str, _Receiver | None]]", raw_methods))
        if isinstance(raw_methods, Mapping)
        else {}
    )
    raw_fn_ret = proved_facts.get("function_returns", {})
    fn_returns = (
        dict(cast("Mapping[str, str | None]", raw_fn_ret))
        if isinstance(raw_fn_ret, Mapping)
        else {}
    )
    raw_summaries = proved_facts.get("return_summaries", {})
    summaries = (
        dict(cast("Mapping[str, str]", raw_summaries))
        if isinstance(raw_summaries, Mapping)
        else {}
    )
    return ProvedFacts(
        disjoint_places=disjoint_pairs,
        arithmetic_disequalities=arith_pairs,
        tag_preserved=_places_seq("tag_preserved"),
        no_realloc=_places_seq("no_realloc"),
        refinements=refs,
        use_refinements=use_refs,
        record_views=views,
        methods=methods,
        function_returns=fn_returns,
        return_summaries=summaries,
    )


def _ast_node(value: object, role: str = "AST node") -> dict[str, object]:
    if not isinstance(value, dict):
        raise AnalysisRefusalError(f"expected {role} mapping")
    return cast("dict[str, object]", value)


def _ast_nodes(value: object, role: str = "AST node list") -> list[dict[str, object]]:
    if not isinstance(value, list):
        raise AnalysisRefusalError(f"expected {role} list")
    return [_ast_node(item, role) for item in value]


def _id_text(value: object) -> str:
    if isinstance(value, str):
        return value
    node = _ast_node(value, "identifier")
    text = node.get("text") or node.get("name")
    if isinstance(text, dict):
        text = text.get("text")
    if not isinstance(text, str):
        raise AnalysisRefusalError("missing identifier text")
    return text.replace(".", "_")


def _op_text(value: object) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, dict) and isinstance(value.get("text"), str):
        return str(value["text"])
    return ""


def _checks_constructor(pattern: object) -> bool:
    while isinstance(pattern, dict) and pattern.get("kind") == "group_pattern":
        pattern = pattern.get("pattern")
    return isinstance(pattern, dict) and _ast_node(pattern).get("kind") == "constructor_pattern"


def _is_ident(node: dict[str, object]) -> bool:
    return node.get("kind") in {"identifier", "name"}


def _extract_borrow_expr(expr: dict[str, object]) -> tuple[str, dict[str, object]] | None:
    curr = expr
    while curr.get("kind") == "group":
        inner_g = curr.get("expression") or curr.get("value")
        if not isinstance(inner_g, dict):
            break
        curr = inner_g
    kind = curr.get("kind")
    if kind == "borrow":
        return str(curr.get("mode", "in")), _ast_node(curr["value"])
    if kind == "unary":
        op = _op_text(curr.get("operator"))
        if op in {"in", "ref", "out", "move", "shared_mut"}:
            inner = curr.get("value") if "value" in curr else curr.get("operand")
            return op, _ast_node(inner)
    return None


def _type_base_name(type_node: object) -> str | None:
    if not isinstance(type_node, dict):
        return None
    kind = type_node.get("kind")
    if kind == "type":
        name_node = type_node.get("name")
        if isinstance(name_node, dict) and isinstance(name_node.get("text"), str):
            return str(name_node["text"])
    if kind in {"name", "identifier"} and "name" in type_node:
        return _id_text(type_node["name"])
    if kind == "member":
        member_val = type_node.get("name") or type_node.get("member")
        if member_val is not None:
            return _id_text(member_val)
    if kind in {"type_application", "generic_application"}:
        return _type_base_name(type_node.get("callee") or type_node.get("value"))
    if kind == "modified_type":
        return _type_base_name(type_node.get("type"))
    if kind in {"group_type", "group"}:
        return _type_base_name(type_node.get("type") or type_node.get("value"))
    return None


def _type_modifiers(type_node: object) -> set[str]:
    mods: set[str] = set()
    curr = type_node
    while isinstance(curr, dict) and curr.get("kind") in {"modified_type", "group_type", "group"}:
        if curr.get("kind") == "modified_type":
            raw_mods = curr.get("modifiers")
            if isinstance(raw_mods, list):
                for m in raw_mods:
                    mtext = _op_text(m)
                    if mtext:
                        mods.add(mtext)
            raw_mod = curr.get("modifier")
            if raw_mod is not None:
                mtext = _op_text(raw_mod)
                if mtext:
                    mods.add(mtext)
        curr = curr.get("type") or curr.get("value")
    return mods


_SCALAR_VALUE_TYPES = frozenset({
    "Nat",
    "bool",
    "char",
    "Unit",
    "unit",
    "byte",
    "u8",
    "u16",
    "u32",
    "u64",
    "usize",
    "i8",
    "i16",
    "i32",
    "i64",
    "isize",
})


def _is_scalar_value_type(type_node: object) -> bool:
    if not isinstance(type_node, dict) or _type_modifiers(type_node):
        return False
    return _type_base_name(type_node) in _SCALAR_VALUE_TYPES


def _body_statements(raw: object) -> list[dict[str, object]]:
    if raw is None:
        return []
    if isinstance(raw, list):
        return _ast_nodes(raw)
    if isinstance(raw, dict):
        if raw.get("kind") == "block":
            return _ast_nodes(raw.get("statements", []))
        return [cast("dict[str, object]", raw)]
    raise AnalysisRefusalError("expected statement block or list")


def _extract_region_name(type_node: object) -> str | None:
    if not isinstance(type_node, dict):
        return None
    kind = type_node.get("kind")
    if kind == "modified_type":
        lifetime = type_node.get("lifetime")
        if isinstance(lifetime, dict):
            ltext = lifetime.get("text")
            if not isinstance(ltext, str) and isinstance(lifetime.get("name"), dict):
                ltext = cast("dict[str, object]", lifetime["name"]).get("text")
            if isinstance(ltext, str):
                stripped = ltext.removeprefix("'")
                if "." not in stripped and _NAME.fullmatch(stripped):
                    return f"'{stripped}"
        return _extract_region_name(type_node.get("type"))
    if kind in {"type", "type_application", "generic_application"}:
        for arg in _ast_nodes(type_node.get("arguments", [])):
            found = _extract_region_name(arg)
            if found is not None:
                return found
    if kind in {"tuple_type", "function_type"}:
        for item in _ast_nodes(type_node.get("elements", type_node.get("parameters", []))):
            found = _extract_region_name(item)
            if found is not None:
                return found
    return None


def _extract_return_lifetime_place(type_node: object) -> Place | None:
    if not isinstance(type_node, dict):
        return None
    kind = type_node.get("kind")
    if kind == "modified_type":
        lifetime = type_node.get("lifetime")
        if isinstance(lifetime, dict):
            ltext = lifetime.get("text")
            if not isinstance(ltext, str) and isinstance(lifetime.get("name"), dict):
                ltext = cast("dict[str, object]", lifetime["name"]).get("text")
            if isinstance(ltext, str):
                parts = [part for part in ltext.removeprefix("'").split(".") if part]
                if parts and _NAME.fullmatch(parts[0]):
                    return Place(parts[0], tuple(parts[1:]))
        return _extract_return_lifetime_place(type_node.get("type"))
    if kind in {"type", "type_application", "generic_application"}:
        for arg in _ast_nodes(type_node.get("arguments", [])):
            found = _extract_return_lifetime_place(arg)
            if found is not None:
                return found
    if kind in {"tuple_type", "function_type"}:
        for item in _ast_nodes(type_node.get("elements", type_node.get("parameters", []))):
            found = _extract_return_lifetime_place(item)
            if found is not None:
                return found
    return None


def _returns_borrow_from(type_node: object, owner: str | None) -> bool:
    if owner is None or not isinstance(type_node, dict):
        return False
    lifetime = type_node.get("lifetime")
    if isinstance(lifetime, dict):
        text = _op_text(lifetime.get("name")) or _op_text(lifetime)
        if text.removeprefix("'").split(".", 1)[0] == owner:
            return True
    for value in type_node.values():
        if isinstance(value, list):
            if any(_returns_borrow_from(item, owner) for item in value):
                return True
        elif isinstance(value, dict) and _returns_borrow_from(value, owner):
            return True
    return False


def _receiver_parameter(param: dict[str, object]) -> tuple[Mode, str | None, bool] | None:
    if param.get("kind") == "receiver_view_parameter":
        mode = param.get("mode")
        return ("shared" if mode == "in" else "exclusive", _id_text(param["view"]), mode == "ref")
    if param.get("name") is not None:
        return None
    annotation = param.get("type")
    if not isinstance(annotation, dict):
        return None
    raw = annotation.get("type") if annotation.get("kind") == "modified_type" else annotation
    if not isinstance(raw, dict) or raw.get("kind") != "type":
        return None
    name = _op_text(raw.get("name"))
    if name != "this" and not name.startswith("this."):
        return None
    modifier = annotation.get("modifier", "in")
    if not isinstance(modifier, str) or modifier not in {"in", "ref", "out"}:
        raise AnalysisRefusalError("unsupported receiver mode")
    return (
        "shared" if modifier == "in" else "exclusive",
        name[5:] if "." in name else None,
        modifier == "ref",
    )


def _view_field(value: object) -> tuple[str, ...] | None:
    if not isinstance(value, dict):
        return None
    if _is_ident(value):
        name = _id_text(value["name"])
        return () if name == "this" else (name,)
    if value.get("kind") == "member":
        path = _view_field(value.get("value") or value.get("receiver"))
        if path is not None:
            return (*path, _id_text(value.get("name") or value.get("member")))
    return None


def _collect_structs(declarations: list[dict[str, object]]) -> dict[str, _StructInfo]:
    structs: dict[str, _StructInfo] = {}
    for decl in declarations:
        kind = decl.get("kind")
        if kind == "namespace":
            nested = _collect_structs(_ast_nodes(decl.get("declarations", [])))
            if duplicate := structs.keys() & nested.keys():
                raise AnalysisRefusalError(f"ambiguous receiver type {min(duplicate)!r}")
            structs.update(nested)
            continue
        if kind not in {"struct", "record"}:
            continue
        name = _id_text(decl["name"])
        field_paths: list[tuple[str, ...]] = []
        views: dict[str, tuple[str, ...]] = {}
        invariants: list[str] = []
        methods: dict[str, _Receiver | None] = {}
        field_types: dict[str, str | None] = {}
        for param_decl in _ast_nodes(decl.get("parameters", [])):
            if param_decl.get("kind") in {"parameter", "field"} and "name" in param_decl:
                fname = _id_text(param_decl["name"])
                field_types[fname] = _type_base_name(param_decl.get("type"))
                if (fname,) not in field_paths:
                    field_paths.append((fname,))
        for field_decl in _ast_nodes(decl.get("fields", [])):
            if field_decl.get("kind") == "field":
                fname = _id_text(field_decl["name"])
                field_types[fname] = _type_base_name(field_decl.get("type"))
                if (fname,) not in field_paths:
                    field_paths.append((fname,))
        member_items = [
            *_ast_nodes(decl.get("members", [])),
            *_ast_nodes(decl.get("declarations", [])),
        ]
        for member in member_items:
            mkind = member.get("kind")
            if mkind == "field":
                fname = _id_text(member["name"])
                field_types[fname] = _type_base_name(member.get("type"))
                if (fname,) not in field_paths:
                    field_paths.append((fname,))
            elif mkind == "view":
                vname = _id_text(member["name"])
                if "parts" in member:
                    parts = _ast_nodes(member["parts"])
                    # A compound or indexed view needs range evidence. Cover its whole receiver.
                    path = _view_field(parts[0].get("value")) if len(parts) == 1 else None
                    views[vname] = path or ()
                    continue
                clauses = _ast_nodes(member.get("clauses", []))
                primary_field: str | None = None
                for clause in clauses:
                    if "name" in clause:
                        primary_field = _id_text(clause["name"])
                        break
                if primary_field is not None:
                    if (primary_field,) not in field_paths:
                        field_paths.append((primary_field,))
                    vpath = (primary_field, vname)
                else:
                    vpath = (vname,)
                views[vname] = vpath
                if vpath not in field_paths:
                    field_paths.append(vpath)
            elif mkind in {"method", "function", "definition"}:
                method_name = _id_text(member["name"])
                parameters = _ast_nodes(member.get("parameters", []))
                receiver = _receiver_parameter(parameters[0]) if parameters else None
                if receiver is None and kind == "record":
                    receiver = ("shared", None, False)
                result = member.get("result") or member.get("return_type")
                retained = _returns_borrow_from(result, "this")
                if receiver is None or method_name in methods:
                    methods[method_name] = None
                else:
                    mode, view, two_phase = receiver
                    methods[method_name] = _Receiver(
                        mode, view, retained, two_phase, scalar_result=_is_scalar_value_type(result)
                    )
        for contract in _ast_nodes(decl.get("contracts", [])):
            ckind = contract.get("kind")
            if ckind == "invariant" or (ckind == "contract" and contract.get("role") == "invariant"):
                label = contract.get("label") or contract.get("name")
                if isinstance(label, dict) and isinstance(label.get("text"), str):
                    cname = _id_text(label)
                else:
                    cname = name
                if cname not in invariants:
                    invariants.append(cname)
        for member in member_items:
            if member.get("kind") == "view" and "parts" in member:
                view = _id_text(member["name"])
                path = views[view]
                views[view] = path[:1] if path and path[0] in field_types else ()
        if name in structs:
            raise AnalysisRefusalError(f"ambiguous receiver type {name!r}")
        structs[name] = _StructInfo(tuple(field_paths), views, tuple(invariants), methods, field_types)
    return structs


def _find_functions(
    declarations: list[dict[str, object]],
    enclosing_type: str | None = None,
) -> list[tuple[str, dict[str, object], str | None]]:
    found: list[tuple[str, dict[str, object], str | None]] = []
    for decl in declarations:
        kind = decl.get("kind")
        if kind == "namespace":
            found.extend(_find_functions(_ast_nodes(decl.get("declarations", [])), enclosing_type))
        elif kind in {"struct", "record"}:
            tname = _id_text(decl["name"])
            member_items = [
                *_ast_nodes(decl.get("members", [])),
                *_ast_nodes(decl.get("declarations", [])),
            ]
            for member in member_items:
                if member.get("kind") in {"method", "function", "definition"} and (
                    member.get("body") is not None or member.get("value") is not None
                ):
                    mname = _id_text(member["name"])
                    found.append((f"{tname}.{mname}", member, tname))
                    found.append((mname, member, tname))
        elif kind == "impl":
            tname = _type_base_name(decl.get("target") or decl.get("type"))
            member_items = [
                *_ast_nodes(decl.get("members", [])),
                *_ast_nodes(decl.get("declarations", [])),
            ]
            for member in member_items:
                if member.get("kind") in {"method", "function", "definition"} and (
                    member.get("body") is not None or member.get("value") is not None
                ):
                    mname = _id_text(member["name"])
                    if tname is not None:
                        found.append((f"{tname}.{mname}", member, tname))
                    found.append((mname, member, tname))
        elif kind in {"function", "method", "definition"} and (
            decl.get("body") is not None or decl.get("value") is not None
        ):
            fname = _id_text(decl["name"])
            if enclosing_type is not None:
                found.append((f"{enclosing_type}.{fname}", decl, enclosing_type))
            found.append((fname, decl, enclosing_type))
    return found


_BUILTIN_CONTAINERS = frozenset({"Vec", "Seq", "Slots", "Span", "List", "Map"})
_UNSTABLE_CONTAINER_METHODS = frozenset({
    "clear",
    "Clear",
    "push",
    "Push",
    "pop",
    "Pop",
    "resize",
    "Resize",
    "truncate",
    "Truncate",
    "insert",
    "Insert",
    "remove",
    "Remove",
    "append",
    "Append",
    "empty",
    "Empty",
    "allocvacant",
    "AllocVacant",
    "restore",
    "Restore",
})
_READONLY_CONTAINER_METHODS = frozenset({
    "count",
    "Count",
    "length",
    "Length",
    "isempty",
    "IsEmpty",
    "canread",
    "CanRead",
    "canwrite",
    "CanWrite",
    "first",
    "First",
    "last",
    "Last",
    "livecount",
    "LiveCount",
})


def _collect_function_returns(
    declarations: list[dict[str, object]],
    enclosing_type: str | None = None,
) -> dict[str, str | None]:
    returns: dict[str, str | None] = {}
    for decl in declarations:
        kind = decl.get("kind")
        if kind == "namespace":
            returns.update(
                _collect_function_returns(_ast_nodes(decl.get("declarations", [])), enclosing_type)
            )
        elif kind in {"struct", "record"}:
            tname = _id_text(decl["name"])
            member_items = [
                *_ast_nodes(decl.get("members", [])),
                *_ast_nodes(decl.get("declarations", [])),
            ]
            for member in member_items:
                if member.get("kind") in {"method", "function", "definition"}:
                    mname = _id_text(member["name"])
                    rtype = _type_base_name(member.get("result") or member.get("return_type"))
                    returns[f"{tname}.{mname}"] = rtype
                    returns.setdefault(mname, rtype)
        elif kind == "impl":
            tname = _type_base_name(decl.get("target") or decl.get("type"))
            member_items = [
                *_ast_nodes(decl.get("members", [])),
                *_ast_nodes(decl.get("declarations", [])),
            ]
            for member in member_items:
                if member.get("kind") in {"method", "function", "definition"}:
                    mname = _id_text(member["name"])
                    rtype = _type_base_name(member.get("result") or member.get("return_type"))
                    if tname is not None:
                        returns[f"{tname}.{mname}"] = rtype
                    returns.setdefault(mname, rtype)
        elif kind in {"function", "method", "definition"}:
            fname = _id_text(decl["name"])
            rtype = _type_base_name(decl.get("result") or decl.get("return_type"))
            if enclosing_type is not None:
                returns[f"{enclosing_type}.{fname}"] = rtype
            returns[fname] = rtype
    return returns


class _FunctionLowerer:
    def __init__(
        self,
        fn_name: str,
        fn_node: dict[str, object],
        enclosing_type: str | None,
        structs: dict[str, _StructInfo],
        function_returns: dict[str, str | None] | None = None,
        proved_facts: ProvedFacts | Mapping[str, object] | None = None,
    ) -> None:
        self.fn_name = fn_name
        self.fn_node = fn_node
        self.result_parameters: set[str] = set()
        self.visible_results: set[str] = set()
        self.result_names: set[str] = set()
        self.result_bindings: dict[int, set[str]] = {}
        self.result_events: dict[str, tuple[str, set[str]]] = {}
        self.in_proof = False
        self.in_receiver_argument = False
        self.enclosing_type = enclosing_type
        self.proved_facts = _normalize_proved_facts(proved_facts)
        merged_structs = dict(structs)
        if self.proved_facts is not None:
            for tname, extra_views in self.proved_facts.record_views.items():
                if tname in merged_structs:
                    info = merged_structs[tname]
                    views = dict(info.views)
                    views.update(extra_views)
                    fields = list(info.fields)
                    for vpath in extra_views.values():
                        if vpath and vpath not in fields:
                            fields.append(vpath)
                    merged_structs[tname] = _StructInfo(
                        tuple(fields), views, info.invariants, dict(info.methods), dict(info.field_types)
                    )
                else:
                    merged_structs[tname] = _StructInfo(
                        tuple(p for p in extra_views.values() if p),
                        dict(extra_views),
                        (),
                    )
            for tname, extra_methods in self.proved_facts.methods.items():
                if tname in merged_structs:
                    info = merged_structs[tname]
                    methods = dict(info.methods)
                    methods.update(extra_methods)
                    merged_structs[tname] = _StructInfo(
                        info.fields, dict(info.views), info.invariants, methods, dict(info.field_types)
                    )
                else:
                    merged_structs[tname] = _StructInfo((), {}, (), dict(extra_methods))
        self.structs = merged_structs
        self.function_returns: dict[str, str | None] = dict(function_returns or {})
        if self.proved_facts is not None:
            self.function_returns.update(self.proved_facts.function_returns)
        self.return_summaries: dict[str, str] = (
            dict(self.proved_facts.return_summaries) if self.proved_facts is not None else {}
        )
        self.checked_receivers: dict[tuple[int, ...], _Receiver | None] = {}
        self.checked_scalar_calls: set[tuple[int, ...]] = set()
        self.owners: dict[str, Owner] = {}
        self.owner_types: dict[str, str] = {}
        self.owner_type_nodes: dict[str, object] = {}
        self.owner_fields: dict[str, set[tuple[str, ...]]] = {}
        self.owner_views: dict[str, dict[str, tuple[str, ...]]] = {}
        self.owner_invariants: dict[str, list[str]] = {}
        # Map variable name -> canonical handle name (for loans or wrappers).
        self.handles: dict[str, str] = {}
        # Map loan handle name -> Place.
        self.handle_places: dict[str, Place] = {}
        self.handle_modes: dict[str, Mode] = {}
        self.handle_origins: dict[str, str] = {}
        self.positive_vars: set[str] = set()
        self.used_binders: set[str] = set()
        self.nodes: list[Node] = []
        self.edges: dict[str, list[str]] = {}
        self.events: dict[str, Event] = {}
        self.node_sites: dict[str, dict[str, object]] = {}
        self.current_site: dict[str, object] = fn_node
        self.counter = 0
        self.loan_counter = 0
        return_type_node = fn_node.get("return_type") or fn_node.get("result")
        self.return_lifetime_place = _extract_return_lifetime_place(return_type_node)
        self.return_origin = _extract_region_name(return_type_node)
        self.returns_scalar_value = _is_scalar_value_type(return_type_node)

    def _fresh_node(self, prefix: str = "n", event: Event | None = None) -> str:
        self.counter += 1
        name = f"{prefix}_{self.counter}"
        self.events[name] = Nop() if event is None else event
        self.edges[name] = []
        self.node_sites[name] = self.current_site
        return name

    def _fresh_loan(self, prefix: str = "loan") -> str:
        self.loan_counter += 1
        return f"_{prefix}_{self.loan_counter}"

    def _fresh_binder(self, bname: str) -> str:
        if bname not in self.owners and bname not in self.used_binders:
            self.used_binders.add(bname)
            return bname
        fresh = self._fresh_loan(bname)
        self.used_binders.add(fresh)
        return fresh

    def _connect(self, src: str | None, dst: str) -> None:
        if src is not None and isinstance(self.events.get(src), Return):
            return
        if src is not None and dst not in self.edges[src]:
            self.edges[src].append(dst)

    def _emit(self, current: str | None, event: Event, prefix: str = "n") -> str:
        if (
            current is not None
            and self.events[current] == Nop()
            and not self.edges[current]
            and not prefix.startswith(("join", "header"))
        ):
            self.events[current] = event
            self.node_sites[current] = self.current_site
            return current
        nxt = self._fresh_node(prefix, event)
        self._connect(current, nxt)
        return nxt

    def _result_event(self, current: str | None, action: str, paths: set[str]) -> str | None:
        if current is None or self.in_proof or not paths:
            return current
        event = self._fresh_node("result")
        self._connect(current, event)
        self.result_events[event] = (action, paths)
        # An independent successor prevents Nop compression from relocating this event's site.
        end = self._fresh_node("after_result")
        self._connect(event, end)
        return end

    def _visible_result_paths(self, name: str) -> set[str]:
        return {path for path in self.visible_results if path == name or path.startswith(name + ".")}

    def _use_result(self, current: str | None, name: str, *, case_only: bool = False) -> str | None:
        paths = self.visible_results & {name} if case_only else self._visible_result_paths(name)
        return self._result_event(current, "use", paths)

    def unexamined_result(self, graph: Graph) -> tuple[str, dict[str, object]] | None:
        if not self.result_names:
            return None
        incoming: dict[str, frozenset[str]] = {graph.entry: frozenset(self.result_parameters)}
        pending = [graph.entry]
        while pending:
            point = pending.pop()
            owed = incoming[point]
            if point in self.result_events:
                action, paths = self.result_events[point]
                if action != "use" and (unhandled := paths & owed):
                    return min(unhandled), self.node_sites[point]
                if action == "new":
                    owed = owed | paths
                elif action == "use":
                    owed = owed - paths
            if isinstance(self.events[point], Return) and owed:
                return min(owed), self.node_sites[point]
            for succ in self.edges[point]:
                merged = incoming[succ] | owed if succ in incoming else owed
                if succ not in incoming or merged != incoming[succ]:
                    incoming[succ] = merged
                    pending.append(succ)
        return None

    def _register_owner(
        self,
        name: str,
        *,
        borrowed: bool,
        type_name: str | None = None,
        type_node: object = None,
        origin: str | None = None,
        mode: Mode | None = None,
    ) -> None:
        if not _NAME.fullmatch(name) or (name in self.used_binders and name not in self.owners):
            return
        if name not in self.owner_fields:
            self.owner_fields[name] = set()
            self.owner_views[name] = {}
            self.owner_invariants[name] = []
        if type_node is not None:
            self.owner_type_nodes[name] = type_node
        if type_name is not None:
            self.owner_types[name] = type_name
            info = self.structs.get(type_name)
            if info is not None:
                self.owner_fields[name].update(info.fields)
                self.owner_views[name].update(info.views)
                for inv in info.invariants:
                    if inv not in self.owner_invariants[name]:
                        self.owner_invariants[name].append(inv)
        prev = self.owners.get(name)
        eff_origin = origin if origin is not None else (prev.origin if prev is not None else None)
        eff_mode = mode if mode is not None else (prev.mode if prev is not None else None)
        self.owners[name] = Owner(
            name,
            borrowed=borrowed,
            fields=tuple(sorted(self.owner_fields[name])),
            invariants=tuple(self.owner_invariants[name]),
            origin=eff_origin,
            mode=eff_mode,
        )

    def _add_owner_field(self, owner_name: str, path: tuple[str, ...]) -> None:
        if owner_name not in self.owners or not path or "*" in path:
            return
        self.owner_fields[owner_name].add(path)
        existing = self.owners[owner_name]
        self.owners[owner_name] = Owner(
            owner_name,
            borrowed=existing.borrowed,
            fields=tuple(sorted(self.owner_fields[owner_name])),
            invariants=existing.invariants,
            origin=existing.origin,
            mode=existing.mode,
        )

    def _add_owner_invariants(self, owner_name: str, clauses: Sequence[str]) -> None:
        if owner_name not in self.owners:
            self._register_owner(owner_name, borrowed=True)
        inv_list = self.owner_invariants[owner_name]
        for clause in clauses:
            if _NAME.fullmatch(clause) and clause not in inv_list:
                inv_list.append(clause)
        existing = self.owners[owner_name]
        self.owners[owner_name] = Owner(
            owner_name,
            borrowed=existing.borrowed,
            fields=existing.fields,
            invariants=tuple(inv_list),
            origin=existing.origin,
            mode=existing.mode,
        )

    def _collect_signature_facts(self) -> None:
        if self.enclosing_type is not None:
            self._register_owner("this", borrowed=True, type_name=self.enclosing_type)
        for param in _ast_nodes(self.fn_node.get("parameters", [])):
            pkind = param.get("kind")
            if _receiver_parameter(param) is not None:
                continue
            if pkind == "parameter" and param.get("name") is not None:
                pname = _id_text(param["name"])
                pmode = param.get("mode", "value")
                ptype_node = param.get("parameter_type") or param.get("type")
                ptype = _type_base_name(ptype_node)
                mods = _type_modifiers(ptype_node)
                borrowed = (
                    (
                        pmode in {"in", "ref", "out", "shared_mut"}
                        or bool(mods & {"in", "ref", "out", "shared_mut"})
                        or ptype in {"Span", "Slots"}
                    )
                    and pmode != "owned"
                    and "owned" not in mods
                )
                origin = _extract_region_name(ptype_node)
                mode: Mode | None = None
                if pmode == "shared_mut" or "shared_mut" in mods:
                    mode = "shared_mut"
                elif pmode in {"ref", "out"} or bool(mods & {"ref", "out"}):
                    mode = "exclusive"
                elif pmode == "in" or "in" in mods:
                    mode = "shared"
                self._register_owner(
                    pname,
                    borrowed=borrowed,
                    type_name=ptype,
                    type_node=ptype_node,
                    origin=origin,
                    mode=mode,
                )

        for contract in _ast_nodes(self.fn_node.get("contracts", [])):
            ckind = contract.get("kind")
            if ckind == "effects":
                for eff in _ast_nodes(contract.get("effects", [])):
                    if eff.get("kind") == "call":
                        for arg in _ast_nodes(eff.get("arguments", [])):
                            val = (
                                _ast_node(arg["value"])
                                if arg.get("kind") in {"call_argument", "argument"}
                                else arg
                            )
                            place = self._try_place(val)
                            if place is not None and place.owner in self.owners and place.fields:
                                self._add_owner_field(place.owner, place.fields)
            elif ckind == "contract" and contract.get("role") == "effects":
                eff_val = contract.get("value")
                if isinstance(eff_val, dict) and eff_val.get("kind") == "call":
                    for arg in _ast_nodes(eff_val.get("arguments", [])):
                        val = (
                            _ast_node(arg["value"])
                            if arg.get("kind") in {"call_argument", "argument"}
                            else arg
                        )
                        place = self._try_place(val)
                        if place is not None and place.owner in self.owners and place.fields:
                            self._add_owner_field(place.owner, place.fields)

        if not self.owners:
            self._register_owner("_unit", borrowed=False)

    def _unwrap_type_node(self, type_node: object) -> object:
        curr = type_node
        while isinstance(curr, dict) and curr.get("kind") in {"modified_type", "group_type", "group"}:
            curr = curr.get("type") or curr.get("value")
        return curr

    def _place_type_info(self, place: Place) -> tuple[str | None, object]:
        type_node = self.owner_type_nodes.get(place.owner)
        type_name = self.owner_types.get(place.owner)
        for component in place.fields:
            if component == "*" or _is_symbolic(component):
                unwrapped = self._unwrap_type_node(type_node)
                if (
                    type_name in _BUILTIN_CONTAINERS
                    and isinstance(unwrapped, dict)
                    and unwrapped.get("kind") in {"type", "type_application", "generic_application"}
                ):
                    args = _ast_nodes(unwrapped.get("arguments", []))
                    if args:
                        type_node = args[0]
                        type_name = _type_base_name(type_node)
                        continue
                type_name = None
                type_node = None
            else:
                info = self.structs.get(type_name) if type_name is not None else None
                type_name = info.field_types.get(component) if info is not None else None
                type_node = None
        return type_name, type_node

    def _place_struct(self, place: Place) -> _StructInfo | None:
        type_name, _ = self._place_type_info(place)
        return self.structs.get(type_name) if type_name is not None else None

    def _index_segment(self, expr: dict[str, object]) -> str:
        if expr.get("kind") != "index":
            return "*"
        idx = expr.get("index")
        while isinstance(idx, dict) and idx.get("kind") == "group":
            idx = idx.get("expression") or idx.get("value")
        if isinstance(idx, dict) and _is_ident(idx):
            idx_name = _id_text(idx["name"])
            if _NAME.fullmatch(idx_name) and idx_name not in self.handles:
                return f"@{idx_name}"
        return "*"

    def _infer_expr_type(self, expr: dict[str, object]) -> str | None:
        curr = expr
        while curr.get("kind") == "group":
            inner = curr.get("expression") or curr.get("value")
            if not isinstance(inner, dict):
                break
            curr = inner
        place = self._try_place(curr)
        if place is not None:
            return self._place_type_info(place)[0]
        kind = curr.get("kind")
        if kind == "call":
            callee = _ast_node(curr["callee"])
            while callee.get("kind") in {"generic_application", "group"}:
                callee = _ast_node(callee["value"])
            if _is_ident(callee):
                cname = _id_text(callee["name"])
                if cname in self.structs:
                    return cname
                return self.function_returns.get(cname)
            if callee.get("kind") == "member":
                recv = _ast_node(callee.get("receiver") or callee["value"])
                mname = _id_text(callee.get("name") or callee.get("member"))
                recv_type = _id_text(recv["name"]) if _is_ident(recv) else self._infer_expr_type(recv)
                if recv_type is not None and f"{recv_type}.{mname}" in self.function_returns:
                    return self.function_returns[f"{recv_type}.{mname}"]
                return self.function_returns.get(mname)
        if kind == "if_expression":
            then_t = self._infer_expr_type(_ast_node(curr.get("then_branch") or curr["then"]))
            else_t = self._infer_expr_type(_ast_node(curr.get("else_branch") or curr["else"]))
            if then_t is not None and then_t == else_t:
                return then_t
        return None

    def _is_unstable_call(self, callee: dict[str, object]) -> bool:
        curr = callee
        while curr.get("kind") in {"generic_application", "group"}:
            curr = _ast_node(curr["value"])
        if curr.get("kind") == "member":
            mname = _id_text(curr.get("name") or curr.get("member"))
            return mname in _UNSTABLE_CONTAINER_METHODS
        if _is_ident(curr):
            return _id_text(curr["name"]) in _UNSTABLE_CONTAINER_METHODS
        return False

    def _is_unstable_assignment(self, target_place: Place | None, value_expr: dict[str, object]) -> bool:
        curr = value_expr
        while curr.get("kind") == "group":
            inner = curr.get("expression") or curr.get("value")
            if not isinstance(inner, dict):
                break
            curr = inner
        if curr.get("kind") == "call" and self._is_unstable_call(_ast_node(curr["callee"])):
            return True
        if target_place is not None:
            tname, _ = self._place_type_info(target_place)
            if tname in _BUILTIN_CONTAINERS:
                return True
        return False

    def _try_place(self, expr: dict[str, object]) -> Place | None:
        kind = expr.get("kind")
        if _is_ident(expr):
            name = _id_text(expr["name"])
            if name in self.handles and name in self.handle_places:
                return self.handle_places[name]
            if name == "this" and "this" not in self.owners:
                self._register_owner("this", borrowed=True, type_name=self.enclosing_type)
            if name in self.owners:
                return Place(name)
            return None
        if kind == "group":
            inner = expr.get("expression") or expr.get("value")
            if isinstance(inner, dict):
                return self._try_place(inner)
        if kind == "member":
            recv = expr.get("receiver") or expr.get("value")
            member_val = expr.get("member") or expr.get("name")
            if isinstance(recv, dict) and member_val is not None:
                base = self._try_place(recv)
                if base is not None:
                    member_name = _id_text(member_val)
                    view_path = self.owner_views.get(base.owner, {}).get(member_name)
                    if view_path is not None and not base.fields:
                        return Place(base.owner, view_path)
                    info = self._place_struct(base)
                    if info is not None and (member_name,) not in info.fields:
                        return base
                    return Place(base.owner, (*base.fields, member_name))
        if kind in {"index", "range_index"}:
            recv = expr.get("receiver") or expr.get("value")
            if isinstance(recv, dict):
                base = self._try_place(recv)
                if base is not None:
                    return Place(base.owner, (*base.fields, self._index_segment(expr)))
        borrow_info = _extract_borrow_expr(expr)
        if borrow_info is not None:
            return self._try_place(borrow_info[1])
        return None

    def _resolve_borrow_target(
        self, current: str | None, expr: dict[str, object]
    ) -> tuple[str | None, str, Place]:
        # Evaluate any index subexpressions first.
        current = self._eval_index_subexpressions(current, expr)
        if _is_ident(expr):
            name = _id_text(expr["name"])
            if name in self.handles:
                place = self.handle_places.get(name, Place(next(iter(self.owners))))
                return current, self.handles[name], place
            if name == "this" and "this" not in self.owners:
                self._register_owner("this", borrowed=True, type_name=self.enclosing_type)
            if name not in self.owners:
                self._register_owner(name, borrowed=False)
            return current, name, Place(name)

        root = expr
        fields: list[str] = []
        while root.get("kind") in {"member", "index", "range_index", "group"}:
            rkind = root.get("kind")
            if rkind == "group":
                root = cast("dict[str, object]", root.get("expression") or root.get("value"))
            elif rkind == "member":
                fields.append(_id_text(root.get("member") or root["name"]))
                root = cast("dict[str, object]", root.get("receiver") or root["value"])
            else:
                fields.append(self._index_segment(root))
                root = cast("dict[str, object]", root.get("receiver") or root["value"])
        fields.reverse()
        if _is_ident(root):
            rname = _id_text(root["name"])
            if rname in self.handles:
                base_place = self.handle_places.get(rname, Place(next(iter(self.owners))))
                if base_place.owner in self.owners and fields and "*" not in (*base_place.fields, *fields):
                    self._add_owner_field(base_place.owner, (*base_place.fields, *fields))
                return current, self.handles[rname], Place(base_place.owner, (*base_place.fields, *fields))
            if rname == "this" and "this" not in self.owners:
                self._register_owner("this", borrowed=True, type_name=self.enclosing_type)
            if rname not in self.owners:
                self._register_owner(rname, borrowed=False)
            if len(fields) == 1 and fields[0] in self.owner_views.get(rname, {}):
                vpath = self.owner_views[rname][fields[0]]
                return current, rname, Place(rname, vpath)
            if fields and "*" not in fields:
                self._add_owner_field(rname, tuple(fields))
            return current, rname, Place(rname, tuple(fields))

        current, _ = self._lower_expr(current, expr)
        tmp_owner = self._fresh_loan("tmp")
        self._register_owner(tmp_owner, borrowed=False)
        return current, tmp_owner, Place(tmp_owner)

    def _eval_index_subexpressions(
        self, current: str | None, expr: dict[str, object]
    ) -> str | None:
        kind = expr.get("kind")
        if kind == "member":
            recv = expr.get("receiver") or expr.get("value")
            if isinstance(recv, dict):
                return self._eval_index_subexpressions(current, recv)
        elif kind == "index":
            recv = expr.get("receiver") or expr.get("value")
            idx = expr.get("index")
            if isinstance(recv, dict):
                current = self._eval_index_subexpressions(current, recv)
            if isinstance(idx, dict):
                if idx.get("kind") == "range":
                    start = idx.get("start")
                    end = idx.get("end")
                    if isinstance(start, dict):
                        current, _ = self._lower_expr(current, start)
                    if isinstance(end, dict):
                        current, _ = self._lower_expr(current, end)
                else:
                    current, _ = self._lower_expr(current, idx)
        elif kind == "range_index":
            recv = expr.get("receiver") or expr.get("value")
            start = expr.get("start")
            end = expr.get("end")
            if isinstance(recv, dict):
                current = self._eval_index_subexpressions(current, recv)
            if isinstance(start, dict):
                current, _ = self._lower_expr(current, start)
            if isinstance(end, dict):
                current, _ = self._lower_expr(current, end)
        return current

    def _pattern_binders(self, pattern: dict[str, object]) -> list[str]:
        pkind = pattern.get("kind")
        if pkind == "binding_pattern":
            return [_id_text(pattern["name"])]
        if pkind == "labeled_pattern":
            inner = pattern.get("pattern")
            return self._pattern_binders(_ast_node(inner)) if inner is not None else []
        if pkind == "group_pattern":
            return self._pattern_binders(_ast_node(pattern["pattern"]))
        if pkind in {"tuple_pattern", "constructor_pattern"}:
            if pkind == "tuple_pattern":
                items = pattern.get("elements") if "elements" in pattern else pattern.get("patterns", [])
            else:
                items = pattern.get("arguments", [])
            result: list[str] = []
            for item in _ast_nodes(items):
                result.extend(self._pattern_binders(item))
            return result
        return []

    def _bind_pattern_from_captures(
        self,
        current: str | None,
        pattern: dict[str, object],
        captures: tuple[str, ...],
        source_place: Place | None = None,
    ) -> str | None:
        binders = self._pattern_binders(pattern)
        for bname in binders:
            if not _NAME.fullmatch(bname) or bname == "_" or bname[0].isupper():
                continue
            if captures:
                if len(captures) == 1 and captures[0] in self.handle_places:
                    parent_handle = captures[0]
                    place = self.handle_places[parent_handle]
                    mode = self.handle_modes.get(parent_handle, "shared")
                    loan_name = self._fresh_binder(bname)
                    current = self._emit(
                        current,
                        Borrow(Loan(loan_name, parent_handle, place, mode=mode)),
                        f"pat_{bname}",
                    )
                    self.handles[bname] = loan_name
                    self.handle_places[bname] = place
                    self.handle_modes[bname] = mode
                else:
                    bind_name = self._fresh_binder(bname)
                    current = self._emit(current, Bind(bind_name, captures), f"pat_{bname}")
                    self.handles[bname] = bind_name
            elif source_place is not None and self.return_lifetime_place is not None:
                place = self.return_lifetime_place
                if place.owner in self.owners:
                    if place.fields:
                        self._add_owner_field(place.owner, place.fields)
                    loan_name = self._fresh_binder(bname)
                    current = self._emit(
                        current,
                        Borrow(Loan(loan_name, place.owner, place, mode="shared")),
                        f"pat_{bname}",
                    )
                    self.handles[bname] = loan_name
                    self.handle_places[bname] = place
                    self.handle_modes[bname] = "shared"
            else:
                self.handles.pop(bname, None)
                self._register_owner(bname, borrowed=False)
        return current

    @staticmethod
    def _unwrap_group_expr(node: object) -> dict[str, object] | None:
        curr = node
        while isinstance(curr, dict) and curr.get("kind") == "group":
            curr = curr.get("expression") or curr.get("value")
        return cast("dict[str, object]", curr) if isinstance(curr, dict) else None

    @staticmethod
    def _nat_literal(node: object) -> int | None:
        if isinstance(node, dict) and node.get("kind") == "nat":
            raw = node.get("value")
            if isinstance(raw, str) and raw.isdigit():
                return int(raw)
        return None

    @classmethod
    def _extract_add_offset(cls, node: object) -> tuple[str, int | None, str | None] | None:
        unwrapped = cls._unwrap_group_expr(node)
        if unwrapped is None or unwrapped.get("kind") != "binary":
            return None
        if _op_text(unwrapped.get("operator")) != "+":
            return None
        left = cls._unwrap_group_expr(unwrapped.get("left"))
        right = cls._unwrap_group_expr(unwrapped.get("right"))
        if left is None or right is None:
            return None
        if _is_ident(left):
            base = _id_text(left["name"])
            lit = cls._nat_literal(right)
            if lit is not None and _NAME.fullmatch(base):
                return base, lit, None
            if _is_ident(right):
                offset_var = _id_text(right["name"])
                if _NAME.fullmatch(base) and _NAME.fullmatch(offset_var):
                    return base, None, offset_var
        if _is_ident(right):
            base = _id_text(right["name"])
            lit = cls._nat_literal(left)
            if lit is not None and _NAME.fullmatch(base):
                return base, lit, None
        return None

    def _extract_index_ne(self, operand: dict[str, object]) -> tuple[str, str, bool] | None:
        curr = operand
        negated = False
        while True:
            if curr.get("kind") == "group":
                curr = _ast_node(curr.get("expression") or curr["value"])
                continue
            if curr.get("kind") == "unary" and _op_text(curr.get("operator")) == "!":
                negated = not negated
                curr = _ast_node(curr.get("operand") if "operand" in curr else curr["value"])
                continue
            break
        if curr.get("kind") != "binary":
            return None
        op = _op_text(curr.get("operator"))
        left = self._unwrap_group_expr(curr["left"])
        right = self._unwrap_group_expr(curr["right"])
        if left is None or right is None:
            return None

        # Check `a + m <= b` / `b >= a + m` / `a + m < b` / `b > a + m` when offset > 0 (or `<`).
        if not negated and op in {"<=", ">=", "<", ">"}:
            add_pair: tuple[tuple[str, int | None, str | None], str, bool] | None = None
            if op in {"<=", "<"} and (add_info := self._extract_add_offset(left)) is not None and _is_ident(right):
                add_pair = (add_info, _id_text(right["name"]), op == "<")
            elif op in {">=", ">"} and (add_info := self._extract_add_offset(right)) is not None and _is_ident(left):
                add_pair = (add_info, _id_text(left["name"]), op == ">")
            if add_pair is not None:
                (base, lit, offset_var), other_name, strict = add_pair
                if base != other_name and _NAME.fullmatch(other_name):
                    positive = strict or (lit is not None and lit >= 1) or (
                        offset_var is not None and offset_var in self.positive_vars
                    )
                    if positive:
                        return f"@{base}", f"@{other_name}", True

        if op in {"!=", "<", ">"}:
            if negated and op in {"<", ">"}:
                return None
            on_true = not negated
        elif op == "==":
            on_true = negated
        else:
            return None

        if _is_ident(left) and _is_ident(right):
            lname = _id_text(left["name"])
            rname = _id_text(right["name"])
            if lname != rname and _NAME.fullmatch(lname) and _NAME.fullmatch(rname):
                return f"@{lname}", f"@{rname}", on_true
        if on_true:
            for ident_side, lit_side, is_gt in (
                (left, right, op == ">"),
                (right, left, op == "<"),
            ):
                if _is_ident(ident_side) and self._nat_literal(lit_side) == 0:
                    iname = _id_text(ident_side["name"])
                    if _NAME.fullmatch(iname) and (op == "!=" or is_gt or (op == "==" and negated)):
                        self.positive_vars.add(iname)
                        return f"@{iname}", "@_0", True
        return None

    def _extract_no_realloc_guard(self, operand: dict[str, object]) -> Place | None:
        curr = self._unwrap_group_expr(operand)
        if curr is None or curr.get("kind") != "binary":
            return None
        op = _op_text(curr.get("operator"))
        if op not in {"<", ">"}:
            return None
        left = self._unwrap_group_expr(curr["left"])
        right = self._unwrap_group_expr(curr["right"])
        if op == ">":
            left, right = right, left
        if left is None or right is None:
            return None
        if left.get("kind") != "member" or right.get("kind") != "member":
            return None
        len_name = _id_text(left.get("member") or left.get("name"))
        cap_name = _id_text(right.get("member") or right.get("name"))
        if len_name not in {"len", "Length", "LiveCount"} or cap_name not in {"cap", "Capacity"}:
            return None
        left_recv = self._unwrap_group_expr(left.get("receiver") or left.get("value"))
        right_recv = self._unwrap_group_expr(right.get("receiver") or right.get("value"))
        if left_recv is None or right_recv is None:
            return None
        lplace = self._try_place(left_recv)
        rplace = self._try_place(right_recv)
        if lplace is not None and lplace == rplace:
            return lplace
        return None

    def _emit_conjunctive_index_facts(self, current: str, expr: object) -> str:
        if not isinstance(expr, dict):
            return current
        pending = [expr]
        while pending:
            operand = pending.pop()
            if operand.get("kind") == "group":
                inner = operand.get("expression") or operand.get("value")
                if isinstance(inner, dict):
                    pending.append(inner)
                continue
            if operand.get("kind") == "binary" and _op_text(operand.get("operator")) == "&&":
                pending.extend((_ast_node(operand["right"]), _ast_node(operand["left"])))
                continue
            ne_fact = self._extract_index_ne(operand)
            if ne_fact is not None and ne_fact[2]:
                current = self._emit(current, AssumeIndexNe(ne_fact[0], ne_fact[1]), "assume_ne")
            norealloc = self._extract_no_realloc_guard(operand)
            if norealloc is not None:
                current = self._emit(current, AssumeNoRealloc(norealloc), "assume_norealloc")
        return current

    def _lower_condition(
        self, current: str | None, condition: dict[str, object],
    ) -> tuple[str | None, str, dict[str, str]]:
        pending = [condition]
        failure = self._fresh_node("if_else")
        outer_handles: dict[str, str] | None = None
        conjunct_count = 0
        else_fact: tuple[str, str] | None = None
        while pending:
            operand = pending.pop()
            if operand.get("kind") == "group":
                pending.append(_ast_node(operand.get("expression") or operand["value"]))
                continue
            if operand.get("kind") == "binary" and _op_text(operand["operator"]) == "&&":
                pending.extend((_ast_node(operand["right"]), _ast_node(operand["left"])))
                continue
            conjunct_count += 1
            if operand.get("kind") == "binary" and _op_text(operand["operator"]) == "||":
                left_then, left_else, saved_or = self._lower_condition(current, _ast_node(operand["left"]))
                if outer_handles is None:
                    outer_handles = dict(saved_or)
                self.handles = dict(saved_or)
                right_then, right_else, _ = self._lower_condition(left_else, _ast_node(operand["right"]))
                self.handles = dict(saved_or)
                or_then = self._fresh_node("or_then")
                self._connect(left_then, or_then)
                self._connect(right_then, or_then)
                self._connect(right_else, failure)
                current = or_then
                continue
            current, captures = self._lower_expr(current, operand)
            if outer_handles is None:
                outer_handles = dict(self.handles)
            split = self._emit(current, Nop(), "if_split")
            current = self._fresh_node("if_then")
            self._connect(split, current)
            self._connect(split, failure)
            ne_fact = self._extract_index_ne(operand)
            if ne_fact is not None:
                left_sym, right_sym, on_true = ne_fact
                if on_true:
                    current = self._emit(current, AssumeIndexNe(left_sym, right_sym), "assume_ne")
                else:
                    else_fact = (left_sym, right_sym)
            norealloc = self._extract_no_realloc_guard(operand)
            if norealloc is not None:
                current = self._emit(current, AssumeNoRealloc(norealloc), "assume_norealloc")
            if operand.get("kind") in {"is", "is_expression"}:
                current = self._bind_pattern_from_captures(
                    current, _ast_node(operand["pattern"]), captures, self._try_place(_ast_node(operand["value"])),
                )
        if conjunct_count == 1 and else_fact is not None:
            failure = self._emit(failure, AssumeIndexNe(*else_fact), "assume_else_ne")
        return current, failure, outer_handles if outer_handles is not None else {}

    def _lower_expr(
        self, current: str | None, expr: dict[str, object], *, handles_result: bool = False, case_only: bool = False,
    ) -> tuple[str | None, tuple[str, ...]]:
        if current is None:
            return None, ()
        prev_site = self.current_site
        self.current_site = expr
        try:
            kind = expr.get("kind")
            if kind in {
                "nat",
                "bool",
                "unit",
                "string",
                "bytes",
                "character",
                "char",
                "hole",
                "operator",
                "type_expression",
            }:
                return current, ()

            if _is_ident(expr):
                name = _id_text(expr["name"])
                if handles_result:
                    current = self._use_result(current, name, case_only=case_only)
                if name in self.handles:
                    handle = self.handles[name]
                    current = self._emit(current, Use(handle), f"use_{name}")
                    return current, (handle,)
                if name in self.owners:
                    current = self._emit(current, Access(Place(name), "read"), f"read_{name}")
                return current, ()

            if kind == "member":
                current = self._eval_index_subexpressions(current, expr)
                place = self._try_place(expr)
                if place is not None:
                    if handles_result and place.fields:
                        current = self._use_result(current, ".".join((place.owner, *place.fields)), case_only=case_only)
                    if place.fields and "*" not in place.fields:
                        self._add_owner_field(place.owner, place.fields)
                    recv = expr.get("receiver") or expr.get("value")
                    if isinstance(recv, dict) and _is_ident(recv):
                        rname = _id_text(recv["name"])
                        if rname in self.handles:
                            via = self.handles[rname]
                            current = self._emit(current, Access(place, "read", via=via), "read_member")
                            return current, (via,)
                    current = self._emit(current, Access(place, "read"), "read_member")
                    return current, ()
                recv = expr.get("receiver") or expr.get("value")
                if isinstance(recv, dict):
                    return self._lower_expr(current, recv)
                return current, ()

            if kind in {"index", "range_index"}:
                current = self._eval_index_subexpressions(current, expr)
                place = self._try_place(expr)
                if place is not None:
                    recv = expr.get("receiver") or expr.get("value")
                    if isinstance(recv, dict) and _is_ident(recv):
                        rname = _id_text(recv["name"])
                        if rname in self.handles:
                            via = self.handles[rname]
                            current = self._emit(current, Access(place, "read", via=via), "read_index")
                            return current, (via,)
                    current = self._emit(current, Access(place, "read"), "read_index")
                    return current, ()
                return current, ()

            borrow_info = _extract_borrow_expr(expr)
            if borrow_info is not None:
                mode, inner = borrow_info
                if mode == "move":
                    if _is_ident(inner):
                        sname = _id_text(inner["name"])
                        if handles_result:
                            current = self._use_result(current, sname, case_only=case_only)
                        if sname in self.handles:
                            old_handle = self.handles.pop(sname)
                            moved_handle = self._fresh_loan(f"moved_{sname}")
                            current = self._emit(current, Move(old_handle, moved_handle), f"move_{sname}")
                            return current, (moved_handle,)
                    current, _, place = self._resolve_borrow_target(current, inner)
                    current = self._emit(current, Access(place, "move"), "move_owner")
                    return current, ()
                loan_mode: Mode = (
                    "shared"
                    if mode == "in"
                    else ("shared_mut" if mode == "shared_mut" else "exclusive")
                )
                current, parent, place = self._resolve_borrow_target(current, inner)
                loan_name = self._fresh_loan("borrow")
                parent_origin = self.handle_origins.get(parent) or (
                    self.owners[parent].origin if parent in self.owners else None
                )
                current = self._emit(
                    current,
                    Borrow(Loan(loan_name, parent, place, mode=loan_mode, origin=parent_origin)),
                    "borrow",
                )
                self.handle_places[loan_name] = place
                self.handle_modes[loan_name] = loan_mode
                if parent_origin is not None:
                    self.handle_origins[loan_name] = parent_origin
                return current, (loan_name,)

            if kind == "interpolated_string":
                if "holes" in expr:
                    for hole in _ast_nodes(expr["holes"]):
                        current, _ = self._lower_expr(current, hole)
                    return current, ()
                for part in _ast_nodes(expr.get("parts", [])):
                    if part.get("kind") == "interpolation":
                        hole_expr = _ast_node(part.get("expression") or part["value"])
                        current, _ = self._lower_expr(current, hole_expr)
                return current, ()

            if kind in {"tuple", "array"}:
                captures: list[str] = []
                raw_elems = expr.get("elements") if "elements" in expr else expr.get("values", [])
                for elem in _ast_nodes(raw_elems):
                    current, caps = self._lower_expr(current, elem, handles_result=handles_result and not case_only)
                    for cap in caps:
                        if cap not in captures:
                            captures.append(cap)
                return current, tuple(captures)

            if kind == "unary":
                op = _op_text(expr.get("operator"))
                operand = _ast_node(expr.get("operand") if "operand" in expr else expr["value"])
                current, caps = self._lower_expr(current, operand)
                if op == "await":
                    current = self._emit(current, Checkpoint("await"), "await")
                    return current, caps
                return current, ()

            if kind == "binary":
                operator = _op_text(expr["operator"])
                if operator == "==>":
                    success, failure, outer = self._lower_condition(current, _ast_node(expr["left"]))
                    end, _ = self._lower_expr(success, _ast_node(expr["right"]))
                    self.handles = outer
                    join = self._fresh_node("join_implies")
                    self._connect(end, join)
                    self._connect(failure, join)
                    return join, ()
                if operator == "&&":
                    success, failure, self.handles = self._lower_condition(current, expr)
                    join = self._fresh_node("join_and")
                    self._connect(success, join)
                    self._connect(failure, join)
                    return join, ()
                if operator == "||":
                    current, _ = self._lower_expr(current, _ast_node(expr["left"]))
                    split = self._emit(current, Nop(), "or_split")
                    join = self._fresh_node("join_or")
                    right = self._fresh_node("or_right")
                    self._connect(split, join)
                    self._connect(split, right)
                    end, _ = self._lower_expr(right, _ast_node(expr["right"]))
                    self._connect(end, join)
                    return join, ()
                left = _ast_node(expr["left"])
                right = _ast_node(expr["right"])
                current, _ = self._lower_expr(current, left)
                current, _ = self._lower_expr(current, right)
                return current, ()

            if kind in {"group", "expression_body"}:
                inner = _ast_node(expr.get("expression") or expr.get("value"))
                return self._lower_expr(current, inner, handles_result=handles_result, case_only=case_only)

            if kind in {"is", "is_expression", "as", "cast_expression"}:
                val = _ast_node(expr["value"])
                checks_case = kind in {"is", "is_expression"} and _checks_constructor(expr["pattern"])
                return self._lower_expr(current, val, handles_result=checks_case, case_only=True)

            if kind in {"update", "with_expression"}:
                src = _ast_node(expr.get("source") or expr["value"])
                raw_fields = expr.get("fields") if "fields" in expr else expr.get("updates", [])
                src_borrow = _extract_borrow_expr(src)
                if src_borrow is not None and src_borrow[0] == "move":
                    for fitem in _ast_nodes(raw_fields):
                        fval = _ast_node(fitem["value"])
                        current, _ = self._lower_expr(current, fval)
                    current, caps = self._lower_expr(current, src)
                    return current, caps
                current, caps = self._lower_expr(current, src)
                for fitem in _ast_nodes(raw_fields):
                    fval = _ast_node(fitem["value"])
                    current, _ = self._lower_expr(current, fval)
                return current, caps

            if kind == "let_expression":
                if "binding" in expr and isinstance(expr["binding"], dict):
                    current = self._lower_statement(current, _ast_node(expr["binding"]))
                    return self._lower_expr(current, _ast_node(expr["body"]), handles_result=handles_result, case_only=case_only)
                bname = _id_text(expr["name"])
                val = _ast_node(expr["value"])
                body = _ast_node(expr["body"])
                current = self._lower_binding(
                    current, bname, val, local_type=expr.get("local_type") or expr.get("type")
                )
                return self._lower_expr(current, body)

            if kind == "block":
                current = self._lower_statements(current, _body_statements(expr))
                return current, ()

            if kind == "if_expression":
                cond = _ast_node(expr["condition"])
                then_br = _ast_node(expr.get("then_branch") or expr["then"])
                else_br = _ast_node(expr.get("else_branch") or expr["else"])
                then_entry, else_entry, saved_handles = self._lower_condition(current, cond)
                then_exit, then_caps = self._lower_expr(then_entry, then_br, handles_result=handles_result)
                self.handles = dict(saved_handles)
                else_exit, else_caps = self._lower_expr(else_entry, else_br, handles_result=handles_result)
                self.handles = saved_handles
                join = self._fresh_node("join_if")
                self._connect(then_exit, join)
                self._connect(else_exit, join)
                return join, tuple(dict.fromkeys((*then_caps, *else_caps)))

            if kind == "match_expression":
                scrutinee = _ast_node(expr.get("scrutinee") or expr["value"])
                raw_arms = expr.get("arms") if "arms" in expr else expr.get("cases", [])
                arms = _ast_nodes(raw_arms)
                checks_case = any(_checks_constructor(arm["pattern"]) for arm in arms)
                transfers = id(expr) in self.result_bindings
                current, scrut_caps = self._lower_expr(current, scrutinee, handles_result=checks_case or transfers, case_only=not transfers)
                scrut_place = self._try_place(scrutinee)
                if not arms:
                    return current, ()
                split = self._emit(current, Nop(), "match_split")
                join = self._fresh_node("join_match")
                all_caps: list[str] = []
                saved_handles = dict(self.handles)
                outer_results = set(self.visible_results)
                for idx, arm in enumerate(arms):
                    arm_entry = self._fresh_node(f"arm_{idx}")
                    self._connect(split, arm_entry)
                    self.handles = dict(saved_handles)
                    pat = _ast_node(arm["pattern"])
                    arm_curr: str | None = self._bind_pattern_from_captures(
                        arm_entry, pat, scrut_caps, scrut_place
                    )
                    paths = self.result_bindings.get(id(pat), set())
                    self.visible_results = outer_results | paths
                    arm_curr = self._result_event(arm_curr, "new", paths)
                    guard = arm.get("guard")
                    if isinstance(guard, dict):
                        arm_curr, _ = self._lower_expr(arm_curr, guard)
                    body_node = _ast_node(arm.get("body") or arm["value"])
                    arm_exit, arm_caps = self._lower_expr(arm_curr, body_node, handles_result=handles_result)
                    arm_exit = self._result_event(arm_exit, "scope", paths)
                    self._connect(arm_exit, join)
                    for cap in arm_caps:
                        if cap not in all_caps:
                            all_caps.append(cap)
                self.handles = saved_handles
                self.visible_results = outer_results
                return join, tuple(all_caps)

            if kind == "call":
                return self._lower_call(current, expr)

            if kind == "propagate":
                inner = _ast_node(expr["value"])
                current, caps = self._lower_expr(current, inner, handles_result=True)
                split = self._emit(current, Nop(), "try_split")
                err_node = self._fresh_node("try_err", Return("Err"))
                ok_node = self._fresh_node("try_ok")
                self._connect(split, ok_node)
                self._connect(split, err_node)
                return ok_node, caps

            return current, ()
        finally:
            self.current_site = prev_site

    def _builtin_method_signature(self, type_name: str | None, method: str) -> _Receiver | None:
        if type_name in _BUILTIN_CONTAINERS:
            if method in _UNSTABLE_CONTAINER_METHODS:
                return _Receiver("exclusive", None, False, two_phase=True, scalar_result=True)
            if method in _READONLY_CONTAINER_METHODS:
                return _Receiver("shared", None, False, two_phase=False, scalar_result=True)
        if type_name in _SCALAR_VALUE_TYPES:
            return _Receiver("shared", None, False, two_phase=False, scalar_result=True)
        return None

    def _lower_call(
        self, current: str | None, expr: dict[str, object]
    ) -> tuple[str | None, tuple[str, ...]]:
        callee = _ast_node(expr["callee"])
        args = _ast_nodes(expr.get("arguments", []))
        arg_loans: list[tuple[str, Mode, Place, bool]] = []
        transferred_results: list[str] = []
        captured_handles: list[str] = []

        while callee.get("kind") in {"generic_application", "group"}:
            callee = _ast_node(callee["value"])
        receiver_loan: Loan | None = None
        receiver_footprint: Place | None = None
        reserve_receiver = False
        call_stability: Stability = "unstable" if self._is_unstable_call(callee) else "stable"
        span = tuple(cast("list[int]", expr.get("span", [])))
        scalar_result = span in self.checked_scalar_calls
        receiver_site = callee
        if callee.get("kind") == "member":
            recv = _ast_node(callee.get("receiver") or callee["value"])
            place = self._try_place(recv)
            projection: tuple[str, ...] = ()
            signature: _Receiver | None = None
            if span in self.checked_receivers:
                signature = self.checked_receivers[span]
                if signature is None:
                    current, _ = self._lower_expr(current, recv)
            elif place is not None:
                method = _id_text(callee.get("name") or callee.get("member"))
                info = self._place_struct(place)
                signature = info.methods.get(method) if info is not None else None
                if info is None or signature is None:
                    place_type, _ = self._place_type_info(place)
                    signature = self._builtin_method_signature(place_type, method)
                if signature is None:
                    raise AnalysisRefusalError(f"cannot resolve receiver mode for {place.owner}.{method}")
                if signature.view is not None:
                    if info is None or signature.view not in info.views:
                        raise AnalysisRefusalError(f"unknown receiver view {signature.view!r} for {method}")
                    projection = info.views[signature.view]
            else:
                method = _id_text(callee.get("name") or callee.get("member"))
                recv_type = self._infer_expr_type(recv)
                info = self.structs.get(recv_type) if recv_type is not None else None
                signature = info.methods.get(method) if info is not None else None
                if signature is None:
                    signature = self._builtin_method_signature(recv_type, method)
                if signature is None and not _is_ident(recv) and _view_field(recv) is None:
                    raise AnalysisRefusalError("cannot resolve receiver of computed method call")
                if signature is not None and signature.view is not None:
                    if info is None or signature.view not in info.views:
                        raise AnalysisRefusalError(f"unknown receiver view {signature.view!r} for {method}")
                    projection = info.views[signature.view]
            if signature is not None:
                scalar_result = scalar_result or signature.scalar_result
                if place is not None:
                    current, parent, _ = self._resolve_borrow_target(current, recv)
                    base = place
                else:
                    current, captures = self._lower_expr(current, recv)
                    if not captures:
                        parent = self._fresh_loan("receiver_value")
                        self._register_owner(parent, borrowed=False)
                        base = Place(parent)
                    elif len(captures) == 1 and captures[0] in self.handle_places:
                        parent = captures[0]
                        base = self.handle_places[parent]
                    else:
                        raise AnalysisRefusalError("cannot resolve the origin of a computed receiver")
                footprint = Place(base.owner, (*base.fields, *projection))
                receiver_footprint = footprint
                self._add_owner_field(footprint.owner, footprint.fields)
                receiver_loan = Loan(self._fresh_loan("recv"), parent, footprint, mode=signature.mode,
                                     scoped=not signature.retained)
                reserve_receiver = signature.two_phase
                self.current_site = receiver_site
                event = Reserve(receiver_loan) if reserve_receiver else Borrow(receiver_loan)
                current = self._emit(current, event, "call_recv")
                self.current_site = expr
                if signature.retained:
                    self.handle_places[receiver_loan.name] = footprint
                    self.handle_modes[receiver_loan.name] = signature.mode
                    captured_handles.append(receiver_loan.name)

        # Evaluate arguments in source order. Reuse matching handles or create
        # scoped loans, then demand them together at the call.
        for arg in args:
            prev_site = self.current_site
            self.current_site = arg
            try:
                if arg.get("kind") in {"call_argument", "argument"}:
                    amode = str(arg.get("mode", "value"))
                    aval = _ast_node(arg["value"])
                else:
                    amode = "value"
                    aval = arg
                if amode == "value":
                    borrow_info = _extract_borrow_expr(aval)
                    if borrow_info is not None:
                        amode, aval = borrow_info

                if amode in {"in", "ref", "out", "shared_mut"}:
                    loan_mode: Mode = (
                        "shared"
                        if amode == "in"
                        else ("shared_mut" if amode == "shared_mut" else "exclusive")
                    )
                    if _is_ident(aval):
                        aname = _id_text(aval["name"])
                        if aname in self.handles and self.handle_modes.get(aname) == loan_mode:
                            hname = self.handles[aname]
                            hplace = self.handle_places.get(aname, Place(next(iter(self.owners))))
                            arg_loans.append((hname, loan_mode, hplace, False))
                            captured_handles.append(hname)
                            continue
                    current, parent, place = self._resolve_borrow_target(current, aval)
                    tmp_loan = self._fresh_loan("arg")
                    current = self._emit(
                        current,
                        Borrow(Loan(tmp_loan, parent, place, mode=loan_mode, scoped=True)),
                        "arg_borrow",
                    )
                    self.handle_places[tmp_loan] = place
                    self.handle_modes[tmp_loan] = loan_mode
                    arg_loans.append((tmp_loan, loan_mode, place, True))
                elif amode == "move":
                    if _is_ident(aval):
                        sname = _id_text(aval["name"])
                        transferred_results.append(sname)
                        if sname in self.handles:
                            old_handle = self.handles.pop(sname)
                            moved_handle = self._fresh_loan(f"moved_{sname}")
                            current = self._emit(current, Move(old_handle, moved_handle), f"move_{sname}")
                            captured_handles.append(moved_handle)
                            continue
                    current, _, place = self._resolve_borrow_target(current, aval)
                    current = self._emit(current, Access(place, "move"), "arg_move")
                else:
                    direct = aval
                    while direct.get("kind") == "group":
                        direct = _ast_node(direct.get("expression") or direct["value"])
                    if _is_ident(direct):
                        transferred_results.append(_id_text(direct["name"]))
                    elif direct.get("kind") == "member" and (place := self._try_place(direct)) is not None and place.fields:
                        transferred_results.append(".".join((place.owner, *place.fields)))
                    in_receiver_argument = self.in_receiver_argument
                    self.in_receiver_argument = in_receiver_argument or reserve_receiver
                    try:
                        current, caps = self._lower_expr(current, aval)
                    finally:
                        self.in_receiver_argument = in_receiver_argument
                    for cap in caps:
                        if cap not in captured_handles:
                            captured_handles.append(cap)
            finally:
                self.current_site = prev_site

        for name in transferred_results:
            current = self._use_result(current, name)

        if reserve_receiver and receiver_loan is not None:
            live_args = tuple(dict.fromkeys(name for name, _, _, _ in arg_loans))
            possible_captures = tuple(
                name for name in dict.fromkeys(captured_handles)
                if name != receiver_loan.name and name not in live_args
            )
            self.current_site = receiver_site
            current = self._emit(
                current, Activate(receiver_loan.name, live_args, possible_captures), "call_activate"
            )
            self.current_site = expr

        # At the call execution point, demand all active `in`/`ref`/`out` argument loans.
        for loan_name, loan_mode, place, is_temp in arg_loans:
            if loan_mode == "shared":
                current = self._emit(current, Use(loan_name), "call_use")
            else:
                current = self._emit(
                    current, Access(place, "write", via=loan_name, stability=call_stability), "call_write"
                )
            if is_temp:
                if loan_mode == "shared" and self.in_receiver_argument and not scalar_result:
                    captured_handles.append(loan_name)
                else:
                    current = self._emit(current, Drop(loan_name), "call_drop")

        if receiver_loan is not None:
            self.current_site = receiver_site
            if receiver_loan.mode == "exclusive" and call_stability == "unstable" and receiver_footprint is not None:
                current = self._emit(
                    current,
                    Access(receiver_footprint, "write", via=receiver_loan.name, stability="unstable"),
                    "call_receiver_write",
                )
            else:
                current = self._emit(current, Use(receiver_loan.name), "call_receiver_use")
            if receiver_loan.scoped:
                current = self._emit(current, Drop(receiver_loan.name), "call_receiver_drop")
            self.current_site = expr
        return current, () if scalar_result else tuple(captured_handles)

    def _lower_binding(
        self,
        current: str | None,
        binder_name: str,
        value_expr: dict[str, object],
        *,
        local_type: object = None,
    ) -> str | None:
        if current is None:
            return None
        mods = _type_modifiers(local_type)
        scoped = "scoped" in mods
        explicit_loan_mode: Mode | None = None
        if "shared_mut" in mods:
            explicit_loan_mode = "shared_mut"
        elif "ref" in mods or "out" in mods:
            explicit_loan_mode = "exclusive"
        elif "in" in mods:
            explicit_loan_mode = "shared"
        explicit_origin = _extract_region_name(local_type)

        borrow_info = _extract_borrow_expr(value_expr)
        if borrow_info is not None:
            mode, inner = borrow_info
            if mode == "move":
                if _is_ident(inner):
                    sname = _id_text(inner["name"])
                    if sname in self.handles:
                        old_handle = self.handles.pop(sname)
                        target_handle = self._fresh_binder(binder_name)
                        current = self._emit(current, Move(old_handle, target_handle), f"move_{binder_name}")
                        self.handles[binder_name] = target_handle
                        if sname in self.handle_places:
                            self.handle_places[binder_name] = self.handle_places[sname]
                            self.handle_places[target_handle] = self.handle_places[sname]
                        if sname in self.handle_modes:
                            self.handle_modes[binder_name] = self.handle_modes[sname]
                            self.handle_modes[target_handle] = self.handle_modes[sname]
                        return current
                current, _, place = self._resolve_borrow_target(current, inner)
                current = self._emit(current, Access(place, "move"), f"move_{binder_name}")
                self.handles.pop(binder_name, None)
                self._register_owner(binder_name, borrowed=False, type_name=_type_base_name(local_type))
                return current

            loan_mode: Mode = (
                "shared"
                if mode == "in"
                else ("shared_mut" if mode == "shared_mut" else "exclusive")
            )
            current, parent, place = self._resolve_borrow_target(current, inner)
            loan_name = self._fresh_binder(binder_name)
            loan_origin = explicit_origin or self.handle_origins.get(parent) or (
                self.owners[parent].origin if parent in self.owners else None
            )
            current = self._emit(
                current,
                Borrow(Loan(loan_name, parent, place, mode=loan_mode, scoped=scoped, origin=loan_origin)),
                f"borrow_{binder_name}",
            )
            self.handles[binder_name] = loan_name
            self.handle_places[binder_name] = place
            self.handle_places[loan_name] = place
            self.handle_modes[binder_name] = loan_mode
            self.handle_modes[loan_name] = loan_mode
            if loan_origin is not None:
                self.handle_origins[binder_name] = loan_origin
                self.handle_origins[loan_name] = loan_origin
            return current

        current, caps = self._lower_expr(current, value_expr, handles_result=id(self.current_site) in self.result_bindings)
        if caps:
            if len(caps) == 1 and explicit_loan_mode is not None and caps[0] in self.handle_places:
                parent_handle = caps[0]
                place = self.handle_places[parent_handle]
                loan_name = self._fresh_binder(binder_name)
                loan_origin = explicit_origin or self.handle_origins.get(parent_handle)
                current = self._emit(
                    current,
                    Borrow(
                        Loan(
                            loan_name,
                            parent_handle,
                            place,
                            mode=explicit_loan_mode,
                            scoped=scoped,
                            origin=loan_origin,
                        )
                    ),
                    f"reborrow_{binder_name}",
                )
                self.handles[binder_name] = loan_name
                self.handle_places[binder_name] = place
                self.handle_places[loan_name] = place
                self.handle_modes[binder_name] = explicit_loan_mode
                self.handle_modes[loan_name] = explicit_loan_mode
                if loan_origin is not None:
                    self.handle_origins[binder_name] = loan_origin
                    self.handle_origins[loan_name] = loan_origin
            elif explicit_loan_mode is None and (
                _is_scalar_value_type(local_type)
                or (_is_ident(value_expr) and len(caps) == 1 and caps[0] in self.handle_places)
            ):
                self.handles.pop(binder_name, None)
                self._register_owner(binder_name, borrowed=False, type_name=_type_base_name(local_type))
            else:
                bind_name = self._fresh_binder(binder_name)
                current = self._emit(current, Bind(bind_name, caps), f"bind_{binder_name}")
                self.handles[binder_name] = bind_name
            return current

        inferred_type = _type_base_name(local_type)
        if inferred_type is None and value_expr.get("kind") == "call":
            inferred_type = self._infer_expr_type(value_expr)
        if binder_name in self.owners and _NAME.fullmatch(binder_name):
            current = self._emit(current, InvalidateSymbol(f"@{binder_name}"), f"rebind_{binder_name}")
        self.handles.pop(binder_name, None)
        self._register_owner(
            binder_name, borrowed=False, type_name=inferred_type, type_node=local_type
        )
        return current

    def _lower_statements(
        self,
        current: str | None,
        statements: list[dict[str, object]],
        *,
        loop_header: str | None = None,
        loop_exit: str | None = None,
    ) -> str | None:
        outer_results = set(self.visible_results)
        for stmt in statements:
            if current is None:
                break
            current = self._lower_statement(
                current, stmt, loop_header=loop_header, loop_exit=loop_exit
            )
        for stmt in statements:
            if id(stmt) in self.result_bindings:
                current = self._result_event(current, "scope", self.result_bindings[id(stmt)])
        self.visible_results = outer_results
        return current

    def _lower_statement(
        self,
        current: str | None,
        stmt: dict[str, object],
        *,
        loop_header: str | None = None,
        loop_exit: str | None = None,
    ) -> str | None:
        if current is None:
            return None
        prev_site = self.current_site
        self.current_site = stmt
        try:
            kind = stmt.get("kind")

            if kind == "block":
                return self._lower_statements(
                    current,
                    _body_statements(stmt),
                    loop_header=loop_header,
                    loop_exit=loop_exit,
                )

            if kind in {"let", "var", "typed_local", "constant_local"}:
                bname = _id_text(stmt["name"])
                val = _ast_node(stmt["value"])
                current = self._lower_binding(
                    current,
                    bname,
                    val,
                    local_type=stmt.get("local_type") or stmt.get("type"),
                )
                if id(stmt) in self.result_bindings:
                    paths = self.result_bindings[id(stmt)]
                else:
                    paths = set()
                previous = self._visible_result_paths(bname)
                current = self._result_event(current, "shadow", previous)
                self.visible_results.difference_update(previous)
                self.visible_results.update(paths)
                return self._result_event(current, "new", paths)

            if kind in {"let_pattern", "var_pattern"}:
                pat = _ast_node(stmt["pattern"])
                val = _ast_node(stmt["value"])
                current, caps = self._lower_expr(current, val, handles_result=id(stmt) in self.result_bindings)
                current = self._bind_pattern_from_captures(current, pat, caps, self._try_place(val))
                if id(stmt) in self.result_bindings:
                    paths = self.result_bindings[id(stmt)]
                    self.visible_results.update(paths)
                    current = self._result_event(current, "new", paths)
                return current

            if kind in {"let_else", "var_else"}:
                pat = _ast_node(stmt["pattern"])
                val = _ast_node(stmt["value"])
                else_raw = stmt.get("else_body") if "else_body" in stmt else stmt.get("else")
                else_body = _body_statements(else_raw)
                current, caps = self._lower_expr(current, val, handles_result=_checks_constructor(pat), case_only=True)
                split = self._emit(current, Nop(), "let_else_split")
                ok_entry = self._fresh_node("let_else_ok")
                else_entry = self._fresh_node("let_else_err")
                self._connect(split, ok_entry)
                self._connect(split, else_entry)
                saved_handles = dict(self.handles)
                else_exit = self._lower_statements(
                    else_entry, else_body, loop_header=loop_header, loop_exit=loop_exit
                )
                if else_exit is not None and not isinstance(self.events.get(else_exit), Return):
                    self._emit(else_exit, Return("else"), "let_else_ret")
                self.handles = saved_handles
                return self._bind_pattern_from_captures(ok_entry, pat, caps, self._try_place(val))

            if kind in {"assign", "assignment"}:
                target = _ast_node(stmt["target"])
                val = _ast_node(stmt["value"])
                op = _op_text(stmt.get("operator", "=")) or "="
                tname = _id_text(target["name"]) if _is_ident(target) else ""
                place = self._try_place(target)
                if place is not None:
                    tname = ".".join((place.owner, *place.fields))
                paths = self._visible_result_paths(tname)
                current, _ = self._lower_expr(current, val, handles_result=bool(paths))
                current = self._result_event(current, "new", paths)
                current = self._eval_index_subexpressions(current, target)
                if op != "=":
                    current, _ = self._lower_expr(current, target)
                if _is_ident(target):
                    tname = _id_text(target["name"])
                    if tname in self.handles and tname in self.handle_places:
                        via = self.handles[tname]
                        target_place = self.handle_places[tname]
                        stability: Stability = (
                            "unstable" if self._is_unstable_assignment(target_place, val) else "stable"
                        )
                        return self._emit(
                            current,
                            Access(target_place, "write", via=via, stability=stability),
                            f"write_{tname}",
                        )
                place = self._try_place(target)
                if place is not None:
                    if place.fields and "*" not in place.fields:
                        self._add_owner_field(place.owner, place.fields)
                    stability = "unstable" if self._is_unstable_assignment(place, val) else "stable"
                    if _is_ident(target):
                        tname = _id_text(target["name"])
                        if tname in self.owners and tname not in self.handles and _NAME.fullmatch(tname):
                            current = self._emit(
                                current, InvalidateSymbol(f"@{tname}"), f"invalidate_{tname}"
                            )
                    recv = target.get("receiver") or target.get("value")
                    if isinstance(recv, dict) and _is_ident(recv):
                        rname = _id_text(recv["name"])
                        if rname in self.handles:
                            return self._emit(
                                current,
                                Access(place, "write", via=self.handles[rname], stability=stability),
                                "write_field",
                            )
                    return self._emit(
                        current, Access(place, "write", stability=stability), "write_field"
                    )
                return current

            if kind == "if":
                cond = _ast_node(stmt["condition"])
                then_raw = stmt.get("then_body") if "then_body" in stmt else stmt.get("then")
                else_raw = stmt.get("else_body") if "else_body" in stmt else stmt.get("else")
                then_body = _body_statements(then_raw)
                else_body = _body_statements(else_raw)
                then_entry, else_entry, saved_handles = self._lower_condition(current, cond)
                then_exit = self._lower_statements(
                    then_entry, then_body, loop_header=loop_header, loop_exit=loop_exit
                )
                self.handles = dict(saved_handles)
                else_exit = self._lower_statements(
                    else_entry, else_body, loop_header=loop_header, loop_exit=loop_exit
                )
                self.handles = saved_handles
                if then_exit is None and else_exit is None:
                    return None
                join = self._fresh_node("join_if")
                if then_exit is not None:
                    self._connect(then_exit, join)
                if else_exit is not None:
                    self._connect(else_exit, join)
                return join

            if kind == "match":
                scrutinee = _ast_node(stmt.get("scrutinee") or stmt["value"])
                raw_arms = stmt.get("arms") if "arms" in stmt else stmt.get("cases", [])
                arms = _ast_nodes(raw_arms)
                checks_case = any(_checks_constructor(arm["pattern"]) for arm in arms)
                transfers = id(stmt) in self.result_bindings
                current, scrut_caps = self._lower_expr(current, scrutinee, handles_result=checks_case or transfers, case_only=not transfers)
                scrut_place = self._try_place(scrutinee)
                if not arms:
                    return current
                split = self._emit(current, Nop(), "match_split")
                join = self._fresh_node("join_match")
                any_fallthrough = False
                saved_handles = dict(self.handles)
                outer_results = set(self.visible_results)
                for idx, arm in enumerate(arms):
                    arm_entry = self._fresh_node(f"arm_{idx}")
                    self._connect(split, arm_entry)
                    self.handles = dict(saved_handles)
                    pat = _ast_node(arm["pattern"])
                    arm_curr = self._bind_pattern_from_captures(
                        arm_entry, pat, scrut_caps, scrut_place
                    )
                    paths = self.result_bindings.get(id(pat), set())
                    self.visible_results = outer_results | paths
                    arm_curr = self._result_event(arm_curr, "new", paths)
                    guard = arm.get("guard")
                    if isinstance(guard, dict):
                        arm_curr, _ = self._lower_expr(arm_curr, guard)
                    raw_arm_body = (
                        arm.get("body")
                        if "body" in arm
                        else (arm.get("statements") if "statements" in arm else arm.get("value"))
                    )
                    arm_body = _body_statements(raw_arm_body)
                    arm_exit = self._lower_statements(
                        arm_curr, arm_body, loop_header=loop_header, loop_exit=loop_exit
                    )
                    arm_exit = self._result_event(arm_exit, "scope", paths)
                    if arm_exit is not None:
                        any_fallthrough = True
                        self._connect(arm_exit, join)
                self.handles = saved_handles
                self.visible_results = outer_results
                return join if any_fallthrough else None

            if kind == "open_invariant":
                raw_lifts = stmt.get("lifts")
                lifts = (
                    tuple(_id_text(item) for item in _ast_nodes(raw_lifts))
                    if isinstance(raw_lifts, list)
                    else ()
                )
                targets: list[str] = []
                if "resources" in stmt and isinstance(stmt["resources"], list):
                    items = _ast_nodes(stmt["resources"])
                else:
                    target_expr = _ast_node(stmt["target"])
                    items = (
                        _ast_nodes(target_expr.get("elements", []))
                        if target_expr.get("kind") == "tuple"
                        else [target_expr]
                    )
                for item in items:
                    place = self._try_place(item)
                    if place is not None:
                        targets.append(place.owner)
                if not targets and "this" in self.owners:
                    targets.append("this")
                for owner_name in targets:
                    if lifts:
                        self._add_owner_invariants(owner_name, lifts)
                    current = self._emit(
                        current, OpenInvariant(owner_name, lifts), f"open_{owner_name}"
                    )
                body = _body_statements(stmt.get("body"))
                current = self._lower_statements(
                    current, body, loop_header=loop_header, loop_exit=loop_exit
                )
                if current is not None:
                    for owner_name in reversed(targets):
                        current = self._emit(
                            current, CloseInvariant(owner_name, lifts), f"close_{owner_name}"
                        )
                return current

            if kind in {"foreach", "foreach_collection", "while"}:
                if kind == "foreach":
                    if "range" in stmt and isinstance(stmt["range"], dict):
                        rnode = _ast_node(stmt["range"])
                        current, _ = self._lower_expr(current, _ast_node(rnode["start"]))
                        current, _ = self._lower_expr(current, _ast_node(rnode["end"]))
                    else:
                        current, _ = self._lower_expr(current, _ast_node(stmt["start"]))
                        current, _ = self._lower_expr(current, _ast_node(stmt["end"]))
                elif kind == "foreach_collection":
                    coll_node = _ast_node(stmt["collection"])
                    if coll_node.get("kind") == "range":
                        current, _ = self._lower_expr(current, _ast_node(coll_node["start"]))
                        current, _ = self._lower_expr(current, _ast_node(coll_node["end"]))
                    else:
                        current, _ = self._lower_expr(current, coll_node)
                header = self._fresh_node("header_loop")
                self._connect(current, header)
                body_entry = self._fresh_node("loop_body")
                exit_node = self._fresh_node("loop_exit")
                self._connect(header, body_entry)
                self._connect(header, exit_node)
                saved_handles = dict(self.handles)
                body_curr: str | None = body_entry
                iter_loan: str | None = None
                if kind == "while":
                    body_curr, _ = self._lower_expr(body_curr, _ast_node(stmt["condition"]))
                elif kind == "foreach":
                    iname = _id_text(stmt["name"])
                    self._register_owner(iname, borrowed=False)
                    if _NAME.fullmatch(iname):
                        body_curr = self._emit(body_curr, InvalidateSymbol(f"@{iname}"), f"iter_sym_{iname}")
                elif kind == "foreach_collection":
                    iname = _id_text(stmt["name"])
                    imode = str(stmt.get("mode", "value"))
                    coll = _ast_node(stmt["collection"])
                    if coll.get("kind") != "range" and imode in {"in", "ref"}:
                        body_curr, parent, cplace = self._resolve_borrow_target(body_curr, coll)
                        elem_place = Place(cplace.owner, (*cplace.fields, "*"))
                        loan_mode = "shared" if imode == "in" else "exclusive"
                        iter_loan = self._fresh_binder(iname)
                        body_curr = self._emit(
                            body_curr,
                            Borrow(Loan(iter_loan, parent, elem_place, mode=loan_mode, scoped=True)),
                            f"iter_{iname}",
                        )
                        self.handles[iname] = iter_loan
                        self.handle_places[iname] = elem_place
                        self.handle_places[iter_loan] = elem_place
                        self.handle_modes[iname] = loan_mode
                        self.handle_modes[iter_loan] = loan_mode
                    else:
                        self.handles.pop(iname, None)
                        self._register_owner(iname, borrowed=False)
                        if _NAME.fullmatch(iname):
                            body_curr = self._emit(
                                body_curr, InvalidateSymbol(f"@{iname}"), f"iter_sym_{iname}"
                            )
                body_exit = self._lower_statements(
                    body_curr,
                    _body_statements(stmt.get("body")),
                    loop_header=header,
                    loop_exit=exit_node,
                )
                if body_exit is not None:
                    if iter_loan is not None:
                        body_exit = self._emit(
                            body_exit, Drop(iter_loan), f"drop_{iter_loan}"
                        )
                    self._connect(body_exit, header)
                self.handles = saved_handles
                return exit_node

            if kind == "break":
                if loop_exit is not None:
                    self._connect(current, loop_exit)
                return None

            if kind == "continue":
                if loop_header is not None:
                    self._connect(current, loop_header)
                return None

            if kind == "return":
                val = stmt.get("value")
                if isinstance(val, dict):
                    outcome = "return"
                    if val.get("kind") == "call":
                        callee = _ast_node(val["callee"])
                        if _is_ident(callee):
                            cname = _id_text(callee["name"])
                            if cname and cname[0].isupper():
                                outcome = cname
                    current, caps = self._lower_expr(current, val, handles_result=True)
                    ret_caps = (
                        ()
                        if self.returns_scalar_value and _extract_borrow_expr(val) is None
                        else caps
                    )
                    self._emit(current, Return(outcome, ret_caps, origin=self.return_origin), "ret")
                else:
                    self._emit(current, Return("return", origin=self.return_origin), "ret")
                return None

            if kind in {"expression", "expression_statement"}:
                expr = _ast_node(stmt.get("expression") or stmt["value"])
                current, _ = self._lower_expr(current, expr)
                return current

            if kind == "assert":
                expr = _ast_node(stmt.get("expression") or stmt["value"])
                self.in_proof = True
                try:
                    current, _ = self._lower_expr(current, expr)
                finally:
                    self.in_proof = False
                if current is None:
                    return None
                return self._emit_conjunctive_index_facts(current, expr)

            return current
        finally:
            self.current_site = prev_site

    def _emit_proved_facts(self, current: str) -> str:
        facts = self.proved_facts
        if facts is None:
            return current
        for left_p, right_p in facts.disjoint_places:
            if left_p.owner in self.owners and right_p.owner in self.owners:
                current = self._emit(current, AssumeDisjoint(left_p, right_p), "fact_disjoint")
        for left_s, right_s in facts.arithmetic_disequalities:
            current = self._emit(current, AssumeIndexNe(left_s, right_s), "fact_ne")
        for place in facts.tag_preserved:
            if place.owner in self.owners:
                current = self._emit(current, AssumeTagPreserved(place), "fact_tag")
        for place in facts.no_realloc:
            if place.owner in self.owners:
                current = self._emit(current, AssumeNoRealloc(place), "fact_norealloc")
        for rname, place in facts.refinements.items():
            if place.owner in self.owners:
                current = self._emit(current, AssumeRefinement(rname, place), "fact_ref")
        for rname in facts.use_refinements:
            if rname in facts.refinements:
                current = self._emit(current, UseRefinement(rname), "fact_use_ref")
        return current

    def build(self) -> LoweredFunction:
        self._collect_signature_facts()
        self.visible_results = set(self.result_parameters)
        entry = self._fresh_node("entry")
        current = self._emit_proved_facts(entry)
        for contract in _ast_nodes(self.fn_node.get("contracts", [])):
            if contract.get("kind") == "requires" or (
                contract.get("kind") == "contract" and contract.get("role") == "requires"
            ):
                clause = contract.get("value") or contract.get("expression") or contract.get("condition")
                current = self._emit_conjunctive_index_facts(current, clause)
        body = (
            self.fn_node.get("body")
            if self.fn_node.get("body") is not None
            else self.fn_node.get("value")
        )
        if isinstance(body, list) or (isinstance(body, dict) and body.get("kind") == "block"):
            end = self._lower_statements(current, _body_statements(body))
            if end is not None and not isinstance(self.events.get(end), Return):
                self._emit(end, Return("return", origin=self.return_origin), "ret")
        elif isinstance(body, dict):
            end, caps = self._lower_expr(current, body, handles_result=True)
            ret_caps = (
                ()
                if self.returns_scalar_value and _extract_borrow_expr(body) is None
                else caps
            )
            if end is not None and not isinstance(self.events.get(end), Return):
                self._emit(end, Return("return", ret_caps, origin=self.return_origin), "ret")
        else:
            self._emit(current, Return("return", origin=self.return_origin), "ret")

        # Keep only reachable nodes from entry so dead post-return placeholders are excluded.
        reached: set[str] = set()
        stack = [entry]
        while stack:
            curr = stack.pop()
            if curr in reached:
                continue
            reached.add(curr)
            stack.extend(
                succ for succ in reversed(self.edges.get(curr, [])) if succ not in reached
            )

        built_nodes = tuple(
            Node(
                name,
                self.events[name],
                tuple(succ for succ in self.edges[name] if succ in reached),
            )
            for name in self.events
            if name in reached
        )
        site_map = {
            name: self.node_sites[name]
            for name in self.events
            if name in reached and name in self.node_sites
        }
        return LoweredFunction(
            self.fn_name,
            tuple(self.owners.values()),
            Graph(entry, built_nodes, return_origin=self.return_origin),
            site_map,
        )


def _unwrap_ast_root(ast: object) -> dict[str, object]:
    node = _ast_node(ast, "AST root")
    if "ast" in node and isinstance(node["ast"], dict):
        return _ast_node(node["ast"], "inner AST root")
    return node


def lower_function(
    ast: object,
    function_name: str | None = None,
    *,
    proved_facts: ProvedFacts | Mapping[str, object] | None = None,
) -> LoweredFunction:
    """Lower a parsed schema-2 function, method or definition into a loan Graph."""
    root = _unwrap_ast_root(ast)
    kind = root.get("kind")
    if kind in {"function", "method", "definition"}:
        fname = _id_text(root["name"])
        if function_name is not None and function_name != fname:
            raise AnalysisRefusalError(f"function {function_name!r} not found")
        return _FunctionLowerer(fname, root, None, {}, proved_facts=proved_facts).build()

    if kind not in {"surface_file", "module", "file"}:
        raise AnalysisRefusalError("expected a parsed module or function AST node")

    declarations = _ast_nodes(root.get("declarations", []))
    structs = _collect_structs(declarations)
    function_returns = _collect_function_returns(declarations)
    functions = _find_functions(declarations)
    if not functions:
        raise AnalysisRefusalError("no function with a body found in module")
    if function_name is None:
        selected_name, selected_node, enclosing = functions[0]
        return _FunctionLowerer(
            selected_name,
            selected_node,
            enclosing,
            structs,
            function_returns,
            proved_facts=proved_facts,
        ).build()
    for candidate_name, candidate_node, enclosing in functions:
        if candidate_name == function_name:
            return _FunctionLowerer(
                candidate_name,
                candidate_node,
                enclosing,
                structs,
                function_returns,
                proved_facts=proved_facts,
            ).build()
    raise AnalysisRefusalError(f"function {function_name!r} not found in module")


def lower_module(
    ast: object,
    *,
    proved_facts: ProvedFacts | Mapping[str, object] | None = None,
) -> tuple[LoweredFunction, ...]:
    """Lower all functions, methods and definitions with bodies in a schema-2 module."""
    root = _unwrap_ast_root(ast)
    if root.get("kind") not in {"surface_file", "module", "file"}:
        return (lower_function(root, proved_facts=proved_facts),)
    declarations = _ast_nodes(root.get("declarations", []))
    structs = _collect_structs(declarations)
    function_returns = _collect_function_returns(declarations)
    seen_nodes: set[int] = set()
    lowered: list[LoweredFunction] = []
    for candidate_name, candidate_node, enclosing in _find_functions(declarations):
        if id(candidate_node) in seen_nodes:
            continue
        seen_nodes.add(id(candidate_node))
        lowered.append(
            _FunctionLowerer(
                candidate_name,
                candidate_node,
                enclosing,
                structs,
                function_returns,
                proved_facts=proved_facts,
            ).build()
        )
    if not lowered:
        raise AnalysisRefusalError("no function with a body found in module")
    return tuple(lowered)


def analyze_function(
    ast: object,
    function_name: str | None = None,
    limits: Limits | None = None,
    *,
    proved_facts: ProvedFacts | Mapping[str, object] | None = None,
) -> Report:
    """Lower and analyze one schema-2 function, method or definition."""
    lowered = lower_function(ast, function_name, proved_facts=proved_facts)
    return analyze(lowered.owners, lowered.graph, limits)


def analyze_module(
    ast: object,
    limits: Limits | None = None,
    *,
    proved_facts: ProvedFacts | Mapping[str, object] | None = None,
) -> dict[str, Report]:
    """Lower and analyze every function with a body in a schema-2 module."""
    return {
        lowered.name: analyze(lowered.owners, lowered.graph, limits)
        for lowered in lower_module(ast, proved_facts=proved_facts)
    }
