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

type Mode = Literal["shared", "exclusive"]
type AccessKind = Literal["read", "write", "move"]
type Overlap = Literal["yes", "no", "unknown"]

_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")


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


@dataclass(frozen=True)
class Loan:
    name: str
    parent: str
    place: Place
    mode: Mode = "shared"
    scoped: bool = False
    invariant: str | None = None


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
class Nop:
    pass


type Event = (Borrow | Reserve | Activate | Access | Bind | Use | Drop | Move | Return | Checkpoint
              | OpenInvariant | CloseInvariant | Nop)


@dataclass(frozen=True)
class Node:
    name: str
    event: Event = Nop()
    successors: tuple[str, ...] = ()


@dataclass(frozen=True)
class Graph:
    entry: str
    nodes: tuple[Node, ...]


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


def _projection(value: tuple[str, ...]) -> None:
    if not isinstance(value, tuple) or len(value) > 32:
        raise AnalysisRefusalError("projection must be an immutable path of at most 32 fields")
    for part in value:
        if part != "*":
            _name(part)


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
        owner_map[owner.name] = owner

    nodes: dict[str, Node] = {}
    known = set(owner_map)
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
                                       Checkpoint, OpenInvariant, CloseInvariant, Nop)):
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
            if not isinstance(place, Place):
                raise AnalysisRefusalError("footprint must be an immutable Place record")
            _name(place.owner)
            _projection(place.fields)
            if place.owner not in owner_map:
                raise AnalysisRefusalError("missing place owner")
        if isinstance(event, (Borrow, Reserve)):
            if event.loan.mode not in ("shared", "exclusive") or type(event.loan.scoped) is not bool:
                raise AnalysisRefusalError("malformed loan mode")
            if isinstance(event, Reserve) and event.loan.mode != "exclusive":
                raise AnalysisRefusalError("receiver reservation requires an exclusive loan")
            if event.loan.invariant is not None:
                _name(event.loan.invariant)
                if event.loan.invariant not in invariants:
                    raise AnalysisRefusalError("missing invariant reference")
        if isinstance(event, Activate) and event.name not in reservations:
            raise AnalysisRefusalError("missing receiver reservation reference")
        if isinstance(event, Access) and event.kind not in ("read", "write", "move"):
            raise AnalysisRefusalError("unknown access kind")
        if isinstance(event, CloseInvariant):
            conjuncts, _ = _invariant_conjuncts(owner_map, event.name, event.clauses)
            if not all(pair in opened_conjuncts for pair in conjuncts):
                raise AnalysisRefusalError("missing invariant reference")
        if isinstance(event, (Return, Checkpoint)):
            label = event.outcome if isinstance(event, Return) else event.kind
            _name(label)

    # Check forward reachability from entry.
    reached: set[str] = set()
    stack = [graph.entry]
    while stack:
        budget.spend()
        current = stack.pop()
        if current in reached:
            continue
        reached.add(current)
        stack.extend(
            successor for successor in reversed(nodes[current].successors) if successor not in reached
        )
    if reached != set(nodes):
        raise AnalysisRefusalError("unreachable graph nodes")

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
        for node in graph.nodes:
            if node.name == graph.entry:
                continue
            budget.spend()
            preds = predecessors[node.name]
            if not preds:
                continue
            intersected = set(dominators[preds[0]])
            for pred in preds[1:]:
                intersected &= dominators[pred]
            intersected.add(node.name)
            updated = frozenset(intersected)
            if updated != dominators[node.name]:
                dominators[node.name] = updated
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


def _containment(child: Place, parent: Place) -> Overlap:
    """A repeated unknown index spelling establishes no index identity."""
    if child.owner != parent.owner:
        return "no"
    unknown = False
    for child_field, parent_field in zip(child.fields, parent.fields, strict=False):
        if child_field == "*" or parent_field == "*":
            unknown = True
        elif child_field != parent_field:
            return "no"
    if len(child.fields) < len(parent.fields):
        return "unknown" if unknown else "no"
    return "unknown" if unknown else "yes"


def _overlap(left: Place, right: Place,
             fields_by_owner: dict[str, frozenset[tuple[str, ...]]]) -> Overlap:
    if left.owner != right.owner:
        return "no"
    if _within(left, right):
        return "unknown" if "*" in right.fields else "yes"
    if _within(right, left):
        return "unknown" if "*" in left.fields else "yes"
    for index, (first, second) in enumerate(zip(left.fields, right.fields, strict=False)):
        if first != second:
            fields = fields_by_owner[left.owner]
            if (first != "*" and second != "*" and left.fields[:index + 1] in fields
                    and right.fields[:index + 1] in fields):
                return "no"
            return "unknown"
        if first == "*":
            return "unknown"
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


class _State:
    def __init__(
        self,
        owners: dict[str, Owner],
        fields: dict[str, frozenset[tuple[str, ...]]],
        budget: _Budget,
        entry_name: str,
    ) -> None:
        self.owners = owners
        self.fields = fields
        self.budget = budget
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
        self.invalid: set[str] = set()

    def clone(self) -> _State:
        self.budget.spend()
        copy = _State.__new__(_State)
        copy.owners = self.owners
        copy.fields = self.fields
        copy.budget = self.budget
        copy.nodes = self.nodes
        copy.outcome = self.outcome
        copy.issues = list(self.issues)
        copy.issues_emitted = self.issues_emitted
        copy.obligations = list(self.obligations)
        copy.restorations = list(self.restorations)
        copy.values = dict(self.values)
        copy.loans = dict(self.loans)
        copy.parents = dict(self.parents)
        copy.last_demand_node = dict(self.last_demand_node)
        copy.seen_binders = dict(self.seen_binders)
        copy.active = set(self.active)
        copy.reserved = set(self.reserved)
        copy.opened = set(self.opened)
        copy.active_invariants = set(self.active_invariants)
        copy.explicit_invariants = dict(self.explicit_invariants)
        copy.returned = self.returned
        copy.moved = set(self.moved)
        copy.invalid = set(self.invalid)
        return copy

    def join_key(self, relevant_names: frozenset[str], history_names: set[str]) -> tuple[object, ...]:
        self.budget.spend(len(relevant_names) + len(self.active) + len(self.reserved))
        relevant_values = {name: self.values[name] for name in relevant_names if name in self.values}
        relevant_loans = self.ancestors(self.active | self.reserved | {
            loan for value in relevant_values.values() for loan in value.captures
        })
        relevant_binders = (relevant_names & history_names) | self.reserved
        return (
            frozenset(relevant_values.items()),
            frozenset((name, self.loans[name], self.parents[name], self.last_demand_node.get(name))
                      for name in relevant_loans),
            frozenset((name, self.seen_binders[name]) for name in relevant_binders if name in self.seen_binders),
            frozenset(self.active),
            frozenset(self.reserved),
            frozenset(self.opened),
            frozenset(self.active_invariants),
            frozenset(self.explicit_invariants.items()),
            frozenset(self.moved),
            frozenset(self.invalid & relevant_loans),
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

    def issue(self, node: Node, kind: str, *resources: str) -> None:
        # Repeated rejection at a loop site still rejects the current grant.
        self.issues_emitted += 1
        item = Issue(node.name, kind, resources)
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
        overlap = _overlap(place, self.loans[other].place, self.fields)
        if overlap == "unknown":
            self.obligation(node, "overlap", place.owner, *place.fields, other)
        return overlap

    def containment(self, node: Node, child: Place, parent: Place, grant: str) -> Overlap:
        self.budget.spend()
        relation = _containment(child, parent)
        if relation == "unknown":
            self.obligation(node, "footprint-containment", grant, child.owner, *child.fields)
        return relation

    def check_reserved(self, node: Node, place: Place, *resources: str) -> None:
        for other in sorted(self.reserved):
            if self.compare(node, place, other) == "yes":
                self.issue(node, "conflicting-receiver-reservation", *resources, other)

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

    def borrow(self, node: Node, name: str, *, reserve: bool = False) -> None:
        loan = self.loans[name]
        parent = self.parents[name]
        prior_issues = self.issues_emitted
        self.obligation(
            node, "receiver-reservation-interpretation" if reserve else "loan-interpretation", name, parent
        )
        if "*" in loan.place.fields:
            self.obligation(node, "unknown-footprint", name, loan.place.owner, *loan.place.fields)
        if loan.place.owner in self.moved:
            self.issue(node, "use-after-owner-move", loan.place.owner)
        if parent in self.owners:
            parent_place = Place(parent)
        else:
            parent_loan = self.loans[parent]
            parent_place = parent_loan.place
            if parent not in self.active:
                self.issue(node, "borrow-parent-has-no-grant", name, parent)
            if parent_loan.mode == "shared" and loan.mode == "exclusive":
                self.issue(node, "exclusive-from-shared", name, parent)
        if self.containment(node, loan.place, parent_place, parent) == "no":
            self.issue(node, "reborrow-outside-parent", name, parent)
        if loan.invariant is not None and self._loan_invariant(loan) not in self.opened:
            self.issue(node, "loan-invariant-not-open", name, loan.invariant)
        ancestors = self.ancestors({name}) - {name}
        for other in sorted(self.active - ancestors):
            if (loan.mode == "exclusive" and not reserve) or self.loans[other].mode == "exclusive":
                overlap = self.compare(node, loan.place, other)
                if overlap == "yes":
                    self.issue(node, "competing-loans", name, other)
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
        if event.place.owner in self.moved:
            self.issue(node, "use-after-owner-move", event.place.owner)
        if not event.place.fields:
            for pair in sorted(self.opened):
                if pair[0] == event.place.owner and self.explicit_invariants.get(pair, False):
                    self.issue(node, "open-invariant-whole-receiver", *self._invariant_res(pair))
        if event.via is not None:
            if route is None:
                return
            if route not in self.active:
                self.issue(node, "access-route-has-no-grant", route)
                return
            loan = self.loans[route]
            if self.containment(node, event.place, loan.place, route) == "no":
                self.issue(node, "access-outside-loan", route)
            if event.kind != "read" and loan.mode != "exclusive":
                self.issue(node, "write-through-shared", route)
            if event.kind == "move":
                self.issue(node, "move-through-loan-unsupported", route)
        ancestors = self.ancestors({route}) if route is not None else frozenset()
        for other in sorted(self.active - ancestors):
            overlap = self.compare(node, event.place, other)
            if overlap == "no":
                continue
            # An owner/ancestor route cannot bypass a live descendant permission.
            descendant = route is None or route in self.ancestors({other})
            exclusive_ancestor = (
                descendant and route is not None and self.loans[route].mode == "exclusive"
            )
            if overlap == "yes" and (
                exclusive_ancestor
                or event.kind != "read"
                or self.loans[other].mode == "exclusive"
            ):
                self.issue(node, "suspended-parent" if descendant else "conflicting-access", other)
        if event.kind == "move" and event.via is None:
            if event.place.fields:
                self.issue(node, "partial-owner-move-unsupported", event.place.owner)
            else:
                self.moved.add(event.place.owner)

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
            if binder in self.owners or (prior is not None and prior != node.name):
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
                        self.loans[loan.name] = loan
                        self.parents[loan.name] = route
                        if isinstance(event, Borrow):
                            self.values[loan.name] = _Value(frozenset({loan.name}), loan.name)
                        creates = loan.name
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
                        self.access(node, Access(self.loans[captured].place, via=name), captured)
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

    def finalize(self, terminal: Node) -> PathReport:
        for pair in sorted(self.opened):
            self.issue(terminal, "unclosed-invariant", *self._invariant_res(pair))
        # Retaining a descendant retains every ancestor's restoration duty and
        # scope. An unscoped descriptor cannot launder a scoped parent grant.
        for name in sorted(self.ancestors(self.returned)):
            if self.loans[name].scoped:
                self.issue(terminal, "scoped-loan-escape", name)
        for name in sorted(self.returned):
            loan = self.loans[name]
            if name in self.invalid:
                self.issue(terminal, "invalid-loan-escape", name)
            if loan.mode != "shared":
                self.issue(terminal, "exclusive-loan-escape", name)
            if not self.owners[loan.place.owner].borrowed:
                self.issue(terminal, "local-loan-escape", name)
            self.obligation(terminal, "returned-loan-lifetime", name, loan.place.owner)
        suspended = tuple(
            sorted(
                {self.loans[name].place for name in self.active},
                key=lambda place: (place.owner, place.fields),
            )
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
        )


def analyze(owners: tuple[Owner, ...], graph: Graph, limits: Limits | None = None) -> Report:
    """Return a complete, deterministic diagnostic or raise AnalysisRefusalError.

    Facts are supplied abstract inputs, not source interpretation or proved laws.
    Even a report with no issues contains unresolved interpretation obligations.
    Exhaustion at any stage discards all path results rather than returning a
    deceptively complete prefix. The API performs no file or external I/O.

    For example, ``analyze((Owner("input", borrowed=True),), Graph("lend", (
    Node("lend", Borrow(Loan("view", "input", Place("input"))), ("read",)),
    Node("read", Use("view")),)))`` proposes ending ``view`` after ``read``.
    The resulting restoration and interpretation obligations remain unresolved.
    """
    if limits is None:
        limits = Limits()
    if not isinstance(limits, Limits):
        raise AnalysisRefusalError("limits must be an immutable Limits record")
    budget = _Budget(limits.work)
    nodes, dominators = _validate(owners, graph, limits, budget)
    demanded_before, demanded_after, reachable_names = _compute_cfg_liveness(graph, nodes, budget)
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
    initial = _State(owner_map, fields, budget, graph.entry)
    entry_key = ()
    if graph.entry in join_states:
        entry_key = initial.join_key(reachable_names[graph.entry], history_names)
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
            if branch.reserved and successor in dominators[node.name]:
                enclosing = dominators[successor] - {successor}
                local_reservations = {
                    name for name in branch.reserved if branch.seen_binders[name] not in enclosing
                }
                if local_reservations:
                    branch.issue(node, "receiver-reservation-at-loop-backedge", *sorted(local_reservations))
                    branch.cancel_reservations(node, local_reservations)
            branch.end_dead(node.name, branch.live_loans(demanded_before[successor]))
            if in_degree[successor] > 1:
                env_key = branch.join_key(reachable_names[successor], history_names)
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
        if op in {"in", "ref", "out", "move"}:
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


class _FunctionLowerer:
    def __init__(
        self,
        fn_name: str,
        fn_node: dict[str, object],
        enclosing_type: str | None,
        structs: dict[str, _StructInfo],
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
        self.structs = structs
        self.checked_receivers: dict[tuple[int, ...], _Receiver | None] = {}
        self.checked_scalar_calls: set[tuple[int, ...]] = set()
        self.owners: dict[str, Owner] = {}
        self.owner_types: dict[str, str] = {}
        self.owner_fields: dict[str, set[tuple[str, ...]]] = {}
        self.owner_views: dict[str, dict[str, tuple[str, ...]]] = {}
        self.owner_invariants: dict[str, list[str]] = {}
        # Map variable name -> canonical handle name (for loans or wrappers).
        self.handles: dict[str, str] = {}
        # Map loan handle name -> Place.
        self.handle_places: dict[str, Place] = {}
        self.handle_modes: dict[str, Mode] = {}
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
    ) -> None:
        if not _NAME.fullmatch(name) or (name in self.used_binders and name not in self.owners):
            return
        if name not in self.owner_fields:
            self.owner_fields[name] = set()
            self.owner_views[name] = {}
            self.owner_invariants[name] = []
        if type_name is not None:
            self.owner_types[name] = type_name
            info = self.structs.get(type_name)
            if info is not None:
                self.owner_fields[name].update(info.fields)
                self.owner_views[name].update(info.views)
                for inv in info.invariants:
                    if inv not in self.owner_invariants[name]:
                        self.owner_invariants[name].append(inv)
        self.owners[name] = Owner(
            name,
            borrowed=borrowed,
            fields=tuple(sorted(self.owner_fields[name])),
            invariants=tuple(self.owner_invariants[name]),
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
                        pmode in {"in", "ref", "out"}
                        or bool(mods & {"in", "ref", "out"})
                        or ptype in {"Span", "Slots"}
                    )
                    and pmode != "owned"
                    and "owned" not in mods
                )
                self._register_owner(pname, borrowed=borrowed, type_name=ptype)

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

    def _place_struct(self, place: Place) -> _StructInfo | None:
        type_name = self.owner_types.get(place.owner)
        for component in place.fields:
            info = self.structs.get(type_name) if type_name is not None else None
            type_name = info.field_types.get(component) if info is not None else None
        return self.structs.get(type_name) if type_name is not None else None

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
                    return Place(base.owner, (*base.fields, "*"))
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
                fields.append("*")
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

    def _lower_condition(
        self, current: str | None, condition: dict[str, object],
    ) -> tuple[str | None, str, dict[str, str]]:
        pending = [condition]
        failure = self._fresh_node("if_else")
        outer_handles: dict[str, str] | None = None
        while pending:
            operand = pending.pop()
            if operand.get("kind") == "group":
                pending.append(_ast_node(operand.get("expression") or operand["value"]))
                continue
            if operand.get("kind") == "binary" and _op_text(operand["operator"]) == "&&":
                pending.extend((_ast_node(operand["right"]), _ast_node(operand["left"])))
                continue
            current, captures = self._lower_expr(current, operand)
            if outer_handles is None:
                outer_handles = dict(self.handles)
            split = self._emit(current, Nop(), "if_split")
            current = self._fresh_node("if_then")
            self._connect(split, current)
            self._connect(split, failure)
            if operand.get("kind") in {"is", "is_expression"}:
                current = self._bind_pattern_from_captures(
                    current, _ast_node(operand["pattern"]), captures, self._try_place(_ast_node(operand["value"])),
                )
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
                loan_mode: Mode = "shared" if mode == "in" else "exclusive"
                current, parent, place = self._resolve_borrow_target(current, inner)
                loan_name = self._fresh_loan("borrow")
                current = self._emit(
                    current,
                    Borrow(Loan(loan_name, parent, place, mode=loan_mode)),
                    "borrow",
                )
                self.handle_places[loan_name] = place
                self.handle_modes[loan_name] = loan_mode
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
        reserve_receiver = False
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
                    raise AnalysisRefusalError(f"cannot resolve receiver mode for {place.owner}.{method}")
                if signature.view is not None:
                    if signature.view not in info.views:
                        raise AnalysisRefusalError(f"unknown receiver view {signature.view!r} for {method}")
                    projection = info.views[signature.view]
            elif not _is_ident(recv) and _view_field(recv) is None:
                raise AnalysisRefusalError("cannot resolve receiver of computed method call")
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

                if amode in {"in", "ref", "out"}:
                    loan_mode: Mode = "shared" if amode == "in" else "exclusive"
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
                current = self._emit(current, Access(place, "write", via=loan_name), "call_write")
            if is_temp:
                if loan_mode == "shared" and self.in_receiver_argument and not scalar_result:
                    captured_handles.append(loan_name)
                else:
                    current = self._emit(current, Drop(loan_name), "call_drop")

        if receiver_loan is not None:
            self.current_site = receiver_site
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
        if "ref" in mods or "out" in mods:
            explicit_loan_mode = "exclusive"
        elif "in" in mods:
            explicit_loan_mode = "shared"

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

            loan_mode: Mode = "shared" if mode == "in" else "exclusive"
            current, parent, place = self._resolve_borrow_target(current, inner)
            loan_name = self._fresh_binder(binder_name)
            current = self._emit(
                current,
                Borrow(Loan(loan_name, parent, place, mode=loan_mode, scoped=scoped)),
                f"borrow_{binder_name}",
            )
            self.handles[binder_name] = loan_name
            self.handle_places[binder_name] = place
            self.handle_places[loan_name] = place
            self.handle_modes[binder_name] = loan_mode
            self.handle_modes[loan_name] = loan_mode
            return current

        current, caps = self._lower_expr(current, value_expr, handles_result=id(self.current_site) in self.result_bindings)
        if caps:
            if len(caps) == 1 and explicit_loan_mode is not None and caps[0] in self.handle_places:
                parent_handle = caps[0]
                place = self.handle_places[parent_handle]
                loan_name = self._fresh_binder(binder_name)
                current = self._emit(
                    current,
                    Borrow(Loan(loan_name, parent_handle, place, mode=explicit_loan_mode, scoped=scoped)),
                    f"reborrow_{binder_name}",
                )
                self.handles[binder_name] = loan_name
                self.handle_places[binder_name] = place
                self.handle_places[loan_name] = place
                self.handle_modes[binder_name] = explicit_loan_mode
                self.handle_modes[loan_name] = explicit_loan_mode
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
            callee = _ast_node(value_expr["callee"])
            if _is_ident(callee):
                cname = _id_text(callee["name"])
                if cname in self.structs:
                    inferred_type = cname
        self.handles.pop(binder_name, None)
        self._register_owner(binder_name, borrowed=False, type_name=inferred_type)
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
                        return self._emit(
                            current,
                            Access(self.handle_places[tname], "write", via=via),
                            f"write_{tname}",
                        )
                place = self._try_place(target)
                if place is not None:
                    if place.fields and "*" not in place.fields:
                        self._add_owner_field(place.owner, place.fields)
                    recv = target.get("receiver") or target.get("value")
                    if isinstance(recv, dict) and _is_ident(recv):
                        rname = _id_text(recv["name"])
                        if rname in self.handles:
                            return self._emit(
                                current,
                                Access(place, "write", via=self.handles[rname]),
                                "write_field",
                            )
                    return self._emit(current, Access(place, "write"), "write_field")
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
                    self._emit(current, Return(outcome, ret_caps), "ret")
                else:
                    self._emit(current, Return("return"), "ret")
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
                return current

            return current
        finally:
            self.current_site = prev_site

    def build(self) -> LoweredFunction:
        self._collect_signature_facts()
        self.visible_results = set(self.result_parameters)
        entry = self._fresh_node("entry")
        body = (
            self.fn_node.get("body")
            if self.fn_node.get("body") is not None
            else self.fn_node.get("value")
        )
        if isinstance(body, list) or (isinstance(body, dict) and body.get("kind") == "block"):
            end = self._lower_statements(entry, _body_statements(body))
            if end is not None and not isinstance(self.events.get(end), Return):
                self._emit(end, Return("return"), "ret")
        elif isinstance(body, dict):
            end, caps = self._lower_expr(entry, body, handles_result=True)
            ret_caps = (
                ()
                if self.returns_scalar_value and _extract_borrow_expr(body) is None
                else caps
            )
            if end is not None and not isinstance(self.events.get(end), Return):
                self._emit(end, Return("return", ret_caps), "ret")
        else:
            self._emit(entry, Return("return"), "ret")

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
            Graph(entry, built_nodes),
            site_map,
        )


def _unwrap_ast_root(ast: object) -> dict[str, object]:
    node = _ast_node(ast, "AST root")
    if "ast" in node and isinstance(node["ast"], dict):
        return _ast_node(node["ast"], "inner AST root")
    return node


def lower_function(ast: object, function_name: str | None = None) -> LoweredFunction:
    """Lower a parsed schema-2 function, method or definition into a loan Graph."""
    root = _unwrap_ast_root(ast)
    kind = root.get("kind")
    if kind in {"function", "method", "definition"}:
        fname = _id_text(root["name"])
        if function_name is not None and function_name != fname:
            raise AnalysisRefusalError(f"function {function_name!r} not found")
        return _FunctionLowerer(fname, root, None, {}).build()

    if kind not in {"surface_file", "module", "file"}:
        raise AnalysisRefusalError("expected a parsed module or function AST node")

    declarations = _ast_nodes(root.get("declarations", []))
    structs = _collect_structs(declarations)
    functions = _find_functions(declarations)
    if not functions:
        raise AnalysisRefusalError("no function with a body found in module")
    if function_name is None:
        selected_name, selected_node, enclosing = functions[0]
        return _FunctionLowerer(selected_name, selected_node, enclosing, structs).build()
    for candidate_name, candidate_node, enclosing in functions:
        if candidate_name == function_name:
            return _FunctionLowerer(candidate_name, candidate_node, enclosing, structs).build()
    raise AnalysisRefusalError(f"function {function_name!r} not found in module")


def lower_module(ast: object) -> tuple[LoweredFunction, ...]:
    """Lower all functions, methods and definitions with bodies in a schema-2 module."""
    root = _unwrap_ast_root(ast)
    if root.get("kind") not in {"surface_file", "module", "file"}:
        return (lower_function(root),)
    declarations = _ast_nodes(root.get("declarations", []))
    structs = _collect_structs(declarations)
    seen_nodes: set[int] = set()
    lowered: list[LoweredFunction] = []
    for candidate_name, candidate_node, enclosing in _find_functions(declarations):
        if id(candidate_node) in seen_nodes:
            continue
        seen_nodes.add(id(candidate_node))
        lowered.append(_FunctionLowerer(candidate_name, candidate_node, enclosing, structs).build())
    if not lowered:
        raise AnalysisRefusalError("no function with a body found in module")
    return tuple(lowered)


def analyze_function(
    ast: object, function_name: str | None = None, limits: Limits | None = None
) -> Report:
    """Lower and analyze one schema-2 function, method or definition."""
    lowered = lower_function(ast, function_name)
    return analyze(lowered.owners, lowered.graph, limits)


def analyze_module(
    ast: object, limits: Limits | None = None
) -> dict[str, Report]:
    """Lower and analyze every function with a body in a schema-2 module."""
    return {
        lowered.name: analyze(lowered.owners, lowered.graph, limits)
        for lowered in lower_module(ast)
    }
