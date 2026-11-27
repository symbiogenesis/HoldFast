# SPDX-License-Identifier: Apache-2.0
"""Loan-flow checks over hand-built graphs, parser ASTs, and authored source."""

import json
import re
import subprocess
from collections.abc import Callable
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import cast

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import parser, proofenv, regions, rocq_cache, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.elaborate import elaborate
from toolchain.loans import (
    Access,
    Activate,
    AnalysisRefusalError,
    AssumeDisjoint,
    AssumeIndexNe,
    AssumeNoRealloc,
    AssumeRefinement,
    AssumeTagPreserved,
    Bind,
    Borrow,
    Checkpoint,
    CloseInvariant,
    Drop,
    DropRefinement,
    Event,
    Graph,
    InvalidateSymbol,
    Limits,
    Loan,
    Move,
    Node,
    Nop,
    OpenInvariant,
    Owner,
    PathReport,
    Place,
    ProvedFacts,
    Reserve,
    Return,
    Use,
    UseRefinement,
    _Budget,
    _State,
    _Value,
    analyze,
    analyze_function,
    analyze_module,
    base_loan_name,
    export_loan_certificate,
    lower_function,
    lower_module,
)

INDEPENDENT_CASES = True

_ROOT = Place("workspace")
_BYTES = Place("workspace", ("bytes",))
_AUDIT = Place("workspace", ("audit",))
_OWNERS = (Owner("workspace", borrowed=True, fields=(("bytes",), ("audit",))),)


def _graph(*events: Event) -> Graph:
    return Graph("n0", tuple(Node(f"n{index}", event,
                                 (f"n{index + 1}",) if index + 1 < len(events) else ())
                             for index, event in enumerate(events)))


def _path(*events: Event) -> PathReport:
    report = analyze(_OWNERS, _graph(*events))
    ensure(report.status == "diagnostic-only", "analysis exposed a safety verdict")
    ensure(len(report.paths) == 1, "linear fixture acquired extra paths")
    return report.paths[0]


def _kinds(path: PathReport) -> set[str]:
    return {issue.kind for issue in path.issues}


def _ends(path: PathReport) -> list[tuple[str, str, str]]:
    return [(end.node, end.loan, end.parent) for end in path.restorations]


def _refuses(action: Callable[[], object], text: str) -> None:
    with raises(AnalysisRefusalError, msg=f"analysis did not refuse {text}") as raised:
        action()
    error = raised.exception
    ensure(text in str(error), f"wrong structural refusal: {error}")


def _last_use_and_residuals() -> None:
    path = _path(Borrow(Loan("reader", "workspace", _BYTES)), Use("reader"),
                 Access(_BYTES, "write"), Return("done"))
    ensure(not path.issues, f"last-use fixture conflicts: {path.issues}")
    ensure(_ends(path) == [("n1", "reader", "workspace")], "loan did not end exactly after its use")
    ensure(not path.retained_loans and not path.suspended, "ended loan still suspends its parent")
    ensure(all(end.status == "unresolved" for end in path.restorations), "restoration was called proved")
    obligations = {(item.node, item.kind, item.resources) for item in path.obligations}
    for expected in (("n0", "supplied-interpretation", ("workspace",)),
                     ("n0", "supplied-separation", ("workspace",)),
                     ("n1", "restoration", ("reader", "workspace")),
                     ("n2", "content-refinement-invalidation", ("workspace",))):
        ensure(expected in obligations, f"lost unresolved model obligation {expected}")
    ensure(all(item.status == "unresolved" for item in path.obligations), "residual status changed")
    unused = _path(Borrow(Loan("unused", "workspace", _BYTES)))
    ensure(_ends(unused) == [("n0", "unused", "workspace")], "terminal unused loan escaped accounting")


def _nested_restoration_and_suspension() -> None:
    prefix = (Borrow(Loan("writer", "workspace", _BYTES, "exclusive")),
              Borrow(Loan("reader", "writer", _BYTES)))
    path = _path(*prefix, Use("reader"), Access(_BYTES, "write"))
    ensure(not path.issues, "nested loan did not restore its parent before owner write")
    ensure(_ends(path) == [("n2", "reader", "writer"), ("n2", "writer", "workspace")],
           "nested restoration lost descendant-first order at last use")
    for interaction in (Use("writer"), Access(_BYTES, "read", "writer"), Access(_ROOT, "read")):
        neighbor = _path(*prefix, interaction, Use("reader"))
        ensure("suspended-parent" in _kinds(neighbor), "live child did not suspend ancestor access")
        ensure(_ends(neighbor)[-2:] == [("n3", "reader", "writer"), ("n3", "writer", "workspace")],
               "rejected parent use prematurely restored a descendant")


def _receiver_reservations() -> None:
    receiver = Reserve(Loan("receiver", "workspace", _BYTES, "exclusive", scoped=True))
    reader = Borrow(Loan("reader", "workspace", _BYTES))
    path = _path(reader, receiver, Access(_AUDIT, "write"), Use("reader"), Activate("receiver"),
                 Access(_BYTES, "write", via="receiver"), Return("done"))
    ensure(not path.issues, f"a short shared loan or a disjoint write blocked the receiver: {path.issues}")
    ensure(_ends(path) == [("n3", "reader", "workspace"), ("n5", "receiver", "workspace")],
           "shared and exclusive grants did not restore in phase order")

    retained = _path(receiver, reader, Bind("capture", ("reader",)), Activate("receiver", ("capture",)),
                     Return("done"))
    ensure(bool(retained.issues) and retained.issues[0].node == "n3"
           and retained.issues[0].kind == "competing-loans",
           f"alias retained by an argument did not conflict at activation: {retained.issues}")

    for access in (Access(_BYTES, "write"), Access(_ROOT, "move")):
        conflict = _path(receiver, access, Activate("receiver"), Return("done"))
        ensure(bool(conflict.issues) and conflict.issues[0].node == "n1"
               and conflict.issues[0].kind == "conflicting-receiver-reservation",
               f"overlapping argument access did not conflict with the reservation: {conflict.issues}")

    report = analyze((*_OWNERS, Owner("item")), Graph("reserve", (
        Node("reserve", receiver, ("transfer",)),
        Node("transfer", Access(Place("item"), "move"), ("ok", "error")),
        Node("ok", Activate("receiver"), ("write",)),
        Node("write", Access(_BYTES, "write", via="receiver"), ("return",)),
        Node("return", Return("done")),
        Node("error", Return("error")),
    )))
    success, failure = (next(path for path in report.paths if path.outcome == outcome)
                        for outcome in ("done", "error"))
    ensure(not success.issues and not failure.issues, f"receiver exit handling failed: {report.paths}")
    ensure(_ends(success) == [("write", "receiver", "workspace")] and not failure.restorations,
           "a cancellation introduced a receiver restoration or a successful call lost it")
    ensure(failure.moved_owners == ("item",) and not failure.retained_loans and not failure.suspended,
           "cancelled receiver changed another argument's ownership or retained a loan")

    nested = Reserve(Loan("nested", "parent", _BYTES, "exclusive", scoped=True))
    report = analyze(_OWNERS, Graph("parent", (
        Node("parent", Borrow(Loan("parent", "workspace", _BYTES, "exclusive")), ("reserve",)),
        Node("reserve", nested, ("branch",)),
        Node("branch", Nop(), ("activate", "error")),
        Node("activate", Activate("nested"), ("write",)),
        Node("write", Access(_BYTES, "write", via="nested"), ("return",)),
        Node("return", Return("done")),
        Node("error", Return("error")),
    )))
    success, failure = (next(path for path in report.paths if path.outcome == outcome)
                        for outcome in ("done", "error"))
    ensure(not success.issues and not failure.issues, f"reservation lost its active parent: {report.paths}")
    ensure(_ends(success) == [("write", "nested", "parent"), ("write", "parent", "workspace")]
           and _ends(failure) == [("error", "parent", "workspace")],
           "the parent must remain held through activation or cancellation")

    report = analyze(_OWNERS, Graph("reserve", (
        Node("reserve", receiver, ("read_bytes", "read_audit")),
        Node("read_bytes", reader, ("activate",)),
        Node("read_audit", Borrow(Loan("sibling", "workspace", _AUDIT)), ("activate",)),
        Node("activate", Activate("receiver", possible_captures=("reader", "sibling")), ("write",)),
        Node("write", Access(_BYTES, "write", via="receiver"), ("return",)),
        Node("return", Return("done")),
    )))
    ensure(len(report.paths) == 2 and sum(not path.issues for path in report.paths) == 1
           and all(path.issues[0].kind == "competing-loans" for path in report.paths if path.issues)
           and all(issue.kind != "unavailable-name" for path in report.paths for issue in path.issues),
           f"argument branch captures were merged or checked off-path: {report.paths}")


def _field_partitions_and_unknowns() -> None:
    path = _path(Borrow(Loan("reader", "workspace", _BYTES)), Access(_AUDIT, "write"), Use("reader"))
    ensure(not path.issues and not any(item.kind == "overlap" for item in path.obligations),
           "declared disjoint audit field was not framed")
    overlap = _path(Borrow(Loan("reader", "workspace", _BYTES)), Access(_ROOT, "write"), Use("reader"))
    ensure("suspended-parent" in _kinds(overlap), "containing footprint did not conflict")
    unknown = Place("workspace", ("other",))
    residual = _path(Borrow(Loan("reader", "workspace", _BYTES)), Access(unknown, "write"), Use("reader"))
    ensure(any(item.kind == "overlap" and item.node == "n1" for item in residual.obligations),
           "undeclared fields were assumed disjoint by spelling")
    indexed = Place("workspace", ("bytes", "*"))
    residual = _path(Borrow(Loan("reader", "workspace", indexed)),
                     Access(indexed, "write"), Use("reader"))
    ensure(any(item.kind == "overlap" for item in residual.obligations),
           "unknown array index was treated as an exact location")
    # A split below an unknown common projection cannot justify array disjointness.
    owner = (Owner("array", fields=(("*", "left"),)),)
    _refuses(lambda: analyze(owner, Graph("entry", (Node("entry"),))), "unknown")


def _unknown_footprints_without_competitors() -> None:
    indexed = Place("workspace", ("bytes", "*"))
    path = _path(Borrow(Loan("reader", "workspace", indexed)),
                 Access(indexed, via="reader"))
    ensure(not path.issues, "unknown projection was mislabeled as definitely outside its grant")
    residuals = {(item.node, item.kind) for item in path.obligations}
    ensure({("n0", "unknown-footprint"), ("n1", "unknown-footprint"),
            ("n1", "footprint-containment")} <= residuals,
           "a lone loan/access assumed equal unknown indices without a specific residual")
    direct = _path(Access(indexed))
    ensure(any(item.kind == "unknown-footprint" for item in direct.obligations),
           "direct owner projection silently resolved its unknown footprint")
    named = Place("workspace", ("bytes", "element"))
    for parent, child in ((indexed, named), (named, indexed)):
        path = _path(Borrow(Loan("writer", "workspace", parent, "exclusive")),
                     Borrow(Loan("reader", "writer", child)), Access(child, via="reader"))
        ensure("reborrow-outside-parent" not in _kinds(path)
               and any(item.node == "n1" and item.kind == "footprint-containment"
                       for item in path.obligations),
               "unknown/named reborrow relation was reported as definitely outside or contained")
    shared_write = _path(Borrow(Loan("reader", "workspace", indexed)),
                         Access(indexed, "write", "reader"))
    ensure("write-through-shared" in _kinds(shared_write),
           "an unknown footprint concealed the independent shared-write violation")
    malformed = _graph(Borrow(Loan("reader", "workspace", Place("workspace", ("bytes", "**")))))
    _refuses(lambda: analyze(_OWNERS, malformed), "normalized identifiers")


def _shared_and_exclusive_grants() -> None:
    shared = _path(Borrow(Loan("first", "workspace", _BYTES)),
                   Borrow(Loan("second", "workspace", _BYTES)), Use("first"), Use("second"))
    ensure(not shared.issues, "compatible shared sibling handles conflict")
    shared_owner_read = _path(Borrow(Loan("first", "workspace", _BYTES)),
                              Access(_BYTES, "read"), Use("first"))
    ensure(not shared_owner_read.issues, "shared borrow conflicted with concurrent owner read")
    for mode in ("shared", "exclusive"):
        loan = Loan("second", "workspace", _BYTES, "shared" if mode == "shared" else "exclusive")
        neighbor = _path(Borrow(Loan("first", "workspace", _BYTES, "exclusive")),
                         Borrow(loan), Use("first"), Use("second"))
        ensure("competing-loans" in _kinds(neighbor), "exclusive grant did not exclude overlapping sibling")
    for operation in ("write", "move"):
        event = Access(_BYTES, "write" if operation == "write" else "move", "reader")
        neighbor = _path(Borrow(Loan("reader", "workspace", _BYTES)), event)
        ensure("write-through-shared" in _kinds(neighbor), "shared grant authorized mutation")
    exclusive = _path(Borrow(Loan("writer", "workspace", _BYTES, "exclusive")),
                      Access(_BYTES, "write", "writer"))
    ensure(not exclusive.issues, "exclusive grant could not write its own footprint")
    outside = _path(Borrow(Loan("writer", "workspace", _BYTES, "exclusive")),
                    Access(_AUDIT, "write", "writer"))
    ensure("access-outside-loan" in _kinds(outside), "grant escaped its supplied footprint")
    invalid = _path(Borrow(Loan("reader", "workspace", _BYTES)),
                    Borrow(Loan("writer", "reader", _BYTES, "exclusive")), Use("writer"))
    ensure("exclusive-from-shared" in _kinds(invalid), "shared ancestor manufactured exclusivity")
    ensure("access-route-has-no-grant" in _kinds(invalid)
           and all(end.loan != "writer" for end in invalid.restorations),
           "invalid reborrow installed/restored a usable grant")
    escaped = _path(Borrow(Loan("writer", "workspace", _BYTES, "exclusive")),
                    Borrow(Loan("reader", "writer", _AUDIT)), Use("reader"))
    ensure("reborrow-outside-parent" in _kinds(escaped), "child footprint escaped its parent")
    ensure("access-route-has-no-grant" in _kinds(escaped), "out-of-footprint child received a grant")


def _transitive_captures_and_moves() -> None:
    path = _path(Borrow(Loan("reader", "workspace", _BYTES)), Bind("inner", ("reader",)),
                 Bind("outer", ("inner",)), Move("outer", "moved"),
                 Access(_BYTES, "write"), Use("moved"), Access(_BYTES, "write"))
    ensure([issue.node for issue in path.issues if issue.kind == "suspended-parent"] == ["n4"],
           "wrapper/move failed to retain transitive capture until its use")
    ensure(_ends(path) == [("n5", "reader", "workspace")], "capture loan ended at lexical binding/move")
    ensure(any(item.kind == "capture-interpretation" and item.resources == ("outer", "reader")
               for item in path.obligations), "outer capture lost its transitive loan")
    unavailable = _path(Borrow(Loan("reader", "workspace", _BYTES)), Move("reader", "next"),
                        Use("reader"), Use("next"))
    ensure([(issue.node, issue.resources) for issue in unavailable.issues
            if issue.kind == "unavailable-name"] == [("n2", ("reader",))], "move kept old handle available")
    ensure(_ends(unavailable) == [("n3", "reader", "workspace")], "moved handle lost its canonical loan")
    retained = _path(Borrow(Loan("reader", "workspace", _BYTES)), Bind("inner", ("reader",)),
                     Bind("outer", ("inner",)), Drop("inner"), Drop("reader"), Use("outer"))
    ensure(not retained.issues and _ends(retained) == [("n5", "reader", "workspace")],
           "dropping original descriptors invalidated a retained capture-of-capture")
    aliases = _path(Borrow(Loan("reader", "workspace", _BYTES)), Bind("inner", ("reader",)),
                    Bind("outer", ("inner",)), Move("reader", "moved"), Drop("inner"),
                    Use("reader"), Use("outer"), Access(_BYTES, "read", "moved"))
    ensure([(issue.node, issue.kind) for issue in aliases.issues] == [("n5", "unavailable-name")],
           "canonical loan identity bypassed moved lexical name availability")
    ensure(_ends(aliases) == [("n7", "reader", "workspace")],
           "capture and moved access lost the shared canonical loan's final use")
    dropped = _path(Borrow(Loan("reader", "workspace", _BYTES)), Drop("reader"), Use("reader"))
    ensure("unavailable-name" in _kinds(dropped), "drop did not remove source availability")
    duplicate = _path(Borrow(Loan("reader", "workspace", _BYTES)), Bind("reader", ("reader",)), Use("reader"))
    ensure("ambiguous-name" in _kinds(duplicate), "shadowing merged two unnormalized resource identities")


def _branch_alternatives_and_returned_wrappers() -> None:
    graph = Graph("choose", (
        Node("choose", successors=("lend", "error")),
        Node("lend", Borrow(Loan("view", "workspace", _BYTES)), ("wrap",)),
        Node("wrap", Bind("packet", ("view",)), ("ready",)),
        Node("ready", Return("Ready", ("packet",))),
        Node("error", Access(_BYTES, "write"), ("reject",)),
        Node("reject", Return("Rejected")),
    ))
    report = analyze(_OWNERS, graph)
    ready, rejected = report.paths
    ensure(ready.outcome == "Ready" and rejected.outcome == "Rejected", "branch outcomes were merged")
    ensure(not ready.issues and not rejected.issues, "exclusive alternatives contaminated each other")
    ensure(ready.returned_loans == ("view",) and ready.retained_loans == ("view",)
           and ready.suspended == (_BYTES,) and not ready.restorations,
           "returned wrapper lost its parent suspension/restoration duty")
    ensure(any(item.kind == "returned-loan-lifetime" for item in ready.obligations),
           "returned view did not expose its lifetime proof")
    ensure(not rejected.retained_loans and not rejected.suspended, "error branch inherited success view")
    # Both paths reach one lexical join, but only one has created the name.
    graph = Graph("choose", (Node("choose", successors=("lend", "empty")),
                             Node("lend", Borrow(Loan("view", "workspace", _BYTES)), ("join",)),
                             Node("empty", successors=("join",)), Node("join", Use("view"))))
    present, absent = analyze(_OWNERS, graph).paths
    ensure(not present.issues and "unavailable-name" in _kinds(absent),
           "join invented a loan defined only on the sibling path")


def _drop_is_availability_only() -> None:
    direct = _path(Borrow(Loan("reader", "workspace", _BYTES)), Use("reader"),
                   Access(_BYTES, "write"), Drop("reader"))
    ensure(not direct.issues and _ends(direct) == [("n1", "reader", "workspace")],
           "availability-only drop extended the loan beyond its actual last use")
    wrapper = _path(Borrow(Loan("reader", "workspace", _BYTES)), Bind("wrapper", ("reader",)),
                    Use("wrapper"), Access(_BYTES, "write"), Drop("wrapper"), Drop("reader"))
    ensure(not wrapper.issues and _ends(wrapper) == [("n2", "reader", "workspace")],
           "dropping a wrapper extended its captured loan after the wrapper's last use")
    retained = _path(Borrow(Loan("reader", "workspace", _BYTES)), Bind("inner", ("reader",)),
                     Bind("outer", ("inner",)), Drop("inner"), Drop("reader"),
                     Access(_BYTES, "write"), Use("outer"), Drop("outer"))
    ensure([(issue.node, issue.kind) for issue in retained.issues] == [("n5", "suspended-parent")]
           and _ends(retained) == [("n6", "reader", "workspace")],
           "dropping original descriptors ended a loan retained by another live wrapper")
    stale = _path(Borrow(Loan("reader", "workspace", _BYTES)), Drop("reader"), Drop("reader"))
    ensure([(issue.node, issue.kind) for issue in stale.issues] == [("n2", "unavailable-name")],
           "demand-free drop stopped validating name availability")


def _escape_limits_and_ancestor_duties() -> None:
    graph = _graph(Borrow(Loan("writer", "workspace", _BYTES, "exclusive")),
                   Borrow(Loan("reader", "writer", _BYTES)), Return("Ready", ("reader",)))
    path = analyze(_OWNERS, graph).paths[0]
    ensure(not path.issues and path.returned_loans == ("reader",)
           and path.retained_loans == ("reader", "writer") and not path.restorations,
           "shared child escape lost its internal ancestor duty or exposed an exclusive grant")
    local = analyze((Owner("workspace"),), _graph(Borrow(Loan("reader", "workspace", _BYTES)),
                                                       Return("Ready", ("reader",)))).paths[0]
    ensure("local-loan-escape" in _kinds(local), "local storage outlived its owner")
    exclusive = _path(Borrow(Loan("writer", "workspace", _BYTES, "exclusive")), Return("Ready", ("writer",)))
    ensure("exclusive-loan-escape" in _kinds(exclusive), "unsupported exclusive escape was accepted")
    scoped = _path(Borrow(Loan("reader", "workspace", _BYTES, scoped=True)),
                   Bind("hidden", ("reader",)), Return("Ready", ("hidden",)))
    ensure("scoped-loan-escape" in _kinds(scoped), "wrapper hid a scoped escape")


def _scoped_ancestor_escapes() -> None:
    for scoped in (False, True):
        path = _path(Borrow(Loan("parent", "workspace", _BYTES, "exclusive", scoped=scoped)),
                     Move("parent", "moved"), Borrow(Loan("middle", "moved", _BYTES)),
                     Borrow(Loan("view", "middle", _BYTES)), Bind("wrapper", ("view",)),
                     Return("Ready", ("wrapper",)))
        expected = [("n5", "scoped-loan-escape", ("parent",))] if scoped else []
        ensure([(issue.node, issue.kind, issue.resources) for issue in path.issues] == expected,
               "a moved, transitively retained scoped ancestor escaped through an unscoped child")
        ensure(path.returned_loans == ("view",) and path.retained_loans == ("middle", "parent", "view")
               and not path.restorations,
               "escape diagnostics lost the child or its unresolved ancestor restoration duties")
    shared = _path(Borrow(Loan("scope", "workspace", _BYTES, scoped=True)),
                   Borrow(Loan("first", "scope", _BYTES)), Borrow(Loan("second", "scope", _BYTES)),
                   Return("Ready", ("first", "second")))
    ensure([(issue.node, issue.kind, issue.resources) for issue in shared.issues]
           == [("n3", "scoped-loan-escape", ("scope",))],
           "multiple returned descendants hid or duplicated their common scoped-ancestor diagnostic")
    local = _path(Borrow(Loan("scope", "workspace", _BYTES, "exclusive", scoped=True)),
                  Borrow(Loan("view", "scope", _BYTES)), Use("view"), Return("done"))
    ensure(not local.issues and _ends(local) == [("n2", "view", "scope"), ("n2", "scope", "workspace")],
           "transitive escape checks rejected locally restored descendants")


def _branch_local_names_and_moved_returns() -> None:
    # Identical resource spellings on exclusive paths denote different loans.
    # Both paths move parent and wrapper handles, then drop the original names.
    graph = Graph("choose", (
        Node("choose", successors=("lend", "reject")),
        Node("lend", Borrow(Loan("parent", "workspace", _BYTES, "exclusive")), ("lendMove",)),
        Node("lendMove", Move("parent", "movedParent"), ("lendView",)),
        Node("lendView", Borrow(Loan("view", "movedParent", _BYTES)), ("lendWrap",)),
        Node("lendWrap", Bind("packet", ("view",)), ("lendResult",)),
        Node("lendResult", Move("packet", "result"), ("lendDropView",)),
        Node("lendDropView", Drop("view"), ("lendDropParent",)),
        Node("lendDropParent", Drop("movedParent"), ("ready",)),
        Node("ready", Return("Ready", ("result",))),
        Node("reject", Borrow(Loan("parent", "workspace", _AUDIT, "exclusive", scoped=True)),
             ("rejectMove",)),
        Node("rejectMove", Move("parent", "movedParent"), ("rejectView",)),
        Node("rejectView", Borrow(Loan("view", "movedParent", _AUDIT)), ("rejectWrap",)),
        Node("rejectWrap", Bind("packet", ("view",)), ("rejectResult",)),
        Node("rejectResult", Move("packet", "result"), ("rejectUse",)),
        Node("rejectUse", Use("result"), ("rejectDropView",)),
        Node("rejectDropView", Drop("view"), ("rejectDropParent",)),
        Node("rejectDropParent", Drop("movedParent"), ("rejected",)),
        Node("rejected", Return("Rejected")),
    ))
    ready, rejected = analyze(_OWNERS, graph).paths
    ensure(not ready.issues and not rejected.issues,
           "exclusive paths merged same-spelled identities or moved captures")
    ensure(ready.outcome == "Ready" and ready.returned_loans == ("view",)
           and ready.retained_loans == ("parent", "view") and ready.suspended == (_BYTES,)
           and not ready.restorations,
           "success lost its returned child, canonical moved ancestor or byte footprint")
    ensure(rejected.outcome == "Rejected" and not rejected.returned_loans
           and not rejected.retained_loans and not rejected.suspended
           and _ends(rejected) == [("rejectUse", "view", "parent"),
                                   ("rejectUse", "parent", "workspace")],
           "failure retained the sibling's byte view or lost local audit restoration")
    for path, node in ((ready, "lendWrap"), (rejected, "rejectWrap")):
        ensure(any(item.node == node and item.kind == "capture-interpretation"
                   and item.resources == ("packet", "view") for item in path.obligations),
               "branch-local wrapper lost its independent capture premise")
    escaped = Graph(graph.entry, tuple(
        Node(node.name, Return("Rejected", ("result",))) if node.name == "rejected" else node
        for node in graph.nodes))
    ready, rejected = analyze(_OWNERS, escaped).paths
    ensure(not ready.issues and [(issue.node, issue.kind, issue.resources) for issue in rejected.issues]
           == [("rejected", "scoped-loan-escape", ("parent",))],
           "returning the moved audit wrapper hid its scoped ancestor or tainted its sibling")
    ensure(rejected.retained_loans == ("parent", "view") and rejected.suspended == (_AUDIT,)
           and not rejected.restorations,
           "rejected escape erased the audit path's retained restoration obligations")


def _invalid_returned_capture_has_no_grant() -> None:
    path = _path(Borrow(Loan("writer", "workspace", _BYTES, "exclusive")),
                 Move("writer", "movedWriter"), Borrow(Loan("view", "movedWriter", _AUDIT)),
                 Bind("inner", ("view",)), Bind("outer", ("inner",)),
                 Move("outer", "result"), Drop("inner"), Drop("view"),
                 Return("Ready", ("result",)))
    ensure([(issue.node, issue.kind, issue.resources) for issue in path.issues]
           == [("n2", "reborrow-outside-parent", ("view", "writer")),
               ("n8", "invalid-loan-escape", ("view",))],
           "nested moved return concealed an out-of-footprint grant's invalidity")
    ensure(path.returned_loans == ("view",) and path.retained_loans == ("writer",)
           and path.suspended == (_BYTES,) and not path.restorations,
           "invalid child installed authority or erased its real ancestor's unresolved duty")
    ensure(any(item.kind == "returned-loan-lifetime" and item.resources == ("view", "workspace")
               for item in path.obligations), "invalid escape silently discarded its lifetime premise")


def _owner_moves() -> None:
    path = _path(Borrow(Loan("reader", "workspace", _BYTES)), Access(_ROOT, "move"), Use("reader"))
    ensure("suspended-parent" in _kinds(path), "owner moved under its live child")
    moved = _path(Access(_ROOT, "move"), Access(_BYTES), Borrow(Loan("reader", "workspace", _BYTES)), Use("reader"))
    ensure("use-after-owner-move" in _kinds(moved) and moved.moved_owners == ("workspace",),
           "old owner route survived move")
    partial_wildcard = _path(Access(Place("workspace", ("bytes", "*")), "move"))
    ensure("partial-owner-move-unsupported" in _kinds(partial_wildcard),
           "wildcard partial move acquired an implicit rule")

    # Partial field moves: disjoint field moves + re-initialization before whole-owner use succeed.
    disjoint_moves = _path(
        Access(_BYTES, "move"),
        Access(_AUDIT, "move"),
        Return("done"),
    )
    ensure(not disjoint_moves.issues and disjoint_moves.moved_places == (_AUDIT, _BYTES),
           f"disjoint partial field moves failed: {disjoint_moves}")

    reinit_ok = _path(
        Access(_BYTES, "move"),
        Access(_AUDIT, "read"),
        Access(_BYTES, "write"),
        Access(_ROOT, "move"),
        Return("done"),
    )
    ensure(not reinit_ok.issues and reinit_ok.moved_owners == ("workspace",) and not reinit_ok.moved_places,
           f"re-initializing moved field before whole-owner move failed: {reinit_ok}")

    # Negative controls: reading a moved field or moving a partially moved owner without re-init.
    read_moved_field = _path(Access(_BYTES, "move"), Access(_BYTES, "read"))
    ensure("use-after-owner-move" in _kinds(read_moved_field),
           f"reading a moved field was not rejected: {read_moved_field.issues}")
    move_partial_owner = _path(Access(_BYTES, "move"), Access(_ROOT, "move"))
    ensure("use-after-owner-move" in _kinds(move_partial_owner),
           f"moving a partially moved owner without re-init was not rejected: {move_partial_owner.issues}")
    double_field_move = _path(Access(_BYTES, "move"), Access(_BYTES, "move"))
    ensure("use-after-owner-move" in _kinds(double_field_move),
           f"double field move was not rejected: {double_field_move.issues}")


def _invariants_and_boundaries() -> None:
    path = _path(OpenInvariant("cell"), Borrow(Loan("guard", "workspace", _BYTES,
                                                 "exclusive", scoped=True, invariant="cell")),
                 Bind("wrapper", ("guard",)), Checkpoint(), Use("wrapper"), CloseInvariant("cell"))
    ensure({"unsupported-boundary", "scoped-loan-at-boundary", "open-invariant-at-boundary"} <= _kinds(path),
           "capture wrapper concealed a live guard/open invariant at await")
    ensure(_ends(path) == [("n4", "guard", "workspace")], "boundary ended a live guard")
    ensure(any(item.kind == "invariant-close" and item.status == "unresolved" for item in path.obligations),
           "last use silently discharged the close debt")
    early = _path(OpenInvariant("cell"), Borrow(Loan("guard", "workspace", _BYTES,
                                                  scoped=True, invariant="cell")),
                  CloseInvariant("cell"), Use("guard"))
    ensure("invariant-closed-with-live-loan" in _kinds(early), "close bypassed a retained descendant")
    unclosed = _path(OpenInvariant("cell"), Return())
    ensure("unclosed-invariant" in _kinds(unclosed), "return discarded its close debt")
    dead = _path(Borrow(Loan("guard", "workspace", _BYTES, scoped=True)), Use("guard"), Checkpoint())
    ensure("scoped-loan-at-boundary" not in _kinds(dead) and "unsupported-boundary" in _kinds(dead),
           "unused guard was retained, or ready/empty await was silently qualified")


def _structural_refusals() -> None:
    examples: tuple[tuple[Graph, str], ...] = (
        (Graph("start", (Node("start"), Node("start"))), "duplicate graph"),
        (Graph("absent", (Node("start"),)), "missing entry"),
        (Graph("start", (Node("start", successors=("absent",)),)), "missing successor"),
        (Graph("start", (Node("start", successors=("end", "end")), Node("end"))), "duplicate edges"),
        (Graph("start", (Node("start", successors=("start",)),)), "cyclic"),
        (Graph("start", (Node("start"), Node("unreachable"))), "unreachable"),
        (Graph("start", (Node("start", Return(), ("end",)), Node("end"))), "return node"),
        (_graph(Use("absent")), "missing resource"),
        (_graph(Access(Place("absent"))), "missing place"),
        (_graph(CloseInvariant("absent")), "missing invariant"),
        (_graph(Bind("first", ("second",)), Bind("second", ("first",))), "cyclic loan/capture"),
    )
    for graph, message in examples:
        _refuses(lambda graph=graph: analyze(_OWNERS, graph), message)
    duplicate = (Owner("workspace"), Owner("workspace"))
    _refuses(lambda: analyze(duplicate, _graph(Return())), "duplicate owner")
    _refuses(lambda: analyze(_OWNERS, _graph(Return()), Limits(work=0)), "positive integers")


def _complete_exploration_and_budgets() -> None:
    graph = Graph("choose", (Node("choose", successors=("left", "right")),
                             Node("left", Return("left")), Node("right", Return("right"))))
    _refuses(lambda: analyze(_OWNERS, graph, Limits(paths=1)), "path budget")
    _refuses(lambda: analyze(_OWNERS, graph, Limits(nodes=2)), "node budget")
    _refuses(lambda: analyze((*_OWNERS, Owner("second")), graph, Limits(owners=1)), "owner")
    _refuses(lambda: analyze(_OWNERS, _graph(Borrow(Loan("view", "workspace", _BYTES)),
                                            Bind("wrapper", ("view", "view"))), Limits(captures=2)),
             "capture/reference")
    _refuses(lambda: analyze(_OWNERS, graph, Limits(work=1)), "work budget")
    # Determinism includes proposed ends, residual order and complete alternatives.
    ensure(analyze(_OWNERS, graph) == analyze(_OWNERS, graph), "unchanged inputs changed diagnostics")
    # Exhaustion during analysis, after preflight/enumeration, still returns no prefix.
    for work in range(1, 60):
        try:
            report = analyze(_OWNERS, graph, Limits(work=work))
        except AnalysisRefusalError:
            continue
        ensure(len(report.paths) == 2, "budget exhaustion exposed a partial report")


def _generated_branch_demand_oracle() -> None:
    # Independent finite model: only explicit reads demand the shared loan.
    # A parent write before that path's last read conflicts; an audit-field
    # write never does. The sibling's reads must not affect either decision.
    alternatives = tuple(product(("use", "write", "audit", "idle"), repeat=2))

    def event(operation: str) -> Event:
        match operation:
            case "use":
                return Use("reader")
            case "write":
                return Access(_BYTES, "write")
            case "audit":
                return Access(_AUDIT, "write")
            case _:
                return Nop()

    for left, right in product(alternatives, repeat=2):
        nodes = [Node("lend", Borrow(Loan("reader", "workspace", _BYTES)), ("left0", "right0"))]
        for branch, operations in (("left", left), ("right", right)):
            nodes.extend(Node(f"{branch}{index}", event(operation),
                              (f"{branch}1",) if index == 0 else ())
                         for index, operation in enumerate(operations))
        reports = analyze(_OWNERS, Graph("lend", tuple(nodes))).paths
        ensure(len(reports) == 2, "finite branch oracle lost an alternative")
        for report, branch, operations in zip(reports, ("left", "right"), (left, right), strict=True):
            last_read = max((index for index, operation in enumerate(operations) if operation == "use"),
                            default=-1)
            end_node = "lend" if last_read < 0 else f"{branch}{last_read}"
            expected = [(f"{branch}{index}", "suspended-parent", ("reader",))
                        for index, operation in enumerate(operations)
                        if operation == "write" and index < last_read]
            ensure([(issue.node, issue.kind, issue.resources) for issue in report.issues] == expected,
                   f"branch demand/conflict differs from independent oracle: {branch}, {operations}")
            ensure(_ends(report) == [(end_node, "reader", "workspace")],
                   f"restoration differs from explicit last-read oracle: {branch}, {operations}")
            ensure(not report.retained_loans and not report.suspended and not report.returned_loans,
                   "finite branch retained a loan after its last demand")
            ensure(all(item.status == "unresolved" for item in report.obligations),
                   "finite oracle promoted supplied facts into checked obligations")


def _malformed_records_and_edges() -> None:
    # Deliberately cross the annotated API boundary: malformed supplied facts
    # must refuse the whole analysis rather than leak an incidental Python error.
    def supplied(value: object) -> object:
        return value

    examples: tuple[tuple[object, str], ...] = (
        (None, "Graph record"),
        (Graph(cast("str", supplied([])), (Node("entry"),)), "normalized identifiers"),
        (Graph("entry", cast("tuple[Node, ...]", supplied([Node("entry")]))), "immutable tuples"),
        (Graph("entry", (cast("Node", supplied(None)),)), "Node record"),
        (Graph("entry", (Node("entry", successors=(cast("str", supplied([])),)),)), "normalized identifiers"),
        (Graph("entry", (Node("entry", successors=cast("tuple[str, ...]", supplied(["entry"]))),)), "edges"),
        (_graph(Borrow(cast("Loan", supplied(None)))), "Loan record"),
        (_graph(Borrow(Loan(cast("str", supplied(None)), "workspace", _BYTES))), "normalized identifiers"),
        (_graph(Bind(cast("str", supplied(None)), ())), "normalized identifiers"),
        (_graph(Move("workspace", cast("str", supplied(None)))), "normalized identifiers"),
        (_graph(Borrow(Loan("view", "workspace", cast("Place", supplied(None))))), "Place record"),
        (_graph(Access(cast("Place", supplied(None)))), "Place record"),
        (_graph(Access(Place(cast("str", supplied([]))))), "normalized identifiers"),
        (_graph(Access(Place("workspace", cast("tuple[str, ...]", supplied(None))))), "projection"),
        (_graph(Borrow(Loan("view", "workspace", _BYTES, invariant=cast("str", supplied([]))))),
         "normalized identifiers"),
        (_graph(CloseInvariant(cast("str", supplied([])))), "normalized identifiers"),
    )
    for graph, message in examples:
        _refuses(lambda graph=graph: analyze(_OWNERS, cast("Graph", graph)), message)
    for owners, message in (
        ((cast("Owner", supplied(None)),), "Owner record"),
        ((Owner("workspace", fields=(cast("tuple[str, ...]", supplied(7)),)),), "projection"),
    ):
        _refuses(lambda owners=owners: analyze(owners, _graph(Return())), message)
    _refuses(lambda: analyze(_OWNERS, _graph(Return()), cast("Limits", supplied({}))), "Limits record")


def _selective_invariant_lifting() -> None:
    paired = tuple(Owner(name, fields=(("value",),), invariants=("Sorted",)) for name in ("a", "b"))
    cross_owner = analyze(paired, _graph(
        OpenInvariant("a", ("Sorted",)),
        Borrow(Loan("guard", "b", Place("b", ("value",)), invariant="Sorted")),
        Use("guard"), CloseInvariant("a", ("Sorted",)), Return(),
    )).paths[0]
    ensure("loan-invariant-not-open" in _kinds(cross_owner), "a.Sorted granted access to b.Sorted")
    buffer_owners = (
        Owner(
            "this",
            borrowed=True,
            fields=(("length",), ("slots",)),
            invariants=("LengthBound", "InitializedPrefix", "VacantSuffix"),
        ),
    )
    slots = Place("this", ("slots",))
    length = Place("this", ("length",))
    graph = _graph(
        OpenInvariant("this", ("InitializedPrefix", "VacantSuffix")),
        Access(slots, "write"),
        Access(length, "write"),
        CloseInvariant("this", ("InitializedPrefix", "VacantSuffix")),
        Return("done"),
    )
    path = analyze(buffer_owners, graph).paths[0]
    ensure(not path.issues, f"selective invariant lifting reported unexpected issues: {path.issues}")
    ensure(
        ("n0", "invariant-active", ("this", "LengthBound"))
        in {(item.node, item.kind, item.resources) for item in path.obligations},
        "unlifted invariant clause was not kept active when sibling clauses were lifted",
    )
    ensure(
        path.active_invariants
        == (
            ("this", "InitializedPrefix"),
            ("this", "LengthBound"),
            ("this", "VacantSuffix"),
        )
        and not path.open_invariants,
        "closing lifted clauses did not restore full active invariant set",
    )

    early_return = analyze(
        buffer_owners,
        _graph(
            OpenInvariant("this", ("InitializedPrefix", "VacantSuffix")),
            Access(slots, "write"),
            Return("early"),
        ),
    ).paths[0]
    ensure(
        [(issue.kind, issue.resources) for issue in early_return.issues]
        == [
            ("unclosed-invariant", ("this", "InitializedPrefix")),
            ("unclosed-invariant", ("this", "VacantSuffix")),
        ],
        "early return while clauses were lifted did not report per-conjunct unclosed-invariant debt",
    )
    ensure(
        early_return.active_invariants == (("this", "LengthBound"),)
        and early_return.open_invariants
        == (("this", "InitializedPrefix"), ("this", "VacantSuffix")),
        "early return lost active vs lifted conjunct partition",
    )

    boundary = analyze(
        buffer_owners,
        _graph(
            OpenInvariant("this", ("InitializedPrefix", "VacantSuffix")),
            Checkpoint("await"),
            CloseInvariant("this", ("InitializedPrefix", "VacantSuffix")),
        ),
    ).paths[0]
    ensure(
        ("open-invariant-at-boundary", ("this", "InitializedPrefix"))
        in {(issue.kind, issue.resources) for issue in boundary.issues}
        and ("open-invariant-at-boundary", ("this", "VacantSuffix"))
        in {(issue.kind, issue.resources) for issue in boundary.issues},
        "checkpoint while clauses were lifted missed per-conjunct boundary issue",
    )

    whole_receiver = analyze(
        buffer_owners,
        _graph(
            OpenInvariant("this", ("InitializedPrefix",)),
            Access(Place("this"), "read"),
            CloseInvariant("this", ("InitializedPrefix",)),
        ),
    ).paths[0]
    ensure(
        ("open-invariant-whole-receiver", ("this", "InitializedPrefix"))
        in {(issue.kind, issue.resources) for issue in whole_receiver.issues},
        "whole-receiver access while a clause was lifted did not report an issue",
    )

    _refuses(
        lambda: analyze(
            buffer_owners,
            _graph(OpenInvariant("this", ("UnknownClause",)), CloseInvariant("this", ("UnknownClause",))),
        ),
        "missing invariant",
    )


def _cfg_join_merging_and_bounded_loops() -> None:
    # Twelve if/else joins represent 4,096 paths. Merging compatible states keeps
    # this graph within the default path limit.
    nodes: list[Node] = []
    for idx in range(12):
        split = f"split_{idx}"
        then_borrow = f"then_b_{idx}"
        then_use = f"then_u_{idx}"
        else_borrow = f"else_b_{idx}"
        else_use = f"else_u_{idx}"
        join = f"join_{idx}"
        next_node = f"split_{idx + 1}" if idx + 1 < 12 else "done"
        nodes.extend(
            (
                Node(split, Nop(), (then_borrow, else_borrow)),
                Node(
                    then_borrow,
                    Borrow(Loan(f"tloan_{idx}", "workspace", _BYTES)),
                    (then_use,),
                ),
                Node(then_use, Use(f"tloan_{idx}"), (join,)),
                Node(
                    else_borrow,
                    Borrow(Loan(f"eloan_{idx}", "workspace", _AUDIT, "exclusive")),
                    (else_use,),
                ),
                Node(else_use, Access(_AUDIT, "write", f"eloan_{idx}"), (join,)),
                Node(join, Access(_BYTES, "write"), (next_node,)),
            )
        )
    nodes.append(Node("done", Return("ok")))
    report = analyze(_OWNERS, Graph("split_0", tuple(nodes)))
    ensure(len(report.paths) == 1, "join-point merging did not coalesce compatible branch states")
    merged = report.paths[0]
    ensure(not merged.issues, f"merged 12-diamond CFG reported unexpected issues: {merged.issues}")
    ensure(len(merged.restorations) == 24, "merged 12-diamond CFG lost branch loan restorations")

    # The back edge reenters the loop after the element loan has ended.
    loop_graph = Graph(
        "entry",
        (
            Node("entry", Nop(), ("header",)),
            Node("header", Nop(), ("body_borrow", "exit")),
            Node(
                "body_borrow",
                Borrow(Loan("elem", "workspace", Place("workspace", ("bytes", "*")), scoped=True)),
                ("body_use",),
            ),
            Node("body_use", Use("elem"), ("body_drop",)),
            Node("body_drop", Drop("elem"), ("header",)),
            Node("exit", Access(_BYTES, "write"), ("done",)),
            Node("done", Return("ok")),
        ),
    )
    loop_report = analyze(_OWNERS, loop_graph)
    ensure(len(loop_report.paths) == 1 and not loop_report.paths[0].issues, "bounded loop failed")
    ensure(
        _ends(loop_report.paths[0]) == [("body_use", "elem", "workspace")],
        "bounded loop did not restore scoped element loan at body_use",
    )

    # The fixpoint must retain the owner move on the back edge and the zero-iteration exit.
    move_in_loop = Graph(
        "entry",
        (
            Node("entry", Nop(), ("header",)),
            Node("header", Nop(), ("body_move", "exit")),
            Node("body_move", Access(_ROOT, "move"), ("header",)),
            Node("exit", Return("done")),
        ),
    )
    moves = {path.moved_owners: _kinds(path) for path in analyze(_OWNERS, move_in_loop).paths}
    ensure(moves == {(): set(), ("workspace",): {"use-after-owner-move"}},
           f"loop fixpoint lost the zero-iteration exit or loop-carried conflict: {moves}")

    rejected_loan = Graph("moved", (
        Node("moved", Access(_ROOT, "move"), ("header",)),
        Node("header", successors=("borrow", "done")),
        Node("borrow", Borrow(Loan("view", "workspace", _BYTES)), ("use",)),
        Node("use", Use("view"), ("drop",)),
        Node("drop", Drop("view"), ("header",)),
        Node("done", Return("done")),
    ))
    [path] = analyze(_OWNERS, rejected_loan).paths
    ensure("use-after-owner-move" in _kinds(path) and not path.restorations,
           "a repeated rejection at the loop site installed a grant")


def _correlated_loan_origins_at_join() -> None:
    arms = ("left", "middle", "right")
    nodes = [Node("choose", successors=arms)]
    for arm in arms:
        moved = f"move_{arm}"
        nodes.extend((
            Node(arm, Borrow(Loan(arm, "workspace", _BYTES, "exclusive")), (moved,)),
            Node(moved, Move(arm, "handle"), ("use",)),
        ))
    nodes.extend((Node("use", Access(_BYTES, "write", via="handle"), ("done",)),
                  Node("done", Return("done"))))
    graph = Graph("choose", tuple(nodes))
    paths = analyze(_OWNERS, graph, Limits(paths=3)).paths
    ensure(len(paths) == 3 and all(not path.issues for path in paths),
           "a grant conflicted with an alternative grant from the same join")
    ensure([_ends(path) for path in paths] == [[("use", arm, "workspace")] for arm in arms],
           "the common write failed to restore the selected origin in each alternative")
    _refuses(lambda: analyze(_OWNERS, graph, Limits(paths=2)), "path budget exhausted at control-flow join")

    for order in (("audit", "bytes"), ("bytes", "audit")):
        sibling_footprints = Graph("choose", (
            Node("choose", successors=order),
            Node("audit", Borrow(Loan("view", "workspace", _AUDIT)), ("write",)),
            Node("bytes", Borrow(Loan("view", "workspace", _BYTES)), ("write",)),
            Node("write", Access(_BYTES, "write"), ("use",)),
            Node("use", Use("view"), ("done",)),
            Node("done", Return("done")),
        ))
        paths = analyze(_OWNERS, sibling_footprints).paths
        by_place = {path.restorations[0].place: path for path in paths}
        ensure(set(by_place) == {_AUDIT, _BYTES}
               and all(_ends(path) == [("use", "view", "workspace")] for path in paths),
               "a branch-local identity overwrote its sibling's footprint or restoration")
        ensure(not by_place[_AUDIT].issues
               and [(issue.node, issue.kind, issue.resources) for issue in by_place[_BYTES].issues]
               == [("write", "suspended-parent", ("view",))],
               "a branch-local identity hid a conflicting access or tainted the disjoint branch")


def _loop_entry_and_conditional_view() -> None:
    header = Node("header", successors=("body", "exit"))
    entry_loop = Graph("header", (
        header,
        Node("body", Access(_ROOT, "move"), ("header",)),
        Node("exit", Return("done")),
    ))
    paths = analyze(_OWNERS, entry_loop, Limits(paths=2)).paths
    ensure({path.moved_owners: _kinds(path) for path in paths}
           == {(): set(), ("workspace",): {"use-after-owner-move"}},
           "loop at entry lost a zero-iteration path or a loop-carried owner move")
    _refuses(lambda: analyze(_OWNERS, entry_loop, Limits(paths=1)), "path budget")
    _refuses(lambda: analyze(_OWNERS, entry_loop, Limits(work=1)), "work budget")

    for order in (("skip", "lend"), ("lend", "skip")):
        graph = Graph("header", (
            header,
            Node("body", successors=("header",)),
            Node("exit", successors=order),
            Node("skip", successors=("read",)),
            Node("lend", Borrow(Loan("view", "workspace", _BYTES)), ("read",)),
            Node("read", Use("view"), ("done",)),
            Node("done", Return("done")),
        ))
        paths = analyze(_OWNERS, graph, Limits(paths=2)).paths
        ensure(len(paths) == 2 and all(path.outcome == "done" for path in paths),
               "the common return lost an incoming view environment")
        by_branch = {("lend" if "lend" in path.nodes else "skip"): path for path in paths}
        ensure(not by_branch["lend"].issues
               and _ends(by_branch["lend"]) == [("read", "view", "workspace")],
               "the read through the live view lost its restoration")
        ensure([(issue.node, issue.kind, issue.resources) for issue in by_branch["skip"].issues]
               == [("read", "unavailable-name", ("view",))],
               "the rejected read lost its unavailable-view diagnostic")
        _refuses(lambda graph=graph: analyze(_OWNERS, graph, Limits(paths=1)), "path budget")


def _surface_ast_to_loan_graph_lowering() -> None:
    def id_node(text: str) -> dict[str, object]:
        return {"text": text, "span": [0, len(text)]}

    def ident(name: str) -> dict[str, object]:
        return {"kind": "identifier", "name": id_node(name), "span": [0, 1]}

    def member(recv: dict[str, object], field_name: str) -> dict[str, object]:
        return {"kind": "member", "receiver": recv, "member": id_node(field_name), "span": [0, 1]}

    def borrow_expr(mode: str, value: dict[str, object]) -> dict[str, object]:
        return {"kind": "borrow", "mode": mode, "value": value, "span": [0, 1]}

    def call_arg(mode: str, value: dict[str, object]) -> dict[str, object]:
        return {"kind": "call_argument", "mode": mode, "value": value, "span": [0, 1]}

    def call_expr(name: str, *args: dict[str, object]) -> dict[str, object]:
        return {
            "kind": "call",
            "callee": ident(name),
            "type_arguments": [],
            "arguments": list(args),
            "span": [0, 1],
        }

    if_chain = [
        {
            "kind": "if",
            "condition": ident("cond"),
            "then_body": [
                {
                    "kind": "let",
                    "name": id_node(f"r_{idx}"),
                    "value": borrow_expr("in", member(ident("this"), "slots")),
                },
                {"kind": "expression", "expression": call_expr("Inspect", call_arg("in", ident(f"r_{idx}")))},
            ],
            "else_body": [
                {
                    "kind": "assign",
                    "operator": "=",
                    "target": member(ident("this"), "length"),
                    "value": {"kind": "nat", "value": "0", "span": [0, 1]},
                }
            ],
        }
        for idx in range(9)
    ]

    module_ast: dict[str, object] = {
        "schema": 2,
        "ast": {
            "kind": "surface_file",
            "name": id_node("BorrowCheckModule"),
            "declarations": [
                {
                    "kind": "struct",
                    "name": id_node("BoundedBuffer"),
                    "contracts": [
                        {"kind": "invariant", "label": id_node("LengthBound"), "expression": ident("true")},
                        {"kind": "invariant", "label": id_node("InitializedPrefix"), "expression": ident("true")},
                        {"kind": "invariant", "label": id_node("VacantSuffix"), "expression": ident("true")},
                    ],
                    "members": [
                        {"kind": "field", "name": id_node("length"), "field_type": {"kind": "type", "name": id_node("usize"), "arguments": []}},
                        {"kind": "field", "name": id_node("slots"), "field_type": {"kind": "type", "name": id_node("Slots"), "arguments": []}},
                        {
                            "kind": "view",
                            "name": id_node("Entries"),
                            "clauses": [{"kind": "view_range", "name": id_node("slots"), "start": ident("zero"), "end": ident("length")}],
                        },
                        {
                            "kind": "view",
                            "name": id_node("Tail"),
                            "clauses": [{"kind": "view_index", "name": id_node("slots"), "index": ident("length")}],
                        },
                        {
                            "kind": "method",
                            "name": id_node("RelocateInto"),
                            "parameters": [
                                {
                                    "kind": "parameter",
                                    "mode": "ref",
                                    "name": id_node("destination"),
                                    "parameter_type": {"kind": "type", "name": id_node("BoundedBuffer"), "arguments": []},
                                }
                            ],
                            "contracts": [],
                            "body": [
                                {
                                    "kind": "open_invariant",
                                    "target": {
                                        "kind": "tuple",
                                        "elements": [borrow_expr("ref", ident("this")), borrow_expr("ref", ident("destination"))],
                                    },
                                    "lifts": [id_node("InitializedPrefix"), id_node("VacantSuffix")],
                                    "body": [
                                        {
                                            "kind": "expression",
                                            "expression": call_expr(
                                                "CopyRepresentation",
                                                call_arg("in", member(ident("this"), "slots")),
                                                call_arg("ref", member(ident("destination"), "slots")),
                                                call_arg("value", member(ident("this"), "length")),
                                            ),
                                        },
                                        {
                                            "kind": "expression",
                                            "expression": call_expr(
                                                "TransferType",
                                                call_arg("ref", member(ident("this"), "slots")),
                                                call_arg("ref", member(ident("destination"), "slots")),
                                                call_arg("value", member(ident("this"), "length")),
                                            ),
                                        },
                                        {
                                            "kind": "assign",
                                            "operator": "=",
                                            "target": member(ident("destination"), "length"),
                                            "value": member(ident("this"), "length"),
                                        },
                                        {
                                            "kind": "assign",
                                            "operator": "=",
                                            "target": member(ident("this"), "length"),
                                            "value": {"kind": "nat", "value": "0", "span": [0, 1]},
                                        },
                                    ],
                                }
                            ],
                        },
                        {
                            "kind": "method",
                            "name": id_node("DisjointViews"),
                            "parameters": [],
                            "contracts": [],
                            "body": [
                                {
                                    "kind": "let",
                                    "name": id_node("entries"),
                                    "value": borrow_expr("in", member(ident("this"), "Entries")),
                                },
                                {
                                    "kind": "var",
                                    "name": id_node("tail"),
                                    "value": borrow_expr("ref", member(ident("this"), "Tail")),
                                },
                                {
                                    "kind": "expression",
                                    "expression": call_expr("WriteSlot", call_arg("ref", ident("tail"))),
                                },
                                {
                                    "kind": "expression",
                                    "expression": call_expr("ReadEntries", call_arg("in", ident("entries"))),
                                },
                            ],
                        },
                        {
                            "kind": "method",
                            "name": id_node("ConflictingViewWrite"),
                            "parameters": [],
                            "contracts": [],
                            "body": [
                                {
                                    "kind": "let",
                                    "name": id_node("entries"),
                                    "value": borrow_expr("in", member(ident("this"), "Entries")),
                                },
                                {
                                    "kind": "assign",
                                    "operator": "=",
                                    "target": member(ident("this"), "slots"),
                                    "value": ident("emptySlots"),
                                },
                                {
                                    "kind": "expression",
                                    "expression": call_expr("ReadEntries", call_arg("in", ident("entries"))),
                                },
                            ],
                        },
                        {
                            "kind": "method",
                            "name": id_node("EarlyExitInScope"),
                            "parameters": [{"kind": "parameter", "mode": "value", "name": id_node("candidate"), "parameter_type": None}],
                            "contracts": [],
                            "body": [
                                {
                                    "kind": "open_invariant",
                                    "target": borrow_expr("ref", ident("this")),
                                    "lifts": [id_node("InitializedPrefix")],
                                    "body": [
                                        {
                                            "kind": "let_else",
                                            "pattern": {
                                                "kind": "constructor_pattern",
                                                "name": id_node("Some"),
                                                "arguments": [{"kind": "binding_pattern", "name": id_node("val")}],
                                            },
                                            "value": ident("candidate"),
                                            "else_body": [{"kind": "return", "value": None}],
                                        },
                                        {
                                            "kind": "assign",
                                            "operator": "=",
                                            "target": member(ident("this"), "length"),
                                            "value": ident("val"),
                                        },
                                    ],
                                }
                            ],
                        },
                        {
                            "kind": "method",
                            "name": id_node("ManyBranchesAndLoop"),
                            "parameters": [{"kind": "parameter", "mode": "value", "name": id_node("cond"), "parameter_type": None}],
                            "contracts": [],
                            "body": [
                                *if_chain,
                                {
                                    "kind": "foreach_collection",
                                    "mode": "in",
                                    "name": id_node("item"),
                                    "collection": member(ident("this"), "slots"),
                                    "contracts": [],
                                    "body": [
                                        {
                                            "kind": "expression",
                                            "expression": call_expr("Inspect", call_arg("in", ident("item"))),
                                        }
                                    ],
                                },
                            ],
                        },
                    ],
                },
                {
                    "kind": "function",
                    "name": id_node("ReceiverAliasCall"),
                    "parameters": [
                        {
                            "kind": "parameter",
                            "mode": "ref",
                            "name": id_node("builder"),
                            "parameter_type": {"kind": "type", "name": id_node("TextBuilder"), "arguments": []},
                        }
                    ],
                    "contracts": [],
                    "body": [
                        {
                            "kind": "expression",
                            "expression": call_expr(
                                "FormatWrite",
                                call_arg("ref", ident("builder")),
                                call_arg(
                                    "value",
                                    {
                                        "kind": "interpolated_string",
                                        "parts": [
                                            {"kind": "text", "value": "len="},
                                            {"kind": "interpolation", "expression": member(ident("builder"), "Length"), "format": None},
                                        ],
                                    },
                                ),
                            ),
                        }
                    ],
                },
            ],
        },
    }

    lowered_all = lower_module(module_ast)
    ensure(len(lowered_all) == 6, f"expected 6 lowered functions, got {len(lowered_all)}")
    reports = analyze_module(module_ast)

    relocate = reports["BoundedBuffer.RelocateInto"].paths[0]
    ensure(not relocate.issues, f"RelocateInto reported unexpected issues: {relocate.issues}")
    ensure(
        ("this", "LengthBound") in relocate.active_invariants
        and ("destination", "LengthBound") in relocate.active_invariants
        and not relocate.open_invariants,
        "RelocateInto did not keep LengthBound active or close lifted clauses",
    )

    disjoint_views = reports["BoundedBuffer.DisjointViews"].paths[0]
    ensure(
        not disjoint_views.issues,
        f"disjoint named views Entries and Tail conflicted: {disjoint_views.issues}",
    )

    conflict_view = reports["BoundedBuffer.ConflictingViewWrite"].paths[0]
    ensure(
        "suspended-parent" in _kinds(conflict_view),
        "writing backing field `slots` while `Entries` view loan was live did not conflict",
    )

    early_scope = reports["BoundedBuffer.EarlyExitInScope"]
    ensure(
        any(
            ("unclosed-invariant", ("this", "InitializedPrefix"))
            in {(issue.kind, issue.resources) for issue in path.issues}
            for path in early_scope.paths
        ),
        "let-else early return inside `open ... lifts` did not report unclosed-invariant",
    )

    many_branches = reports["BoundedBuffer.ManyBranchesAndLoop"]
    ensure(
        len(many_branches.paths) == 1 and not many_branches.paths[0].issues,
        f"9-branch + foreach function failed or did not merge: {many_branches.paths}",
    )

    alias_call = analyze_function(module_ast, "ReceiverAliasCall").paths[0]
    ensure(
        "suspended-parent" in _kinds(alias_call),
        "reading builder.Length inside interpolated string under active `ref builder` loan did not conflict",
    )


def _holdfast_parser_schema2_surface_ast_lowering() -> None:
    def id_node(text: str) -> dict[str, object]:
        return {"kind": "identifier", "text": text, "span": [0, len(text)]}

    def name_expr(text: str) -> dict[str, object]:
        return {"kind": "name", "name": id_node(text), "span": [0, len(text)]}

    def member_expr(value: dict[str, object], field_name: str) -> dict[str, object]:
        return {"kind": "member", "value": value, "name": id_node(field_name), "span": [0, 1]}

    def unary_borrow(mode: str, value: dict[str, object]) -> dict[str, object]:
        return {
            "kind": "unary",
            "operator": {"kind": "operator", "text": mode, "span": [0, len(mode)]},
            "value": value,
            "span": [0, 1],
        }

    parser_module: dict[str, object] = {
        "schema": 2,
        "ast": {
            "kind": "module",
            "name": id_node("ParserAstBorrowModule"),
            "declarations": [
                {
                    "kind": "record",
                    "name": id_node("Window"),
                    "parameters": [
                        {"kind": "parameter", "name": id_node("Low"), "type": name_expr("u32")},
                        {"kind": "parameter", "name": id_node("High"), "type": name_expr("u32")},
                    ],
                    "contracts": [
                        {"kind": "contract", "role": "invariant", "name": id_node("Ordered"), "value": name_expr("true")}
                    ],
                    "declarations": [],
                },
                {
                    "kind": "function",
                    "name": id_node("DisjointRecordFields"),
                    "parameters": [
                        {
                            "kind": "parameter",
                            "name": id_node("seed"),
                            "type": name_expr("Window"),
                        }
                    ],
                    "result": name_expr("u32"),
                    "contracts": [],
                    "body": {
                        "kind": "block",
                        "statements": [
                            {
                                "kind": "var",
                                "name": id_node("w"),
                                "type": None,
                                "value": name_expr("seed"),
                            },
                            {
                                "kind": "let",
                                "name": id_node("low"),
                                "type": None,
                                "value": unary_borrow("in", member_expr(name_expr("w"), "Low")),
                            },
                            {
                                "kind": "assignment",
                                "operator": {"kind": "operator", "text": "="},
                                "target": member_expr(name_expr("w"), "High"),
                                "value": {"kind": "nat", "value": "9", "suffix": "u32", "span": [0, 4]},
                            },
                            {
                                "kind": "return",
                                "value": name_expr("low"),
                            },
                        ],
                    },
                },
                {
                    "kind": "function",
                    "name": id_node("ConflictingRecordFieldWrite"),
                    "parameters": [
                        {
                            "kind": "parameter",
                            "name": id_node("seed"),
                            "type": name_expr("Window"),
                        }
                    ],
                    "result": name_expr("u32"),
                    "contracts": [],
                    "body": {
                        "kind": "block",
                        "statements": [
                            {
                                "kind": "var",
                                "name": id_node("w"),
                                "type": None,
                                "value": name_expr("seed"),
                            },
                            {
                                "kind": "let",
                                "name": id_node("low"),
                                "type": None,
                                "value": unary_borrow("in", member_expr(name_expr("w"), "Low")),
                            },
                            {
                                "kind": "assignment",
                                "operator": {"kind": "operator", "text": "="},
                                "target": member_expr(name_expr("w"), "Low"),
                                "value": {"kind": "nat", "value": "9", "suffix": "u32", "span": [0, 4]},
                                "span": [10, 20],
                            },
                            {
                                "kind": "return",
                                "value": name_expr("low"),
                            },
                        ],
                    },
                },
            ],
        },
    }

    disjoint_report = analyze_function(parser_module, "DisjointRecordFields").paths[0]
    ensure(
        not disjoint_report.issues,
        f"DisjointRecordFields reported unexpected issues: {disjoint_report.issues}",
    )

    conflict_lowered = lower_function(parser_module, "ConflictingRecordFieldWrite")
    conflict_report = analyze_function(parser_module, "ConflictingRecordFieldWrite").paths[0]
    ensure(
        "suspended-parent" in _kinds(conflict_report),
        f"ConflictingRecordFieldWrite did not report suspended-parent: {conflict_report.issues}",
    )
    issue_node = conflict_report.issues[0].node
    ensure(
        issue_node in conflict_lowered.node_sites
        and conflict_lowered.node_sites[issue_node].get("span") == [10, 20],
        f"expected node_sites to map {issue_node} to offending assignment span",
    )


def _located_receiver_timing() -> None:
    source = b"""module ReceiverTrial;
public struct Buffer {
    public Nat length;
    public Nat payload;
    public view Data = payload;
    public Unit Update(ref this, Nat x);
    public Unit WithRead(ref this, in Nat x);
    public Nat ReadCount(in this);
    public Nat Mutate(ref this);
    public Unit WriteData(ref this.Data, Nat x);
    public in<'this.payload> Nat BorrowData(in this.Data);
}
public Unit Explicit(ref Buffer buf, Nat n);
public Unit Direct(ref Buffer buf) { buf.Update(buf.length); }
public Unit Snapshot(ref Buffer buf) { let n = buf.length; buf.Update(n); }
public Unit Count(ref Buffer buf) { buf.Update(buf.ReadCount()); }
public Unit Alias(ref Buffer buf) { let ref Buffer local = ref buf; local.Update(local.ReadCount()); }
public Unit Nested(ref Buffer buf) { buf.Update(buf.Mutate()); }
public Unit Disjoint(ref Buffer buf) { buf.WriteData(buf.length); }
public Unit Retained(ref Buffer buf) { buf.WithRead(in buf.payload); }
public Unit Hold(ref Buffer buf) { let in Nat loan = buf.BorrowData(); buf.Update(0); Observe(in loan); }
public Unit Immediate(ref Buffer buf) { Explicit(ref buf, buf.length); }
"""
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        tree = parser.parse_source(compiled, source, surface=True)
    expected = {
        "Direct": None, "Snapshot": None, "Count": None, "Alias": None, "Disjoint": None,
        "Nested": b"buf.Mutate", "Retained": b"buf.WithRead", "Hold": b"buf.Update",
        "Immediate": b"buf.length",
    }
    for name, conflict_span in expected.items():
        lowered = lower_function(tree, name)
        report = analyze(lowered.owners, lowered.graph).paths[0]
        ensure(bool(report.issues) == (conflict_span is not None),
               f"unexpected receiver result in {name}: {report.issues}")
        if conflict_span is not None:
            span = cast("list[int]", lowered.node_sites[report.issues[0].node]["span"])
            ensure(source[span[0]:span[1]] == conflict_span,
                   f"receiver conflict points outside its competing access in {name}: {source[span[0]:span[1]]!r}")
        events = [node.event for node in lowered.graph.nodes]
        if name in {"Direct", "Snapshot"}:
            read = next(i for i, e in enumerate(events) if isinstance(e, Access) and e.place == Place("buf", ("length",)))
            begin = next(i for i, e in enumerate(events) if isinstance(e, Reserve))
            activate = next(i for i, e in enumerate(events) if isinstance(e, Activate))
            ensure(read < begin < activate if name == "Snapshot" else begin < read < activate,
                   f"incorrect order of the length read and receiver phases in {name}")
        if name == "Disjoint":
            reserved = next(e.loan.place for e in events if isinstance(e, Reserve))
            ensure(reserved == Place("buf", ("payload",)), "named receiver view lost its field footprint")
        if name == "Count":
            phases = [type(e) for e in events if isinstance(e, (Reserve, Borrow, Activate))]
            ensure(phases == [Reserve, Borrow, Activate], "nested read did not run once between receiver phases")
        if name == "Hold":
            loan = next(e.loan for e in events if isinstance(e, Borrow))
            ensure(loan.mode == "shared" and not loan.scoped,
                   "the source-declared receiver return loan was discarded at the call")


def _receiver_view_representation_change() -> None:
    client = """public Unit Client(ref Buffer buf) {
    let in Nat count = buf.BorrowCount();
    buf.WriteData(0);
    Observe(in count);
}"""
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        for count_field, data_field, overlap in (
            ("length", "payload", False),
            ("used", "storage", False),
            ("used", "storage", True),
        ):
            count_view = data_field if overlap else count_field
            source = f"""module ViewClient;
public struct Buffer {{
    private Nat {count_field};
    private Nat {data_field};
    public view Count = {count_view};
    public view Data = {data_field};
    public in<'this.{count_view}> Nat BorrowCount(in this.Count);
    public Unit WriteData(ref this.Data, Nat n);
}}
{client}
""".encode()
            tree = parser.parse_source(compiled, source, surface=True)
            lowered = lower_function(tree, "Client")
            report = analyze(lowered.owners, lowered.graph).paths[0]
            if overlap:
                ensure(bool(report.issues) and report.issues[0].kind == "competing-loans",
                       f"overlapping public views need a borrow conflict: {report.issues}")
                span = cast("list[int]", lowered.node_sites[report.issues[0].node]["span"])
                ensure(source[span[0]:span[1]] == b"buf.WriteData", "conflict missed the receiver activation")
            else:
                ensure(not report.issues, f"disjoint public views conflicted: {report.issues}")
                ensure(all(obligation.kind != "overlap" for obligation in report.obligations),
                       "disjoint private fields left a residual overlap obligation")


def _checked_receiver_read() -> None:
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        for snapshot in (False, True):
            statements = (
                b"let next = buf.LiveCount; return buf.Write(next, 7u8);"
                if snapshot else b"return buf.Write(buf.LiveCount, 7u8);"
            )
            source = (b"module ReceiverMath; public Slots<u8, 4> Fill() { "
                      b"let buf = Slots.AllocVacant<u8, 4>(); " + statements + b" }")
            tree = parser.parse_source(compiled, source, surface=True)
            translated = elaborate(source, tree)
            ensure(not solver_ledger.ledger(translated.gallina), "receiver read relies on solver-trusted obligations")


def _receiver_argument_view_captures() -> None:
    source = b"""module ReceiverArguments;
public struct Buffer {
    public Nat value;
    public Unit Update(ref this, Option<in Nat> retained);
    public Option<in<'this> Nat> BorrowValue(in this);
}
public Option<in<'buf> Nat> Lend(in Buffer buf);
public Unit Disjoint(ref Buffer target, in Buffer left, in Buffer right, in Buffer third, bool pick, bool backup) {
    target.Update(if (pick) left.BorrowValue() else if (backup) right.BorrowValue() else third.BorrowValue());
}
public Unit Retained(ref Buffer buf) { buf.Update(Lend(in buf)); }
"""
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        tree = parser.parse_source(compiled, source, surface=True)
        invalid = source.replace(b"else third.BorrowValue()", b"else target.BorrowValue()")
        bad_tree = parser.parse_source(compiled, invalid, surface=True)
    report = analyze_function(tree, "Disjoint")
    ensure(len(report.paths) == 3 and all(not path.issues for path in report.paths),
           f"one branch evaluated a sibling's argument capture: {report.paths}")
    report = analyze_function(bad_tree, "Disjoint")
    rejected = [path for path in report.paths if path.issues]
    ensure(len(report.paths) == 3 and len(rejected) == 1
           and rejected[0].issues[0].kind == "competing-loans",
           "receiver activation lost the retained overlap or rejected a disjoint sibling")
    lowered = lower_function(tree, "Retained")
    report = analyze(lowered.owners, lowered.graph)
    ensure(all(path.issues and path.issues[0].kind == "competing-loans" for path in report.paths),
           f"a possible view through a fresh helper input ended before activation: {report.paths}")


def _element_loan_during_relocation() -> None:
    declarations = b"""module RelocationLoans;
public bool Relocate(ref Slots<u32, 4> src, ref Slots<u32, 4> dst)
    requires src.CanWrite && dst.CanRead
    requires src.LivePrefix(1usize) && dst.VacantRange(0usize, 1usize)
    requires src.VacantRange(1usize, 4usize)
    requires Slots.Disjoint(src, dst)
    ensures dst.LivePrefix(1usize)
    ensures src.VacantRange(0usize, 4usize)
{
    CopyRepresentation(src, ref dst, 1usize);
    TransferType<u32>(ref src, ref dst, 1usize);
    return true;
}
public u32 Observe(in u32 value, bool relocated) ensures result == value { return value; }
public u32 Client(ref Slots<u32, 4> src, ref Slots<u32, 4> dst)
    requires src.CanWrite && src.CanRead && dst.CanRead
    requires 0usize < src.LiveCount
    requires src.LivePrefix(1usize) && dst.VacantRange(0usize, 1usize)
    requires src.VacantRange(1usize, 4usize)
    requires Slots.Disjoint(src, dst)
    ensures result == old(src[0usize])
{
"""
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        for snapshot in (False, True):
            body = b"    let saved = src[0usize];\n" if snapshot else b""
            argument = b"in saved" if snapshot else b"in src[0usize]"
            source = declarations + body + b"    return Observe(" + argument + b",\n        Relocate(ref src, ref dst));\n}"
            tree = parser.parse_source(compiled, source, surface=True)
            try:
                translated = elaborate(source, tree)
            except HoldFastError as error:
                lines = source.splitlines()
                origin_line = len(lines) - 2
                origin_column = lines[-3].index(argument) + 1
                ensure(not snapshot and error.kind == "type"
                       and f"live shared loan of 'src[*]' created at line {origin_line}, column {origin_column}" in error.message
                       and "competing-loans" in error.message, f"line {error.line}, column {error.column}: {error}")
                ensure((error.line, error.column) == (origin_line + 1, lines[-2].index(b"ref src") + 1),
                       f"relocation conflict has the wrong source location: {error.line}, {error.column}")
            else:
                ensure(snapshot, "the source backing was relocated with an outstanding element loan")
                trusted = solver_ledger.ledger(translated.gallina)
                ensure(not trusted, f"the relocation snapshot relies on solver-trusted obligations: {trusted}")


def _indexed_symbolic_disjointness() -> None:
    source = b"""module IndexedLoans;

private Unit SetTwo(ref byte a, ref byte b)
    ensures a == 9u8 && b == 8u8
{
    a = 9u8;
    b = 8u8;
    return;
}

public bool Client(ref Span<byte> values, usize i, usize j)
    requires values.CanRead && values.CanWrite
    requires values.Length == 4usize
    ensures result == (i < 4usize && j < 4usize && i != j)
{
    if (i < 4usize && j < 4usize && i != j) {
        SetTwo(ref values[i], ref values[j]);
        return true;
    }
    return false;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        tree = parser.parse_source(compiled, source, surface=True)
        gallina = elaborate(source, tree).gallina
        invalid = source.replace(b"ref values[j]", b"ref values[i]")
        bad_tree = parser.parse_source(compiled, invalid, surface=True)
        with raises(HoldFastError, msg="coincident loans reached Gallina emission") as failure:
            elaborate(invalid, bad_tree)
        error = failure.exception
        call = b"SetTwo(ref values[i], ref values[i]);"
        line = invalid[:invalid.index(call)].count(b"\n") + 1
        column = invalid.splitlines()[line - 1].index(b"ref values[i]") + 1
        ensure(error.kind == "type" and (error.line, error.column) == (line, column)
               and "cannot prove indexed loan of 'values' is disjoint from argument 2" in error.message,
               f"wrong rejection for coincident loans: {error.line}:{error.column}: {error}")

    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "indexed loans depended on a solver assumption")
    [client] = re.findall(r"^Definition (holdfast_d\d+_Client) :", gallina, re.MULTILINE)
    proof = f"""
Import HoldFast_IndexedLoans.
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).

Theorem indexed_writeback : forall values i j,
  ({client} values i j = true ->
    trial_read ({client}_post_values values i j) i = trial_byte 9 /\\
    trial_read ({client}_post_values values i j) j = trial_byte 8) /\\
  ({client} values i j = false -> {client}_post_values values i j = values) /\\
  (forall k, holdfast_int_ne 4 i k = true -> holdfast_int_ne 4 j k = true ->
    trial_read ({client}_post_values values i j) k = trial_read values k).
Proof.
  intros values i j. unfold {client}, {client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then true else false] => destruct guard eqn:allowed
  end.
  - split.
    + intros _. apply holdfast_and_right in allowed. apply holdfast_int_ne_false in allowed.
      assert (reverse_separation : holdfast_int_ne 4 j i = true).
      {{ unfold holdfast_int_ne. rewrite (holdfast_int_eq_sym_false 4 i j allowed). reflexivity. }}
      unfold trial_read. split.
      * rewrite (holdfast_Span_Read_write_other_ne _ _ _ _ _ reverse_separation).
        apply holdfast_Span_Read_write_same.
      * apply holdfast_Span_Read_write_same.
    + split.
      * discriminate.
      * intros k outside_i outside_j. unfold trial_read.
        rewrite (holdfast_Span_Read_write_other_ne _ _ _ _ _ outside_j).
        apply holdfast_Span_Read_write_other_ne. exact outside_i.
  - split; [discriminate | split; reflexivity].
Qed.

Local Definition trial_span :=
  holdfast_mk_span (holdfast_int 0) (trial_index 0) (trial_index 4) true true true holdfast_bs_empty.
Example indexed_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\\
  holdfast_Span_CanWrite _ trial_span = true /\\
  holdfast_Span_Length _ trial_span = trial_index 4 /\\
  {client} trial_span (trial_index 1) (trial_index 0) = true /\\
  {client} trial_span (trial_index 1) (trial_index 1) = false /\\
  {client} trial_span (trial_index 4) (trial_index 0) = false.
Proof. repeat split; reflexivity. Qed.
"""
    exports = [*solver_ledger.math_exports(gallina), "indexed_writeback", "indexed_entry_is_inhabited"]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory() as tmp:
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + proof + audit, Path(tmp))
        (Path(tmp) / "IndexedLoans.v").write_text(unit_text, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", "IndexedLoans.v"],
                                cwd=tmp, capture_output=True, timeout=180, check=False)
        ensure(replay.returncode == 0, f"rocq c refused the indexed writeback proof: {replay.stderr[-2400:]!r}")
        solver_ledger.audit(replay.stdout.decode("utf-8"), len(exports), "HoldFast_IndexedLoans", entries)
        units = ["HoldFastPrelude", "IndexedLoans"] if used_prelude else ["IndexedLoans"]
        kernel = subprocess.run([*proofenv.rocqchk_command(), "-silent", *units],
                                cwd=tmp, capture_output=True, timeout=180, check=False)
        ensure(kernel.returncode == 0, f"rocqchk refused the indexed writeback proof: {kernel.stderr[-2400:]!r}")


def _mixed_indexed_loans() -> None:
    source = b"""module MixedIndexedLoans;

private byte CopyPeer(in byte source, ref byte target) {
    target = source;
    return source;
}

public byte Client(ref Span<byte> values, usize i, usize j)
    requires values.CanRead && values.CanWrite
    requires values.Length == 4usize
{
    if (i < j && j < 4usize) {
        return CopyPeer(in values[i], ref values[j]);
    }
    return 0u8;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        tree = parser.parse_source(compiled, source, surface=True)
        gallina = elaborate(source, tree).gallina
        for invalid in (
            source.replace(b"ref values[j]", b"ref values[i]"),
            source.replace(b"i < j", b"i <= j"),
            source.replace(
                b"return CopyPeer(in values[i], ref values[j]);",
                b"let shifted = Span.Slice(values, 1usize, 3usize);\n"
                b"        return CopyPeer(in shifted[0usize], ref values[1usize]);",
            ),
        ):
            bad_tree = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="possibly overlapping mixed loans reached Gallina emission") as failure:
                elaborate(invalid, bad_tree)
            error = failure.exception
            line = next(n for n, row in enumerate(invalid.splitlines(), 1) if b"return CopyPeer" in row)
            column = invalid.splitlines()[line - 1].index(b"ref values") + 1
            ensure(error.kind == "type" and (error.line, error.column) == (line, column)
                   and "cannot prove indexed loan of 'values' is disjoint from argument 1" in error.message,
                   f"wrong rejection for possibly overlapping mixed loans: {error.line}:{error.column}: {error}")

    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "mixed indexed loans depended on a solver assumption")
    [client] = re.findall(r"^Definition (holdfast_d\d+_Client) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_MixedIndexedLoans.
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition ordered i j := holdfast_and (holdfast_int_lt 4 i j)
  (holdfast_int_lt 4 j (trial_index 4)).

Theorem mixed_writeback : forall values i j,
  (ordered i j = true ->
    {client} values i j = trial_read values i /\
    trial_read ({client}_post_values values i j) j = trial_read values i /\
    trial_read ({client}_post_values values i j) i = trial_read values i) /\
  (ordered i j = false ->
    {client} values i j = trial_byte 0 /\ {client}_post_values values i j = values) /\
  (forall k, holdfast_int_ne 4 j k = true ->
    trial_read ({client}_post_values values i j) k = trial_read values k).
Proof.
  intros values i j. unfold {client}, {client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:allowed
  end.
  all: match type of allowed with
       | _ = ?outcome => change (ordered i j = outcome) in allowed
       end; rewrite allowed.
  - split.
    + intros _. unfold ordered in allowed. apply holdfast_and_left in allowed.
      assert (separate : holdfast_int_ne 4 j i = true).
      {{ unfold holdfast_int_ne. destruct (holdfast_int_eq 4 j i) eqn:equal; [|reflexivity].
         exact (holdfast_int_lt_ge_false _ i j j allowed (holdfast_usize_le_refl j) equal). }}
      split; [reflexivity |]. unfold trial_read. split.
      * apply holdfast_Span_Read_write_same.
      * now apply holdfast_Span_Read_write_other_ne.
    + split.
      * discriminate.
      * intros k outside. now apply holdfast_Span_Read_write_other_ne.
  - split; [discriminate | split; intros; repeat split; reflexivity].
Qed.

Local Definition trial_span :=
  holdfast_Span_Write _ (holdfast_mk_span (holdfast_int 0) (trial_index 0)
    (trial_index 4) true true true holdfast_bs_empty) (trial_index 0) (trial_byte 7).
Example mixed_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\
  holdfast_Span_CanWrite _ trial_span = true /\
  holdfast_Span_Length _ trial_span = trial_index 4 /\
  {client} trial_span (trial_index 0) (trial_index 1) = trial_byte 7 /\
  {client} trial_span (trial_index 0) (trial_index 0) = trial_byte 0 /\
  {client} trial_span (trial_index 0) (trial_index 4) = trial_byte 0.
Proof. repeat split; reflexivity. Qed.
"""
    exports = [*solver_ledger.math_exports(gallina), "mixed_writeback", "mixed_entry_is_inhabited"]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory() as tmp:
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + proof + audit, Path(tmp))
        (Path(tmp) / "MixedIndexedLoans.v").write_text(unit_text, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", "MixedIndexedLoans.v"],
                                cwd=tmp, capture_output=True, timeout=180, check=False)
        ensure(replay.returncode == 0, f"rocq c refused the mixed writeback proof: {replay.stderr[:3600]!r}")
        solver_ledger.audit(replay.stdout.decode("utf-8"), len(exports), "HoldFast_MixedIndexedLoans", entries)
        units = ["HoldFastPrelude", "MixedIndexedLoans"] if used_prelude else ["MixedIndexedLoans"]
        kernel = subprocess.run([*proofenv.rocqchk_command(), "-silent", *units],
                                cwd=tmp, capture_output=True, timeout=180, check=False)
        ensure(kernel.returncode == 0, f"rocqchk refused the mixed writeback proof: {kernel.stderr[:3600]!r}")


def _owner_coordinate_indexed_loans() -> None:
    source = b"""module OwnerCoordinateLoans;

private byte CopyPeer(in byte source, ref byte target) {
    target = source;
    return source;
}

public byte Client(ref Span<byte> values, usize i, usize j)
    requires values.CanRead && values.CanWrite
    requires values.Length == 4usize
{
    if ((i < 3usize && j < 4usize) && j != 1usize + i) {
        let shifted = Span.Slice(values, 1usize, 3usize);
        return CopyPeer(in shifted[i], ref values[j]);
    }
    return 0u8;
}
"""
    nested = source.replace(b"public byte Client", b"public byte Nested").replace(
        b"i < 3usize", b"i < 2usize",
    ).replace(b"j != 1usize + i", b"j != 2usize + i").replace(
        b"return CopyPeer(in shifted[i], ref values[j]);",
        b"let nested = Span.Slice(shifted, 1usize, 2usize);\n"
        b"        return CopyPeer(in nested[i], ref values[j]);",
    )
    inline = nested.replace(b"public byte Nested", b"public byte Inline").replace(
        b"let shifted = Span.Slice(values, 1usize, 3usize);\n        "
        b"let nested = Span.Slice(shifted, 1usize, 2usize);",
        b"let nested = Span.Slice(Span.Slice(values, 1usize, 3usize), 1usize, 2usize);",
    )
    updated = nested.replace(b"public byte Nested", b"public byte Updated").replace(
        b"return CopyPeer", b"values[0usize] = 9u8;\n        return CopyPeer",
    )
    readonly = updated.replace(
        b"Span.Slice(values, 1usize, 3usize)", b"Span.Slice(Span.ReadOnly(values), 1usize, 3usize)",
    ).replace(
        b"Span.Slice(shifted, 1usize, 2usize)", b"Span.ReadOnly(Span.Slice(shifted, 1usize, 2usize))",
    )
    whole_readonly = source.replace(
        b"i < 3usize", b"i < 4usize",
    ).replace(
        b"j != 1usize + i", b"j != i",
    ).replace(
        b"Span.Slice(values, 1usize, 3usize)", b"Span.ReadOnly(values)",
    )
    branch_update = updated.replace(
        b"values[0usize] = 9u8;",
        b"if (j < 2usize) { values[j] = 9u8; } else { values[1usize] = 8u8; }",
    )
    combined = (source + nested[nested.index(b"public byte Nested"):] + inline[inline.index(b"public byte Inline"):]
                + readonly[readonly.index(b"public byte Updated"):])
    effectful = source.replace(b"public byte Client", b"""private usize Pick(ref Span<byte> values, usize idx)
    requires values.CanRead && values.CanWrite
    requires values.Length == 4usize
{
    values[1usize] = 5u8;
    return idx;
}

public byte Client""").replace(b"ref values[j]", b"ref values[Pick(ref values, j)]")
    with parser.cached_build(TOOLS.parent) as compiled:
        tree = parser.parse_source(compiled, combined, surface=True)
        gallina = elaborate(combined, tree).gallina
        for valid in (
            source.replace(b"return CopyPeer", b"values[0usize] = 5u8;\n        return CopyPeer"),
            updated,
            updated.replace(b"values[0usize] = 9u8;", b"Span.Fill(ref values, 0usize, 2usize, 9u8);"),
            branch_update,
            whole_readonly,
            whole_readonly.replace(
                b"return CopyPeer", b"Span.Fill(ref values, 4usize, 0usize, 9u8);\n        return CopyPeer",
            ),
            readonly.replace(b"values[0usize] = 9u8;", b"Span.Fill(ref values, 0usize, 2usize, 9u8);"),
            readonly.replace(
                b"values[0usize] = 9u8;",
                b"if (j < 2usize) { values[j] = 9u8; } else { values[1usize] = 8u8; }",
            ),
        ):
            elaborate(valid, parser.parse_source(compiled, valid, surface=True))
        temporary = nested.replace(
            b"in nested[i]",
            b"in (Span.Slice(shifted, 1usize, 2usize))[i]",
        )
        with raises(HoldFastError, msg="temporary slice supplied an untracked call loan") as failure:
            elaborate(temporary, parser.parse_source(compiled, temporary, surface=True))
        error = failure.exception
        ensure(error.kind == "type" and "an 'in' loan requires a place" in error.message,
               f"wrong rejection for an unnamed slice loan: {error.line}:{error.column}: {error}")
        for invalid in (
            source.replace(b"ref values[j]", b"ref values[1usize + i]"),
            source.replace(b"j != 1usize + i", b"j != i"),
            source.replace(b"return CopyPeer", b"Span.Restore(ref values, shifted);\n        return CopyPeer"),
            nested.replace(b"ref values[j]", b"ref values[2usize + i]"),
            nested.replace(b"j != 2usize + i", b"j != 1usize + i"),
            nested.replace(b"return CopyPeer", b"values[2usize] = 5u8;\n        return CopyPeer"),
            inline.replace(b"ref values[j]", b"ref values[2usize + i]"),
            inline.replace(b"return CopyPeer", b"values[2usize] = 5u8;\n        return CopyPeer"),
            inline.replace(b"return CopyPeer", b"if (i == 0usize) { values[2usize] = 5u8; }\n        return CopyPeer"),
            updated.replace(b"values[0usize] = 9u8;", b"values[2usize + i] = 9u8;"),
            updated.replace(b"values[0usize] = 9u8;", b"Span.Fill(ref values, 0usize, 3usize, 9u8);"),
            branch_update.replace(b"values[1usize] = 8u8;", b"values[j] = 8u8;"),
            whole_readonly.replace(b"ref values[j]", b"ref values[i]"),
            whole_readonly.replace(b"return CopyPeer", b"values[0usize] = 5u8;\n        return CopyPeer"),
            source.replace(
                b"return CopyPeer(in shifted[i]",
                b"let readOnly = Span.ReadOnly(shifted);\n        Span.Restore(ref values, shifted);\n"
                b"        return CopyPeer(in readOnly[i]",
            ),
            readonly.replace(b"ref values[j]", b"ref values[2usize + i]"),
            readonly.replace(b"values[0usize] = 9u8;", b"values[2usize + i] = 9u8;"),
            readonly.replace(b"values[0usize] = 9u8;", b"Span.Fill(ref values, 0usize, 3usize, 9u8);"),
            effectful,
            effectful.replace(b"CopyPeer(in byte source, ref byte target)", b"CopyPeer(ref byte target, in byte source)").replace(
                b"CopyPeer(in shifted[i], ref values[Pick(ref values, j)])",
                b"CopyPeer(ref values[Pick(ref values, j)], in shifted[i])",
            ),
        ):
            bad_tree = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="unproven owner-coordinate separation reached Gallina emission") as failure:
                elaborate(invalid, bad_tree)
            error = failure.exception
            line = next(n for n, row in enumerate(invalid.splitlines(), 1) if b"return CopyPeer" in row)
            call = invalid.splitlines()[line - 1]
            column = call.index(b"ref values") + 1
            other_argument = 1 if call.index(b"in ") < column else 2
            ensure(error.kind == "type" and (error.line, error.column) == (line, column)
                   and f"cannot prove indexed loan of 'values' is disjoint from argument {other_argument}" in error.message,
                   f"wrong rejection for an unresolved owner-coordinate loan: {error.line}:{error.column}: {error}")

    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "owner-coordinate loans depended on a solver assumption")
    clients = {name: constant for constant, name in re.findall(
        r"^Definition (holdfast_d\d+_(Client|Nested|Inline|Updated)) :", gallina, re.MULTILINE,
    )}
    proof = """
Import HoldFast_OwnerCoordinateLoans.

Local Lemma composed_slice_read : forall (values : holdfast_Span (holdfast_int 0))
    outer inner outer_count inner_count i,
  holdfast_Span_Read _ (holdfast_Span_Slice _
    (holdfast_Span_Slice _ values outer outer_count) inner inner_count) i =
  holdfast_Span_Read _ values (holdfast_int_add 4 (holdfast_int_add 4 outer inner) i).
Proof.
  intros.
  change (holdfast_store_lookup (holdfast_Span_Store _ values)
    (holdfast_int_add 4 outer (holdfast_int_add 4 inner i)) =
    holdfast_store_lookup (holdfast_Span_Store _ values)
    (holdfast_int_add 4 (holdfast_int_add 4 outer inner) i)).
  now rewrite holdfast_int_add_assoc.
Qed.

Local Lemma composed_readonly_slice_read : forall (values : holdfast_Span (holdfast_int 0))
    outer inner outer_count inner_count i,
  holdfast_Span_Read _ (holdfast_Span_ReadOnly _ (holdfast_Span_Slice _
    (holdfast_Span_Slice _ (holdfast_Span_ReadOnly _ values) outer outer_count) inner inner_count)) i =
  holdfast_Span_Read _ values (holdfast_int_add 4 (holdfast_int_add 4 outer inner) i).
Proof. exact composed_slice_read. Qed.
"""
    exports = solver_ledger.math_exports(gallina)
    for name in ("Client", "Nested", "Inline"):
        client = clients[name]
        offset = 1 if name == "Client" else 2
        compose_offsets = "rewrite !composed_slice_read. " if offset == 2 else ""
        proof += rf"""
Module {name}Trial.
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition owner_index i := holdfast_int_add 4 (trial_index {offset}) i.
Local Definition can_copy i j := holdfast_and
  (holdfast_and (holdfast_int_lt 4 i (trial_index {4 - offset})) (holdfast_int_lt 4 j (trial_index 4)))
  (holdfast_int_ne 4 j (owner_index i)).

Theorem owner_coordinate_writeback : forall values i j,
  (can_copy i j = true ->
    {client} values i j = trial_read values (owner_index i) /\
    trial_read ({client}_post_values values i j) j = trial_read values (owner_index i) /\
    trial_read ({client}_post_values values i j) (owner_index i) = trial_read values (owner_index i)) /\
  (can_copy i j = false ->
    {client} values i j = trial_byte 0 /\ {client}_post_values values i j = values) /\
  (forall k, holdfast_int_ne 4 j k = true ->
    trial_read ({client}_post_values values i j) k = trial_read values k).
Proof.
  intros values i j. unfold {client}, {client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:allowed
  end.
  all: match type of allowed with
       | _ = ?outcome => change (can_copy i j = outcome) in allowed
       end; rewrite allowed.
  - {compose_offsets}split.
    + intros _. unfold can_copy in allowed. apply holdfast_and_right in allowed.
      split; [reflexivity |]. unfold trial_read. split.
      * apply holdfast_Span_Read_write_same.
      * now apply holdfast_Span_Read_write_other_ne.
    + split.
      * discriminate.
      * intros k outside. now apply holdfast_Span_Read_write_other_ne.
  - split; [discriminate | split; intros; repeat split; reflexivity].
Qed.

Local Definition trial_span :=
  holdfast_Span_Write _ (holdfast_mk_span (holdfast_int 0) (trial_index 0)
    (trial_index 4) true true true holdfast_bs_empty) (trial_index {offset}) (trial_byte 7).
Example owner_coordinate_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\
  holdfast_Span_CanWrite _ trial_span = true /\
  holdfast_Span_Length _ trial_span = trial_index 4 /\
  {client} trial_span (trial_index 0) (trial_index 0) = trial_byte 7 /\
  {client} trial_span (trial_index 0) (trial_index {offset}) = trial_byte 0 /\
  {client} trial_span (trial_index 0) (trial_index 4) = trial_byte 0.
Proof. repeat split; reflexivity. Qed.
End {name}Trial.
"""
        exports.extend((f"{name}Trial.owner_coordinate_writeback", f"{name}Trial.owner_coordinate_entry_is_inhabited"))
    updated_client = clients["Updated"]
    proof += rf"""
Module UpdatedTrial.
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition owner_index i := holdfast_int_add 4 (trial_index 2) i.
Local Definition can_copy i j := holdfast_and
  (holdfast_and (holdfast_int_lt 4 i (trial_index 2)) (holdfast_int_lt 4 j (trial_index 4)))
  (holdfast_int_ne 4 j (owner_index i)).

Theorem saved_view_writeback : forall values i j,
  (can_copy i j = true ->
    {updated_client} values i j = trial_read values (owner_index i) /\
    trial_read ({updated_client}_post_values values i j) j = trial_read values (owner_index i) /\
    (holdfast_int_ne 4 j (trial_index 0) = true ->
      trial_read ({updated_client}_post_values values i j) (trial_index 0) = trial_byte 9)) /\
  (can_copy i j = false ->
    {updated_client} values i j = trial_byte 0 /\ {updated_client}_post_values values i j = values) /\
  (forall k, holdfast_int_ne 4 j k = true -> holdfast_int_ne 4 (trial_index 0) k = true ->
    trial_read ({updated_client}_post_values values i j) k = trial_read values k).
Proof.
  intros values i j. unfold {updated_client}, {updated_client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:allowed
  end.
  all: match type of allowed with
       | _ = ?outcome => change (can_copy i j = outcome) in allowed
       end; rewrite allowed.
  - rewrite !composed_readonly_slice_read. split.
    + intros _. split; [reflexivity |]. split.
      * apply holdfast_Span_Read_write_same.
      * intro apart. unfold trial_read.
        rewrite holdfast_Span_Read_write_other_ne by exact apart.
        apply holdfast_Span_Read_write_same.
    + split; [discriminate |]. intros k outside_target outside_patch. unfold trial_read.
      now rewrite !holdfast_Span_Read_write_other_ne.
  - split; [discriminate | split; intros; repeat split; reflexivity].
Qed.

Local Definition initial_span := List.fold_left
  (fun values k => holdfast_Span_Write _ values (trial_index k) (trial_byte (S k)))
  (List.seq 0 4) (holdfast_mk_span (holdfast_int 0) (trial_index 0)
    (trial_index 4) true true true holdfast_bs_empty).
Local Definition agrees_with_oracle (i j : nat) : bool :=
  let allowed := andb (andb (Nat.ltb i 2) (Nat.ltb j 4)) (negb (Nat.eqb j (2 + i))) in
  let expected_read := if allowed then 3 + i else 0 in
  let post := {updated_client}_post_values initial_span (trial_index i) (trial_index j) in
  andb
    (holdfast_int_eq 0 ({updated_client} initial_span (trial_index i) (trial_index j)) (trial_byte expected_read))
    (List.forallb (fun k =>
      let expected_byte := if allowed then
        (if Nat.eqb k j then expected_read else if Nat.eqb k 0 then 9 else S k) else S k in
      holdfast_int_eq 0 (trial_read post (trial_index k)) (trial_byte expected_byte)) (List.seq 0 4)).

Example saved_view_observations :
  List.forallb (fun i => List.forallb (agrees_with_oracle i) (List.seq 0 6)) (List.seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.
End UpdatedTrial.
"""
    exports.extend(("UpdatedTrial.saved_view_writeback", "UpdatedTrial.saved_view_observations"))
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory() as tmp:
        unit_text, used_prelude = rocq_cache.use_cached_prelude(gallina + proof + audit, Path(tmp))
        (Path(tmp) / "OwnerCoordinateLoans.v").write_text(unit_text, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", "OwnerCoordinateLoans.v"],
                                cwd=tmp, capture_output=True, timeout=180, check=False)
        ensure(replay.returncode == 0, f"rocq c refused owner-coordinate writeback: {replay.stderr[:3600]!r}")
        solver_ledger.audit(replay.stdout.decode("utf-8"), len(exports), "HoldFast_OwnerCoordinateLoans", entries)
        units = ["HoldFastPrelude", "OwnerCoordinateLoans"] if used_prelude else ["OwnerCoordinateLoans"]
        kernel = subprocess.run([*proofenv.rocqchk_command(), "-silent", *units],
                                cwd=tmp, capture_output=True, timeout=180, check=False)
        ensure(kernel.returncode == 0, f"rocqchk refused owner-coordinate writeback: {kernel.stderr[:3600]!r}")


def _correlated_indexed_loans() -> None:
    source = b"""module CorrelatedIndexedLoans;

private byte CopyPeer(in byte source, ref byte target) {
    target = source;
    return source;
}

public byte CopySelected(ref Span<byte> values, bool first)
    effects writes(values)
    requires values.CanRead && values.CanWrite
    requires values.Length == 4usize
{
    let selected = if (first) Span.ReadOnly(Span.Slice(values, 0usize, 1usize))
                   else Span.ReadOnly(Span.Slice(values, 1usize, 1usize));
    if (first) {
        values[1usize] = 8u8;
    } else {
        values[0usize] = 9u8;
    }
    return CopyPeer(in selected[0usize], ref values[2usize]);
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        selected_preconditions = b"""module SelectedPreconditions;
public byte ReadSelected(Span<byte> left, Span<byte> right, bool first, usize i)
    requires (if (first) left else right).CanRead
    requires i < (if (first) left else right).Length
{
    let selected = if (first) left else right;
    return selected[i];
}
"""
        elaborate(selected_preconditions, parser.parse_source(compiled, selected_preconditions, surface=True))
        for invalid in (
            source.replace(b"values[1usize] = 8u8;", b"values[0usize] = 8u8;"),
            source.replace(b"values[0usize] = 9u8;", b"values[1usize] = 9u8;"),
            source.replace(b"bool first)", b"bool first, bool patchFirst)").replace(b"    if (first)", b"    if (patchFirst)"),
            source.replace(b"ref values[2usize]", b"ref values[0usize]"),
            source.replace(b"ref values[2usize]", b"ref values[1usize]"),
        ):
            tree = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="an overlapping joined call loan reached Gallina emission") as failure:
                elaborate(invalid, tree)
            error = failure.exception
            line, call = next((n, row) for n, row in enumerate(invalid.splitlines(), 1) if b"return CopyPeer" in row)
            ensure(error.kind == "type" and (error.line, error.column) == (line, call.index(b"ref values") + 1)
                   and "cannot prove indexed loan of 'values' is disjoint from argument 1" in error.message,
                   f"wrong refusal for an overlapping indexed loan: {error}")

        empty_alternative = source.replace(b"1usize, 1usize));", b"1usize, 0usize));")
        with raises(HoldFastError, msg="an empty slice alternative supplied an out-of-bounds element") as failure:
            elaborate(empty_alternative, parser.parse_source(compiled, empty_alternative, surface=True))
        ensure(failure.exception.kind == "type" and "cannot prove Span index is within Span.Length bounds" in failure.exception.message,
               f"wrong refusal for an empty view alternative: {failure.exception}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_CopySelected) :", gallina, re.MULTILINE)
    [copy] = re.findall(r"^Definition (holdfast_d\d+_CopyPeer) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_CorrelatedIndexedLoans.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition read_index (first : bool) := trial_index (if first then 0 else 1).
Local Definition patch_index (first : bool) := trial_index (if first then 1 else 0).
Local Definition patch_byte (first : bool) := trial_byte (if first then 8 else 9).

Theorem correlated_indexed_writeback : forall values first,
  let post := {client}_post_values values first in
  {client} values first = trial_read values (read_index first) /\
  trial_read post (trial_index 2) = trial_read values (read_index first) /\
  trial_read post (patch_index first) = patch_byte first /\
  (forall k, holdfast_int_ne 4 (patch_index first) k = true ->
             holdfast_int_ne 4 (trial_index 2) k = true ->
    trial_read post k = trial_read values k).
Proof.
  intros values []; unfold {client}, {client}_post_values, {copy}, {copy}_post_target,
    read_index, patch_index, patch_byte; cbv beta iota zeta.
  all: split; [reflexivity |]; split; [apply holdfast_Span_Read_write_same |]; split.
  all: unfold trial_read.
  1,3: rewrite holdfast_Span_Read_write_other_ne by reflexivity; apply holdfast_Span_Read_write_same.
  all: intros k outside_patch outside_target; etransitivity;
    [apply holdfast_Span_Read_write_other_ne; exact outside_target |
     apply holdfast_Span_Read_write_other_ne; exact outside_patch].
Qed.

Local Definition initial_span := List.fold_left
  (fun values k => holdfast_Span_Write _ values (trial_index k) (trial_byte (S k)))
  (List.seq 0 4) (holdfast_mk_span (holdfast_int 0) (trial_index 0)
    (trial_index 4) true true true holdfast_bs_empty).
Example correlated_indexed_observations :
  holdfast_Span_CanRead _ initial_span = true /\
  holdfast_Span_CanWrite _ initial_span = true /\
  holdfast_Span_Length _ initial_span = trial_index 4 /\
  {client} initial_span true = trial_byte 1 /\
  {client} initial_span false = trial_byte 2 /\
  trial_read ({client}_post_values initial_span true) (trial_index 2) = trial_byte 1 /\
  trial_read ({client}_post_values initial_span false) (trial_index 2) = trial_byte 2.
Proof. vm_compute. repeat split; reflexivity. Qed.
"""
    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "branch-selected indexed loans depended on a solver assumption")
    exports = [*solver_ledger.math_exports(gallina), "correlated_indexed_writeback", "correlated_indexed_observations"]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory(prefix="holdfast-correlated-indexed-") as tmp:
        unit = Path(tmp) / "CorrelatedIndexedLoans.v"
        unit.write_text(gallina + proof + audit, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", unit.name], cwd=tmp, capture_output=True,
                                encoding="utf-8", timeout=180, check=False)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(exports), "HoldFast_CorrelatedIndexedLoans", entries)


def _symbolic_index_projections_and_disjointness() -> None:
    arr_owner = (Owner("arr", borrowed=True),)
    item_owner = (Owner("items", borrowed=True, fields=(("@i", "Header"), ("@i", "Payload"))),)
    grid_owner = (Owner("grid", borrowed=True),)

    # 1D symbolic disjointness via AssumeIndexNe and AssumeDisjoint.
    arr_i = Place("arr", ("@i",))
    arr_j = Place("arr", ("@j",))
    for assumption in (AssumeIndexNe("@i", "@j"), AssumeDisjoint(arr_i, arr_j)):
        disjoint = analyze(arr_owner, _graph(
            assumption,
            Borrow(Loan("elem_i", "arr", arr_i)),
            Access(arr_j, "write"),
            Use("elem_i"),
            Return("ok"),
        )).paths[0]
        ensure(not disjoint.issues and not any(o.kind == "overlap" for o in disjoint.obligations),
               f"proved symbolic disjointness left conflicts or overlap obligations: {disjoint}")

    # Missing disjointness assumption produces overlap obligation; coincident @i == @i conflicts.
    unproven = analyze(arr_owner, _graph(
        Borrow(Loan("elem_i", "arr", arr_i)),
        Access(arr_j, "write"),
        Use("elem_i"),
    )).paths[0]
    ensure(not unproven.issues and any(o.kind == "overlap" for o in unproven.obligations),
           f"unproven distinct symbolic indices bypassed overlap obligation: {unproven}")
    coincident = analyze(arr_owner, _graph(
        AssumeIndexNe("@i", "@j"),
        Borrow(Loan("elem_i", "arr", arr_i)),
        Access(arr_i, "write"),
        Use("elem_i"),
    )).paths[0]
    ensure("suspended-parent" in _kinds(coincident),
           f"coincident symbolic index write did not conflict: {coincident.issues}")

    # Same symbolic index @i with distinct declared sibling fields is disjoint.
    item_hdr = Place("items", ("@i", "Header"))
    item_pay = Place("items", ("@i", "Payload"))
    sibling = analyze(item_owner, _graph(
        Borrow(Loan("hdr", "items", item_hdr)),
        Access(item_pay, "write"),
        Use("hdr"),
    )).paths[0]
    ensure(not sibling.issues and not any(o.kind == "overlap" for o in sibling.obligations),
           f"declared sibling fields under same symbolic index were not disjoint: {sibling}")
    same_field = analyze(item_owner, _graph(
        Borrow(Loan("hdr", "items", item_hdr)),
        Access(item_hdr, "write"),
        Use("hdr"),
    )).paths[0]
    ensure("suspended-parent" in _kinds(same_field),
           f"same field under same symbolic index did not conflict: {same_field.issues}")

    # 2D grid: disjoint if EITHER row OR col is proved disjoint.
    cell_1 = Place("grid", ("@r1", "@c1"))
    cell_2 = Place("grid", ("@r2", "@c2"))
    for assumption in (
        AssumeIndexNe("@r1", "@r2"),
        AssumeIndexNe("@c1", "@c2"),
        AssumeDisjoint(Place("grid", ("@r1",)), Place("grid", ("@r2",))),
        AssumeDisjoint(cell_1, cell_2),
    ):
        grid_ok = analyze(grid_owner, _graph(
            assumption,
            Borrow(Loan("left", "grid", cell_1, "exclusive")),
            Borrow(Loan("right", "grid", cell_2, "exclusive")),
            Use("left"),
            Use("right"),
        )).paths[0]
        ensure(not grid_ok.issues and not any(o.kind == "overlap" for o in grid_ok.obligations),
               f"2D grid failed under {assumption}: {grid_ok}")

    # Whole row vs cell when only col is disjoint must remain unknown.
    row_vs_cell = analyze(grid_owner, _graph(
        AssumeIndexNe("@c1", "@c2"),
        Borrow(Loan("row", "grid", Place("grid", ("@r1",)), "exclusive")),
        Access(cell_2, "write"),
        Use("row"),
    )).paths[0]
    ensure(any(o.kind == "overlap" for o in row_vs_cell.obligations),
           f"whole row vs cell with only col disequality did not leave overlap obligation: {row_vs_cell}")

    # InvalidateSymbol drops facts involving the invalidated symbol while keeping unrelated facts,
    # and freezes active loans mentioning that symbol.
    invalidated = analyze(grid_owner, _graph(
        AssumeIndexNe("@r1", "@r2"),
        AssumeIndexNe("@c1", "@c2"),
        InvalidateSymbol("@r1"),
        Borrow(Loan("left", "grid", cell_1, "exclusive")),
        Access(cell_2, "write"),
        Use("left"),
    )).paths[0]
    ensure(not invalidated.issues and not any(o.kind == "overlap" for o in invalidated.obligations),
           "InvalidateSymbol(@r1) wrongly dropped unrelated @c1 != @c2 fact")

    dropped_fact = analyze(arr_owner, _graph(
        AssumeIndexNe("@i", "@j"),
        InvalidateSymbol("@i"),
        Borrow(Loan("left", "arr", arr_i, "exclusive")),
        Access(arr_j, "write"),
        Use("left"),
    )).paths[0]
    ensure(any(o.kind == "overlap" for o in dropped_fact.obligations),
           "InvalidateSymbol(@i) failed to drop @i != @j fact")

    stale_loan_after_reassign = analyze(arr_owner, _graph(
        Borrow(Loan("left", "arr", arr_i)),
        InvalidateSymbol("@i"),
        Access(arr_i, "write"),
        Use("left"),
    )).paths[0]
    ensure("suspended-parent" not in _kinds(stale_loan_after_reassign)
           and any(o.kind == "overlap" for o in stale_loan_after_reassign.obligations),
           "reassigned index symbol falsely matched old loan's @i")

    # Branch join must keep paths with and without disjointness separate.
    join_graph = Graph("split", (
        Node("split", successors=("disjoint_arm", "plain_arm")),
        Node("disjoint_arm", AssumeIndexNe("@i", "@j"), ("join",)),
        Node("plain_arm", Nop(), ("join",)),
        Node("join", Borrow(Loan("left", "arr", arr_i)), ("write",)),
        Node("write", Access(arr_j, "write", stability="unstable"), ("use",)),
        Node("use", Use("left"), ("done",)),
        Node("done", Return("done")),
    ))
    paths = analyze(arr_owner, join_graph).paths
    ensure(len(paths) == 2, f"join unsoundly merged branches with different disjoint_facts: {paths}")
    by_arm = {("disjoint_arm" if "disjoint_arm" in p.nodes else "plain_arm"): p for p in paths}
    ensure(not by_arm["disjoint_arm"].issues,
           f"disjoint arm reported unexpected conflict: {by_arm['disjoint_arm'].issues}")
    ensure("invalidated-by-unstable-mutation" in _kinds(by_arm["plain_arm"]),
           f"plain arm missed unstable invalidation after join: {by_arm['plain_arm'].issues}")

    # Malformed symbolic projections and disjointness assumptions refuse cleanly.
    _refuses(lambda: analyze(arr_owner, _graph(Borrow(Loan("bad", "arr", Place("arr", ("@",)))))),
             "normalized identifiers")
    _refuses(lambda: analyze(arr_owner, _graph(Borrow(Loan("bad", "arr", Place("arr", ("@1bad",)))))),
             "normalized identifiers")
    _refuses(lambda: analyze(arr_owner, _graph(AssumeDisjoint(Place("arr", ("*",)), arr_j))),
             "disjointness assumption")
    _refuses(lambda: analyze(arr_owner, _graph(UseRefinement("missing"))),
             "missing refinement")


def _ante_stable_vs_unstable_and_refinements() -> None:
    buf_owners = (Owner("buf", borrowed=True, fields=(("length",), ("payload",))),)
    length_p = Place("buf", ("length",))
    payload_p = Place("buf", ("payload",))

    # Stable write invalidates overlapping refinements while preserving disjoint refinements and loans.
    stable_ok = analyze(buf_owners, _graph(
        AssumeRefinement("r_len", length_p),
        AssumeRefinement("r_pay", payload_p),
        Borrow(Loan("len_view", "buf", length_p)),
        Access(payload_p, "write", stability="stable"),
        Use("len_view"),
        UseRefinement("r_len"),
        Return("done"),
    )).paths[0]
    ensure(not stable_ok.issues, f"disjoint stable write broke refinement or loan: {stable_ok.issues}")

    stale_ref = analyze(buf_owners, _graph(
        AssumeRefinement("r_pay", payload_p),
        Access(payload_p, "write", stability="stable"),
        UseRefinement("r_pay"),
    )).paths[0]
    ensure([(i.node, i.kind, i.resources) for i in stale_ref.issues]
           == [("n2", "stale-refinement", ("r_pay",))],
           f"overlapping stable write did not mark refinement stale: {stale_ref.issues}")

    # Re-establishing a stale refinement makes it usable again; dropping clears it.
    reestablished = analyze(buf_owners, _graph(
        AssumeRefinement("r_pay", payload_p),
        Access(payload_p, "write", stability="stable"),
        AssumeRefinement("r_pay", payload_p),
        UseRefinement("r_pay"),
        DropRefinement("r_pay"),
        UseRefinement("r_pay"),
    )).paths[0]
    ensure([(i.node, i.kind, i.resources) for i in reestablished.issues]
           == [("n5", "unavailable-refinement", ("r_pay",))],
           f"re-establish/drop refinement sequence behaved unexpectedly: {reestablished.issues}")

    # Symbolic index refinements survive disjoint stable writes and invalidate on unproved/overlapping writes.
    vec_owners = (Owner("vec", borrowed=True),)
    vec_i = Place("vec", ("@i",))
    vec_j = Place("vec", ("@j",))
    sym_ref_ok = analyze(vec_owners, _graph(
        AssumeIndexNe("@i", "@j"),
        AssumeRefinement("r_i", vec_i),
        Access(vec_j, "write", stability="stable"),
        UseRefinement("r_i"),
    )).paths[0]
    ensure(not sym_ref_ok.issues, f"disjoint indexed write invalidated refinement: {sym_ref_ok.issues}")

    sym_ref_stale = analyze(vec_owners, _graph(
        AssumeRefinement("r_i", vec_i),
        Borrow(Loan("elem_i", "vec", vec_i)),
        Access(vec_j, "write", stability="stable"),
        Use("elem_i"),
        UseRefinement("r_i"),
    )).paths[0]
    ensure([(i.node, i.kind) for i in sym_ref_stale.issues] == [("n4", "stale-refinement")],
           f"stable unproved indexed write broke address validity or missed stale refinement: {sym_ref_stale.issues}")

    # Unstable container mutation invalidates live interior loan on that path, NOT on sibling path.
    unstable_branch = Graph("lend", (
        Node("lend", Borrow(Loan("elem", "vec", vec_i)), ("split",)),
        Node("split", Nop(), ("clear_then_use", "safe_use")),
        Node("clear_then_use", Access(Place("vec"), "write", stability="unstable"), ("bad_use",)),
        Node("bad_use", Use("elem"), ("ret_bad",)),
        Node("ret_bad", Return("Bad")),
        Node("safe_use", Use("elem"), ("ret_ok",)),
        Node("ret_ok", Return("Ok")),
    ))
    paths = analyze(vec_owners, unstable_branch).paths
    by_outcome = {p.outcome: p for p in paths}
    ensure(not by_outcome["Ok"].issues,
           f"sibling branch without unstable mutation lost interior loan validity: {by_outcome['Ok'].issues}")
    ensure("invalidated-by-unstable-mutation" in _kinds(by_outcome["Bad"])
           and any(i.node == "bad_use" and i.kind == "invalidated-by-unstable-mutation"
                   for i in by_outcome["Bad"].issues),
           f"unstable mutation path did not report invalidated-by-unstable-mutation at use: {by_outcome['Bad'].issues}")

    # Dead interior loan before unstable write is allowed (Polonius + Ante).
    dead_before_clear = analyze(vec_owners, _graph(
        Borrow(Loan("elem", "vec", vec_i)),
        Use("elem"),
        Access(Place("vec"), "write", stability="unstable"),
        Return("ok"),
    )).paths[0]
    ensure(not dead_before_clear.issues,
           f"unstable write after last use reported unexpected issues: {dead_before_clear.issues}")

    # Unstable write to unproved vec[@j] invalidates vec[@i]; with AssumeIndexNe(@i, @j) it survives!
    unproved_unstable = analyze(vec_owners, _graph(
        Borrow(Loan("elem", "vec", vec_i)),
        Access(vec_j, "write", stability="unstable"),
        Use("elem"),
    )).paths[0]
    ensure([(i.node, i.kind) for i in unproved_unstable.issues]
           == [("n2", "invalidated-by-unstable-mutation")],
           f"unproved unstable indexed write missed invalidation: {unproved_unstable.issues}")
    proved_unstable = analyze(vec_owners, _graph(
        AssumeIndexNe("@i", "@j"),
        Borrow(Loan("elem", "vec", vec_i)),
        Access(vec_j, "write", stability="unstable"),
        Use("elem"),
    )).paths[0]
    ensure(not proved_unstable.issues,
           f"proved-disjoint unstable indexed write conflicted: {proved_unstable.issues}")


def _loop_carried_cursor_reborrowing() -> None:
    head_owners = (Owner("head", borrowed=True, fields=(("visits",), ("next",))),)

    # 1-step cursor advancing loop: cursor = &mut cursor.next across iterations.
    one_step = Graph("entry", (
        Node("entry", Borrow(Loan("cursor", "head", Place("head"), mode="exclusive")), ("header",)),
        Node("header", Nop(), ("body_borrow", "exit")),
        Node("body_borrow", Borrow(Loan("next", "cursor", Place("head", ("next",)), mode="exclusive")),
             ("body_move",)),
        Node("body_move", Move("next", "cursor"), ("header",)),
        Node("exit", Use("cursor"), ("done",)),
        Node("done", Return("done")),
    ))
    report = analyze(head_owners, one_step, Limits(paths=8, work=10_000))
    ensure(len(report.paths) == 2 and all(not p.issues for p in report.paths),
           f"1-step cursor loop failed or exploded: {report.paths}")

    # 2-step loop_reborrowing.rs pattern: node = cursor; node.visits write; if advance: cursor = &mut node.next.
    two_step = Graph("entry", (
        Node("entry", Borrow(Loan("cursor", "head", Place("head"), mode="exclusive")), ("header",)),
        Node("header", Nop(), ("body_node", "exit")),
        Node("body_node", Borrow(Loan("node", "cursor", Place("head", ("next",)), mode="exclusive")),
             ("body_visit",)),
        Node("body_visit", Access(Place("head", ("next",)), "write", via="node"),
             ("body_adv", "body_stay")),
        Node("body_adv", Borrow(Loan("next", "node", Place("head", ("next",)), mode="exclusive")),
             ("body_move",)),
        Node("body_move", Move("next", "cursor"), ("header",)),
        Node("body_stay", Drop("node"), ("header",)),
        Node("exit", Use("cursor"), ("done",)),
        Node("done", Return("done")),
    ))
    two_report = analyze(head_owners, two_step, Limits(paths=16, work=20_000))
    ensure(all(not p.issues for p in two_report.paths),
           f"2-step cursor reborrow loop reported unexpected issues: {two_report.paths}")

    # Live-conflict: overwriting *cursor while descendant loan `node` is live catches suspended-parent.
    live_conflict = Graph("entry", (
        Node("entry", Borrow(Loan("cursor", "head", Place("head"), mode="exclusive")), ("header",)),
        Node("header", Nop(), ("body_node", "exit")),
        Node("body_node", Borrow(Loan("node", "cursor", Place("head", ("next",)), mode="exclusive")),
             ("overwrite",)),
        Node("overwrite", Access(Place("head"), "write", via="cursor"), ("body_visit",)),
        Node("body_visit", Access(Place("head", ("next",)), "write", via="node"), ("body_adv",)),
        Node("body_adv", Borrow(Loan("next", "node", Place("head", ("next",)), mode="exclusive")),
             ("body_move",)),
        Node("body_move", Move("next", "cursor"), ("header",)),
        Node("exit", Use("cursor"), ("done",)),
        Node("done", Return("done")),
    ))
    conflict_report = analyze(head_owners, live_conflict, Limits(paths=16, work=20_000))
    ensure(any("suspended-parent" in _kinds(p) for p in conflict_report.paths),
           f"overwriting cursor while descendant was live missed conflict: {conflict_report.paths}")


def _lowered_symbolic_disjointness_and_unstable_mutations() -> None:
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        direct_src = (TOOLS / "tests" / "fixtures" / "direct-indexed-borrows.hf").read_bytes()
        direct_tree = parser.parse_source(compiled, direct_src, surface=True)
        for fn_name in ("ReadAfterClearDirect", "JoinedDisjointClear", "UpdatePairDirect",
                        "UpdateSpanPair", "ReadSlotsDirect", "ReadSeqDirect"):
            lowered = lower_function(direct_tree, fn_name)
            report = analyze(lowered.owners, lowered.graph)
            ensure(all(not p.issues for p in report.paths),
                   f"lowered {fn_name} reported unexpected issues: {report.paths}")
            if fn_name == "ReadAfterClearDirect":
                ensure(any(isinstance(n.event, AssumeIndexNe) for n in lowered.graph.nodes),
                       "ReadAfterClearDirect did not lower i != j to AssumeIndexNe")
                ensure(any(isinstance(n.event, Access) and n.event.stability == "unstable"
                           for n in lowered.graph.nodes),
                       "Seq.Empty assignment did not lower with stability='unstable'")

        # Removing i != j in ReadAfterClearDirect must catch invalidated-by-unstable-mutation.
        unguarded_src = direct_src.replace(b"if (i < 2 && j < 2 && i != j)", b"if (i < 2 && j < 2)")
        unguarded_tree = parser.parse_source(compiled, unguarded_src, surface=True)
        unguarded_report = analyze_function(unguarded_tree, "ReadAfterClearDirect")
        ensure(any("invalidated-by-unstable-mutation" in _kinds(p) for p in unguarded_report.paths),
               f"unguarded ReadAfterClearDirect missed unstable invalidation: {unguarded_report.paths}")

        # Nested indexed invalidation fixture also lowers and checks cleanly.
        nested_src = (TOOLS / "tests" / "fixtures" / "nested-indexed-invalidation.hf").read_bytes()
        nested_tree = parser.parse_source(compiled, nested_src, surface=True)
        nested_report = analyze_module(nested_tree)
        ensure(all(not p.issues for r in nested_report.values() for p in r.paths),
               f"nested-indexed-invalidation.hf lowered with issues: {nested_report}")

        # Index reassignment invalidates prior AssumeIndexNe, and method Vec.clear lowers as unstable.
        extra_src = b"""module ExtraSymbolicAnte;
public Unit ReassignedIndex(ref Vec<Seq<byte>, 3> rows, Nat i, Nat j) {
    if (i != j) {
        let selected = in rows[i];
        i = j;
        rows[j] = Seq.Empty<byte>();
        Observe(in selected);
    }
}
public Unit VecClearConflict(ref Vec<byte, 4> vec, Nat i) {
    let elem = in vec[i];
    vec.clear();
    Observe(in elem);
}
public Unit VecEmptyConflict(ref Vec<byte, 4> vec, Nat i) {
    let elem = in vec[i];
    vec = Vec.Empty<byte>();
    Observe(in elem);
}
public Unit VecClearAfterLastUse(ref Vec<byte, 4> vec, Nat i) {
    let elem = in vec[i];
    Observe(in elem);
    vec.clear();
}
"""
        extra_tree = parser.parse_source(compiled, extra_src, surface=True)
        reassigned = analyze_function(extra_tree, "ReassignedIndex")
        ensure(any("invalidated-by-unstable-mutation" in _kinds(p) for p in reassigned.paths),
               f"reassigned index symbol did not invalidate i != j: {reassigned.paths}")
        vec_clear_lowered = lower_function(extra_tree, "VecClearConflict")
        ensure(any(isinstance(n.event, Access) and n.event.stability == "unstable"
                   for n in vec_clear_lowered.graph.nodes),
               "vec.clear() did not lower with stability='unstable'")
        vec_conflict = analyze(vec_clear_lowered.owners, vec_clear_lowered.graph)
        ensure(any("competing-loans" in _kinds(p) for p in vec_conflict.paths),
               f"vec.clear() with live elem did not conflict: {vec_conflict.paths}")
        vec_empty = analyze_function(extra_tree, "VecEmptyConflict")
        ensure(any("invalidated-by-unstable-mutation" in _kinds(p) for p in vec_empty.paths),
               f"vec = Vec.Empty() with live elem did not trigger unstable invalidation: {vec_empty.paths}")
        vec_ok = analyze_function(extra_tree, "VecClearAfterLastUse")
        ensure(all(not p.issues for p in vec_ok.paths),
               f"vec.clear() after last use failed: {vec_ok.paths}")


def _two_phase_receiver_qualification() -> None:
    fixture = TOOLS / "tests" / "fixtures" / "two-phase-receiver-trial.hf"
    source = fixture.read_bytes()
    with parser.cached_build(Path(__file__).resolve().parents[2]) as compiled:
        tree = parser.parse_source(compiled, source, surface=True)

    positives = (
        "DirectCount",
        "SnapshotCount",
        "ComputedReceiver",
        "EffectfulArgument",
        "PreActivationExit",
        "DisjointNamedView",
        "DisjointRetainedNamedView",
    )
    for fn_name in positives:
        lowered = lower_function(tree, fn_name)
        report = analyze(lowered.owners, lowered.graph)
        ensure(all(not p.issues for p in report.paths),
               f"Q25cd positive {fn_name} reported issues: {report.paths}")
        events = [node.event for node in lowered.graph.nodes]
        if fn_name in {"DirectCount", "SnapshotCount"}:
            read_idx = next(
                i for i, e in enumerate(events)
                if (isinstance(e, Reserve) and e.loan.mode == "shared")
                or (isinstance(e, Borrow) and e.loan.mode == "shared")
            )
            res_idx = next(
                i for i, e in enumerate(events) if isinstance(e, Reserve) and e.loan.mode == "exclusive"
            )
            act_idx = next(i for i, e in enumerate(events) if isinstance(e, Activate))
            ensure(
                (read_idx < res_idx < act_idx) if fn_name == "SnapshotCount" else (res_idx < read_idx < act_idx),
                f"unexpected phase order in {fn_name}: {(read_idx, res_idx, act_idx)}",
            )
        if fn_name == "ComputedReceiver":
            phases = [type(e) for e in events if isinstance(e, (Reserve, Activate))]
            ensure(phases == [Reserve, Activate], f"computed receiver lost two-phase order: {phases}")
        if fn_name == "EffectfulArgument":
            bump_idx = next(
                i for i, e in enumerate(events)
                if isinstance(e, Access) and e.place == Place("log") and e.kind == "write"
            )
            res_idx = next(
                i for i, e in enumerate(events)
                if isinstance(e, Reserve) and e.loan.place == Place("buf")
            )
            read_idx = next(
                i for i, e in enumerate(events)
                if isinstance(e, Borrow) and e.loan.place == Place("buf") and e.loan.mode == "shared"
            )
            act_idx = next(i for i, e in enumerate(events) if isinstance(e, Activate))
            ensure(res_idx < bump_idx < read_idx < act_idx,
                   f"effectful argument did not run between Reserve and ReadCount: {(res_idx, bump_idx, read_idx, act_idx)}")
        if fn_name == "PreActivationExit":
            ensure(len(report.paths) == 2, f"PreActivationExit lost error/ok split: {report.paths}")
            err_path = next(p for p in report.paths if p.outcome == "Err")
            ok_path = next(p for p in report.paths if p.outcome != "Err")
            ensure(err_path.moved_owners == ("item",) and not err_path.restorations,
                   f"pre-activation early exit lost move or created receiver restoration: {err_path}")
            ensure(ok_path.moved_owners == ("item",) and bool(ok_path.restorations),
                   f"activated branch lost move or receiver restoration: {ok_path}")

    negatives = {
        "OverlappingMutation": ("conflicting-receiver-reservation", b"buf.Mutate"),
        "OverlappingMove": ("conflicting-receiver-reservation", b"move buf"),
        "RetainedView": ("competing-loans", b"buf.WithRead"),
        "RetainedCapture": ("competing-loans", b"buf.WithRetained"),
        "ExplicitRefMethodRead": ("competing-loans", b"buf.ReadCount"),
        "ExplicitRefFieldRead": ("suspended-parent", b"buf.length"),
    }
    for fn_name, (expected_kind, expected_snippet) in negatives.items():
        lowered = lower_function(tree, fn_name)
        report = analyze(lowered.owners, lowered.graph)
        issues = [issue for p in report.paths for issue in p.issues]
        ensure(bool(issues) and issues[0].kind == expected_kind,
               f"Q25cd negative {fn_name} expected {expected_kind}, got {issues}")
        span = cast("list[int]", lowered.node_sites[issues[0].node]["span"])
        ensure(source[span[0]:span[1]] == expected_snippet,
               f"Q25cd negative {fn_name} pointed to {source[span[0]:span[1]]!r} instead of {expected_snippet!r}")


def _polonius_regions_and_nll_case3() -> None:
    # 1. NLL Problem Case #3 in regions.RegionSolver: conditional return of loan 'L' vs else write.
    solver = regions.RegionSolver(
        entry="entry",
        successors={
            "entry": ("then_ret", "else_write"),
            "then_ret": (),
            "else_write": ("else_ret",),
            "else_ret": (),
        },
        origins=(
            regions.Origin("a", "param"),
            regions.Origin("r", "local"),
        ),
        origin_loans=(regions.OriginLoan("entry", "r", "L"),),
        subset_edges=(regions.SubsetEdge("then_ret", "r", "a"),),
        origin_uses={"then_ret": ("a",)},
        invalidations={"else_write": ("L",)},
    )
    sol = solver.solve()
    ensure(not sol.diagnostics, f"NLL #3 positive failed in RegionSolver: {sol.diagnostics}")
    ensure("L" in sol.origin_contains_loan_at("then_ret", "a"),
           "returned branch origin did not receive loan L")
    ensure("L" not in sol.live_loans_at("else_write"),
           "dead local origin leaked loan L onto else_write")

    # Negative control: invalidating L on the returning branch before then_ret emits a 3-span witness.
    conflict_solver = regions.RegionSolver(
        entry="entry",
        successors={"entry": ("then_mid",), "then_mid": ("then_ret",), "then_ret": ()},
        origins=(regions.Origin("a", "param"), regions.Origin("r", "local")),
        origin_loans=(regions.OriginLoan("entry", "r", "L"),),
        subset_edges=(regions.SubsetEdge("then_ret", "r", "a"),),
        origin_uses={"then_ret": ("a",)},
        invalidations={"then_mid": ("L",)},
    )
    conflict_sol = conflict_solver.solve()
    ensure(len(conflict_sol.conflicts) == 1, f"expected 1 conflict witness, got {conflict_sol.diagnostics}")
    witness = conflict_sol.conflicts[0].witness
    ensure((witness.origin_point, witness.conflict_point, witness.live_use_point)
           == ("entry", "then_mid", "then_ret"),
           f"wrong 3-span witness points: {witness}")
    ensure("r" in witness.origin_chain, f"missing origin chain in witness: {witness}")

    # 2. Multi-region 'a vs 'b separation and declared outlives.
    bad_regions = regions.RegionSolver(
        entry="p0",
        successors={"p0": ()},
        origins=(regions.Origin("a", "param"), regions.Origin("b", "param")),
        outlives=(regions.OutlivesConstraint("b", "a", "p0"),),
    ).solve()
    ensure(len(bad_regions.outlives_errors) == 1,
           f"undeclared 'b: 'a outlives was accepted: {bad_regions.diagnostics}")

    good_regions = regions.RegionSolver(
        entry="p0",
        successors={"p0": ()},
        origins=(regions.Origin("a", "param"), regions.Origin("b", "param")),
        outlives=(regions.OutlivesConstraint("b", "a", "p0"),),
        declared_outlives=(("b", "a"),),
    ).solve()
    ensure(not good_regions.diagnostics, f"declared 'b: 'a outlives failed: {good_regions.diagnostics}")

    # 3. Variance: covariant, contravariant, and invariant.
    cov_ok = regions.RegionSolver(
        entry="p0",
        successors={"p0": ()},
        origins=(regions.Origin("outer", "param"), regions.Origin("fresh", "hrtb")),
    )
    cov_ok.add_variance(regions.Variance.COVARIANT, "outer", "fresh", "p0")
    ensure(not cov_ok.solve().diagnostics, "covariant outer -> fresh should succeed")

    cov_bad = regions.RegionSolver(
        entry="p0",
        successors={"p0": ()},
        origins=(regions.Origin("outer", "param"), regions.Origin("fresh", "hrtb")),
    )
    cov_bad.add_variance(regions.Variance.COVARIANT, "fresh", "outer", "p0")
    ensure(len(cov_bad.solve().hrtb_escapes) == 1, "covariant fresh -> outer must fail HRTB check")

    contra_ok = regions.RegionSolver(
        entry="p0",
        successors={"p0": ()},
        origins=(regions.Origin("outer", "param"), regions.Origin("fresh", "hrtb")),
    )
    contra_ok.add_variance(regions.Variance.CONTRAVARIANT, "fresh", "outer", "p0")
    ensure(not contra_ok.solve().diagnostics, "contravariant fn(fresh) <: fn(outer) should succeed")

    inv_bad = regions.RegionSolver(
        entry="p0",
        successors={"p0": ()},
        origins=(regions.Origin("outer", "param"), regions.Origin("fresh", "hrtb")),
    )
    inv_bad.add_variance(regions.Variance.INVARIANT, "outer", "fresh", "p0")
    ensure(len(inv_bad.solve().hrtb_escapes) == 1,
           "invariant ref<'outer> vs ref<'fresh> must reject bidirectional escape")

    # 4. Transitive HRTB 'fresh non-escape through intermediate local origin.
    hrtb_chain = regions.RegionSolver(
        entry="n0",
        successors={"n0": ("n1",), "n1": ()},
        origins=(
            regions.Origin("fresh", "hrtb"),
            regions.Origin("tmp", "local"),
            regions.Origin("outer", "param"),
        ),
        subset_edges=(
            regions.SubsetEdge("n0", "fresh", "tmp"),
            regions.SubsetEdge("n1", "tmp", "outer"),
        ),
        origin_uses={"n1": ("outer",)},
    ).solve()
    ensure(len(hrtb_chain.hrtb_escapes) == 1
           and hrtb_chain.hrtb_escapes[0].witness.origin_chain == ("fresh", "tmp", "outer"),
           f"transitive HRTB escape lost origin chain: {hrtb_chain.diagnostics}")

    # 5. CFG-level exclusive ref<'a> conditional return (NLL #3) + negative controls.
    ref_owners = (Owner("map", borrowed=True, fields=(("slot",), ("other",)), origin="'a", mode="exclusive"),)
    slot_p = Place("map", ("slot",))
    other_p = Place("map", ("other",))
    nll3_graph = Graph(
        "entry",
        (
            Node("entry", Borrow(Loan("val", "map", slot_p, "exclusive", origin="'a")), ("found", "missing")),
            Node("found", Return("Found", ("val",), origin="'a")),
            Node("missing", Access(slot_p, "write"), ("missing_ret",)),
            Node("missing_ret", Return("Missing")),
        ),
        return_origin="'a",
    )
    nll3_paths = analyze(ref_owners, nll3_graph).paths
    found_p = next(p for p in nll3_paths if p.outcome == "Found")
    missing_p = next(p for p in nll3_paths if p.outcome == "Missing")
    ensure(not found_p.issues and found_p.returned_loans == ("val",) and found_p.retained_loans == ("val",),
           f"exclusive ref<'a> return failed: {found_p}")
    ensure(any(ob.kind == "returned-loan-restoration" for ob in found_p.obligations),
           f"exclusive ref<'a> return did not emit restoration duty: {found_p.obligations}")
    ensure(not missing_p.issues and not missing_p.returned_loans,
           f"NLL #3 else write failed: {missing_p}")

    # Negative controls: local owner exclusive escape, wrong region 'b -> 'a, and conflicting sibling return.
    local_exc = analyze(
        (Owner("local", borrowed=False, origin="'a"),),
        Graph("n0", (
            Node("n0", Borrow(Loan("v", "local", Place("local"), "exclusive", origin="'a")), ("n1",)),
            Node("n1", Return("Ok", ("v",), origin="'a")),
        )),
    ).paths[0]
    ensure({"local-loan-escape", "exclusive-loan-escape"} <= _kinds(local_exc),
           f"local exclusive escape was not refused: {local_exc.issues}")

    wrong_region = analyze(
        (Owner("b_owner", borrowed=True, origin="'b", mode="exclusive"),),
        Graph("n0", (
            Node("n0", Borrow(Loan("v", "b_owner", Place("b_owner"), "exclusive", origin="'b")), ("n1",)),
            Node("n1", Return("Ok", ("v",), origin="'a")),
        ), return_origin="'a"),
    ).paths[0]
    ensure("exclusive-loan-escape" in _kinds(wrong_region),
           f"mismatched region 'b -> 'a exclusive return was accepted: {wrong_region.issues}")

    conflict_sibling = analyze(
        ref_owners,
        Graph("n0", (
            Node("n0", Borrow(Loan("v1", "map", slot_p, "exclusive", origin="'a")), ("n1",)),
            Node("n1", Borrow(Loan("v2", "map", slot_p, "shared", origin="'a")), ("n2",)),
            Node("n2", Return("Ok", ("v1", "v2"), origin="'a")),
        ), return_origin="'a"),
    ).paths[0]
    ensure("competing-loans" in _kinds(conflict_sibling) and "exclusive-loan-escape" in _kinds(conflict_sibling),
           f"conflicting sibling exclusive return was accepted: {conflict_sibling.issues}")

    disjoint_siblings = analyze(
        ref_owners,
        Graph("n0", (
            Node("n0", Borrow(Loan("v1", "map", slot_p, "exclusive", origin="'a")), ("n1",)),
            Node("n1", Borrow(Loan("v2", "map", other_p, "exclusive", origin="'a")), ("n2",)),
            Node("n2", Return("Ok", ("v1", "v2"), origin="'a")),
        ), return_origin="'a"),
    ).paths[0]
    ensure(not disjoint_siblings.issues and disjoint_siblings.returned_loans == ("v1", "v2"),
           f"disjoint field exclusive sibling returns conflicted: {disjoint_siblings.issues}")


def _shared_mut_and_ante_proof_events() -> None:
    # 1. Aliased shared_mut stable writes succeed without conflicting-access/suspended-parent.
    buf_owners = (Owner("buf", borrowed=True, fields=(("x",), ("y",))),)
    xp = Place("buf", ("x",))
    yp = Place("buf", ("y",))
    aliased_sm = analyze(buf_owners, _graph(
        AssumeRefinement("r_x", xp),
        AssumeRefinement("r_y", yp),
        Borrow(Loan("sm1", "buf", xp, "shared_mut")),
        Borrow(Loan("sm2", "buf", xp, "shared_mut")),
        Access(xp, "write", via="sm1", stability="stable"),
        Access(xp, "write", via="sm2", stability="stable"),
        Use("sm1"),
        Use("sm2"),
        UseRefinement("r_y"),
        Return("ok"),
    )).paths[0]
    ensure(not aliased_sm.issues,
           f"aliased shared_mut stable writes or disjoint refinement failed: {aliased_sm.issues}")

    # Overlapping refinement becomes stale after shared_mut write.
    stale_sm = analyze(buf_owners, _graph(
        AssumeRefinement("r_x", xp),
        Borrow(Loan("sm1", "buf", xp, "shared_mut")),
        Borrow(Loan("sm2", "buf", xp, "shared_mut")),
        Access(xp, "write", via="sm1", stability="stable"),
        Use("sm2"),
        UseRefinement("r_x"),
    )).paths[0]
    ensure([(i.node, i.kind) for i in stale_sm.issues] == [("n5", "stale-refinement")],
           f"shared_mut write did not invalidate overlapping refinement: {stale_sm.issues}")

    # 2. Unstable shared_mut writes rejected unless justified by explicit proof fact.
    vec_owners = (Owner("vec", borrowed=True, fields=(("tag",), ("payload",))),)
    vec_i = Place("vec", ("@i",))
    vec_j = Place("vec", ("@j",))
    unjustified_unstable = analyze(vec_owners, _graph(
        Borrow(Loan("sm", "vec", Place("vec"), "shared_mut")),
        Access(Place("vec"), "write", via="sm", stability="unstable"),
    )).paths[0]
    ensure("unstable-shared-mut-write" in _kinds(unjustified_unstable),
           f"unjustified unstable shared_mut write was accepted: {unjustified_unstable.issues}")

    # Justified by AssumeIndexNe, AssumeDisjoint, AssumeTagPreserved, AssumeNoRealloc:
    for assumption, target_place in (
        (AssumeIndexNe("@i", "@j"), vec_i),
        (AssumeDisjoint(vec_i, vec_j), vec_i),
        (AssumeTagPreserved(Place("vec")), Place("vec")),
        (AssumeNoRealloc(Place("vec")), Place("vec")),
    ):
        justified = analyze(vec_owners, _graph(
            assumption,
            Borrow(Loan("sm", "vec", target_place, "shared_mut")),
            Access(target_place, "write", via="sm", stability="unstable"),
        )).paths[0]
        ensure(not justified.issues,
               f"justified unstable shared_mut write under {assumption} failed: {justified.issues}")

    # 3. Tag-preserving union mutation (AssumeTagPreserved) beats Ante.
    payload_p = Place("vec", ("payload",))
    union_bad = analyze(vec_owners, _graph(
        Borrow(Loan("inner", "vec", payload_p, "shared_mut")),
        Access(Place("vec"), "write", stability="unstable"),
        Use("inner"),
    )).paths[0]
    ensure({"suspended-parent", "invalidated-by-unstable-mutation"} <= _kinds(union_bad),
           f"unguarded union unstable write did not invalidate interior shared_mut: {union_bad.issues}")

    union_ok = analyze(vec_owners, _graph(
        AssumeTagPreserved(Place("vec")),
        Borrow(Loan("inner", "vec", payload_p, "shared_mut")),
        Access(Place("vec"), "write", stability="unstable"),
        Use("inner"),
    )).paths[0]
    ensure(not union_ok.issues, f"AssumeTagPreserved union mutation failed: {union_ok.issues}")

    # 4. len < cap container push (AssumeNoRealloc) beats Ante.
    push_bad = analyze(vec_owners, _graph(
        Borrow(Loan("elem", "vec", vec_i, "shared")),
        Access(Place("vec"), "write", stability="unstable"),
        Use("elem"),
    )).paths[0]
    ensure({"suspended-parent", "invalidated-by-unstable-mutation"} <= _kinds(push_bad),
           f"unguarded push did not conflict with element loan: {push_bad.issues}")

    push_ok = analyze(vec_owners, _graph(
        AssumeNoRealloc(Place("vec")),
        Borrow(Loan("elem", "vec", vec_i, "shared")),
        Access(Place("vec"), "write", stability="unstable"),
        Use("elem"),
    )).paths[0]
    ensure(not push_ok.issues, f"AssumeNoRealloc container push failed: {push_ok.issues}")


def _field_cursor_3span_and_certificate() -> None:
    # 1. base_loan_name and 3-span diagnostics.
    ensure(base_loan_name("cursor#2") == "cursor" and base_loan_name("cursor") == "cursor",
           "base_loan_name did not strip #suffix cleanly")
    span_report = analyze(_OWNERS, _graph(
        Borrow(Loan("reader", "workspace", _BYTES)),
        Access(_BYTES, "write"),
        Use("reader"),
    ))
    span_issue = span_report.paths[0].issues[0]
    ensure((span_issue.origin_node, span_issue.conflict_node, span_issue.live_use_node, span_issue.proposed_end_node)
           == ("n0", "n1", "n2", "n2"),
           f"3-span fields incorrect: {span_issue}")

    # Loop-step #suffix conflict normalizes resource name so borrow_origins lookup succeeds.
    head_owners = (Owner("head", borrowed=True, fields=(("next",), ("visits",))),)
    loop_conflict = analyze(head_owners, Graph("entry", (
        Node("entry", Borrow(Loan("cursor", "head", Place("head"), "exclusive")), ("header",)),
        Node("header", Nop(), ("body_node", "exit")),
        Node("body_node", Borrow(Loan("node", "cursor", Place("head", ("next",)), "exclusive")), ("overwrite",)),
        Node("overwrite", Access(Place("head"), "write", via="cursor"), ("body_visit",)),
        Node("body_visit", Access(Place("head", ("next",)), "write", via="node"), ("body_adv",)),
        Node("body_adv", Borrow(Loan("next", "node", Place("head", ("next",)), "exclusive")), ("body_move",)),
        Node("body_move", Move("next", "cursor"), ("header",)),
        Node("exit", Use("cursor"), ("done",)),
        Node("done", Return("done")),
    )), Limits(paths=16, work=20_000))
    conflict_issues = [i for p in loop_conflict.paths for i in p.issues if i.kind == "suspended-parent"]
    ensure(bool(conflict_issues) and all("#" not in res for i in conflict_issues for res in i.resources),
           f"loop conflict leaked #suffix into Issue.resources: {conflict_issues}")

    # 2. Field-projecting fold_loop_cursor() preserves parent suspension and descendant containment.
    state = _State(
        {"head": head_owners[0]},
        {"head": frozenset({("next",), ("visits",)})},
        _Budget(1000),
        "entry",
    )
    state.loans["cursor"] = Loan("cursor", "head", Place("head"), "exclusive")
    state.parents["cursor"] = "head"
    state.active.add("cursor")
    state.loans["next"] = Loan("next", "cursor", Place("head", ("next",)), "exclusive")
    state.parents["next"] = "cursor"
    state.active.add("next")
    state.loans["next#1"] = Loan("next#1", "next", Place("head", ("next", "next")), "exclusive")
    state.parents["next#1"] = "next"
    state.step_bases["next#1"] = "next"
    state.active.add("next#1")
    state.values["cursor"] = _Value(frozenset({"next#1"}), "next#1")
    state.fold_loop_cursor()
    ensure("next#1" not in state.active and "next" in state.active
           and state.values["cursor"].handle == "next",
           f"field-projecting fold_loop_cursor did not collapse next#1 into next: {state.active}, {state.values}")
    # Parent suspension is preserved when overwriting cursor's parent after folding.
    state.access(Node("write_head", Access(Place("head"), "write")), Access(Place("head"), "write"), None)
    ensure(any(i.kind == "suspended-parent" for i in state.issues),
           f"parent suspension lost after field-projecting fold_loop_cursor: {state.issues}")

    # Run via real CFG with field-projecting child reborrow:
    projecting = analyze(head_owners, Graph("entry", (
        Node("entry", Borrow(Loan("cursor", "head", Place("head", ("next",)), "exclusive")), ("header",)),
        Node("header", Nop(), ("step", "exit")),
        Node("step", Borrow(Loan("next", "cursor", Place("head", ("next", "next")), "exclusive")), ("mv",)),
        Node("mv", Move("next", "cursor"), ("header",)),
        Node("exit", Use("cursor"), ("done",)),
        Node("done", Return("done")),
    )), Limits(paths=8, work=10_000))
    ensure(all(not p.issues for p in projecting.paths),
           f"field-projecting loop cursor failed: {projecting.paths}")

    outside = analyze(head_owners, Graph("entry", (
        Node("entry", Borrow(Loan("cursor", "head", Place("head", ("next",)), "exclusive")), ("header",)),
        Node("header", Nop(), ("step", "exit")),
        Node("step", Borrow(Loan("bad", "cursor", Place("head", ("visits",)), "exclusive")), ("mv",)),
        Node("mv", Move("bad", "cursor"), ("header",)),
        Node("exit", Use("cursor"), ("done",)),
        Node("done", Return("done")),
    )), Limits(paths=8, work=10_000))
    ensure(any("reborrow-outside-parent" in _kinds(p) for p in outside.paths),
           f"field-projecting loop hid reborrow-outside-parent: {outside.paths}")

    # 3. Certificate exporter produces serializable JSON matching schema.
    cert = export_loan_certificate(span_report)
    encoded = json.dumps(cert)
    decoded = json.loads(encoded)
    ensure(decoded["schema"] == "holdfast-loan-certificate-v1" and decoded["valid"] is False
           and decoded["path_count"] == 1
           and decoded["paths"][0]["issues"][0]["live_use_node"] == "n2",
           f"unexpected certificate export: {decoded}")

    # 4. Targeted state merging: identical live loan origins used at different branches merge into 1 path.
    diamond = analyze(_OWNERS, Graph("split", (
        Node("split", Borrow(Loan("reader", "workspace", _BYTES)), ("left", "right")),
        Node("left", Use("reader"), ("join",)),
        Node("right", Use("reader"), ("join",)),
        Node("join", Use("reader"), ("done",)),
        Node("done", Return("ok")),
    )), Limits(paths=2))
    ensure(len(diamond.paths) == 1 and not diamond.paths[0].issues,
           f"targeted state merging split identical live loan origins: {diamond.paths}")


def _lowered_proved_facts_and_richer_guards() -> None:
    def id_node(text: str) -> dict[str, object]:
        return {"kind": "identifier", "text": text, "span": [0, len(text)]}

    def name_expr(text: str) -> dict[str, object]:
        return {"kind": "name", "name": id_node(text), "span": [0, len(text)]}

    def member_expr(recv: dict[str, object], field: str) -> dict[str, object]:
        return {"kind": "member", "value": recv, "name": id_node(field), "span": [0, 1]}

    def index_expr(recv: dict[str, object], idx: dict[str, object]) -> dict[str, object]:
        return {"kind": "index", "value": recv, "index": idx, "span": [0, 1]}

    def bin_expr(op: str, left: dict[str, object], right: dict[str, object]) -> dict[str, object]:
        return {
            "kind": "binary",
            "operator": {"kind": "operator", "text": op},
            "left": left,
            "right": right,
            "span": [0, 1],
        }

    def nat_lit(val: str) -> dict[str, object]:
        return {"kind": "nat", "value": val, "span": [0, len(val)]}

    def borrow_expr(mode: str, val: dict[str, object]) -> dict[str, object]:
        return {
            "kind": "unary",
            "operator": {"kind": "operator", "text": mode},
            "value": val,
            "span": [0, 1],
        }

    # Lowering disjunctive guard `r1 != r2 || c1 != c2` + `a + m <= b` + `i != 0` + `vec.Length < vec.Capacity`.
    fn_ast: dict[str, object] = {
        "kind": "function",
        "name": id_node("RicherGuardsAndFacts"),
        "parameters": [
            {"kind": "parameter", "mode": "ref", "name": id_node("grid"), "type": name_expr("Vec")},
            {"kind": "parameter", "mode": "ref", "name": id_node("vec"), "type": name_expr("Vec")},
            {"kind": "parameter", "mode": "value", "name": id_node("r1"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("r2"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("c1"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("c2"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("a"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("b"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("m"), "type": name_expr("usize")},
            {"kind": "parameter", "mode": "value", "name": id_node("i"), "type": name_expr("usize")},
        ],
        "contracts": [],
        "body": {
            "kind": "block",
            "statements": [
                {
                    "kind": "if",
                    "condition": bin_expr(
                        "||",
                        bin_expr("!=", name_expr("r1"), name_expr("r2")),
                        bin_expr("!=", name_expr("c1"), name_expr("c2")),
                    ),
                    "then_body": [
                        {
                            "kind": "let",
                            "name": id_node("cell1"),
                            "value": borrow_expr("ref", index_expr(index_expr(name_expr("grid"), name_expr("r1")), name_expr("c1"))),
                        },
                        {
                            "kind": "let",
                            "name": id_node("cell2"),
                            "value": borrow_expr("ref", index_expr(index_expr(name_expr("grid"), name_expr("r2")), name_expr("c2"))),
                        },
                        {"kind": "expression", "expression": name_expr("cell1")},
                        {"kind": "expression", "expression": name_expr("cell2")},
                    ],
                    "else_body": [],
                },
                {
                    "kind": "if",
                    "condition": bin_expr(
                        "&&",
                        bin_expr(">", name_expr("m"), nat_lit("0")),
                        bin_expr("<=", bin_expr("+", name_expr("a"), name_expr("m")), name_expr("b")),
                    ),
                    "then_body": [
                        {
                            "kind": "let",
                            "name": id_node("va"),
                            "value": borrow_expr("ref", index_expr(name_expr("vec"), name_expr("a"))),
                        },
                        {
                            "kind": "let",
                            "name": id_node("vb"),
                            "value": borrow_expr("ref", index_expr(name_expr("vec"), name_expr("b"))),
                        },
                        {"kind": "expression", "expression": name_expr("va")},
                        {"kind": "expression", "expression": name_expr("vb")},
                    ],
                    "else_body": [],
                },
                {
                    "kind": "if",
                    "condition": bin_expr("!=", name_expr("i"), nat_lit("0")),
                    "then_body": [],
                    "else_body": [],
                },
                {
                    "kind": "if",
                    "condition": bin_expr(
                        "<",
                        member_expr(name_expr("vec"), "Length"),
                        member_expr(name_expr("vec"), "Capacity"),
                    ),
                    "then_body": [],
                    "else_body": [],
                },
            ],
        },
    }

    facts = ProvedFacts(
        disjoint_places=((Place("grid", ("@r1", "@c1")), Place("grid", ("@r2", "@c2"))),),
        arithmetic_disequalities=(("@x", "@y"),),
        tag_preserved=(Place("vec"),),
        no_realloc=(Place("vec"),),
        refinements={"vec_nonempty": Place("vec")},
        use_refinements=("vec_nonempty",),
    )
    lowered = lower_function(fn_ast, proved_facts=facts)
    events = [n.event for n in lowered.graph.nodes]
    ensure(any(isinstance(e, AssumeDisjoint) for e in events), "proved_facts missed AssumeDisjoint")
    ensure(any(isinstance(e, AssumeTagPreserved) for e in events), "proved_facts missed AssumeTagPreserved")
    ensure(any(isinstance(e, AssumeNoRealloc) for e in events), "proved_facts missed AssumeNoRealloc")
    ensure(any(isinstance(e, AssumeRefinement) for e in events), "proved_facts missed AssumeRefinement")
    ensure(any(isinstance(e, UseRefinement) for e in events), "proved_facts missed UseRefinement")
    ensure(any(isinstance(e, AssumeIndexNe) and e.left == "@i" and e.right == "@_0" for e in events),
           "i != 0 guard did not lower to AssumeIndexNe(@i, @_0)")
    ensure(any(isinstance(e, AssumeIndexNe) and e.left == "@a" and e.right == "@b" for e in events),
           "m > 0 && a + m <= b did not lower to AssumeIndexNe(@a, @b)")
    ensure(any(isinstance(e, AssumeIndexNe) and e.left == "@r1" and e.right == "@r2" for e in events)
           and any(isinstance(e, AssumeIndexNe) and e.left == "@c1" and e.right == "@c2" for e in events),
           "r1 != r2 || c1 != c2 did not lower both disjunct AssumeIndexNe facts")
    report = analyze_function(fn_ast, proved_facts=facts)
    ensure(all(not p.issues for p in report.paths),
           f"richer guards and proved_facts reported unexpected issues: {report.paths}")


def cases() -> list[Case]:
    return [
        Case("located receiver order, snapshots, views and retained loans", _located_receiver_timing, lane="toolchain"),
        Case("public receiver views across private field renaming", _receiver_view_representation_change, lane="toolchain"),
        Case("checked implicit receiver reads on actual slots", _checked_receiver_read, lane="toolchain"),
        Case("receiver argument views through branch results and helper inputs", _receiver_argument_view_captures,
             lane="toolchain"),
        Case("element loan and value snapshot across slot relocation", _element_loan_during_relocation, lane="toolchain"),
        Case("symbolically disjoint indexed call loans and coincident control", _indexed_symbolic_disjointness,
             lane="toolchain"),
        Case("ordered mixed indexed call loans and possible alias controls", _mixed_indexed_loans, lane="toolchain"),
        Case("owner-coordinate shared and exclusive element loans", _owner_coordinate_indexed_loans, lane="toolchain"),
        Case("branch-selected shared and exclusive element loans", _correlated_indexed_loans, lane="toolchain"),
            Case("last-use restoration and unresolved facts", _last_use_and_residuals),
            Case("nested restoration and suspended ancestors", _nested_restoration_and_suspension),
            Case("receiver reservation, activation and cancellation", _receiver_reservations),
            Case("declared field partitions and unknown overlap", _field_partitions_and_unknowns),
            Case("unknown footprints and containment without competing loans", _unknown_footprints_without_competitors),
            Case("shared/exclusive access and reborrow grants", _shared_and_exclusive_grants),
            Case("transitive captures, moves and availability", _transitive_captures_and_moves),
            Case("branch-specific returned views and unavailable names", _branch_alternatives_and_returned_wrappers),
            Case("availability-only drops preserve actual last use", _drop_is_availability_only),
            Case("escape restrictions and retained ancestor duties", _escape_limits_and_ancestor_duties),
            Case("scoped ancestors cannot escape through returned descendants", _scoped_ancestor_escapes),
            Case("branch-local identities and moved returned captures stay separate",
                 _branch_local_names_and_moved_returns),
            Case("invalid returned captures never install a grant", _invalid_returned_capture_has_no_grant),
            Case("owner movement and blocked routes", _owner_moves),
            Case("invariant and suspension boundaries", _invariants_and_boundaries),
            Case("malformed graphs and absent references", _structural_refusals),
            Case("malformed records and edge identities refuse completely", _malformed_records_and_edges),
            Case("generated independent branch-demand and restoration oracle", _generated_branch_demand_oracle),
            Case("complete deterministic exploration and bounded refusal", _complete_exploration_and_budgets),
            Case("selective per-conjunct invariant lifting and unlifted active clauses", _selective_invariant_lifting),
            Case("cfg join-point state merging and bounded loop fixpoint", _cfg_join_merging_and_bounded_loops),
            Case("moved routes and branch-local loan footprints stay correlated at joins",
                 _correlated_loan_origins_at_join),
            Case("entry loop and branch-specific view diagnostics", _loop_entry_and_conditional_view),
            Case("schema-2 surface ast to loan graph lowering pass", _surface_ast_to_loan_graph_lowering),
            Case("holdfast_parser schema-2 surface ast lowering and site mapping", _holdfast_parser_schema2_surface_ast_lowering),
            Case("symbolic index projections, multi-d disjointness and invalidation",
                 _symbolic_index_projections_and_disjointness),
            Case("ante-style stable vs unstable place invalidation and content refinements",
                 _ante_stable_vs_unstable_and_refinements),
            Case("loop-carried cursor reborrowing fixpoint and live-conflict detection",
                 _loop_carried_cursor_reborrowing),
            Case("lowered symbolic disjointness and unstable container mutations",
                 _lowered_symbolic_disjointness_and_unstable_mutations, lane="toolchain"),
            Case("q25cd two-phase receiver trial fixture and phase verification",
                 _two_phase_receiver_qualification, lane="toolchain"),
            Case("polonius regions, variance, hrtb, and exclusive ref returns",
                 _polonius_regions_and_nll_case3),
            Case("shared_mut writes, refinement preservation, tag and no-realloc proofs",
                 _shared_mut_and_ante_proof_events),
            Case("field-projecting loop cursor, 3-span diagnostics, certificate, and merging",
                 _field_cursor_3span_and_certificate),
            Case("lowered proved_facts injection and richer arithmetic/disjunctive guards",
                 _lowered_proved_facts_and_richer_guards)]
