# SPDX-License-Identifier: Apache-2.0
"""Location-sensitive Polonius-style origin, subset, variance, and HRTB region solver."""

from collections import deque
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import StrEnum
from typing import Literal

type OriginKind = Literal["param", "local", "hrtb"]


class Variance(StrEnum):
    """Region variance governing outlives direction under subtyping."""

    COVARIANT = "covariant"
    INVARIANT = "invariant"
    CONTRAVARIANT = "contravariant"


@dataclass(frozen=True)
class Origin:
    """Named lifetime/region origin with parameter, local, or higher-ranked kind."""

    name: str
    kind: OriginKind = "local"
    scope: frozenset[str] | None = None


@dataclass(frozen=True)
class OutlivesConstraint:
    """Point-specific outlives constraint: ``sup`` outlives ``sub`` at ``point``."""

    sup: str
    sub: str
    point: str


@dataclass(frozen=True)
class SubsetEdge:
    """Directed loan-flow edge ``from_origin <= to_origin`` active at ``point``."""

    point: str
    from_origin: str
    to_origin: str


@dataclass(frozen=True)
class OriginLoan:
    """Introduction of ``loan`` into ``origin`` at ``point``."""

    point: str
    origin: str
    loan: str


@dataclass(frozen=True)
class RegionWitness:
    """Structured 3-span diagnostic witness with the offending origin chain."""

    origin_point: str
    conflict_point: str
    live_use_point: str
    origin_chain: tuple[str, ...]


@dataclass(frozen=True)
class RegionDiagnostic:
    """Structured region error (loan conflict, HRTB escape, or undeclared outlives)."""

    kind: str
    witness: RegionWitness
    loan: str | None = None
    origin: str | None = None
    detail: str = ""


def variance_outlives(
    variance: Variance, lhs: str, rhs: str, point: str
) -> tuple[OutlivesConstraint, ...]:
    """Emit outlives constraints relating ``T<lhs> <: T<rhs>`` at ``point``."""
    match variance:
        case Variance.COVARIANT:
            return (OutlivesConstraint(lhs, rhs, point),)
        case Variance.CONTRAVARIANT:
            return (OutlivesConstraint(rhs, lhs, point),)
        case Variance.INVARIANT:
            return (
                OutlivesConstraint(lhs, rhs, point),
                OutlivesConstraint(rhs, lhs, point),
            )


class RegionSolution:
    """Query interface over solved per-point origin-loan, subset, and liveness sets."""

    def __init__(
        self,
        *,
        origin_loans_map: dict[str, dict[str, frozenset[str]]],
        live_origins_map: dict[str, frozenset[str]],
        live_loans_map: dict[str, frozenset[str]],
        subset_map: dict[str, frozenset[tuple[str, str]]],
        diagnostics: tuple[RegionDiagnostic, ...],
    ) -> None:
        self._origin_loans = origin_loans_map
        self._live_origins = live_origins_map
        self._live_loans = live_loans_map
        self._subsets = subset_map
        self.diagnostics = diagnostics
        self.witnesses = tuple(diag.witness for diag in diagnostics)
        self.conflicts = tuple(diag for diag in diagnostics if diag.kind == "loan-conflict")
        self.hrtb_escapes = tuple(diag for diag in diagnostics if diag.kind == "hrtb-escape")
        self.outlives_errors = tuple(diag for diag in diagnostics if diag.kind == "outlives-error")

    def origin_contains_loan_at(self, point: str, origin: str) -> frozenset[str]:
        """Return all loans reachable in ``origin`` at CFG ``point``."""
        return self._origin_loans.get(point, {}).get(origin, frozenset())

    def live_loans_at(self, point: str) -> frozenset[str]:
        """Return all loans live on entry/use at CFG ``point``."""
        return self._live_loans.get(point, frozenset())

    def live_origins_at(self, point: str) -> frozenset[str]:
        """Return all origins live on entry/use at CFG ``point``."""
        return self._live_origins.get(point, frozenset())

    def subset_at(self, point: str) -> frozenset[tuple[str, str]]:
        """Return the closed subset relation ``(from_origin, to_origin)`` at ``point``."""
        return self._subsets.get(point, frozenset())

    def can_outlive(self, sup: str, sub: str, point: str) -> bool:
        """Check whether ``sup`` flows into ``sub`` without an outlives/HRTB error."""
        if sup == sub:
            return True
        if any(
            diag.kind in {"hrtb-escape", "outlives-error"}
            and diag.witness.conflict_point == point
            and diag.witness.origin_chain
            and diag.witness.origin_chain[0] == sup
            and diag.witness.origin_chain[-1] == sub
            for diag in self.diagnostics
        ):
            return False
        return (sup, sub) in self.subset_at(point)


class RegionSolver:
    """Polonius-style location-sensitive fixed-point solver over a CFG."""

    def __init__(
        self,
        entry: str = "entry",
        successors: Mapping[str, Sequence[str]] | None = None,
        *,
        origins: Sequence[Origin] = (),
        outlives: Sequence[OutlivesConstraint] = (),
        subset_edges: Sequence[SubsetEdge] = (),
        origin_loans: Sequence[OriginLoan] = (),
        origin_uses: Mapping[str, Sequence[str]] | None = None,
        invalidations: Mapping[str, Sequence[str]] | None = None,
        kills: Mapping[str, Sequence[str]] | None = None,
        declared_outlives: Sequence[tuple[str, str]] = (),
    ) -> None:
        self.entry = entry
        self.successors: dict[str, list[str]] = (
            {pt: list(succs) for pt, succs in successors.items()} if successors is not None else {}
        )
        self.origins: dict[str, Origin] = {origin.name: origin for origin in origins}
        self.subset_edges: list[SubsetEdge] = list(subset_edges)
        for constraint in outlives:
            self.add_outlives(constraint)
        self.origin_loans: list[OriginLoan] = list(origin_loans)
        self.origin_uses: dict[str, set[str]] = (
            {pt: set(names) for pt, names in origin_uses.items()} if origin_uses is not None else {}
        )
        self.invalidations: dict[str, set[str]] = (
            {pt: set(loans) for pt, loans in invalidations.items()}
            if invalidations is not None
            else {}
        )
        self.kills: dict[str, set[str]] = (
            {pt: set(loans) for pt, loans in kills.items()} if kills is not None else {}
        )
        self.declared_outlives: set[tuple[str, str]] = set(declared_outlives)

    def _ensure_point(self, point: str) -> None:
        if point not in self.successors:
            self.successors[point] = []

    def _ensure_origin(self, name: str) -> Origin:
        if name not in self.origins:
            self.origins[name] = Origin(name, kind="local")
        return self.origins[name]

    def add_edge(self, src: str, dst: str) -> None:
        """Register a directed CFG edge ``src -> dst``."""
        self._ensure_point(src)
        self._ensure_point(dst)
        if dst not in self.successors[src]:
            self.successors[src].append(dst)

    def add_origin(self, origin: Origin) -> None:
        """Declare or update an origin."""
        self.origins[origin.name] = origin

    def add_outlives(self, constraint: OutlivesConstraint) -> None:
        """Add a point-specific ``sup: sub`` constraint (loans in ``sup`` flow to ``sub``)."""
        self.add_subset(SubsetEdge(constraint.point, constraint.sup, constraint.sub))

    def add_subset(self, edge: SubsetEdge) -> None:
        """Add a directed subset edge ``from_origin <= to_origin`` at ``point``."""
        self._ensure_point(edge.point)
        self._ensure_origin(edge.from_origin)
        self._ensure_origin(edge.to_origin)
        self.subset_edges.append(edge)

    def add_variance(self, variance: Variance, lhs: str, rhs: str, point: str) -> None:
        """Add subset constraints matching ``variance`` for ``T<lhs> <: T<rhs>``."""
        for constraint in variance_outlives(variance, lhs, rhs, point):
            self.add_outlives(constraint)

    def add_origin_loan(self, origin_loan: OriginLoan) -> None:
        """Record that ``origin`` receives ``loan`` at ``point``."""
        self._ensure_point(origin_loan.point)
        self._ensure_origin(origin_loan.origin)
        self.origin_loans.append(origin_loan)

    def add_origin_use(self, point: str, origin: str) -> None:
        """Record a live use of ``origin`` at ``point``."""
        self._ensure_point(point)
        self._ensure_origin(origin)
        self.origin_uses.setdefault(point, set()).add(origin)

    def add_invalidation(self, point: str, loan: str) -> None:
        """Record that ``point`` accesses storage in a way that invalidates ``loan`` if live."""
        self._ensure_point(point)
        self.invalidations.setdefault(point, set()).add(loan)

    def add_kill(self, point: str, loan: str) -> None:
        """Record that ``loan`` is killed/ended on exit of ``point``."""
        self._ensure_point(point)
        self.kills.setdefault(point, set()).add(loan)

    def add_declared_outlives(self, sup: str, sub: str) -> None:
        """Declare a caller-guaranteed parameter outlives bound ``sup: sub``."""
        self._ensure_origin(sup)
        self._ensure_origin(sub)
        self.declared_outlives.add((sup, sub))

    def _collect_points(self) -> list[str]:
        points: list[str] = []
        seen: set[str] = set()

        def add(pt: str) -> None:
            if pt not in seen:
                seen.add(pt)
                points.append(pt)

        if self.entry in self.successors or not self.successors:
            add(self.entry)
        for pt, succs in self.successors.items():
            add(pt)
            for succ in succs:
                add(succ)
        for edge in self.subset_edges:
            add(edge.point)
        for ol in self.origin_loans:
            add(ol.point)
        for pt in self.origin_uses:
            add(pt)
        for pt in self.invalidations:
            add(pt)
        for pt in self.kills:
            add(pt)
        return points

    def _closure_declared_outlives(self) -> set[tuple[str, str]]:
        closure = set(self.declared_outlives)
        for name in self.origins:
            closure.add((name, name))
        changed = True
        while changed:
            changed = False
            for a, b in list(closure):
                for c, d in list(closure):
                    if b == c and (a, d) not in closure:
                        closure.add((a, d))
                        changed = True
        return closure

    @staticmethod
    def _find_origin_chain(
        start: str,
        target: str,
        edges: set[tuple[str, str]],
    ) -> tuple[str, ...]:
        if start == target:
            return (start,)
        adj: dict[str, list[str]] = {}
        for u, v in sorted(edges):
            if u != v:
                adj.setdefault(u, []).append(v)
        queue: deque[tuple[str, tuple[str, ...]]] = deque([(start, (start,))])
        visited = {start}
        while queue:
            curr, path = queue.popleft()
            for nxt in adj.get(curr, ()):
                if nxt == target:
                    return (*path, nxt)
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append((nxt, (*path, nxt)))
        return (start, target)

    def solve(self) -> RegionSolution:
        """Run backward origin liveness and forward subset/loan fixed-point propagation."""
        points = self._collect_points()
        succs: dict[str, list[str]] = {pt: list(self.successors.get(pt, ())) for pt in points}
        param_origins = {name for name, orig in self.origins.items() if orig.kind == "param"}
        exit_points = {pt for pt in points if not succs[pt]}

        base_subsets_at: dict[str, set[tuple[str, str]]] = {pt: set() for pt in points}
        for edge in self.subset_edges:
            base_subsets_at[edge.point].add((edge.from_origin, edge.to_origin))
        for sup, sub in self.declared_outlives:
            for pt in points:
                base_subsets_at[pt].add((sup, sub))

        defined_local_at: dict[str, set[str]] = {pt: set() for pt in points}
        issued_at: dict[str, dict[str, set[str]]] = {pt: {} for pt in points}
        loan_origin_points: dict[tuple[str, str], str] = {}
        loan_fallback_origin_point: dict[str, str] = {}
        for ol in self.origin_loans:
            issued_at[ol.point].setdefault(ol.origin, set()).add(ol.loan)
            loan_origin_points.setdefault((ol.origin, ol.loan), ol.point)
            loan_fallback_origin_point.setdefault(ol.loan, ol.point)
            orig = self._ensure_origin(ol.origin)
            if orig.kind == "local" and ol.origin not in self.origin_uses.get(ol.point, set()):
                defined_local_at[ol.point].add(ol.origin)

        # 1. Backward origin liveness.
        live_in: dict[str, set[str]] = {pt: set() for pt in points}
        live_out: dict[str, set[str]] = {
            pt: (set(param_origins) if pt in exit_points else set()) for pt in points
        }
        changed = True
        while changed:
            changed = False
            for pt in reversed(points):
                out_set = set(param_origins) if pt in exit_points else set()
                for succ in succs[pt]:
                    out_set.update(live_in[succ])
                needed = set(self.origin_uses.get(pt, ())) | out_set
                inner_changed = True
                while inner_changed:
                    inner_changed = False
                    for src_o, dst_o in base_subsets_at[pt]:
                        if dst_o in needed and src_o not in needed:
                            needed.add(src_o)
                            inner_changed = True
                in_set = needed - defined_local_at[pt]
                if out_set != live_out[pt] or in_set != live_in[pt]:
                    live_out[pt] = out_set
                    live_in[pt] = in_set
                    changed = True

        # 2. Forward location-sensitive subset propagation.
        subset_at: dict[str, set[tuple[str, str]]] = {
            pt: set(base_subsets_at[pt]) for pt in points
        }
        changed = True
        while changed:
            changed = False
            for pt in points:
                rel = subset_at[pt]
                # Transitive closure at point `pt`.
                trans_changed = True
                while trans_changed:
                    trans_changed = False
                    snapshot = list(rel)
                    by_src: dict[str, list[str]] = {}
                    for a, b in snapshot:
                        by_src.setdefault(a, []).append(b)
                    for a, b in snapshot:
                        for c in by_src.get(b, ()):
                            if a != c and (a, c) not in rel:
                                rel.add((a, c))
                                trans_changed = True
                                changed = True
                # Propagate subset edges to successors where both origins remain live.
                for succ in succs[pt]:
                    succ_live = live_in[succ] | self.origin_uses.get(succ, set())
                    succ_rel = subset_at[succ]
                    for a, b in rel:
                        if a in succ_live and b in succ_live and (a, b) not in succ_rel:
                            succ_rel.add((a, b))
                            changed = True

        # 3. Location-sensitive origin_contains_loan_at propagation.
        origin_loans_at: dict[str, dict[str, set[str]]] = {pt: {} for pt in points}
        for pt in points:
            for orig_name, loans in issued_at[pt].items():
                origin_loans_at[pt].setdefault(orig_name, set()).update(loans)

        changed = True
        while changed:
            changed = False
            for pt in points:
                pt_map = origin_loans_at[pt]
                pt_kills = self.kills.get(pt, set())
                # Propagate along subset edges at `pt`.
                for src_o, dst_o in subset_at[pt]:
                    src_loans = pt_map.get(src_o)
                    if not src_loans:
                        continue
                    dst_loans = pt_map.setdefault(dst_o, set())
                    before_len = len(dst_loans)
                    dst_loans.update(src_loans)
                    if len(dst_loans) != before_len:
                        changed = True
                # Propagate along CFG edges to successors where `orig` is live on entry.
                for succ in succs[pt]:
                    succ_live = live_in[succ] | self.origin_uses.get(succ, set())
                    succ_map = origin_loans_at[succ]
                    for orig_name, loans in pt_map.items():
                        if orig_name not in succ_live:
                            continue
                        surviving = loans - pt_kills
                        if not surviving:
                            continue
                        dest_loans = succ_map.setdefault(orig_name, set())
                        before_len = len(dest_loans)
                        dest_loans.update(surviving)
                        if len(dest_loans) != before_len:
                            changed = True

        live_origins_at: dict[str, frozenset[str]] = {
            pt: frozenset(live_in[pt] | self.origin_uses.get(pt, set())) for pt in points
        }
        live_loans_at: dict[str, frozenset[str]] = {}
        for pt in points:
            loans_here: set[str] = set()
            for orig_name in live_origins_at[pt]:
                loans_here.update(origin_loans_at[pt].get(orig_name, ()))
            live_loans_at[pt] = frozenset(loans_here)

        # Helper to find nearest downstream use point of any origin reachable from `orig`.
        def find_live_use_point(conflict_pt: str, start_origin: str) -> str:
            reachable_origins = {start_origin} | {
                dst for src, dst in subset_at[conflict_pt] if src == start_origin
            }
            if reachable_origins & self.origin_uses.get(conflict_pt, set()):
                return conflict_pt
            queue: deque[str] = deque(succs[conflict_pt])
            visited = {conflict_pt}
            while queue:
                curr = queue.popleft()
                if curr in visited:
                    continue
                visited.add(curr)
                curr_reachable = set(reachable_origins)
                for src, dst in subset_at[curr]:
                    if src in curr_reachable:
                        curr_reachable.add(dst)
                if curr_reachable & self.origin_uses.get(curr, set()):
                    return curr
                if curr in exit_points and (curr_reachable & param_origins):
                    return curr
                queue.extend(succs[curr])
            return conflict_pt

        # 3b. Cross-node universal origin (hrtb/param) flow propagation along live origins.
        universal_flow: dict[str, dict[str, dict[str, tuple[str, ...]]]] = {
            pt: {} for pt in points
        }
        universal_origins = {
            name for name, orig in self.origins.items() if orig.kind in {"hrtb", "param"}
        }
        for pt in points:
            for u in universal_origins:
                universal_flow[pt].setdefault(u, {})[u] = (u,)
        changed = True
        while changed:
            changed = False
            for pt in points:
                flow_pt = universal_flow[pt]
                for src_o, dst_o in sorted(subset_at[pt]):
                    src_map = flow_pt.get(src_o)
                    if not src_map:
                        continue
                    dst_map = flow_pt.setdefault(dst_o, {})
                    for u, chain in src_map.items():
                        if u not in dst_map and dst_o not in chain:
                            dst_map[u] = (*chain, dst_o)
                            changed = True
                for succ in succs[pt]:
                    succ_live = live_in[succ] | self.origin_uses.get(succ, set())
                    flow_succ = universal_flow[succ]
                    for orig_name, u_map in flow_pt.items():
                        if orig_name not in succ_live:
                            continue
                        succ_map = flow_succ.setdefault(orig_name, {})
                        for u, chain in u_map.items():
                            if u not in succ_map:
                                succ_map[u] = chain
                                changed = True

        # 4. Collect diagnostics with 3-span witnesses.
        diagnostics: list[RegionDiagnostic] = []
        seen_diags: set[tuple[str, str, str, str, tuple[str, ...]]] = set()
        declared_closure = self._closure_declared_outlives()

        # 4a. Loan invalidation conflicts.
        for pt in points:
            inv_loans = self.invalidations.get(pt, set())
            if not inv_loans:
                continue
            for loan in sorted(inv_loans & live_loans_at[pt]):
                # Prefer direct live origin holding `loan`, otherwise via subset chain.
                holding = sorted(
                    orig_name
                    for orig_name in live_origins_at[pt]
                    if loan in origin_loans_at[pt].get(orig_name, ())
                )
                chosen_use_orig = holding[0] if holding else ""
                # Find an origin where `loan` was originally issued that flows to `chosen_use_orig`.
                source_candidates = sorted(
                    orig_name
                    for (orig_name, l_name) in loan_origin_points
                    if l_name == loan
                )
                chosen_src = source_candidates[0] if source_candidates else chosen_use_orig
                for src_o in source_candidates:
                    if src_o == chosen_use_orig or (src_o, chosen_use_orig) in subset_at[pt]:
                        chosen_src = src_o
                        break
                origin_pt = loan_origin_points.get(
                    (chosen_src, loan), loan_fallback_origin_point.get(loan, pt)
                )
                chain = (
                    self._find_origin_chain(chosen_src, chosen_use_orig, subset_at[pt])
                    if chosen_src and chosen_use_orig
                    else (chosen_use_orig,)
                    if chosen_use_orig
                    else ()
                )
                live_use_pt = find_live_use_point(pt, chosen_use_orig) if chosen_use_orig else pt
                witness = RegionWitness(
                    origin_point=origin_pt,
                    conflict_point=pt,
                    live_use_point=live_use_pt,
                    origin_chain=chain,
                )
                key = ("loan-conflict", loan, origin_pt, pt, chain)
                if key not in seen_diags:
                    seen_diags.add(key)
                    diagnostics.append(
                        RegionDiagnostic(
                            kind="loan-conflict",
                            witness=witness,
                            loan=loan,
                            origin=chosen_use_orig or None,
                            detail=f"loan '{loan}' invalidated while live",
                        )
                    )

        # 4b. HRTB 'fresh non-escape & undeclared param outlives checks.
        for pt in points:
            for dst_o, u_map in sorted(universal_flow[pt].items()):
                dst_kind = self.origins[dst_o].kind
                for src_o, chain in sorted(u_map.items()):
                    if src_o == dst_o:
                        continue
                    src_kind = self.origins[src_o].kind
                    if src_kind == "hrtb" and dst_kind == "param":
                        live_use_pt = find_live_use_point(pt, dst_o)
                        witness = RegionWitness(
                            origin_point=pt,
                            conflict_point=pt,
                            live_use_point=live_use_pt,
                            origin_chain=chain,
                        )
                        key = ("hrtb-escape", src_o, pt, pt, chain)
                        if key not in seen_diags:
                            seen_diags.add(key)
                            diagnostics.append(
                                RegionDiagnostic(
                                    kind="hrtb-escape",
                                    witness=witness,
                                    origin=src_o,
                                    detail=f"higher-ranked origin '{src_o}' escaped into '{dst_o}'",
                                )
                            )
                    elif (
                        src_kind == "param"
                        and dst_kind == "param"
                        and (src_o, dst_o) not in declared_closure
                    ):
                        live_use_pt = find_live_use_point(pt, dst_o)
                        witness = RegionWitness(
                            origin_point=pt,
                            conflict_point=pt,
                            live_use_point=live_use_pt,
                            origin_chain=chain,
                        )
                        key = ("outlives-error", src_o, pt, pt, chain)
                        if key not in seen_diags:
                            seen_diags.add(key)
                            diagnostics.append(
                                RegionDiagnostic(
                                    kind="outlives-error",
                                    witness=witness,
                                    origin=src_o,
                                    detail=f"undeclared outlives '{src_o}' : '{dst_o}'",
                                )
                            )

            # Check explicit HRTB scope boundaries when provided.
            for orig_name in sorted(live_origins_at[pt]):
                orig = self.origins[orig_name]
                if orig.kind == "hrtb" and orig.scope is not None and pt not in orig.scope:
                    witness = RegionWitness(
                        origin_point=pt,
                        conflict_point=pt,
                        live_use_point=find_live_use_point(pt, orig_name),
                        origin_chain=(orig_name,),
                    )
                    key = ("hrtb-escape", orig_name, pt, pt, (orig_name,))
                    if key not in seen_diags:
                        seen_diags.add(key)
                        diagnostics.append(
                            RegionDiagnostic(
                                kind="hrtb-escape",
                                witness=witness,
                                origin=orig_name,
                                detail=f"higher-ranked origin '{orig_name}' live outside its scope",
                            )
                        )

        frozen_origin_loans = {
            pt: {orig: frozenset(loans) for orig, loans in omap.items()}
            for pt, omap in origin_loans_at.items()
        }
        frozen_subsets = {pt: frozenset(pairs) for pt, pairs in subset_at.items()}
        return RegionSolution(
            origin_loans_map=frozen_origin_loans,
            live_origins_map=live_origins_at,
            live_loans_map=live_loans_at,
            subset_map=frozen_subsets,
            diagnostics=tuple(diagnostics),
        )
