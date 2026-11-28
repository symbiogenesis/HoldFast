# SPDX-License-Identifier: Apache-2.0
"""Proof-producing congruence closure and arithmetic certificate builders.

Implements three untrusted, bounded proof-skeleton engines that reconstruct
axiom-free Gallina terms for independent checking by the Rocq 9.3.0 kernel:

- ``VersionedEGraph``: branch-scoped congruence closure with trail-backed
  ``push_version`` / ``pop_version`` isolation and shortest-path proof
  reconstruction using ``Refl``, ``Symm``, ``Trans``, and ``Congr``.
- ``NatDifferenceProver``: weighted difference-logic prover over Peano ``nat``
  comparisons and guarded offsets, including unreachable-branch contradictions.
- ``FixedIntOrderProver``: order and contradiction prover over signed and
  unsigned fixed-width machine integers (``u8``..``i64``, ``usize``).
"""

from collections import defaultdict, deque
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from toolchain.ast import HoldFastError
from toolchain.elaborate_types import (
    _BOOL,
    _INT_SPECS,
    _NAT,
    _SORT,
    _app,
    _apps,
    _Binding,
    _constant,
    _int_term,
    _IntSpec,
    _Term,
    _term,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator

MAX_EGRAPH_NODES = 1024
MAX_EGRAPH_MERGES = 512
MAX_EXPLAIN_STEPS = 128
MAX_INT_ORDER_STEPS = 256
MAX_POLY_VARS = 32
MAX_POLY_TERMS = 64
MAX_POLY_DEGREE = 8
MAX_POLY_DEPTH = 32
MAX_POLY_CONST = 256
MAX_AC_LEAVES = 8
MAX_PRECHECKER_STEPS = 128
MAX_PRECHECKER_ATOMS = 5


@dataclass(frozen=True)
class _ProofEdge:
    dst: int
    eq_type: _Term | None
    proof: _Term | None
    reverse: bool = False


class VersionedEGraph:
    """Trail-backed versioned e-graph for branch-scoped proof reconstruction."""

    def __init__(self, elaborator: _Elaborator) -> None:
        self.elab = elaborator
        self.nodes: list[_Term] = []
        self.term_to_id: dict[_Term, int] = {}
        self.parent: list[int] = []
        self.classes: dict[int, list[int]] = {}
        self.parents_of_class: dict[int, list[int]] = {}
        self.sig_table: dict[tuple[object, ...], int] = {}
        self.adj: dict[int, list[_ProofEdge]] = defaultdict(list)
        self.merge_count = 0

        self._undo_trail: list[tuple[object, ...]] = []
        self._versions: list[tuple[int, int, int]] = []

    def push_version(self) -> int:
        """Start a nested e-graph scope whose merges and nodes roll back on pop."""
        self._versions.append((len(self.nodes), len(self._undo_trail), self.merge_count))
        return len(self._versions)

    def pop_version(self) -> None:
        """Roll back every node, union, signature entry, and proof edge in the top version."""
        if not self._versions:
            raise ValueError("cannot pop from empty VersionedEGraph version stack")
        n_nodes, n_undo, old_merges = self._versions.pop()
        self.merge_count = old_merges
        while len(self._undo_trail) > n_undo:
            entry = self._undo_trail.pop()
            kind = entry[0]
            if kind == "adj":
                _, u, v = cast("tuple[str, int, int]", entry)
                self.adj[u].pop()
                self.adj[v].pop()
            elif kind == "sig":
                _, key, old_val = cast("tuple[str, tuple[object, ...], int | None]", entry)
                if old_val is None:
                    self.sig_table.pop(key, None)
                else:
                    self.sig_table[key] = old_val
            elif kind == "pnode":
                _, cls_root = cast("tuple[str, int]", entry)
                self.parents_of_class[cls_root].pop()
            elif kind == "pclass":
                _, kept, merged, old_list = cast("tuple[str, int, int, list[int]]", entry)
                if old_list:
                    del self.parents_of_class[kept][-len(old_list) :]
                self.parents_of_class[merged] = old_list
            elif kind == "class":
                _, kept, merged, old_list = cast("tuple[str, int, int, list[int]]", entry)
                if old_list:
                    del self.classes[kept][-len(old_list) :]
                self.classes[merged] = old_list
            elif kind == "parent":
                _, idx, old_p = cast("tuple[str, int, int]", entry)
                self.parent[idx] = old_p
        while len(self.nodes) > n_nodes:
            nid = len(self.nodes) - 1
            term = self.nodes.pop()
            self.term_to_id.pop(term, None)
            self.parent.pop()
            self.classes.pop(nid, None)
            self.parents_of_class.pop(nid, None)
            self.adj.pop(nid, None)

    def find(self, nid: int) -> int:
        p = self.parent[nid]
        return nid if p == nid else self.find(p)

    def _decompose_slotted(
        self, term: _Term,
    ) -> tuple[object, tuple[_Term, ...], Callable[[Sequence[_Term]], _Term]] | None:
        """Decompose ``lam``/``pi``/``let`` into an alpha-canonical slotted template and bound-free holes."""
        if term.kind not in {"lam", "pi", "let"}:
            return None
        holes: list[_Term] = []

        def const_rebuilder(node: _Term) -> Callable[[Sequence[_Term]], _Term]:
            return lambda _hs: node

        def hole_rebuilder(idx: int) -> Callable[[Sequence[_Term]], _Term]:
            return lambda hs: hs[idx]

        def walk(
            cur: _Term, bound: dict[int, int], *, allow_hole: bool,
        ) -> tuple[object, Callable[[Sequence[_Term]], _Term]] | None:
            cur = self.elab.resolve(cur)
            if cur.kind in {"meta", "fix"}:
                return None
            if cur.kind == "var":
                vid = cast("int", cur.value)
                if vid in bound:
                    return ("$slot", bound[vid]), const_rebuilder(cur)
                if allow_hole and bound:
                    idx = len(holes)
                    holes.append(cur)
                    return ("$hole", idx), hole_rebuilder(idx)
                return ("var", vid), const_rebuilder(cur)
            if allow_hole and bound and cur.kind not in {"sort", "pi"} and not (self.elab.free(cur) & bound.keys()):
                idx = len(holes)
                holes.append(cur)
                return ("$hole", idx), hole_rebuilder(idx)
            if cur.kind in {"lam", "pi"}:
                vid = cast("int", cur.value)
                dom = walk(cur.args[0], bound, allow_hole=False)
                if dom is None:
                    return None
                inner_bound = {**bound, vid: len(bound)}
                body = walk(cur.args[1], inner_bound, allow_hole=(cur.kind == "lam"))
                if body is None:
                    return None
                dom_k, dom_r = dom
                body_k, body_r = body
                kind = cur.kind

                def rebuild_binder(
                    hs: Sequence[_Term],
                    *,
                    _k: str = kind,
                    _v: int = vid,
                    _dr: Callable[[Sequence[_Term]], _Term] = dom_r,
                    _br: Callable[[Sequence[_Term]], _Term] = body_r,
                ) -> _Term:
                    return _term(_k, _dr(hs), _br(hs), value=_v)

                return ("binder", kind, dom_k, body_k), rebuild_binder
            if cur.kind == "let":
                vid = cast("int", cur.value)
                dom = walk(cur.args[0], bound, allow_hole=False)
                val = walk(cur.args[1], bound, allow_hole=bool(bound))
                inner_bound = {**bound, vid: len(bound)}
                body = walk(cur.args[2], inner_bound, allow_hole=True)
                if dom is None or val is None or body is None:
                    return None
                dom_k, dom_r = dom
                val_k, val_r = val
                body_k, body_r = body

                def rebuild_let(
                    hs: Sequence[_Term],
                    *,
                    _v: int = vid,
                    _dr: Callable[[Sequence[_Term]], _Term] = dom_r,
                    _vr: Callable[[Sequence[_Term]], _Term] = val_r,
                    _br: Callable[[Sequence[_Term]], _Term] = body_r,
                ) -> _Term:
                    return _term("let", _dr(hs), _vr(hs), _br(hs), value=_v)

                return ("binder", "let", dom_k, val_k, body_k), rebuild_let
            if cur.kind == "app":
                head, args = self.elab.spine(cur)
                head_res = walk(head, bound, allow_hole=False)
                if head_res is None:
                    return None
                arg_res = [walk(arg, bound, allow_hole=bool(bound)) for arg in args]
                if any(item is None for item in arg_res):
                    return None
                head_k, head_r = head_res
                resolved_args = [cast("tuple[object, Callable[[Sequence[_Term]], _Term]]", a) for a in arg_res]
                arg_keys = tuple(ak for ak, _ in resolved_args)
                arg_rs = tuple(ar for _, ar in resolved_args)

                def rebuild_app(
                    hs: Sequence[_Term],
                    *,
                    _hr: Callable[[Sequence[_Term]], _Term] = head_r,
                    _ars: tuple[Callable[[Sequence[_Term]], _Term], ...] = arg_rs,
                ) -> _Term:
                    return _apps(_hr(hs), *(ar(hs) for ar in _ars))

                return ("app", head_k, arg_keys), rebuild_app
            if not cur.args:
                return ("leaf", cur.kind, cur.value), const_rebuilder(cur)
            child_res = [walk(arg, bound, allow_hole=bool(bound)) for arg in cur.args]
            if any(item is None for item in child_res):
                return None
            resolved_children = [cast("tuple[object, Callable[[Sequence[_Term]], _Term]]", c) for c in child_res]
            child_keys = tuple(ck for ck, _ in resolved_children)
            child_rs = tuple(cr for _, cr in resolved_children)
            kind = cur.kind
            val = cur.value

            def rebuild_node(
                hs: Sequence[_Term],
                *,
                _k: str = kind,
                _v: str | int = val,
                _crs: tuple[Callable[[Sequence[_Term]], _Term], ...] = child_rs,
            ) -> _Term:
                return _Term(_k, _v, tuple(cr(hs) for cr in _crs))

            return ("node", kind, val, child_keys), rebuild_node

        walked = walk(term, {}, allow_hole=False)
        if walked is None:
            return None
        template_key, rebuild_fn = walked
        return ("slotted", template_key), tuple(holes), rebuild_fn

    def _decompose(self, term: _Term) -> tuple[object, tuple[_Term, ...]] | None:
        if term.kind == "app":
            head, args = self.elab.spine(term)
            if args and head.kind not in {"pi", "lam", "let", "fix", "meta"}:
                return ("app", head), tuple(args)
            return None
        if term.kind in {"lam", "pi", "let"}:
            slotted = self._decompose_slotted(term)
            if slotted is not None:
                return slotted[0], slotted[1]
            return None
        if term.kind not in {"fix", "meta"} and term.args:
            return (term.kind, term.value), term.args
        return None

    def _set_sig(self, key: tuple[object, ...], nid: int) -> None:
        old = self.sig_table.get(key)
        if old == nid:
            return
        self._undo_trail.append(("sig", key, old))
        self.sig_table[key] = nid

    def _add_edge(
        self, u: int, v: int, eq_type: _Term | None, proof: _Term | None,
    ) -> None:
        self.adj[u].append(_ProofEdge(v, eq_type, proof, False))
        self.adj[v].append(_ProofEdge(u, eq_type, proof, True))
        self._undo_trail.append(("adj", u, v))

    def intern(self, term: _Term) -> int | None:
        """Intern ``term`` (and first-order subterms), discovering congruences."""
        resolved = self.elab.resolve(term)
        if resolved in self.term_to_id:
            return self.term_to_id[resolved]
        if len(self.nodes) >= MAX_EGRAPH_NODES:
            return None

        decomp = self._decompose(resolved)
        child_ids: list[int] = []
        if decomp is not None:
            op_key, children = decomp
            if isinstance(op_key, tuple) and op_key[0] == "app":
                head_term = cast("_Term", op_key[1])
                if self.intern(head_term) is None:
                    return None
            for child in children:
                cid = self.intern(child)
                if cid is None:
                    return None
                child_ids.append(cid)
        if resolved in self.term_to_id:
            return self.term_to_id[resolved]
        if len(self.nodes) >= MAX_EGRAPH_NODES:
            return None

        nid = len(self.nodes)
        self.nodes.append(resolved)
        self.term_to_id[resolved] = nid
        self.parent.append(nid)
        self.classes[nid] = [nid]
        self.parents_of_class[nid] = []

        if decomp is not None:
            op_key, _ = decomp
            seen_roots: set[int] = set()
            canon_children: list[int] = []
            for cid in child_ids:
                croot = self.find(cid)
                canon_children.append(croot)
                if croot not in seen_roots:
                    seen_roots.add(croot)
                    self.parents_of_class[croot].append(nid)
                    self._undo_trail.append(("pnode", croot))
            sig_key = (op_key, tuple(canon_children))
            existing = self.sig_table.get(sig_key)
            if existing is not None:
                self._merge_worklist([(nid, existing, None, None)])
            else:
                self._set_sig(sig_key, nid)
        return nid

    def assert_equality(self, eq_type: _Term, lhs: _Term, rhs: _Term, proof: _Term) -> bool:
        """Record ``proof : Eq eq_type lhs rhs`` and close under congruence."""
        lid = self.intern(lhs)
        rid = self.intern(rhs)
        if lid is None or rid is None:
            return False
        if self.find(lid) == self.find(rid):
            return True
        return self._merge_worklist([(lid, rid, eq_type, proof)])

    def _merge_worklist(
        self, initial: list[tuple[int, int, _Term | None, _Term | None]],
    ) -> bool:
        pending = deque(initial)
        while pending:
            u, v, eq_type, proof = pending.popleft()
            ru = self.find(u)
            rv = self.find(v)
            if ru == rv:
                continue
            if self.merge_count >= MAX_EGRAPH_MERGES:
                return False
            self.merge_count += 1
            self._add_edge(u, v, eq_type, proof)
            if len(self.classes[ru]) < len(self.classes[rv]):
                ru, rv = rv, ru
            self._undo_trail.append(("parent", rv, self.parent[rv]))
            self.parent[rv] = ru
            merged_members = self.classes.pop(rv)
            self.classes[ru].extend(merged_members)
            self._undo_trail.append(("class", ru, rv, merged_members))

            merged_parents = self.parents_of_class.pop(rv, [])
            self.parents_of_class[ru].extend(merged_parents)
            self._undo_trail.append(("pclass", ru, rv, merged_parents))

            for pnode in merged_parents:
                decomp = self._decompose(self.nodes[pnode])
                if decomp is None:
                    continue
                op_key, children = decomp
                sig_key = (op_key, tuple(self.find(self.term_to_id[self.elab.resolve(c)]) for c in children))
                existing = self.sig_table.get(sig_key)
                if existing is not None and self.find(existing) != self.find(pnode):
                    pending.append((pnode, existing, None, None))
                else:
                    self._set_sig(sig_key, pnode)
        return True

    def equivalent(self, lhs: _Term, rhs: _Term) -> bool:
        """Return whether ``lhs`` and ``rhs`` sit in the same e-class."""
        self.push_version()
        try:
            lid = self.intern(lhs)
            rid = self.intern(rhs)
            return lid is not None and rid is not None and self.find(lid) == self.find(rid)
        finally:
            self.pop_version()

    def explain(self, goal_type: _Term, lhs: _Term, rhs: _Term) -> _Term | None:
        """Synthesize an axiom-free Gallina proof of ``Eq goal_type lhs rhs`` if equivalent."""
        self.push_version()
        try:
            return self._explain_pair(goal_type, lhs, rhs, set())
        finally:
            self.pop_version()

    @staticmethod
    def _uses_prelude_lemma(term: _Term) -> bool:
        stack = [term]
        while stack:
            cur = stack.pop()
            if cur.kind == "const" and isinstance(cur.value, str) and cur.value.startswith("holdfast_"):
                return True
            stack.extend(cur.args)
        return False

    def _explain_pair(
        self,
        goal_type: _Term,
        lhs: _Term,
        rhs: _Term,
        visited_pairs: set[tuple[int, int]],
    ) -> _Term | None:
        lhs_r = self.elab.resolve(lhs)
        rhs_r = self.elab.resolve(rhs)
        if lhs_r == rhs_r:
            return _apps(_constant("Refl"), goal_type, lhs_r)
        lid = self.intern(lhs_r)
        rid = self.intern(rhs_r)
        if lid is None or rid is None or self.find(lid) != self.find(rid):
            return None
        pair_key = (min(lid, rid), max(lid, rid))
        if pair_key in visited_pairs:
            return None
        visited_pairs.add(pair_key)
        try:
            # BFS over the proof forest yields a minimal proof skeleton.
            queue = deque([lid])
            prev: dict[int, tuple[int, _ProofEdge] | None] = {lid: None}
            steps_budget = MAX_EXPLAIN_STEPS
            while queue and rid not in prev:
                cur = queue.popleft()
                for edge in self.adj[cur]:
                    steps_budget -= 1
                    if steps_budget < 0:
                        return None
                    if edge.dst not in prev:
                        prev[edge.dst] = (cur, edge)
                        queue.append(edge.dst)
                        if edge.dst == rid:
                            break
            if rid not in prev:
                return None
            path: list[tuple[int, _ProofEdge]] = []
            cursor = rid
            while cursor != lid:
                entry = prev[cursor]
                if entry is None:
                    return None
                parent_id, edge = entry
                path.append((parent_id, edge))
                cursor = parent_id
            path.reverse()

            step_terms: list[tuple[_Term, _Term, _Term]] = []
            for src_id, edge in path:
                u_node = self.nodes[src_id]
                v_node = self.nodes[edge.dst]
                if edge.proof is not None and edge.eq_type is not None:
                    saved = self.elab.snapshot_metas()
                    if not self.elab._try_unify(edge.eq_type, goal_type):
                        self.elab.restore_metas(saved)
                        return None
                    step_p = (
                        _apps(_constant("Symm"), goal_type, v_node, u_node, edge.proof)
                        if edge.reverse
                        else edge.proof
                    )
                else:
                    step_p = self._explain_congruence(goal_type, u_node, v_node, visited_pairs)
                    if step_p is None:
                        return None
                step_terms.append((u_node, v_node, step_p))

            if not step_terms:
                return _apps(_constant("Refl"), goal_type, lhs_r)
            acc_u, acc_v, acc_p = step_terms[0]
            for _, next_v, next_p in step_terms[1:]:
                acc_p = _apps(_constant("Trans"), goal_type, acc_u, acc_v, next_v, acc_p, next_p)
                acc_v = next_v

            if not self._uses_prelude_lemma(acc_p):
                saved_chk = self.elab.snapshot_metas()
                try:
                    inferred = self.elab.infer(acc_p)
                    expected = _apps(_constant("Eq"), goal_type, lhs_r, rhs_r)
                    if not self.elab.convertible(inferred, expected):
                        self.elab.restore_metas(saved_chk)
                        return None
                except HoldFastError:
                    self.elab.restore_metas(saved_chk)
                    return None
            return acc_p
        finally:
            visited_pairs.discard(pair_key)

    def _synthesize_congruence_chain(
        self,
        goal_type: _Term,
        l_args: tuple[_Term, ...],
        r_args: tuple[_Term, ...],
        rebuild: Callable[[Sequence[_Term]], _Term],
        visited_pairs: set[tuple[int, int]],
    ) -> _Term | None:
        current_args = list(l_args)
        acc_start: _Term | None = None
        acc_curr: _Term | None = None
        acc_proof: _Term | None = None

        for idx, (a_i, b_i) in enumerate(zip(l_args, r_args, strict=True)):
            if a_i == b_i:
                continue
            saved = self.elab.snapshot_metas()
            try:
                arg_ty = self.elab.infer(a_i)
                arg_ty_b = self.elab.infer(b_i)
                if not self.elab.convertible(arg_ty, arg_ty_b):
                    self.elab.restore_metas(saved)
                    return None
                if not self.elab._try_unify(self.elab.infer(arg_ty), _SORT):
                    self.elab.restore_metas(saved)
                    return None
            except HoldFastError:
                self.elab.restore_metas(saved)
                return None

            sub_p = self._explain_pair(arg_ty, a_i, b_i, visited_pairs)
            if sub_p is None:
                self.elab.restore_metas(saved)
                return None

            z = self.elab.fresh(arg_ty)
            z_id = cast("int", z.value)
            ctx_args = [*current_args[:idx], z, *current_args[idx + 1 :]]
            ctx_term = rebuild(ctx_args)
            try:
                ctx_ty = self.elab.infer(ctx_term)
                if z_id in self.elab.free(ctx_ty):
                    self.elab.restore_metas(saved)
                    return None
                if not self.elab._try_unify(self.elab.infer(ctx_ty), _SORT):
                    self.elab.restore_metas(saved)
                    return None
                if not self.elab._try_unify(ctx_ty, goal_type):
                    self.elab.restore_metas(saved)
                    return None
            except HoldFastError:
                self.elab.restore_metas(saved)
                return None

            lam = _term("lam", arg_ty, ctx_term, value=z_id)
            step_p = _apps(_constant("Congr"), arg_ty, goal_type, a_i, b_i, lam, sub_p)
            before_term = rebuild(current_args)
            current_args[idx] = b_i
            after_term = rebuild(current_args)
            if acc_proof is None or acc_start is None or acc_curr is None:
                acc_start = before_term
                acc_curr = after_term
                acc_proof = step_p
            else:
                acc_proof = _apps(
                    _constant("Trans"), goal_type, acc_start, acc_curr, after_term, acc_proof, step_p,
                )
                acc_curr = after_term
        return acc_proof

    def _explain_congruence(
        self,
        goal_type: _Term,
        lhs: _Term,
        rhs: _Term,
        visited_pairs: set[tuple[int, int]],
    ) -> _Term | None:
        if lhs == rhs:
            return _apps(_constant("Refl"), goal_type, lhs)
        if lhs.kind in {"lam", "pi", "let"} and rhs.kind == lhs.kind:
            sl_l = self._decompose_slotted(lhs)
            sl_r = self._decompose_slotted(rhs)
            if sl_l is None or sl_r is None or sl_l[0] != sl_r[0] or len(sl_l[1]) != len(sl_r[1]):
                return None
            if sl_l[1] == sl_r[1]:
                return _apps(_constant("Refl"), goal_type, lhs) if self.elab.convertible(lhs, rhs) else None
            return self._synthesize_congruence_chain(goal_type, sl_l[1], sl_r[1], sl_l[2], visited_pairs)
        decomp_l = self._decompose(lhs)
        decomp_r = self._decompose(rhs)
        if decomp_l is None or decomp_r is None or decomp_l[0] != decomp_r[0]:
            return None
        op_key, l_args = decomp_l
        _, r_args = decomp_r
        if len(l_args) != len(r_args):
            return None

        is_app = isinstance(op_key, tuple) and op_key[0] == "app"
        head_term = cast("_Term", op_key[1]) if is_app else None

        def rebuild(args_seq: Sequence[_Term]) -> _Term:
            if is_app and head_term is not None:
                return _apps(head_term, *args_seq)
            return _Term(lhs.kind, lhs.value, tuple(args_seq))

        return self._synthesize_congruence_chain(goal_type, l_args, r_args, rebuild, visited_pairs)

    def saturate_equalizer(self, max_rounds: int = 4) -> None:
        """Apply bounded Mizar-style algebraic properties, reductions, and Nat polynomial merges."""
        truth = _term("bool", value=1)
        false_t = _term("bool", value=0)
        refl_true = _apps(_constant("Refl"), _BOOL, truth)
        comm_specs: dict[str, tuple[_Term, str, _IntSpec | None]] = {
            "&&": (_BOOL, "holdfast_and_comm", None),
            "||": (_BOOL, "holdfast_or_comm", None),
            "eq_bool": (_BOOL, "holdfast_eq_bool_comm", None),
            "<==>": (_BOOL, "holdfast_eq_bool_comm", None),
            "ne_bool": (_BOOL, "holdfast_ne_bool_comm", None),
            "eq_nat": (_BOOL, "holdfast_eq_nat_comm", None),
            "ne_nat": (_BOOL, "holdfast_ne_nat_comm", None),
        }
        ac_specs: dict[str, tuple[_IntSpec, str, str]] = {}
        for spec in _INT_SPECS.values():
            comm_specs[f"int_eq_{spec.name}"] = (_BOOL, "holdfast_int_eq_comm", spec)
            comm_specs[f"int_ne_{spec.name}"] = (_BOOL, "holdfast_int_ne_comm", spec)
            comm_specs[f"int_add_{spec.name}"] = (spec.const, "holdfast_int_add_comm", spec)
            comm_specs[f"int_and_{spec.name}"] = (spec.const, "holdfast_int_and_comm", spec)
            comm_specs[f"int_or_{spec.name}"] = (spec.const, "holdfast_int_or_comm", spec)
            comm_specs[f"int_xor_{spec.name}"] = (spec.const, "holdfast_int_xor_comm", spec)
            ac_specs[f"int_add_{spec.name}"] = (spec, "holdfast_int_add_comm", "holdfast_int_add_assoc")
            ac_specs[f"int_and_{spec.name}"] = (spec, "holdfast_int_and_comm", "holdfast_int_and_assoc")
            ac_specs[f"int_or_{spec.name}"] = (spec, "holdfast_int_or_comm", "holdfast_int_or_assoc")
            ac_specs[f"int_xor_{spec.name}"] = (spec, "holdfast_int_xor_comm", "holdfast_int_xor_assoc")

        poly_eq = NatPolyEqualizer(self.elab)

        for _ in range(max_rounds):
            before_merges = self.merge_count
            snapshot_count = len(self.nodes)
            comm_seen: dict[tuple[str, int, int], tuple[int, _Term, _Term, _Term]] = {}
            ac_buckets: dict[tuple[str, tuple[int, ...]], list[int]] = defaultdict(list)
            nat_candidates: list[int] = []

            for nid in range(snapshot_count):
                if self.merge_count >= MAX_EGRAPH_MERGES or len(self.nodes) >= MAX_EGRAPH_NODES:
                    break
                node = self.nodes[nid]
                if node.kind == "nat":
                    nat_candidates.append(nid)
                    continue
                head, args = self.elab.spine(node)
                if head.kind != "const" or not isinstance(head.value, str):
                    continue
                cname = head.value

                # 1. Involutiveness: !!b == b and ~~x == x
                if cname == "!" and len(args) == 1:
                    inner = self.elab.resolve(args[0])
                    ih, ia = self.elab.spine(inner)
                    if ih == _constant("!") and len(ia) == 1:
                        self.assert_equality(_BOOL, node, ia[0], _app(_constant("holdfast_not_involutive"), ia[0]))
                    continue
                if cname.startswith("int_not_") and len(args) == 1:
                    spec = _INT_SPECS.get(cname[len("int_not_") :])
                    if spec is not None:
                        inner = self.elab.resolve(args[0])
                        ih, ia = self.elab.spine(inner)
                        if ih == head and len(ia) == 1:
                            self.assert_equality(
                                spec.const,
                                node,
                                ia[0],
                                _apps(_constant("holdfast_int_not_involutive"), _term("nat", value=spec.tag), ia[0]),
                            )
                    continue

                if cname == "Seq_Take" and len(args) == 3:
                    inner = self.elab.resolve(args[1])
                    ih, ia = self.elab.spine(inner)
                    if ih == head and len(ia) == 3:
                        n1_id = self.term_to_id.get(self.elab.resolve(args[2]))
                        n2_id = self.term_to_id.get(self.elab.resolve(ia[2]))
                        if n1_id is not None and n2_id is not None and self.find(n1_id) == self.find(n2_id):
                            p_base = _apps(_constant("holdfast_Seq_take_idempotent"), ia[0], ia[2], ia[1])
                            if args[2] == ia[2]:
                                self.assert_equality(_apps(_constant("Seq"), args[0]), node, inner, p_base)
                            elif (pn := self.explain(_NAT, args[2], ia[2])) is not None:
                                seq_ty = _apps(_constant("Seq"), args[0])
                                z = self.elab.fresh(_NAT)
                                lam = _term("lam", _NAT, _apps(head, args[0], inner, z), value=cast("int", z.value))
                                p_step = _apps(_constant("Congr"), _NAT, seq_ty, args[2], ia[2], lam, pn)
                                self.assert_equality(
                                    seq_ty,
                                    node,
                                    inner,
                                    _apps(_constant("Trans"), seq_ty, node, _apps(head, args[0], inner, ia[2]), inner, p_step, p_base),
                                )
                    continue

                if cname == "Succ" and len(args) == 1:
                    nat_candidates.append(nid)
                    if (arg_id := self.term_to_id.get(self.elab.resolve(args[0]))) is not None:
                        nat_candidates.append(arg_id)
                    continue

                if len(args) != 2:
                    continue

                if cname in {"+", "*"}:
                    nat_candidates.append(nid)
                    nat_candidates.extend(
                        arg_id for arg in args
                        if (arg_id := self.term_to_id.get(self.elab.resolve(arg))) is not None
                    )
                elif cname in {"eq_nat", "ne_nat", "<", "<=", ">", ">="}:
                    nat_candidates.extend(
                        arg_id for arg in args
                        if (arg_id := self.term_to_id.get(self.elab.resolve(arg))) is not None
                    )

                a_res = self.elab.resolve(args[0])
                b_res = self.elab.resolve(args[1])
                aid = self.term_to_id.get(a_res)
                bid = self.term_to_id.get(b_res)
                if aid is None or bid is None:
                    continue
                ra = self.find(aid)
                rb = self.find(bid)

                # 2. Boolean reductions & idempotence
                if cname == "&&":
                    self._saturate_bool_and(node, a_res, b_res, ra, rb, truth, false_t)
                elif cname == "||":
                    self._saturate_bool_or(node, a_res, b_res, ra, rb, truth, false_t)

                # 3. Fixed-width integer reductions & idempotence
                if cname.startswith("int_"):
                    self._saturate_int_binary(node, head, cname, a_res, b_res, ra, rb, refl_true)

                # 4. Commutativity (zero speculative nodes: only merge when swapped partner exists)
                if (cspec := comm_specs.get(cname)) is not None:
                    eq_ty, comm_lemma, int_spec = cspec
                    canon_key = (cname, min(ra, rb), max(ra, rb))
                    prev = comm_seen.get(canon_key)
                    if prev is None:
                        comm_seen[canon_key] = (nid, head, a_res, b_res)
                    else:
                        prev_nid, _, pa_res, pb_res = prev
                        if self.find(prev_nid) != self.find(nid):
                            paid = self.find(self.term_to_id[pa_res])
                            pbid = self.find(self.term_to_id[pb_res])
                            if ra == pbid and rb == paid:
                                swapped = _apps(head, b_res, a_res)
                                comm_p = (
                                    _apps(_constant(comm_lemma), _term("nat", value=int_spec.tag), a_res, b_res)
                                    if int_spec is not None
                                    else _apps(_constant(comm_lemma), a_res, b_res)
                                )
                                self.assert_equality(eq_ty, node, swapped, comm_p)

                # 5. AC grouping for associative-commutative integer operators
                if cname in ac_specs:
                    leaves = self._flatten_ac(head, node)
                    if 3 <= len(leaves) <= MAX_AC_LEAVES:
                        leaf_roots: list[int] = []
                        ok = True
                        for leaf in leaves:
                            lid = self.term_to_id.get(self.elab.resolve(leaf))
                            if lid is None:
                                ok = False
                                break
                            leaf_roots.append(self.find(lid))
                        if ok:
                            ac_buckets[(cname, tuple(sorted(leaf_roots)))].append(nid)

            # Merge AC buckets that share the same sorted multiset of argument e-class roots
            for (cname, _), group in ac_buckets.items():
                if len(group) < 2 or self.merge_count >= MAX_EGRAPH_MERGES:
                    continue
                int_spec, comm_lemma, assoc_lemma = ac_specs[cname]
                rep_nid = group[0]
                rep_node = self.nodes[rep_nid]
                rep_canon, rep_proof = self._ac_canonicalize(
                    _constant(cname), int_spec, comm_lemma, assoc_lemma, rep_node,
                )
                if rep_proof is None:
                    continue
                for other_nid in group[1:]:
                    if self.find(other_nid) == self.find(rep_nid):
                        continue
                    other_node = self.nodes[other_nid]
                    other_canon, other_proof = self._ac_canonicalize(
                        _constant(cname), int_spec, comm_lemma, assoc_lemma, other_node,
                    )
                    if other_proof is None or rep_canon != other_canon:
                        continue
                    eq_p = _apps(
                        _constant("Trans"),
                        int_spec.const,
                        rep_node,
                        rep_canon,
                        other_node,
                        rep_proof,
                        _apps(_constant("Symm"), int_spec.const, other_node, other_canon, other_proof),
                    )
                    self.assert_equality(int_spec.const, rep_node, other_node, eq_p)

            # 6. Reflective Nat polynomial equivalence modulo e-graph classes
            if nat_candidates and self.merge_count < MAX_EGRAPH_MERGES:
                poly_buckets: dict[tuple[tuple[tuple[int, ...], int], ...], list[int]] = defaultdict(list)
                seen_nat: set[int] = set()
                for nid in nat_candidates:
                    if nid in seen_nat:
                        continue
                    seen_nat.add(nid)
                    sig = poly_eq.polynomial_key(self, self.nodes[nid])
                    if sig is not None:
                        poly_buckets[sig].append(nid)
                for group in poly_buckets.values():
                    if len(group) < 2 or self.merge_count >= MAX_EGRAPH_MERGES:
                        continue
                    rep_nid = group[0]
                    rep_node = self.nodes[rep_nid]
                    for other_nid in group[1:]:
                        if self.find(other_nid) == self.find(rep_nid):
                            continue
                        other_node = self.nodes[other_nid]
                        if (poly_p := poly_eq.prove_equal_mod_egraph(self, rep_node, other_node)) is not None:
                            self.assert_equality(_NAT, rep_node, other_node, poly_p)

            if self.merge_count == before_merges:
                break

    def _saturate_bool_and(
        self, node: _Term, a: _Term, b: _Term, ra: int, rb: int, truth: _Term, false_t: _Term,
    ) -> None:
        tid_true = self.term_to_id.get(truth)
        tid_false = self.term_to_id.get(false_t)
        r_true = self.find(tid_true) if tid_true is not None else -1
        r_false = self.find(tid_false) if tid_false is not None else -1
        if ra == rb:
            if a == b:
                self.assert_equality(_BOOL, node, a, _app(_constant("holdfast_and_idem"), a))
            elif (p_ab := self.explain(_BOOL, a, b)) is not None:
                z = self.elab.fresh(_BOOL)
                lam = _term("lam", _BOOL, _apps(_constant("&&"), a, z), value=cast("int", z.value))
                step = _apps(_constant("Congr"), _BOOL, _BOOL, a, b, lam, p_ab)
                p_idem = _app(_constant("holdfast_and_idem"), a)
                self.assert_equality(
                    _BOOL,
                    node,
                    a,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("&&"), a, a), a, _apps(_constant("Symm"), _BOOL, _apps(_constant("&&"), a, a), node, step), p_idem),
                )
        elif b == truth or rb == r_true:
            if b == truth:
                self.assert_equality(_BOOL, node, a, _app(_constant("holdfast_bool_and_true_r"), a))
            elif (p_bt := self.explain(_BOOL, b, truth)) is not None:
                z = self.elab.fresh(_BOOL)
                lam = _term("lam", _BOOL, _apps(_constant("&&"), a, z), value=cast("int", z.value))
                step = _apps(_constant("Congr"), _BOOL, _BOOL, b, truth, lam, p_bt)
                self.assert_equality(
                    _BOOL,
                    node,
                    a,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("&&"), a, truth), a, step, _app(_constant("holdfast_bool_and_true_r"), a)),
                )
        elif a == truth or ra == r_true:
            if a == truth:
                self.assert_equality(
                    _BOOL,
                    node,
                    b,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("&&"), b, truth), b, _apps(_constant("holdfast_and_comm"), a, b), _app(_constant("holdfast_bool_and_true_r"), b)),
                )
        elif b == false_t or rb == r_false:
            if b == false_t:
                self.assert_equality(_BOOL, node, false_t, _app(_constant("holdfast_bool_and_false_r"), a))
        elif a == false_t or ra == r_false:
            if a == false_t:
                self.assert_equality(
                    _BOOL,
                    node,
                    false_t,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("&&"), b, false_t), false_t, _apps(_constant("holdfast_and_comm"), a, b), _app(_constant("holdfast_bool_and_false_r"), b)),
                )
        else:
            bh, ba = self.elab.spine(b)
            if bh == _constant("!") and len(ba) == 1:
                neg_id = self.term_to_id.get(self.elab.resolve(ba[0]))
                if neg_id is not None and self.find(neg_id) == ra and a == ba[0]:
                    self.assert_equality(_BOOL, node, false_t, _app(_constant("holdfast_bool_and_not_r"), a))
            ah, aa = self.elab.spine(a)
            if ah == _constant("!") and len(aa) == 1:
                neg_id = self.term_to_id.get(self.elab.resolve(aa[0]))
                if neg_id is not None and self.find(neg_id) == rb and b == aa[0]:
                    self.assert_equality(
                        _BOOL,
                        node,
                        false_t,
                        _apps(_constant("Trans"), _BOOL, node, _apps(_constant("&&"), b, a), false_t, _apps(_constant("holdfast_and_comm"), a, b), _app(_constant("holdfast_bool_and_not_r"), b)),
                    )

    def _saturate_bool_or(
        self, node: _Term, a: _Term, b: _Term, ra: int, rb: int, truth: _Term, false_t: _Term,
    ) -> None:
        tid_true = self.term_to_id.get(truth)
        tid_false = self.term_to_id.get(false_t)
        r_true = self.find(tid_true) if tid_true is not None else -1
        r_false = self.find(tid_false) if tid_false is not None else -1
        if ra == rb:
            if a == b:
                self.assert_equality(_BOOL, node, a, _app(_constant("holdfast_or_idem"), a))
            elif (p_ab := self.explain(_BOOL, a, b)) is not None:
                z = self.elab.fresh(_BOOL)
                lam = _term("lam", _BOOL, _apps(_constant("||"), a, z), value=cast("int", z.value))
                step = _apps(_constant("Congr"), _BOOL, _BOOL, a, b, lam, p_ab)
                p_idem = _app(_constant("holdfast_or_idem"), a)
                self.assert_equality(
                    _BOOL,
                    node,
                    a,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("||"), a, a), a, _apps(_constant("Symm"), _BOOL, _apps(_constant("||"), a, a), node, step), p_idem),
                )
        elif b == false_t or rb == r_false:
            if b == false_t:
                self.assert_equality(_BOOL, node, a, _app(_constant("holdfast_bool_or_false_r"), a))
            elif (p_bf := self.explain(_BOOL, b, false_t)) is not None:
                z = self.elab.fresh(_BOOL)
                lam = _term("lam", _BOOL, _apps(_constant("||"), a, z), value=cast("int", z.value))
                step = _apps(_constant("Congr"), _BOOL, _BOOL, b, false_t, lam, p_bf)
                self.assert_equality(
                    _BOOL,
                    node,
                    a,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("||"), a, false_t), a, step, _app(_constant("holdfast_bool_or_false_r"), a)),
                )
        elif a == false_t or ra == r_false:
            if a == false_t:
                self.assert_equality(
                    _BOOL,
                    node,
                    b,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("||"), b, false_t), b, _apps(_constant("holdfast_or_comm"), a, b), _app(_constant("holdfast_bool_or_false_r"), b)),
                )
        elif b == truth or rb == r_true:
            if b == truth:
                self.assert_equality(_BOOL, node, truth, _app(_constant("holdfast_bool_or_true_r"), a))
        elif a == truth or ra == r_true:
            if a == truth:
                self.assert_equality(
                    _BOOL,
                    node,
                    truth,
                    _apps(_constant("Trans"), _BOOL, node, _apps(_constant("||"), b, truth), truth, _apps(_constant("holdfast_or_comm"), a, b), _app(_constant("holdfast_bool_or_true_r"), b)),
                )
        else:
            bh, ba = self.elab.spine(b)
            if bh == _constant("!") and len(ba) == 1:
                neg_id = self.term_to_id.get(self.elab.resolve(ba[0]))
                if neg_id is not None and self.find(neg_id) == ra and a == ba[0]:
                    self.assert_equality(_BOOL, node, truth, _app(_constant("holdfast_bool_or_not_r"), a))
            ah, aa = self.elab.spine(a)
            if ah == _constant("!") and len(aa) == 1:
                neg_id = self.term_to_id.get(self.elab.resolve(aa[0]))
                if neg_id is not None and self.find(neg_id) == rb and b == aa[0]:
                    self.assert_equality(
                        _BOOL,
                        node,
                        truth,
                        _apps(_constant("Trans"), _BOOL, node, _apps(_constant("||"), b, a), truth, _apps(_constant("holdfast_or_comm"), a, b), _app(_constant("holdfast_bool_or_not_r"), b)),
                    )

    def _saturate_int_binary(
        self, node: _Term, head: _Term, cname: str, a: _Term, b: _Term, ra: int, rb: int, refl_true: _Term,
    ) -> None:
        if "_" not in cname[4:]:
            return
        prefix, spec_name = cname.rsplit("_", 1)
        spec = _INT_SPECS.get(spec_name)
        if spec is None:
            return
        op = prefix[4:]
        tag = _term("nat", value=spec.tag)
        zero_t = _int_term(spec, 0)

        if ra == rb:
            if op in {"and", "or"}:
                lemma = f"holdfast_int_{op}_idem"
                if a == b:
                    self.assert_equality(spec.const, node, a, _apps(_constant(lemma), tag, a))
                elif (p_ab := self.explain(spec.const, a, b)) is not None:
                    z = self.elab.fresh(spec.const)
                    lam = _term("lam", spec.const, _apps(head, a, z), value=cast("int", z.value))
                    step = _apps(_constant("Congr"), spec.const, spec.const, a, b, lam, p_ab)
                    self.assert_equality(
                        spec.const,
                        node,
                        a,
                        _apps(
                            _constant("Trans"),
                            spec.const,
                            node,
                            _apps(head, a, a),
                            a,
                            _apps(_constant("Symm"), spec.const, _apps(head, a, a), node, step),
                            _apps(_constant(lemma), tag, a),
                        ),
                    )
            elif op == "xor":
                p_self = _apps(_constant("holdfast_int_xor_self"), tag, a, zero_t, refl_true)
                if a == b:
                    self.assert_equality(spec.const, node, zero_t, p_self)
                elif (p_ab := self.explain(spec.const, a, b)) is not None:
                    z = self.elab.fresh(spec.const)
                    lam = _term("lam", spec.const, _apps(head, a, z), value=cast("int", z.value))
                    step = _apps(_constant("Congr"), spec.const, spec.const, a, b, lam, p_ab)
                    self.assert_equality(
                        spec.const,
                        node,
                        zero_t,
                        _apps(
                            _constant("Trans"),
                            spec.const,
                            node,
                            _apps(head, a, a),
                            zero_t,
                            _apps(_constant("Symm"), spec.const, _apps(head, a, a), node, step),
                            p_self,
                        ),
                    )
            return

        if op not in {"add", "xor", "and", "or"}:
            return
        zero_id = self.term_to_id.get(zero_t)
        r_zero = self.find(zero_id) if zero_id is not None else -1
        if b.kind == "int" and b.value == 0:
            res = zero_t if op == "and" else a
            self.assert_equality(spec.const, node, res, _apps(_constant(f"holdfast_int_{op}_zero_r"), tag, a, b, refl_true))
        elif rb == r_zero and (p_bz := self.explain(spec.const, b, zero_t)) is not None:
            res = zero_t if op == "and" else a
            z = self.elab.fresh(spec.const)
            lam = _term("lam", spec.const, _apps(head, a, z), value=cast("int", z.value))
            step = _apps(_constant("Congr"), spec.const, spec.const, b, zero_t, lam, p_bz)
            self.assert_equality(
                spec.const,
                node,
                res,
                _apps(
                    _constant("Trans"),
                    spec.const,
                    node,
                    _apps(head, a, zero_t),
                    res,
                    step,
                    _apps(_constant(f"holdfast_int_{op}_zero_r"), tag, a, zero_t, refl_true),
                ),
            )
        elif a.kind == "int" and a.value == 0:
            res = zero_t if op == "and" else b
            self.assert_equality(spec.const, node, res, _apps(_constant(f"holdfast_int_{op}_zero_l"), tag, a, b, refl_true))
        elif ra == r_zero and (p_az := self.explain(spec.const, a, zero_t)) is not None:
            res = zero_t if op == "and" else b
            z = self.elab.fresh(spec.const)
            lam = _term("lam", spec.const, _apps(head, z, b), value=cast("int", z.value))
            step = _apps(_constant("Congr"), spec.const, spec.const, a, zero_t, lam, p_az)
            self.assert_equality(
                spec.const,
                node,
                res,
                _apps(
                    _constant("Trans"),
                    spec.const,
                    node,
                    _apps(head, zero_t, b),
                    res,
                    step,
                    _apps(_constant(f"holdfast_int_{op}_zero_l"), tag, zero_t, b, refl_true),
                ),
            )

    def _flatten_ac(self, op_head: _Term, term: _Term, depth: int = 0) -> list[_Term]:
        if depth > MAX_AC_LEAVES:
            return [term]
        resolved = self.elab.resolve(term)
        h, args = self.elab.spine(resolved)
        if h == op_head and len(args) == 2:
            left = self._flatten_ac(op_head, args[0], depth + 1)
            right = self._flatten_ac(op_head, args[1], depth + 1)
            return [*left, *right]
        return [resolved]

    def _ac_canonicalize(
        self,
        op_head: _Term,
        spec: _IntSpec,
        comm_lemma: str,
        assoc_lemma: str,
        term: _Term,
    ) -> tuple[_Term, _Term | None]:
        """Normalize an AC expression to a right-associated, root-sorted chain with proof."""
        ty = spec.const
        tag = _term("nat", value=spec.tag)
        comm_c = _constant(comm_lemma)
        assoc_c = _constant(assoc_lemma)

        def congr_l(l1: _Term, l2: _Term, r: _Term, p: _Term) -> _Term:
            z = self.elab.fresh(ty)
            lam = _term("lam", ty, _apps(op_head, z, r), value=cast("int", z.value))
            return _apps(_constant("Congr"), ty, ty, l1, l2, lam, p)

        def congr_r(left: _Term, r1: _Term, r2: _Term, p: _Term) -> _Term:
            z = self.elab.fresh(ty)
            lam = _term("lam", ty, _apps(op_head, left, z), value=cast("int", z.value))
            return _apps(_constant("Congr"), ty, ty, r1, r2, lam, p)

        def trans(a: _Term, b: _Term, c: _Term, p1: _Term | None, p2: _Term | None) -> tuple[_Term, _Term | None]:
            if p1 is None:
                return c, p2
            if p2 is None:
                return b, p1
            return c, _apps(_constant("Trans"), ty, a, b, c, p1, p2)

        def canon_leaf(leaf: _Term) -> tuple[_Term, _Term | None]:
            res = self.elab.resolve(leaf)
            nid = self.term_to_id.get(res)
            if nid is None:
                return res, None
            root = self.find(nid)
            rep = self.nodes[root]
            if res == rep:
                return res, None
            p = self.explain(ty, res, rep)
            return (rep, p) if p is not None else (res, None)

        def right_assoc(cur: _Term) -> tuple[_Term, _Term | None]:
            cur = self.elab.resolve(cur)
            h, args = self.elab.spine(cur)
            if h != op_head or len(args) != 2:
                return canon_leaf(cur)
            l_cur, r_cur = args
            l_right, p_l = right_assoc(l_cur)
            r_right, p_r = right_assoc(r_cur)
            mid_term = _apps(op_head, l_right, r_right)
            p_acc: _Term | None = None
            if p_l is not None:
                p_acc = congr_l(l_cur, l_right, r_cur, p_l)
            if p_r is not None:
                step_r = congr_r(l_right, r_cur, r_right, p_r)
                _, p_acc = trans(cur, _apps(op_head, l_right, r_cur), mid_term, p_acc, step_r)
            lh, la = self.elab.spine(l_right)
            if lh == op_head and len(la) == 2:
                x, y = la
                step_assoc = _apps(assoc_c, tag, x, y, r_right)
                shifted_inner, p_inner = right_assoc(_apps(op_head, y, r_right))
                res_t = _apps(op_head, x, shifted_inner)
                p_tail = step_assoc if p_inner is None else _apps(
                    _constant("Trans"),
                    ty,
                    mid_term,
                    _apps(op_head, x, _apps(op_head, y, r_right)),
                    res_t,
                    step_assoc,
                    congr_r(x, _apps(op_head, y, r_right), shifted_inner, p_inner),
                )
                _, p_acc = trans(cur, mid_term, res_t, p_acc, p_tail)
                return res_t, p_acc
            return mid_term, p_acc

        def leaf_key(leaf: _Term) -> tuple[int, str]:
            nid = self.term_to_id.get(leaf)
            return (self.find(nid) if nid is not None else -1, repr(leaf))

        def insert_sorted(x: _Term, chain: _Term) -> tuple[_Term, _Term | None]:
            ch, ca = self.elab.spine(chain)
            if ch != op_head or len(ca) != 2:
                if leaf_key(x) <= leaf_key(chain):
                    return _apps(op_head, x, chain), None
                return _apps(op_head, chain, x), _apps(comm_c, tag, x, chain)
            y, ys = ca
            if leaf_key(x) <= leaf_key(y):
                return _apps(op_head, x, chain), None
            # x + (y + ys) == (x + y) + ys == (y + x) + ys == y + (x + ys)
            start = _apps(op_head, x, chain)
            l_assoc = _apps(op_head, _apps(op_head, x, y), ys)
            l_swapped = _apps(op_head, _apps(op_head, y, x), ys)
            r_mid = _apps(op_head, y, _apps(op_head, x, ys))
            p1 = _apps(_constant("Symm"), ty, l_assoc, start, _apps(assoc_c, tag, x, y, ys))
            p2 = congr_l(_apps(op_head, x, y), _apps(op_head, y, x), ys, _apps(comm_c, tag, x, y))
            p3 = _apps(assoc_c, tag, y, x, ys)
            p12 = _apps(_constant("Trans"), ty, start, l_assoc, l_swapped, p1, p2)
            p123 = _apps(_constant("Trans"), ty, start, l_swapped, r_mid, p12, p3)
            inner_sorted, p_ins = insert_sorted(x, ys)
            if p_ins is None:
                return r_mid, p123
            final_t = _apps(op_head, y, inner_sorted)
            p4 = congr_r(y, _apps(op_head, x, ys), inner_sorted, p_ins)
            return final_t, _apps(_constant("Trans"), ty, start, r_mid, final_t, p123, p4)

        def sort_right_chain(chain: _Term) -> tuple[_Term, _Term | None]:
            ch, ca = self.elab.spine(chain)
            if ch != op_head or len(ca) != 2:
                return chain, None
            x, rest = ca
            rest_sorted, p_rest = sort_right_chain(rest)
            mid = _apps(op_head, x, rest_sorted)
            p_lift = congr_r(x, rest, rest_sorted, p_rest) if p_rest is not None else None
            inserted, p_ins = insert_sorted(x, rest_sorted)
            return trans(chain, mid, inserted, p_lift, p_ins)

        try:
            ra_term, p_ra = right_assoc(term)
            sorted_term, p_sort = sort_right_chain(ra_term)
            final_term, p_all = trans(term, ra_term, sorted_term, p_ra, p_sort)
            return final_term, p_all if p_all is not None else _apps(_constant("Refl"), ty, term)
        except HoldFastError:
            return term, None


class _OrderGraphSearch:
    """Shared bounded BFS graph composer for natural-difference and fixed-int order provers."""

    @staticmethod
    def build_adj[E](edges: list[E], src_of: Callable[[E], _Term]) -> defaultdict[_Term, list[E]]:
        adj: defaultdict[_Term, list[E]] = defaultdict(list)
        for edge in edges:
            adj[src_of(edge)].append(edge)
        return adj

    @staticmethod
    def search[E](
        adj: defaultdict[_Term, list[E]],
        starts: tuple[_Term, ...] | list[_Term],
        budget: list[int],
        *,
        max_hops: int | None,
        compose: Callable[[E, E], E | None],
        dst_of: Callable[[E], _Term],
        record_better: Callable[[dict[_Term, object], E], bool],
        check: Callable[[E], _Term | None],
    ) -> _Term | None:
        for start in starts:
            state: dict[_Term, object] = {}
            queue: deque[tuple[E, int]] = deque()
            for edge in adj.get(start, ()):
                if (done := check(edge)) is not None:
                    return done
                if record_better(state, edge):
                    queue.append((edge, 1))
            while queue:
                cur, hops = queue.popleft()
                if max_hops is not None and hops >= max_hops:
                    continue
                for nxt in adj.get(dst_of(cur), ()):
                    budget[0] -= 1
                    if budget[0] < 0:
                        return None
                    composed = compose(cur, nxt)
                    if composed is None:
                        continue
                    if (done := check(composed)) is not None:
                        return done
                    if record_better(state, composed):
                        queue.append((composed, hops + 1))
        return None


@dataclass(frozen=True)
class _NatDiffEdge:
    src: _Term
    dst: _Term
    weight: int  # Represents src + weight <= dst when weight >= 0, or src <= dst + (-weight) when weight < 0.
    proof: _Term


class NatDifferenceProver:
    """Bounded proof-producing difference-logic reconstructor over Peano ``nat``."""

    def __init__(self, elaborator: _Elaborator) -> None:
        self.elab = elaborator

    def _decompose_nat(self, term: _Term) -> tuple[_Term, int]:
        w = self.elab.whnf(term)
        if w.kind == "nat":
            return _term("nat", value=0), cast("int", w.value)
        head, args = self.elab.spine(w)
        if head == _constant("Succ") and len(args) == 1:
            base, off = self._decompose_nat(args[0])
            return base, off + 1
        if head == _constant("+") and len(args) == 2:
            l_w = self.elab.whnf(args[0])
            r_w = self.elab.whnf(args[1])
            if r_w.kind == "nat":
                base, off = self._decompose_nat(l_w)
                return base, off + cast("int", r_w.value)
            if l_w.kind == "nat":
                base, off = self._decompose_nat(r_w)
                return base, off + cast("int", l_w.value)
        return w, 0

    def _canonical_nat_edge(
        self,
        raw_lhs: _Term,
        raw_rhs: _Term,
        strict: bool,
        witness: _Term,
        is_ltb_term: bool,
    ) -> _NatDiffEdge | None:
        truth = _term("bool", value=1)
        lhs_w = self.elab.whnf(raw_lhs)
        rhs_w = self.elab.whnf(raw_rhs)
        u, kl = self._decompose_nat(lhs_w)
        v, kr = self._decompose_nat(rhs_w)
        if strict:
            kl += 1
        delta = kl - kr

        # Step 1: normalize witness to Nat.leb <lhs_expr> <rhs_expr> = true where lhs_expr, rhs_expr are canonical.
        cur_p = witness
        lh_head, lh_args = self.elab.spine(lhs_w)
        rh_head, rh_args = self.elab.spine(rhs_w)

        if is_ltb_term:
            if (
                lh_head == _constant("+")
                and len(lh_args) == 2
                and self.elab.whnf(lh_args[1]).kind == "nat"
                and self.elab.whnf(lh_args[0]) == u
            ):
                c = cast("int", self.elab.whnf(lh_args[1]).value)
                cur_p = _apps(
                    _constant("holdfast_nat_leb_add_succ_of_ltb"),
                    u,
                    _term("nat", value=c),
                    rhs_w,
                    cur_p,
                )
            elif lhs_w == u:
                cur_p = _apps(_constant("holdfast_nat_leb_succ_of_ltb"), u, rhs_w, cur_p)
            else:
                return None
        elif lh_head == _constant("Succ") and len(lh_args) == 1 and self.elab.whnf(lh_args[0]) == u:
            cur_p = _apps(_constant("holdfast_nat_leb_add1_of_succ"), u, rhs_w, cur_p)
        elif (
            lh_head == _constant("+")
            and len(lh_args) == 2
            and self.elab.whnf(lh_args[0]).kind == "nat"
            and self.elab.whnf(lh_args[1]) == u
            and u != _term("nat", value=0)
        ):
            c = cast("int", self.elab.whnf(lh_args[0]).value)
            cur_p = _apps(_constant("holdfast_nat_leb_add_comm_left"), _term("nat", value=c), u, rhs_w, cur_p)

        if rh_head == _constant("Succ") and len(rh_args) == 1 and self.elab.whnf(rh_args[0]) == v:
            cur_p = _apps(
                _constant("holdfast_nat_leb_r_add1_of_succ"),
                _apps(_constant("+"), u, _term("nat", value=kl)) if kl > 0 else u,
                v,
                cur_p,
            )
        elif (
            rh_head == _constant("+")
            and len(rh_args) == 2
            and self.elab.whnf(rh_args[0]).kind == "nat"
            and self.elab.whnf(rh_args[1]) == v
            and v != _term("nat", value=0)
        ):
            c = cast("int", self.elab.whnf(rh_args[0]).value)
            cur_p = _apps(
                _constant("holdfast_nat_leb_add_comm_right"),
                _apps(_constant("+"), u, _term("nat", value=kl)) if kl > 0 else u,
                _term("nat", value=c),
                v,
                cur_p,
            )

        # Ensure cur_p has type Nat.leb (u + kl) (v + kr) = true (or without +0 when 0)
        if kl > 0 and kr > 0:
            if delta >= 0:
                refl_mk = _apps(_constant("Refl"), _BOOL, truth)
                cur_p = _apps(
                    _constant("holdfast_nat_leb_offset_cancel"),
                    u,
                    v,
                    _term("nat", value=kl),
                    _term("nat", value=kr),
                    cur_p,
                    refl_mk,
                )
            else:
                return None

        return _NatDiffEdge(u, v, delta, cur_p)

    def _harvest_edges(
        self, environment: dict[str, _Binding], facts: tuple[_Binding, ...],
    ) -> list[_NatDiffEdge]:
        scoped = self.elab._expand_fact_bindings((*facts, *environment.values()))
        edges: list[_NatDiffEdge] = []
        nodes: set[_Term] = set()
        for fact in scoped:
            ext = self.elab._extract_equality(fact.type)
            if ext is None:
                continue
            eq_ty, lhs, rhs = ext
            eq_ty_w = self.elab.whnf(eq_ty)
            if eq_ty_w == _NAT:
                p_lr = _apps(_constant("holdfast_nat_leb_of_eq"), lhs, rhs, fact.term)
                sym = _apps(_constant("Symm"), _NAT, lhs, rhs, fact.term)
                p_rl = _apps(_constant("holdfast_nat_leb_of_eq"), rhs, lhs, sym)
                if (e1 := self._canonical_nat_edge(lhs, rhs, False, p_lr, False)) is not None:
                    edges.append(e1)
                    nodes.update((e1.src, e1.dst))
                if (e2 := self._canonical_nat_edge(rhs, lhs, False, p_rl, False)) is not None:
                    edges.append(e2)
                    nodes.update((e2.src, e2.dst))
                continue
            if eq_ty_w != _BOOL:
                continue
            rhs_w = self.elab.whnf(rhs)
            if rhs_w.kind != "bool":
                continue
            truth_val = bool(rhs_w.value)
            head, args = self.elab.spine(self.elab.resolve(lhs))
            if len(args) != 2:
                continue
            if head == _constant("eq_nat") and truth_val:
                p_lr = _apps(_constant("holdfast_nat_leb_of_eqb"), args[0], args[1], fact.term)
                if (e1 := self._canonical_nat_edge(args[0], args[1], False, p_lr, False)) is not None:
                    edges.append(e1)
                    nodes.update((e1.src, e1.dst))
                continue
            if head in {_constant("<="), _constant("<"), _constant(">="), _constant(">")}:
                if head in {_constant("<="), _constant("<")}:
                    a, b, strict, is_ltb = args[0], args[1], head == _constant("<"), head == _constant("<")
                else:
                    a, b, strict, is_ltb = args[1], args[0], head == _constant(">"), head == _constant(">")
                witness = fact.term
                if not truth_val:
                    lemma = "holdfast_nat_leb_of_ltb_false" if strict else "holdfast_nat_ltb_of_leb_false"
                    witness = _apps(_constant(lemma), a, b, witness)
                    a, b, strict, is_ltb = b, a, not strict, not strict
                if (edge := self._canonical_nat_edge(a, b, strict, witness, is_ltb)) is not None:
                    edges.append(edge)
                    nodes.update((edge.src, edge.dst))
        zero = _term("nat", value=0)
        edges.extend(
            _NatDiffEdge(zero, node, 0, _app(_constant("holdfast_nat_zero_leb"), node))
            for node in sorted(nodes, key=repr)
            if node != zero
        )
        return edges

    def _compose_edges(self, e1: _NatDiffEdge, e2: _NatDiffEdge) -> _NatDiffEdge | None:
        if e1.dst != e2.src:
            return None
        truth = _term("bool", value=1)
        refl = _apps(_constant("Refl"), _BOOL, truth)
        u, w, v = e1.src, e1.dst, e2.dst
        w1, w2 = e1.weight, e2.weight
        if w1 == 0 and w2 == 0:
            p = _apps(_constant("holdfast_nat_leb_trans"), u, w, v, e1.proof, e2.proof)
            return _NatDiffEdge(u, v, 0, p)
        if w1 >= 0 and w2 >= 0:
            p1 = _app(_apps(_constant("holdfast_nat_leb_add0_r"), u, w), e1.proof) if w1 == 0 else e1.proof
            p2 = _app(_apps(_constant("holdfast_nat_leb_add0_r"), w, v), e2.proof) if w2 == 0 else e2.proof
            p = _apps(
                _constant("holdfast_nat_leb_shift_trans"),
                u, w, v, _term("nat", value=w1), _term("nat", value=w2), p1, p2,
            )
            return _NatDiffEdge(u, v, w1 + w2, p)
        if w1 >= 0 and w2 < 0:
            k, m = w1, -w2
            p1 = _app(_apps(_constant("holdfast_nat_leb_add0_r"), u, w), e1.proof) if k == 0 else e1.proof
            if k >= m:
                p = _apps(
                    _constant("holdfast_nat_leb_shift_cancel_r"),
                    u, w, v, _term("nat", value=k), _term("nat", value=m), p1, e2.proof, refl,
                )
                if k == m:
                    p = _app(_apps(_constant("holdfast_nat_leb_drop0_r"), u, v), p)
                return _NatDiffEdge(u, v, k - m, p)
            p = _apps(
                _constant("holdfast_nat_leb_shift_cancel_l"),
                u, w, v, _term("nat", value=k), _term("nat", value=m), p1, e2.proof, refl,
            )
            return _NatDiffEdge(u, v, k - m, p)
        if w1 < 0 and w2 >= 0:
            m, k = -w1, w2
            p2 = _app(_apps(_constant("holdfast_nat_leb_add0_r"), w, v), e2.proof) if k == 0 else e2.proof
            if k >= m:
                p = _apps(
                    _constant("holdfast_nat_leb_cancel_shift_r"),
                    u, w, v, _term("nat", value=m), _term("nat", value=k), e1.proof, p2, refl,
                )
                if k == m:
                    p = _app(_apps(_constant("holdfast_nat_leb_drop0_r"), u, v), p)
                return _NatDiffEdge(u, v, k - m, p)
            p = _apps(
                _constant("holdfast_nat_leb_cancel_shift_l"),
                u, w, v, _term("nat", value=m), _term("nat", value=k), e1.proof, p2, refl,
            )
            return _NatDiffEdge(u, v, k - m, p)
        m1, m2 = -w1, -w2
        p = _apps(
            _constant("holdfast_nat_leb_neg_trans"),
            u, w, v, _term("nat", value=m1), _term("nat", value=m2), e1.proof, e2.proof,
        )
        return _NatDiffEdge(u, v, -(m1 + m2), p)

    def _finish_goal(
        self,
        edge: _NatDiffEdge,
        raw_lhs: _Term,
        raw_rhs: _Term,
        strict: bool,
        is_ltb_term: bool,
    ) -> _Term | None:
        u, kl = self._decompose_nat(raw_lhs)
        v, kr = self._decompose_nat(raw_rhs)
        if edge.src != u or edge.dst != v:
            return None
        req_kl = kl + (1 if strict else 0)
        req_delta = req_kl - kr
        if edge.weight < req_delta:
            return None
        truth = _term("bool", value=1)
        refl = _apps(_constant("Refl"), _BOOL, truth)
        if kr == 0:
            if edge.weight > req_kl:
                p = _apps(
                    _constant("holdfast_nat_leb_weaken_l"),
                    u, v, _term("nat", value=edge.weight), _term("nat", value=req_kl), refl, edge.proof,
                )
                if req_kl == 0:
                    p = _app(_apps(_constant("holdfast_nat_leb_drop0_r"), u, v), p)
            elif edge.weight == req_kl:
                p = edge.proof
            else:
                return None
        elif edge.weight >= 0:
            p = _apps(
                _constant("holdfast_nat_leb_weaken_r"),
                u, v, _term("nat", value=edge.weight), _term("nat", value=kr),
                _app(_apps(_constant("holdfast_nat_leb_add0_r"), u, v), edge.proof) if edge.weight == 0 else edge.proof,
            )
            if req_kl > 0:
                return None
        else:
            m = -edge.weight
            if m > kr or req_kl > 0:
                return None
            p = _apps(
                _constant("holdfast_nat_leb_weaken_neg"),
                u, v, _term("nat", value=m), _term("nat", value=kr), refl, edge.proof,
            )

        # Adapt canonical (u + req_kl <= v + kr) back to raw syntax (Succ, commuted addends, or <).
        rhs_w = self.elab.whnf(raw_rhs)
        rh_head, rh_args = self.elab.spine(rhs_w)
        cur_rhs = _apps(_constant("+"), v, _term("nat", value=kr)) if kr > 0 else v
        if rh_head == _constant("Succ") and len(rh_args) == 1 and kr == 1:
            cur_lhs = _apps(_constant("+"), u, _term("nat", value=req_kl)) if req_kl > 0 else u
            p = _apps(_constant("holdfast_nat_leb_r_succ_of_add1"), cur_lhs, v, p)
            cur_rhs = rhs_w
        elif (
            rh_head == _constant("+")
            and len(rh_args) == 2
            and self.elab.whnf(rh_args[0]).kind == "nat"
            and self.elab.whnf(rh_args[1]) == v
            and v != _term("nat", value=0)
        ):
            cur_lhs = _apps(_constant("+"), u, _term("nat", value=req_kl)) if req_kl > 0 else u
            p = _apps(_constant("holdfast_nat_leb_add_comm_goal_right"), cur_lhs, _term("nat", value=kr), v, p)
            cur_rhs = rhs_w

        lhs_w = self.elab.whnf(raw_lhs)
        lh_head, lh_args = self.elab.spine(lhs_w)
        if is_ltb_term:
            if kl == 0:
                p = _apps(_constant("holdfast_nat_ltb_of_leb_add1"), u, cur_rhs, p)
            elif (
                lh_head == _constant("+")
                and len(lh_args) == 2
                and self.elab.whnf(lh_args[1]).kind == "nat"
                and self.elab.whnf(lh_args[0]) == u
            ):
                p = _apps(
                    _constant("holdfast_nat_ltb_of_leb_add_succ"),
                    u,
                    _term("nat", value=kl),
                    cur_rhs,
                    p,
                )
            else:
                return None
        elif lh_head == _constant("Succ") and len(lh_args) == 1 and req_kl == 1:
            p = _apps(_constant("holdfast_nat_leb_l_succ_of_add1"), u, cur_rhs, p)
        elif (
            lh_head == _constant("+")
            and len(lh_args) == 2
            and self.elab.whnf(lh_args[0]).kind == "nat"
            and self.elab.whnf(lh_args[1]) == u
            and u != _term("nat", value=0)
        ):
            p = _apps(_constant("holdfast_nat_leb_add_comm_goal_left"), _term("nat", value=req_kl), u, cur_rhs, p)

        return p

    @staticmethod
    def _record_better(best: dict[_Term, object], edge: _NatDiffEdge) -> bool:
        prev = cast("_NatDiffEdge | None", best.get(edge.dst))
        if prev is None or edge.weight > prev.weight:
            best[edge.dst] = edge
            return True
        return False

    def find_contradiction(
        self, goal: _Term, environment: dict[str, _Binding], facts: tuple[_Binding, ...], max_joins: int,
    ) -> _Term | None:
        """Detect a positive-weight cycle ``a + k <= a`` (``k >= 1``) and emit a kernel proof of ``goal``."""
        edges = self._harvest_edges(environment, facts)
        if not edges:
            return None
        truth = _term("bool", value=1)
        refl = _apps(_constant("Refl"), _BOOL, truth)
        adj = _OrderGraphSearch.build_adj(edges, lambda e: e.src)
        zero = _term("nat", value=0)
        starts = sorted((n for n in adj if n != zero), key=repr)
        if zero in adj:
            starts.append(zero)

        def _check(edge: _NatDiffEdge) -> _Term | None:
            if edge.src == edge.dst and edge.weight >= 1:
                return _apps(
                    _constant("holdfast_nat_leb_add_contra"),
                    goal,
                    edge.src,
                    _term("nat", value=edge.weight),
                    refl,
                    edge.proof,
                )
            return None

        return _OrderGraphSearch.search(
            adj,
            starts,
            [max_joins],
            max_hops=len(adj),
            compose=self._compose_edges,
            dst_of=lambda e: e.dst,
            record_better=self._record_better,
            check=_check,
        )

    def prove(
        self,
        goal: _Term,
        environment: dict[str, _Binding],
        facts: tuple[_Binding, ...],
        max_joins: int,
    ) -> _Term | None:
        """Prove a ``Nat`` comparison assertion via weighted difference-logic chaining."""
        ext = self.elab._extract_equality(goal)
        if ext is None or self.elab.whnf(ext[0]) != _BOOL or ext[2] != _term("bool", value=1):
            return None
        head, args = self.elab.spine(self.elab.resolve(ext[1]))
        if len(args) != 2 or head not in {_constant("<="), _constant("<"), _constant(">="), _constant(">")}:
            return None
        if head in {_constant("<="), _constant("<")}:
            raw_lhs, raw_rhs, strict, is_ltb = args[0], args[1], head == _constant("<"), head == _constant("<")
        else:
            raw_lhs, raw_rhs, strict, is_ltb = args[1], args[0], head == _constant(">"), head == _constant(">")

        edges = self._harvest_edges(environment, facts)
        if not edges:
            return None
        u, _ = self._decompose_nat(raw_lhs)
        refl_u = _NatDiffEdge(u, u, 0, _app(_constant("holdfast_nat_leb_refl"), u))
        if (direct := self._finish_goal(refl_u, raw_lhs, raw_rhs, strict, is_ltb)) is not None:
            return direct
        adj = _OrderGraphSearch.build_adj(edges, lambda e: e.src)
        return _OrderGraphSearch.search(
            adj,
            [u],
            [max_joins],
            max_hops=len(adj),
            compose=self._compose_edges,
            dst_of=lambda e: e.dst,
            record_better=self._record_better,
            check=lambda edge: self._finish_goal(edge, raw_lhs, raw_rhs, strict, is_ltb),
        )


@dataclass(frozen=True)
class _IntOrderEdge:
    src: _Term
    dst: _Term
    strict: bool
    proof: _Term


class FixedIntOrderProver:
    """Bounded proof-producing order and contradiction prover for fixed-width integers."""

    def __init__(self, elaborator: _Elaborator) -> None:
        self.elab = elaborator

    def _harvest(
        self, spec: _IntSpec, environment: dict[str, _Binding], facts: tuple[_Binding, ...],
    ) -> list[_IntOrderEdge]:
        scoped = self.elab._expand_fact_bindings((*facts, *environment.values()))
        tag = _term("nat", value=spec.tag)
        edges: list[_IntOrderEdge] = []
        nodes: set[_Term] = set()
        for fact in scoped:
            ext = self.elab._extract_equality(fact.type)
            if ext is None:
                continue
            eq_ty, lhs, rhs = ext
            eq_ty_w = self.elab.whnf(eq_ty)
            if eq_ty_w == spec.const:
                p_lr = _apps(_constant("holdfast_int_eq_imp_le"), tag, lhs, rhs, _apps(_constant("holdfast_int_eq_of_eq"), tag, lhs, rhs, fact.term))
                p_rl = _apps(_constant("holdfast_int_eq_imp_le_sym"), tag, lhs, rhs, _apps(_constant("holdfast_int_eq_of_eq"), tag, lhs, rhs, fact.term))
                edges.append(_IntOrderEdge(lhs, rhs, False, p_lr))
                edges.append(_IntOrderEdge(rhs, lhs, False, p_rl))
                nodes.update((lhs, rhs))
                continue
            if eq_ty_w != _BOOL:
                continue
            rhs_w = self.elab.whnf(rhs)
            if rhs_w.kind != "bool":
                continue
            truth_val = bool(rhs_w.value)
            head, args = self.elab.spine(self.elab.resolve(lhs))
            if head.kind != "const" or not isinstance(head.value, str) or len(args) != 2:
                continue
            cname = head.value
            if not cname.endswith(f"_{spec.name}") or not cname.startswith("int_"):
                continue
            op = cname[4 : -len(spec.name) - 1]
            a, b = args
            nodes.update((a, b))
            if op == "eq" and truth_val:
                edges.append(_IntOrderEdge(a, b, False, _apps(_constant("holdfast_int_eq_imp_le"), tag, a, b, fact.term)))
                edges.append(_IntOrderEdge(b, a, False, _apps(_constant("holdfast_int_eq_imp_le_sym"), tag, a, b, fact.term)))
            elif op == "le":
                if truth_val:
                    edges.append(_IntOrderEdge(a, b, False, fact.term))
                else:
                    edges.append(_IntOrderEdge(b, a, True, _apps(_constant("holdfast_int_lt_of_le_false"), tag, a, b, fact.term)))
            elif op == "lt":
                if truth_val:
                    edges.append(_IntOrderEdge(a, b, True, fact.term))
                else:
                    edges.append(_IntOrderEdge(b, a, False, _apps(_constant("holdfast_int_le_of_lt_false"), tag, a, b, fact.term)))
            elif op == "ge":
                if truth_val:
                    edges.append(_IntOrderEdge(b, a, False, fact.term))
                else:
                    edges.append(_IntOrderEdge(a, b, True, _apps(_constant("holdfast_int_lt_of_le_false"), tag, b, a, fact.term)))
            elif op == "gt":
                if truth_val:
                    edges.append(_IntOrderEdge(b, a, True, fact.term))
                else:
                    edges.append(_IntOrderEdge(a, b, False, _apps(_constant("holdfast_int_le_of_lt_false"), tag, b, a, fact.term)))
        if spec.name == "usize":
            zero_u = _int_term(spec, 0)
            edges.extend(
                _IntOrderEdge(zero_u, node, False, _app(_constant("holdfast_usize_zero_le"), node))
                for node in sorted(nodes, key=repr)
                if node != zero_u
            )
        return edges

    @staticmethod
    def _compose(tag: _Term, e1: _IntOrderEdge, e2: _IntOrderEdge) -> _IntOrderEdge:
        if not e1.strict and not e2.strict:
            lemma = "holdfast_int_le_trans"
        elif e1.strict and not e2.strict:
            lemma = "holdfast_int_lt_le_trans"
        elif not e1.strict and e2.strict:
            lemma = "holdfast_int_le_lt_trans"
        else:
            lemma = "holdfast_int_lt_trans"
        proof = _apps(_constant(lemma), tag, e1.src, e1.dst, e2.dst, e1.proof, e2.proof)
        return _IntOrderEdge(e1.src, e2.dst, e1.strict or e2.strict, proof)

    @staticmethod
    def _record_better(seen: dict[_Term, object], edge: _IntOrderEdge) -> bool:
        prev = cast("bool | None", seen.get(edge.dst))
        if prev is None or (edge.strict and not prev):
            seen[edge.dst] = edge.strict
            return True
        return False

    def prove(
        self,
        goal: _Term,
        environment: dict[str, _Binding],
        facts: tuple[_Binding, ...],
        max_steps: int = MAX_INT_ORDER_STEPS,
    ) -> _Term | None:
        """Prove a fixed-width integer comparison assertion via transitive order certificates."""
        ext = self.elab._extract_equality(goal)
        if ext is None or self.elab.whnf(ext[0]) != _BOOL or ext[2] != _term("bool", value=1):
            return None
        head, args = self.elab.spine(self.elab.resolve(ext[1]))
        if head.kind != "const" or not isinstance(head.value, str) or len(args) != 2:
            return None
        cname = head.value
        if not cname.startswith("int_"):
            return None
        prefix, spec_name = cname.rsplit("_", 1)
        spec = _INT_SPECS.get(spec_name)
        op = prefix[4:]
        if spec is None or op not in {"le", "lt", "ge", "gt"}:
            return None
        tag = _term("nat", value=spec.tag)
        if op in {"le", "lt"}:
            lhs, rhs, need_strict = args[0], args[1], op == "lt"
        else:
            lhs, rhs, need_strict = args[1], args[0], op == "gt"

        if not need_strict and self.elab.convertible(lhs, rhs):
            return _apps(_constant("holdfast_int_le_refl"), tag, lhs)

        edges = self._harvest(spec, environment, facts)
        if not edges:
            return None
        adj = _OrderGraphSearch.build_adj(edges, lambda e: e.src)

        def _check(edge: _IntOrderEdge) -> _Term | None:
            if edge.dst == rhs and (edge.strict or not need_strict):
                return (
                    edge.proof
                    if (need_strict or not edge.strict)
                    else _apps(_constant("holdfast_int_lt_imp_le"), tag, lhs, rhs, edge.proof)
                )
            return None

        return _OrderGraphSearch.search(
            adj,
            [lhs],
            [max_steps],
            max_hops=None,
            compose=lambda cur, nxt: self._compose(tag, cur, nxt),
            dst_of=lambda e: e.dst,
            record_better=self._record_better,
            check=_check,
        )

    def find_contradiction(
        self,
        goal: _Term,
        environment: dict[str, _Binding],
        facts: tuple[_Binding, ...],
        max_steps: int = MAX_INT_ORDER_STEPS,
    ) -> _Term | None:
        """Detect a strict cycle ``x < x`` on any integer type and emit a kernel proof of ``goal``."""
        for spec in _INT_SPECS.values():
            edges = self._harvest(spec, environment, facts)
            if not edges:
                continue
            tag = _term("nat", value=spec.tag)
            adj = _OrderGraphSearch.build_adj(edges, lambda e: e.src)

            def _check(edge: _IntOrderEdge, tag: _Term = tag) -> _Term | None:
                if edge.src == edge.dst and edge.strict:
                    return _apps(
                        _constant("holdfast_int_lt_le_contra"),
                        goal, tag, edge.src, edge.src, edge.proof,
                        _apps(_constant("holdfast_int_le_refl"), tag, edge.src),
                    )
                return None

            res = _OrderGraphSearch.search(
                adj,
                sorted(adj, key=repr),
                [max_steps],
                max_hops=None,
                compose=lambda cur, nxt, tag=tag: self._compose(tag, cur, nxt),
                dst_of=lambda e: e.dst,
                record_better=self._record_better,
                check=_check,
            )
            if res is not None:
                return res
        return None


type _Poly = dict[tuple[int, ...], int]
type _BoolSkel = tuple[object, ...]


class NatPolyEqualizer:
    """Reflective ``Nat`` semiring polynomial normalizer and e-graph bridge."""

    def __init__(self, elaborator: _Elaborator) -> None:
        self.elab = elaborator

    @staticmethod
    def _poly_add(p1: _Poly, p2: _Poly) -> _Poly | None:
        res = dict(p1)
        for mono, coeff in p2.items():
            nxt = res.get(mono, 0) + coeff
            if nxt > 0:
                res[mono] = nxt
            if len(res) > MAX_POLY_TERMS:
                return None
        return res

    @staticmethod
    def _poly_mul(p1: _Poly, p2: _Poly) -> _Poly | None:
        res: _Poly = {}
        for m1, c1 in p1.items():
            for m2, c2 in p2.items():
                mono = tuple(sorted((*m1, *m2)))
                if len(mono) > MAX_POLY_DEGREE:
                    return None
                res[mono] = res.get(mono, 0) + c1 * c2
                if len(res) > MAX_POLY_TERMS:
                    return None
        return res

    def _collect_rep_map(self, egraph: VersionedEGraph, terms: Sequence[_Term]) -> dict[int, _Term]:
        rep_map: dict[int, _Term] = {}
        seen_roots: set[int] = set()

        def visit(t: _Term, depth: int = 0) -> None:
            if depth > MAX_POLY_DEPTH:
                return
            r = self.elab.resolve(t)
            if r.kind == "nat":
                return
            h, args = self.elab.spine(r)
            if h == _constant("Succ") and len(args) == 1:
                visit(args[0], depth + 1)
                return
            if h in {_constant("+"), _constant("*")} and len(args) == 2:
                visit(args[0], depth + 1)
                visit(args[1], depth + 1)
                return
            nid = egraph.term_to_id.get(r)
            if nid is None:
                return
            root = egraph.find(nid)
            if root in seen_roots:
                return
            seen_roots.add(root)
            # Prefer a small Nat literal in the e-class if one exists so e.g. a == 2 folds a + a == 4.
            chosen = r
            for member_id in egraph.classes.get(root, ()):
                m_node = egraph.nodes[member_id]
                if m_node.kind == "nat" and cast("int", m_node.value) <= MAX_POLY_CONST:
                    chosen = m_node
                    break
            rep_map[root] = chosen

        for term in terms:
            visit(term)
        return rep_map

    def _reflect(
        self,
        term: _Term,
        atoms: list[_Term],
        atom_idx: dict[_Term, int],
        *,
        egraph: VersionedEGraph | None = None,
        rep_map: dict[int, _Term] | None = None,
        depth: int = 0,
    ) -> tuple[_Term, _Poly] | None:
        if depth > MAX_POLY_DEPTH:
            return None
        r = self.elab.resolve(term)
        if r.kind == "nat":
            val = cast("int", r.value)
            if val <= MAX_POLY_CONST:
                poly: _Poly = {(): val} if val > 0 else {}
                return _app(_constant("holdfast_npe_const"), r), poly
        else:
            h, args = self.elab.spine(r)
            if h == _constant("Succ") and len(args) == 1:
                inner = self._reflect(args[0], atoms, atom_idx, egraph=egraph, rep_map=rep_map, depth=depth + 1)
                if inner is None:
                    return None
                ast_x, poly_x = inner
                poly_s = self._poly_add({(): 1}, poly_x)
                if poly_s is None:
                    return None
                return _apps(_constant("holdfast_npe_add"), _app(_constant("holdfast_npe_const"), _term("nat", value=1)), ast_x), poly_s
            if h == _constant("+") and len(args) == 2:
                left = self._reflect(args[0], atoms, atom_idx, egraph=egraph, rep_map=rep_map, depth=depth + 1)
                right = self._reflect(args[1], atoms, atom_idx, egraph=egraph, rep_map=rep_map, depth=depth + 1)
                if left is None or right is None:
                    return None
                poly_sum = self._poly_add(left[1], right[1])
                if poly_sum is None:
                    return None
                return _apps(_constant("holdfast_npe_add"), left[0], right[0]), poly_sum
            if h == _constant("*") and len(args) == 2:
                left = self._reflect(args[0], atoms, atom_idx, egraph=egraph, rep_map=rep_map, depth=depth + 1)
                right = self._reflect(args[1], atoms, atom_idx, egraph=egraph, rep_map=rep_map, depth=depth + 1)
                if left is None or right is None:
                    return None
                poly_prod = self._poly_mul(left[1], right[1])
                if poly_prod is None:
                    return None
                return _apps(_constant("holdfast_npe_mul"), left[0], right[0]), poly_prod

        key_term = r
        if egraph is not None and rep_map is not None:
            nid = egraph.term_to_id.get(r)
            if nid is not None:
                key_term = rep_map.get(egraph.find(nid), r)
        if key_term.kind == "nat" and cast("int", key_term.value) <= MAX_POLY_CONST:
            val = cast("int", key_term.value)
            poly_lit: _Poly = {(): val} if val > 0 else {}
            return _app(_constant("holdfast_npe_const"), key_term), poly_lit
        idx = atom_idx.get(key_term)
        if idx is None:
            if len(atoms) >= MAX_POLY_VARS:
                return None
            idx = len(atoms)
            atoms.append(key_term)
            atom_idx[key_term] = idx
        return _app(_constant("holdfast_npe_var"), _term("nat", value=idx)), {(idx,): 1}

    def polynomial_key(
        self, egraph: VersionedEGraph, term: _Term,
    ) -> tuple[tuple[tuple[int, ...], int], ...] | None:
        """Return a canonical polynomial key modulo current e-graph roots."""
        r = self.elab.resolve(term)
        rep_map = self._collect_rep_map(egraph, (r,))
        atoms: list[_Term] = []
        atom_idx: dict[_Term, int] = {}
        reflected = self._reflect(r, atoms, atom_idx, egraph=egraph, rep_map=rep_map)
        if reflected is None:
            return None
        _, poly = reflected
        remapped: dict[tuple[int, ...], int] = {}
        for mono, coeff in poly.items():
            mapped_mono: list[int] = []
            for var_idx in mono:
                atom = atoms[var_idx]
                nid = egraph.term_to_id.get(atom)
                mapped_mono.append(egraph.find(nid) if nid is not None else -(var_idx + 1))
            key_m = tuple(sorted(mapped_mono))
            remapped[key_m] = remapped.get(key_m, 0) + coeff
        return tuple(sorted(remapped.items()))

    @staticmethod
    def _build_env(atoms: Sequence[_Term]) -> _Term:
        env = _app(_constant("Seq_Empty"), _NAT)
        for atom in reversed(atoms):
            env = _apps(_constant("Seq_Cons"), _NAT, atom, env)
        return env

    def prove_equal(self, lhs: _Term, rhs: _Term) -> _Term | None:
        """Synthesize an axiom-free reflective proof of ``Eq nat lhs rhs`` if equal as polynomials."""
        lhs_r = self.elab.resolve(lhs)
        rhs_r = self.elab.resolve(rhs)
        if lhs_r == rhs_r:
            return _apps(_constant("Refl"), _NAT, lhs_r)
        atoms: list[_Term] = []
        atom_idx: dict[_Term, int] = {}
        left = self._reflect(lhs_r, atoms, atom_idx)
        right = self._reflect(rhs_r, atoms, atom_idx)
        if left is None or right is None or left[1] != right[1]:
            return None
        env = self._build_env(atoms)
        refl_true = _apps(_constant("Refl"), _BOOL, _term("bool", value=1))
        return _apps(_constant("holdfast_npoly_sound"), env, left[0], right[0], refl_true)

    def _rewrite_nat_atoms(
        self,
        egraph: VersionedEGraph,
        term: _Term,
        rep_map: dict[int, _Term],
        depth: int = 0,
    ) -> tuple[_Term, _Term | None]:
        if depth > MAX_POLY_DEPTH:
            return term, None
        r = self.elab.resolve(term)
        if r.kind == "nat":
            return r, None
        h, args = self.elab.spine(r)
        if h == _constant("Succ") and len(args) == 1:
            a_canon, p_a = self._rewrite_nat_atoms(egraph, args[0], rep_map, depth + 1)
            if p_a is None:
                return r, None
            z = self.elab.fresh(_NAT)
            lam = _term("lam", _NAT, _app(h, z), value=cast("int", z.value))
            return _app(h, a_canon), _apps(_constant("Congr"), _NAT, _NAT, args[0], a_canon, lam, p_a)
        if h in {_constant("+"), _constant("*")} and len(args) == 2:
            l_canon, p_l = self._rewrite_nat_atoms(egraph, args[0], rep_map, depth + 1)
            r_canon, p_r = self._rewrite_nat_atoms(egraph, args[1], rep_map, depth + 1)
            if p_l is None and p_r is None:
                return r, None
            mid = _apps(h, l_canon, args[1])
            final_t = _apps(h, l_canon, r_canon)
            p_acc: _Term | None = None
            if p_l is not None:
                z = self.elab.fresh(_NAT)
                lam = _term("lam", _NAT, _apps(h, z, args[1]), value=cast("int", z.value))
                p_acc = _apps(_constant("Congr"), _NAT, _NAT, args[0], l_canon, lam, p_l)
            if p_r is not None:
                z = self.elab.fresh(_NAT)
                lam = _term("lam", _NAT, _apps(h, l_canon, z), value=cast("int", z.value))
                step_r = _apps(_constant("Congr"), _NAT, _NAT, args[1], r_canon, lam, p_r)
                p_acc = step_r if p_acc is None else _apps(_constant("Trans"), _NAT, r, mid, final_t, p_acc, step_r)
            return final_t, p_acc
        nid = egraph.term_to_id.get(r)
        if nid is None:
            return r, None
        rep = rep_map.get(egraph.find(nid))
        if rep is None or rep == r:
            return r, None
        p = egraph.explain(_NAT, r, rep)
        return (rep, p) if p is not None else (r, None)

    def prove_equal_mod_egraph(
        self, egraph: VersionedEGraph, lhs: _Term, rhs: _Term,
    ) -> _Term | None:
        """Equate ``lhs`` and ``rhs`` as ``Nat`` polynomials modulo e-graph equivalence classes."""
        lhs_r = self.elab.resolve(lhs)
        rhs_r = self.elab.resolve(rhs)
        if lhs_r == rhs_r:
            return _apps(_constant("Refl"), _NAT, lhs_r)
        rep_map = self._collect_rep_map(egraph, (lhs_r, rhs_r))
        atoms: list[_Term] = []
        atom_idx: dict[_Term, int] = {}
        left = self._reflect(lhs_r, atoms, atom_idx, egraph=egraph, rep_map=rep_map)
        right = self._reflect(rhs_r, atoms, atom_idx, egraph=egraph, rep_map=rep_map)
        if left is None or right is None or left[1] != right[1]:
            return None
        lhs_canon, p_l = self._rewrite_nat_atoms(egraph, lhs_r, rep_map)
        rhs_canon, p_r = self._rewrite_nat_atoms(egraph, rhs_r, rep_map)
        p_poly = self.prove_equal(lhs_canon, rhs_canon)
        if p_poly is None:
            return None
        acc_p = p_poly
        if p_l is not None:
            acc_p = _apps(_constant("Trans"), _NAT, lhs_r, lhs_canon, rhs_canon, p_l, acc_p)
        if p_r is not None:
            p_r_sym = _apps(_constant("Symm"), _NAT, rhs_r, rhs_canon, p_r)
            acc_p = _apps(_constant("Trans"), _NAT, lhs_r, rhs_canon, rhs_r, acc_p, p_r_sym)
        return acc_p


class PropositionalPrechecker:
    """Mizar-style proof-producing propositional forward-chainer and bounded tableau."""

    def __init__(self, elaborator: _Elaborator) -> None:
        self.elab = elaborator

    def _goal_supports_contra(self, goal: _Term) -> bool:
        try:
            return self.elab._is_prop_type(goal) or self.elab.sort(goal) <= 0
        except HoldFastError:
            return False

    @staticmethod
    def _parse_skel(term: _Term, resolve: Callable[[_Term], _Term], spine: Callable[[_Term], tuple[_Term, list[_Term]]],
                    depth: int = 0) -> _BoolSkel:
        t = resolve(term)
        if depth > 24:
            return ("atom", t)
        if t.kind == "bool":
            return ("lit", bool(t.value))
        h, args = spine(t)
        if h == _constant("!") and len(args) == 1:
            return ("not", PropositionalPrechecker._parse_skel(args[0], resolve, spine, depth + 1))
        if h == _constant("&&") and len(args) == 2:
            return (
                "and",
                PropositionalPrechecker._parse_skel(args[0], resolve, spine, depth + 1),
                PropositionalPrechecker._parse_skel(args[1], resolve, spine, depth + 1),
            )
        if h == _constant("||") and len(args) == 2:
            return (
                "or",
                PropositionalPrechecker._parse_skel(args[0], resolve, spine, depth + 1),
                PropositionalPrechecker._parse_skel(args[1], resolve, spine, depth + 1),
            )
        if h == _constant("==>") and len(args) == 2:
            return (
                "imp",
                PropositionalPrechecker._parse_skel(args[0], resolve, spine, depth + 1),
                PropositionalPrechecker._parse_skel(args[1], resolve, spine, depth + 1),
            )
        if h in {_constant("eq_bool"), _constant("<==>")} and len(args) == 2:
            return (
                "iff",
                PropositionalPrechecker._parse_skel(args[0], resolve, spine, depth + 1),
                PropositionalPrechecker._parse_skel(args[1], resolve, spine, depth + 1),
            )
        if h == _constant("ne_bool") and len(args) == 2:
            return (
                "xor",
                PropositionalPrechecker._parse_skel(args[0], resolve, spine, depth + 1),
                PropositionalPrechecker._parse_skel(args[1], resolve, spine, depth + 1),
            )
        return ("atom", t)

    @staticmethod
    def _skel_atoms(skel: _BoolSkel, out: list[_Term], seen: set[_Term]) -> None:
        tag = skel[0]
        if tag == "atom":
            atom = cast("_Term", skel[1])
            if atom not in seen:
                seen.add(atom)
                out.append(atom)
        elif tag == "not":
            PropositionalPrechecker._skel_atoms(cast("_BoolSkel", skel[1]), out, seen)
        elif tag in {"and", "or", "imp", "iff", "xor"}:
            PropositionalPrechecker._skel_atoms(cast("_BoolSkel", skel[1]), out, seen)
            PropositionalPrechecker._skel_atoms(cast("_BoolSkel", skel[2]), out, seen)

    @staticmethod
    def _eval_skel(skel: _BoolSkel, assign: dict[_Term, bool]) -> bool | None:
        tag = skel[0]
        if tag == "lit":
            return cast("bool", skel[1])
        if tag == "atom":
            return assign.get(cast("_Term", skel[1]))
        if tag == "not":
            v = PropositionalPrechecker._eval_skel(cast("_BoolSkel", skel[1]), assign)
            return None if v is None else (not v)
        lv = PropositionalPrechecker._eval_skel(cast("_BoolSkel", skel[1]), assign)
        rv = PropositionalPrechecker._eval_skel(cast("_BoolSkel", skel[2]), assign)
        if tag == "and":
            if lv is False or rv is False:
                return False
            return True if (lv is True and rv is True) else None
        if tag == "or":
            if lv is True or rv is True:
                return True
            return False if (lv is False and rv is False) else None
        if tag == "imp":
            if lv is False or rv is True:
                return True
            return False if (lv is True and rv is False) else None
        if lv is None or rv is None:
            return None
        if tag == "iff":
            return lv == rv
        return lv != rv

    @staticmethod
    def _rebuild_skel(skel: _BoolSkel, subst: dict[_Term, _Term]) -> _Term:
        tag = skel[0]
        if tag == "lit":
            return _term("bool", value=int(cast("bool", skel[1])))
        if tag == "atom":
            atom = cast("_Term", skel[1])
            return subst.get(atom, atom)
        if tag == "not":
            return _app(_constant("!"), PropositionalPrechecker._rebuild_skel(cast("_BoolSkel", skel[1]), subst))
        left = PropositionalPrechecker._rebuild_skel(cast("_BoolSkel", skel[1]), subst)
        right = PropositionalPrechecker._rebuild_skel(cast("_BoolSkel", skel[2]), subst)
        op = {
            "and": "&&",
            "or": "||",
            "imp": "==>",
            "iff": "eq_bool",
            "xor": "ne_bool",
        }[cast("str", tag)]
        return _apps(_constant(op), left, right)

    def _prove_tableau(
        self,
        goal: _Term,
        goal_skel: _BoolSkel | None,
        goal_target: bool | None,
        hyps: list[tuple[_BoolSkel, _Term, bool]],
    ) -> _Term | None:
        if not self._goal_supports_contra(goal):
            return None
        atoms: list[_Term] = []
        seen_atoms: set[_Term] = set()
        if goal_skel is not None:
            self._skel_atoms(goal_skel, atoms, seen_atoms)
        if len(atoms) > MAX_PRECHECKER_ATOMS:
            return None

        # Select relevant hypotheses without exceeding MAX_PRECHECKER_ATOMS.
        selected: list[tuple[_BoolSkel, _Term, bool]] = []
        if goal_skel is not None:
            hyp_info = []
            for hs, hp, hexp in hyps:
                ha: list[_Term] = []
                self._skel_atoms(hs, ha, set())
                hyp_info.append((hs, hp, hexp, ha))
            changed = True
            while changed:
                changed = False
                for hs, hp, hexp, ha in hyp_info:
                    if any(hp is shp for _, shp, _ in selected):
                        continue
                    if not ha or any(a in seen_atoms for a in ha):
                        new_atoms = [a for a in ha if a not in seen_atoms]
                        if len(atoms) + len(new_atoms) <= MAX_PRECHECKER_ATOMS:
                            atoms.extend(new_atoms)
                            seen_atoms.update(new_atoms)
                            selected.append((hs, hp, hexp))
                            changed = True
        else:
            for hs, hp, hexp in hyps:
                ha = []
                self._skel_atoms(hs, ha, set())
                new_atoms = [a for a in ha if a not in seen_atoms]
                if len(atoms) + len(new_atoms) <= MAX_PRECHECKER_ATOMS:
                    atoms.extend(new_atoms)
                    seen_atoms.update(new_atoms)
                    selected.append((hs, hp, hexp))

        if not atoms and goal_skel is None and not selected:
            return None

        # Fast truth-table validity check before constructing any Gallina term.
        n_atoms = len(atoms)
        for mask in range(1 << n_atoms):
            assign = {atoms[i]: bool((mask >> i) & 1) for i in range(n_atoms)}
            if all(self._eval_skel(hs, assign) == hexp for hs, _, hexp in selected):
                if goal_skel is None or goal_target is None:
                    return None
                if self._eval_skel(goal_skel, assign) != goal_target:
                    return None

        def solve(
            idx: int,
            assign: dict[_Term, bool],
            cur_goal: _Term,
            cur_goal_skel: _BoolSkel | None,
            cur_hyps: list[tuple[_BoolSkel, _Term, bool]],
        ) -> _Term | None:
            for hs, hp, hexp in cur_hyps:
                val = self._eval_skel(hs, assign)
                if val is not None and val != hexp:
                    lemma = "holdfast_false_true_elim" if hexp else "holdfast_false_elim"
                    return _apps(_constant(lemma), cur_goal, hp)
            if cur_goal_skel is not None and goal_target is not None:
                gval = self._eval_skel(cur_goal_skel, assign)
                if gval is not None and gval == goal_target:
                    return _apps(_constant("Refl"), _BOOL, _term("bool", value=int(goal_target)))
            if idx >= n_atoms:
                return None

            atom = atoms[idx]
            b_var = self.elab.fresh(_BOOL)
            b_id = cast("int", b_var.value)
            true_t = _term("bool", value=1)
            false_t = _term("bool", value=0)
            eq_true_t = _apps(_constant("Eq"), _BOOL, atom, true_t)
            eq_false_t = _apps(_constant("Eq"), _BOOL, atom, false_t)
            h_true = self.elab.fresh(eq_true_t)
            h_false = self.elab.fresh(eq_false_t)
            h_true_id = cast("int", h_true.value)
            h_false_id = cast("int", h_false.value)

            goal_b = cur_goal
            goal_true = cur_goal
            goal_false = cur_goal
            if cur_goal_skel is not None and goal_target is not None:
                g_expr_b = self._rebuild_skel(cur_goal_skel, {atom: b_var})
                goal_b = _apps(_constant("Eq"), _BOOL, g_expr_b, _term("bool", value=int(goal_target)))
                goal_true = _apps(
                    _constant("Eq"), _BOOL, self._rebuild_skel(cur_goal_skel, {atom: true_t}), _term("bool", value=int(goal_target)),
                )
                goal_false = _apps(
                    _constant("Eq"), _BOOL, self._rebuild_skel(cur_goal_skel, {atom: false_t}), _term("bool", value=int(goal_target)),
                )

            def specialize_hyps(repl: _Term, eq_proof: _Term) -> list[tuple[_BoolSkel, _Term, bool]]:
                next_hyps: list[tuple[_BoolSkel, _Term, bool]] = []
                for hs, hp, hexp in cur_hyps:
                    ha: list[_Term] = []
                    self._skel_atoms(hs, ha, set())
                    if atom not in ha:
                        next_hyps.append((hs, hp, hexp))
                        continue
                    h_orig = self._rebuild_skel(hs, {})
                    h_b = self._rebuild_skel(hs, {atom: b_var})
                    h_new = self._rebuild_skel(hs, {atom: repl})
                    lam = _term("lam", _BOOL, h_b, value=b_id)
                    p_congr = _apps(_constant("Congr"), _BOOL, _BOOL, atom, repl, lam, eq_proof)
                    p_sym = _apps(_constant("Symm"), _BOOL, h_orig, h_new, p_congr)
                    p_new = _apps(_constant("Trans"), _BOOL, h_new, h_orig, _term("bool", value=int(hexp)), p_sym, hp)
                    new_skel = self._parse_skel(h_new, self.elab.resolve, self.elab.spine)
                    next_hyps.append((new_skel, p_new, hexp))
                return next_hyps

            yes_proof = solve(idx + 1, {**assign, atom: True}, goal_true, cur_goal_skel, specialize_hyps(true_t, h_true))
            if yes_proof is None:
                return None
            no_proof = solve(idx + 1, {**assign, atom: False}, goal_false, cur_goal_skel, specialize_hyps(false_t, h_false))
            if no_proof is None:
                return None

            if h_true_id not in self.elab.free(yes_proof) and h_false_id not in self.elab.free(no_proof):
                motive_lam = _term("lam", _BOOL, goal_b, value=b_id)
                return _term("bool_match", motive_lam, atom, yes_proof, no_proof)
            eq_b_t = _apps(_constant("Eq"), _BOOL, atom, b_var)
            motive_lam = _term("lam", _BOOL, self.elab.pi(eq_b_t, goal_b), value=b_id)
            yes_lam = _term("lam", eq_true_t, yes_proof, value=h_true_id)
            no_lam = _term("lam", eq_false_t, no_proof, value=h_false_id)
            match_t = _term("bool_match", motive_lam, atom, yes_lam, no_lam)
            return _app(match_t, _apps(_constant("Refl"), _BOOL, atom))

        return solve(0, {}, goal, goal_skel, selected)

    def prove(self, goal: _Term, facts: tuple[_Binding, ...]) -> _Term | None:
        """Discharge propositional entailments, tautologies, or equality/disequality contradictions."""
        pos: dict[_Term, _Term] = {}
        neg: dict[_Term, _Term] = {}
        eq_facts: list[tuple[_Term, _Term, _Term, _Term]] = []
        raw_hyps: list[tuple[_BoolSkel, _Term, bool]] = []
        contra: list[tuple[_Term, _Term, _Term]] = []
        can_contra = self._goal_supports_contra(goal)

        def record_pos(t: _Term, p: _Term, depth: int = 0) -> None:
            if depth > 16 or contra:
                return
            t = self.elab.resolve(t)
            if t == _term("bool", value=0):
                contra.append((t, p, _apps(_constant("Refl"), _BOOL, t)))
                return
            if t in neg:
                contra.append((t, p, neg[t]))
                return
            if t in pos:
                return
            pos[t] = p
            h, args = self.elab.spine(t)
            if h == _constant("&&") and len(args) == 2:
                record_pos(args[0], _apps(_constant("holdfast_and_left"), args[0], args[1], p), depth + 1)
                record_pos(args[1], _apps(_constant("holdfast_and_right"), args[0], args[1], p), depth + 1)
            elif h == _constant("!") and len(args) == 1:
                record_neg(args[0], _apps(_constant("holdfast_not_true_to_false"), args[0], p), depth + 1)
            elif h == _constant("ne_nat") and len(args) == 2:
                record_neg(_apps(_constant("eq_nat"), args[0], args[1]), _apps(_constant("holdfast_ne_nat_false"), args[0], args[1], p), depth + 1)
            elif h == _constant("ne_bool") and len(args) == 2:
                record_neg(_apps(_constant("eq_bool"), args[0], args[1]), _apps(_constant("holdfast_ne_bool_false"), args[0], args[1], p), depth + 1)
            elif h == _constant("eq_nat") and len(args) == 2:
                eq_facts.append((_NAT, args[0], args[1], _apps(_constant("holdfast_nat_eq_of_eqb"), args[0], args[1], p)))
            elif h in {_constant("eq_bool"), _constant("<==>")} and len(args) == 2:
                eq_facts.append((_BOOL, args[0], args[1], _apps(_constant("holdfast_eq_bool_true"), args[0], args[1], p)))
            elif h.kind == "const" and isinstance(h.value, str) and len(args) == 2:
                if h.value.startswith("int_ne_") and (spec := _INT_SPECS.get(h.value[len("int_ne_") :])) is not None:
                    record_neg(
                        _apps(_constant(f"int_eq_{spec.name}"), args[0], args[1]),
                        _apps(_constant("holdfast_int_ne_false"), _term("nat", value=spec.tag), args[0], args[1], p),
                        depth + 1,
                    )
                elif h.value.startswith("int_eq_") and (spec := _INT_SPECS.get(h.value[len("int_eq_") :])) is not None:
                    eq_facts.append((
                        spec.const,
                        args[0],
                        args[1],
                        _apps(_constant("holdfast_int_eq_true"), _term("nat", value=spec.tag), args[0], args[1], p),
                    ))

        def record_neg(t: _Term, p: _Term, depth: int = 0) -> None:
            if depth > 16 or contra:
                return
            t = self.elab.resolve(t)
            if t == _term("bool", value=1):
                contra.append((t, _apps(_constant("Refl"), _BOOL, t), p))
                return
            if t in pos:
                contra.append((t, pos[t], p))
                return
            if t in neg:
                return
            neg[t] = p
            h, args = self.elab.spine(t)
            if h == _constant("||") and len(args) == 2:
                record_neg(args[0], _apps(_constant("holdfast_or_false_l"), args[0], args[1], p), depth + 1)
                record_neg(args[1], _apps(_constant("holdfast_or_false_r"), args[0], args[1], p), depth + 1)
            elif h == _constant("!") and len(args) == 1:
                record_pos(args[0], _apps(_constant("holdfast_not_false_to_true"), args[0], p), depth + 1)
            elif h == _constant("==>") and len(args) == 2:
                record_pos(args[0], _apps(_constant("holdfast_implies_false_l"), args[0], args[1], p), depth + 1)
                record_neg(args[1], _apps(_constant("holdfast_implies_false_r"), args[0], args[1], p), depth + 1)

        truth = _term("bool", value=1)
        false_t = _term("bool", value=0)

        for fact in facts:
            ext = self.elab._extract_equality(fact.type)
            if ext is None:
                continue
            eq_ty, u, v = ext
            eq_ty_w = self.elab.whnf(eq_ty)
            if eq_ty_w != _BOOL:
                eq_facts.append((eq_ty, u, v, fact.term))
                u_r = self.elab.resolve(u)
                v_r = self.elab.resolve(v)
                if eq_ty_w == _NAT:
                    record_pos(_apps(_constant("eq_nat"), u_r, v_r), _apps(_constant("holdfast_nat_eqb_of_eq"), u_r, v_r, fact.term))
                elif (spec := self.elab._int_spec(eq_ty_w)) is not None:
                    record_pos(
                        _apps(_constant(f"int_eq_{spec.name}"), u_r, v_r),
                        _apps(_constant("holdfast_int_eq_of_eq"), _term("nat", value=spec.tag), u_r, v_r, fact.term),
                    )
                continue
            eq_facts.append((_BOOL, u, v, fact.term))
            uw = self.elab.whnf(u)
            vw = self.elab.whnf(v)
            if vw == truth:
                record_pos(u, fact.term)
                raw_hyps.append((self._parse_skel(u, self.elab.resolve, self.elab.spine), fact.term, True))
            elif uw == truth:
                sym_p = _apps(_constant("Symm"), _BOOL, u, v, fact.term)
                record_pos(v, sym_p)
                raw_hyps.append((self._parse_skel(v, self.elab.resolve, self.elab.spine), sym_p, True))
            elif vw == false_t:
                record_neg(u, fact.term)
                raw_hyps.append((self._parse_skel(u, self.elab.resolve, self.elab.spine), fact.term, False))
            elif uw == false_t:
                sym_p = _apps(_constant("Symm"), _BOOL, u, v, fact.term)
                record_neg(v, sym_p)
                raw_hyps.append((self._parse_skel(v, self.elab.resolve, self.elab.spine), sym_p, False))
            else:
                ur = self.elab.resolve(u)
                vr = self.elab.resolve(v)
                eqb_p = _apps(_constant("holdfast_eq_bool_of_eq"), ur, vr, fact.term)
                record_pos(_apps(_constant("eq_bool"), ur, vr), eqb_p)
                raw_hyps.append((self._parse_skel(_apps(_constant("eq_bool"), ur, vr), self.elab.resolve, self.elab.spine), eqb_p, True))

        # Phase 1: Bounded unit-propagation natural deduction.
        steps = 0
        changed = True
        while changed and not contra and steps < MAX_PRECHECKER_STEPS:
            changed = False
            for t, p in list(pos.items()):
                if contra or steps >= MAX_PRECHECKER_STEPS:
                    break
                h, args = self.elab.spine(t)
                if h == _constant("==>") and len(args) == 2:
                    a, b = self.elab.resolve(args[0]), self.elab.resolve(args[1])
                    if a in pos and b not in pos:
                        record_pos(b, _apps(_constant("holdfast_implies_mp"), a, b, p, pos[a]))
                        changed = True
                        steps += 1
                    if b in neg and a not in neg:
                        record_neg(a, _apps(_constant("holdfast_implies_mt"), a, b, p, neg[b]))
                        changed = True
                        steps += 1
                elif h == _constant("||") and len(args) == 2:
                    a, b = self.elab.resolve(args[0]), self.elab.resolve(args[1])
                    if a in neg and b not in pos:
                        record_pos(b, _apps(_constant("holdfast_or_elim_l"), a, b, p, neg[a]))
                        changed = True
                        steps += 1
                    if b in neg and a not in pos:
                        record_pos(a, _apps(_constant("holdfast_or_elim_r"), a, b, p, neg[b]))
                        changed = True
                        steps += 1
                elif h in {_constant("eq_bool"), _constant("<==>")} and len(args) == 2:
                    a, b = self.elab.resolve(args[0]), self.elab.resolve(args[1])
                    eq_ab = _apps(_constant("holdfast_eq_bool_true"), a, b, p)
                    if a in pos and b not in pos:
                        record_pos(b, _apps(_constant("Trans"), _BOOL, b, a, truth, _apps(_constant("Symm"), _BOOL, a, b, eq_ab), pos[a]))
                        changed = True
                        steps += 1
                    if b in pos and a not in pos:
                        record_pos(a, _apps(_constant("Trans"), _BOOL, a, b, truth, eq_ab, pos[b]))
                        changed = True
                        steps += 1
                    if a in neg and b not in neg:
                        record_neg(b, _apps(_constant("Trans"), _BOOL, b, a, false_t, _apps(_constant("Symm"), _BOOL, a, b, eq_ab), neg[a]))
                        changed = True
                        steps += 1
                    if b in neg and a not in neg:
                        record_neg(a, _apps(_constant("Trans"), _BOOL, a, b, false_t, eq_ab, neg[b]))
                        changed = True
                        steps += 1
            for t, p in list(neg.items()):
                if contra or steps >= MAX_PRECHECKER_STEPS:
                    break
                h, args = self.elab.spine(t)
                if h == _constant("&&") and len(args) == 2:
                    a, b = self.elab.resolve(args[0]), self.elab.resolve(args[1])
                    if a in pos and b not in neg:
                        record_neg(b, _apps(_constant("holdfast_and_false_elim_l"), a, b, p, pos[a]))
                        changed = True
                        steps += 1
                    if b in pos and a not in neg:
                        record_neg(a, _apps(_constant("holdfast_and_false_elim_r"), a, b, p, pos[b]))
                        changed = True
                        steps += 1

        if contra and can_contra:
            ct, pt, pf = contra[0]
            return _apps(_constant("holdfast_bool_contra"), goal, ct, pt, pf)

        # Check Equalizer-coupled equality/disequality contradiction.
        if can_contra and eq_facts and neg:
            diseqs = [
                (t, neg_p)
                for t, neg_p in neg.items()
                if (sp := self.elab.spine(t))[0].kind == "const"
                and isinstance(sp[0].value, str)
                and len(sp[1]) == 2
                and (sp[0].value in {"eq_nat", "eq_bool", "<==>"} or sp[0].value.startswith("int_eq_"))
            ]
            if diseqs:
                egraph = VersionedEGraph(self.elab)
                for eq_ty, u, v, p in eq_facts:
                    egraph.assert_equality(eq_ty, u, v, p)
                for t, _ in diseqs:
                    _, args = self.elab.spine(t)
                    egraph.intern(args[0])
                    egraph.intern(args[1])
                egraph.saturate_equalizer()
                poly_eq = NatPolyEqualizer(self.elab)
                for t, neg_p in diseqs:
                    dh, da = self.elab.spine(t)
                    u, v = da[0], da[1]
                    if dh == _constant("eq_nat"):
                        eq_p = egraph.explain(_NAT, u, v) or poly_eq.prove_equal_mod_egraph(egraph, u, v)
                        if eq_p is not None:
                            return _apps(_constant("holdfast_nat_eq_contra"), goal, u, v, eq_p, neg_p)
                    elif dh in {_constant("eq_bool"), _constant("<==>")}:
                        if (eq_p := egraph.explain(_BOOL, u, v)) is not None:
                            pos_p = _apps(_constant("holdfast_eq_bool_of_eq"), u, v, eq_p)
                            return _apps(_constant("holdfast_bool_contra"), goal, t, pos_p, neg_p)
                    elif isinstance(dh.value, str) and dh.value.startswith("int_eq_"):
                        spec = _INT_SPECS.get(dh.value[len("int_eq_") :])
                        if spec is not None and (eq_p := egraph.explain(spec.const, u, v)) is not None:
                            return _apps(
                                _constant("holdfast_int_eq_contra"), goal, _term("nat", value=spec.tag), u, v, eq_p, neg_p,
                            )

        def build_goal_direct(expr: _Term, want_true: bool, depth: int = 0) -> _Term | None:
            if depth > 16:
                return None
            r = self.elab.resolve(expr)
            if want_true:
                if r == truth:
                    return _apps(_constant("Refl"), _BOOL, truth)
                if r in pos:
                    return pos[r]
                h, args = self.elab.spine(r)
                if h == _constant("&&") and len(args) == 2:
                    pa = build_goal_direct(args[0], True, depth + 1)
                    pb = build_goal_direct(args[1], True, depth + 1)
                    if pa is not None and pb is not None:
                        return _apps(_constant("holdfast_and_intro"), args[0], args[1], pa, pb)
                if h == _constant("||") and len(args) == 2:
                    if (pa := build_goal_direct(args[0], True, depth + 1)) is not None:
                        return _apps(_constant("holdfast_or_intro_l"), args[0], args[1], pa)
                    if (pb := build_goal_direct(args[1], True, depth + 1)) is not None:
                        return _apps(_constant("holdfast_or_intro_r"), args[0], args[1], pb)
                if h == _constant("!") and len(args) == 1 and (na := build_goal_direct(args[0], False, depth + 1)) is not None:
                    return _apps(_constant("holdfast_not_intro"), args[0], na)
                if h == _constant("==>") and len(args) == 2:
                    if (na := build_goal_direct(args[0], False, depth + 1)) is not None:
                        return _apps(_constant("holdfast_implies_of_false"), args[0], args[1], na)
                    if (pb := build_goal_direct(args[1], True, depth + 1)) is not None:
                        return _apps(_constant("holdfast_implies_of_true"), args[0], args[1], pb)
                if h in {_constant("eq_bool"), _constant("<==>")} and len(args) == 2:
                    a_r, b_r = self.elab.resolve(args[0]), self.elab.resolve(args[1])
                    if a_r in pos and b_r in pos:
                        eq_p = _apps(_constant("Trans"), _BOOL, a_r, truth, b_r, pos[a_r], _apps(_constant("Symm"), _BOOL, b_r, truth, pos[b_r]))
                        return _apps(_constant("holdfast_eq_bool_of_eq"), a_r, b_r, eq_p)
                    if a_r in neg and b_r in neg:
                        eq_p = _apps(_constant("Trans"), _BOOL, a_r, false_t, b_r, neg[a_r], _apps(_constant("Symm"), _BOOL, b_r, false_t, neg[b_r]))
                        return _apps(_constant("holdfast_eq_bool_of_eq"), a_r, b_r, eq_p)
                return None
            if r == false_t:
                return _apps(_constant("Refl"), _BOOL, false_t)
            if r in neg:
                return neg[r]
            h, args = self.elab.spine(r)
            if h == _constant("!") and len(args) == 1 and (pa := build_goal_direct(args[0], True, depth + 1)) is not None:
                z = self.elab.fresh(_BOOL)
                lam = _term("lam", _BOOL, _app(_constant("!"), z), value=cast("int", z.value))
                return _apps(
                    _constant("Trans"),
                    _BOOL,
                    r,
                    _app(_constant("!"), truth),
                    false_t,
                    _apps(_constant("Congr"), _BOOL, _BOOL, args[0], truth, lam, pa),
                    _apps(_constant("Refl"), _BOOL, false_t),
                )
            return None

        goal_eq = self.elab._extract_equality(goal)
        if goal_eq is not None and self.elab.whnf(goal_eq[0]) == _BOOL:
            gl = self.elab.resolve(goal_eq[1])
            gr = self.elab.resolve(goal_eq[2])
            if gr in {truth, false_t}:
                want_true = gr == truth
                if (direct := build_goal_direct(gl, want_true)) is not None:
                    return direct
                skel = self._parse_skel(gl, self.elab.resolve, self.elab.spine)
                return self._prove_tableau(goal, skel, want_true, raw_hyps)
            if gl in {truth, false_t}:
                want_true = gl == truth
                if (direct := build_goal_direct(gr, want_true)) is not None:
                    return _apps(_constant("Symm"), _BOOL, gr, gl, direct)
                flipped = _apps(_constant("Eq"), _BOOL, gr, gl)
                skel = self._parse_skel(gr, self.elab.resolve, self.elab.spine)
                if (tab := self._prove_tableau(flipped, skel, want_true, raw_hyps)) is not None:
                    return _apps(_constant("Symm"), _BOOL, gr, gl, tab)
                return None
            # Propositional equivalence between two bool expressions (e.g. De Morgan).
            eqb_expr = _apps(_constant("eq_bool"), gl, gr)
            eqb_goal = _apps(_constant("Eq"), _BOOL, eqb_expr, truth)
            skel = self._parse_skel(eqb_expr, self.elab.resolve, self.elab.spine)
            if (tab := self._prove_tableau(eqb_goal, skel, True, raw_hyps)) is not None:
                return _apps(_constant("holdfast_eq_bool_true"), gl, gr, tab)
            return None

        # Non-boolean goal: check if boolean hypotheses are unsatisfiable via bounded tableau.
        if raw_hyps:
            return self._prove_tableau(goal, None, None, raw_hyps)
        return None
