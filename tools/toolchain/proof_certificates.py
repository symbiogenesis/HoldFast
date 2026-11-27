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
    _Meta,
    _Term,
    _term,
)

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator

MAX_EGRAPH_NODES = 1024
MAX_EGRAPH_MERGES = 512
MAX_EXPLAIN_STEPS = 128
MAX_INT_ORDER_STEPS = 256


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

        self._parent_trail: list[tuple[int, int]] = []
        self._class_trail: list[tuple[int, int, list[int]]] = []
        self._pclass_trail: list[tuple[int, int, list[int]]] = []
        self._sig_trail: list[tuple[tuple[object, ...], int | None]] = []
        self._adj_trail: list[tuple[int, int]] = []
        self._pnode_trail: list[tuple[int, int]] = []
        self._versions: list[tuple[int, int, int, int, int, int, int, int]] = []

    def push_version(self) -> int:
        """Start a nested e-graph scope whose merges and nodes roll back on pop."""
        self._versions.append((
            len(self.nodes),
            len(self._parent_trail),
            len(self._class_trail),
            len(self._pclass_trail),
            len(self._sig_trail),
            len(self._adj_trail),
            len(self._pnode_trail),
            self.merge_count,
        ))
        return len(self._versions)

    def pop_version(self) -> None:
        """Roll back every node, union, signature entry, and proof edge in the top version."""
        if not self._versions:
            raise ValueError("cannot pop from empty VersionedEGraph version stack")
        (
            n_nodes,
            n_parent,
            n_class,
            n_pclass,
            n_sig,
            n_adj,
            n_pnode,
            old_merges,
        ) = self._versions.pop()
        self.merge_count = old_merges
        while len(self._adj_trail) > n_adj:
            u, v = self._adj_trail.pop()
            self.adj[u].pop()
            self.adj[v].pop()
        while len(self._sig_trail) > n_sig:
            key, old_val = self._sig_trail.pop()
            if old_val is None:
                self.sig_table.pop(key, None)
            else:
                self.sig_table[key] = old_val
        while len(self._pnode_trail) > n_pnode:
            cls_root, _ = self._pnode_trail.pop()
            self.parents_of_class[cls_root].pop()
        while len(self._pclass_trail) > n_pclass:
            kept, merged, old_list = self._pclass_trail.pop()
            if old_list:
                del self.parents_of_class[kept][-len(old_list) :]
            self.parents_of_class[merged] = old_list
        while len(self._class_trail) > n_class:
            kept, merged, old_list = self._class_trail.pop()
            if old_list:
                del self.classes[kept][-len(old_list) :]
            self.classes[merged] = old_list
        while len(self._parent_trail) > n_parent:
            idx, old_p = self._parent_trail.pop()
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

    def _decompose(self, term: _Term) -> tuple[object, tuple[_Term, ...]] | None:
        if term.kind == "app":
            head, args = self.elab.spine(term)
            if args and head.kind not in {"pi", "lam", "let", "fix", "meta"}:
                return ("app", head), tuple(args)
            return None
        if term.kind not in {"pi", "lam", "let", "fix", "meta"} and term.args:
            return (term.kind, term.value), term.args
        return None

    def _set_sig(self, key: tuple[object, ...], nid: int) -> None:
        old = self.sig_table.get(key)
        if old == nid:
            return
        self._sig_trail.append((key, old))
        self.sig_table[key] = nid

    def _add_edge(
        self, u: int, v: int, eq_type: _Term | None, proof: _Term | None,
    ) -> None:
        self.adj[u].append(_ProofEdge(v, eq_type, proof, False))
        self.adj[v].append(_ProofEdge(u, eq_type, proof, True))
        self._adj_trail.append((u, v))

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
                    self._pnode_trail.append((croot, nid))
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
            self._parent_trail.append((rv, self.parent[rv]))
            self.parent[rv] = ru
            merged_members = self.classes.pop(rv)
            self.classes[ru].extend(merged_members)
            self._class_trail.append((ru, rv, merged_members))

            merged_parents = self.parents_of_class.pop(rv, [])
            self.parents_of_class[ru].extend(merged_parents)
            self._pclass_trail.append((ru, rv, merged_parents))

            for pnode in list(self.parents_of_class[ru]):
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
                    saved = [_Meta(m.type, m.scope, m.solution) for m in self.elab.metas]
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
                saved_chk = [_Meta(m.type, m.scope, m.solution) for m in self.elab.metas]
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

    def _explain_congruence(
        self,
        goal_type: _Term,
        lhs: _Term,
        rhs: _Term,
        visited_pairs: set[tuple[int, int]],
    ) -> _Term | None:
        if lhs == rhs:
            return _apps(_constant("Refl"), goal_type, lhs)
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

        def rebuild(args_seq: list[_Term]) -> _Term:
            if is_app and head_term is not None:
                return _apps(head_term, *args_seq)
            return _Term(lhs.kind, lhs.value, tuple(args_seq))

        current_args = list(l_args)
        acc_start: _Term | None = None
        acc_curr: _Term | None = None
        acc_proof: _Term | None = None

        for idx, (a_i, b_i) in enumerate(zip(l_args, r_args, strict=True)):
            if a_i == b_i:
                continue
            saved = [_Meta(m.type, m.scope, m.solution) for m in self.elab.metas]
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

    def find_contradiction(
        self, goal: _Term, environment: dict[str, _Binding], facts: tuple[_Binding, ...], max_joins: int,
    ) -> _Term | None:
        """Detect a positive-weight cycle ``a + k <= a`` (``k >= 1``) and emit a kernel proof of ``goal``."""
        edges = self._harvest_edges(environment, facts)
        if not edges:
            return None
        truth = _term("bool", value=1)
        refl = _apps(_constant("Refl"), _BOOL, truth)
        for edge in edges:
            if edge.src == edge.dst and edge.weight >= 1:
                return _apps(
                    _constant("holdfast_nat_leb_add_contra"),
                    goal,
                    edge.src,
                    _term("nat", value=edge.weight),
                    refl,
                    edge.proof,
                )
        adj: defaultdict[_Term, list[_NatDiffEdge]] = defaultdict(list)
        for edge in edges:
            adj[edge.src].append(edge)
        zero = _term("nat", value=0)
        starts = sorted((n for n in adj if n != zero), key=repr)
        if zero in adj:
            starts.append(zero)
        max_hops = len(adj)
        joins = 0
        for start in starts:
            best: dict[_Term, _NatDiffEdge] = {}
            queue: deque[tuple[_NatDiffEdge, int]] = deque()
            for e in adj[start]:
                prev = best.get(e.dst)
                if prev is None or e.weight > prev.weight:
                    best[e.dst] = e
                    queue.append((e, 1))
            while queue:
                cur, hops = queue.popleft()
                if hops >= max_hops:
                    continue
                for nxt in adj.get(cur.dst, ()):
                    joins += 1
                    if joins > max_joins:
                        return None
                    composed = self._compose_edges(cur, nxt)
                    if composed is None:
                        continue
                    if composed.src == composed.dst and composed.weight >= 1:
                        return _apps(
                            _constant("holdfast_nat_leb_add_contra"),
                            goal,
                            composed.src,
                            _term("nat", value=composed.weight),
                            refl,
                            composed.proof,
                        )
                    prev = best.get(composed.dst)
                    if prev is None or composed.weight > prev.weight:
                        best[composed.dst] = composed
                        queue.append((composed, hops + 1))
        return None

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
        v, _ = self._decompose_nat(raw_rhs)
        adj: defaultdict[_Term, list[_NatDiffEdge]] = defaultdict(list)
        for edge in edges:
            adj[edge.src].append(edge)

        best: dict[_Term, _NatDiffEdge] = {}
        queue: deque[tuple[_NatDiffEdge, int]] = deque()
        refl_u = _NatDiffEdge(u, u, 0, _app(_constant("holdfast_nat_leb_refl"), u))
        if (direct := self._finish_goal(refl_u, raw_lhs, raw_rhs, strict, is_ltb)) is not None:
            return direct
        best[u] = refl_u
        for e in adj.get(u, ()):
            if (done := self._finish_goal(e, raw_lhs, raw_rhs, strict, is_ltb)) is not None:
                return done
            prev = best.get(e.dst)
            if prev is None or e.weight > prev.weight:
                best[e.dst] = e
                queue.append((e, 1))

        max_hops = len(adj)
        joins = 0
        while queue:
            cur, hops = queue.popleft()
            if hops >= max_hops:
                continue
            for nxt in adj.get(cur.dst, ()):
                joins += 1
                if joins > max_joins:
                    return None
                composed = self._compose_edges(cur, nxt)
                if composed is None:
                    continue
                if composed.dst == v and (done := self._finish_goal(
                    composed, raw_lhs, raw_rhs, strict, is_ltb,
                )) is not None:
                    return done
                prev = best.get(composed.dst)
                if prev is None or composed.weight > prev.weight:
                    best[composed.dst] = composed
                    queue.append((composed, hops + 1))
        return None


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
        adj: defaultdict[_Term, list[_IntOrderEdge]] = defaultdict(list)
        for edge in edges:
            adj[edge.src].append(edge)

        # Check direct literal/edge or BFS shortest path.
        seen: dict[_Term, bool] = {}
        queue: deque[_IntOrderEdge] = deque()
        for e in adj.get(lhs, ()):
            if e.dst == rhs and (e.strict or not need_strict):
                return (
                    e.proof
                    if (need_strict or not e.strict)
                    else _apps(_constant("holdfast_int_lt_imp_le"), tag, lhs, rhs, e.proof)
                )
            if e.dst not in seen or (e.strict and not seen[e.dst]):
                seen[e.dst] = e.strict
                queue.append(e)

        steps = 0
        while queue:
            cur = queue.popleft()
            for nxt in adj.get(cur.dst, ()):
                steps += 1
                if steps > max_steps:
                    return None
                composed = self._compose(tag, cur, nxt)
                if composed.dst == rhs and (composed.strict or not need_strict):
                    return (
                        composed.proof
                        if (need_strict or not composed.strict)
                        else _apps(_constant("holdfast_int_lt_imp_le"), tag, lhs, rhs, composed.proof)
                    )
                if composed.dst not in seen or (composed.strict and not seen[composed.dst]):
                    seen[composed.dst] = composed.strict
                    queue.append(composed)
        return None

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
            adj: defaultdict[_Term, list[_IntOrderEdge]] = defaultdict(list)
            for edge in edges:
                adj[edge.src].append(edge)
            steps = 0
            for start in sorted(adj, key=repr):
                seen: dict[_Term, bool] = {}
                queue: deque[_IntOrderEdge] = deque()
                for e in adj[start]:
                    if e.dst == start and e.strict:
                        return _apps(
                            _constant("holdfast_int_lt_le_contra"),
                            goal, tag, start, start, e.proof,
                            _apps(_constant("holdfast_int_le_refl"), tag, start),
                        )
                    if e.dst not in seen or (e.strict and not seen[e.dst]):
                        seen[e.dst] = e.strict
                        queue.append(e)
                while queue:
                    cur = queue.popleft()
                    for nxt in adj.get(cur.dst, ()):
                        steps += 1
                        if steps > max_steps:
                            return None
                        composed = self._compose(tag, cur, nxt)
                        if composed.dst == start and composed.strict:
                            return _apps(
                                _constant("holdfast_int_lt_le_contra"),
                                goal, tag, start, start, composed.proof,
                                _apps(_constant("holdfast_int_le_refl"), tag, start),
                            )
                        if composed.dst not in seen or (composed.strict and not seen[composed.dst]):
                            seen[composed.dst] = composed.strict
                            queue.append(composed)
        return None
