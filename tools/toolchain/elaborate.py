# SPDX-License-Identifier: Apache-2.0
"""Bounded, untrusted elaboration of mathematical HoldFast into CIC terms.

The surface parser owns syntax. This consumer checks its exact-source protocol,
then proposes terms for independent kernel checking; it supplies neither checked
parsing nor an independent source semantics. Vec is a recursive product family,
Fin an indexed inductive, and lookup recurses structurally on the finite index.
"""

import copy
import hashlib
import re
from collections import Counter
from collections.abc import Callable, Sequence
from contextlib import AbstractContextManager, ExitStack, nullcontext
from pathlib import Path
from types import MappingProxyType
from typing import cast

from toolchain import StaticEvaluation, gallina_module_name, graded_source, loans
from toolchain.ast import MAX_SOURCE_BYTES, HoldFastError, ValueType
from toolchain.elaborate_borrows import _BorrowMixin
from toolchain.elaborate_contract_lints import _ContractLintsMixin
from toolchain.elaborate_declarations import _DeclarationsMixin
from toolchain.elaborate_holes import HoleInspection
from toolchain.elaborate_intrinsics import _IntrinsicsMixin
from toolchain.elaborate_patterns import _PatternsMixin
from toolchain.elaborate_proofs import _ProofsMixin
from toolchain.elaborate_protocol import (
    _IDENTIFIER,
    _OPERATORS,
    _Protocol,
)
from toolchain.elaborate_solver import _SolverMixin
from toolchain.elaborate_statements import _StatementsMixin
from toolchain.elaborate_strings import _StringsMixin
from toolchain.elaborate_types import (
    _BOOL,
    _CHAR,
    _INT_SPECS,
    _NAT,
    _NUMERICS_ALIASES,
    _PRELUDE,
    _PROP,
    _SORT,
    _U8,
    _UNIT,
    _USIZE,
    _WORD_REPLAY_PRELUDE,
    MAX_CONSTANT_NAT,
    MAX_DEPTH,
    MAX_NAT_BITS,
    MAX_OUTPUT_BYTES,
    MAX_PATTERN_NAT,
    MAX_REDUCTIONS,
    MAX_STRING_BYTES,
    MAX_UNIVERSE,
    MAX_WORK,
    CheckedElaboration,
    Elaboration,
    GallinaOrigin,
    Node,
    PackageScope,
    _app,
    _apps,
    _Binding,
    _constant,
    _FnContract,
    _ImplInstance,
    _IndexedBorrowPeer,
    _IndexedLocalBorrow,
    _int_term,
    _InterfaceInfo,
    _IntSpec,
    _Meta,
    _parse_numeric_magnitude,
    _RecordField,
    _RecordInfo,
    _Term,
    _term,
    _UnionCtor,
    _UnionInfo,
)
from toolchain.elaborate_whnf import _WhnfMixin
from toolchain.package_navigation import Navigation

FRONTEND_SOURCES = (
    "__init__.py", "ast.py", "authoring.py", "compiler_trace.py", "documentation.py", "facts.py", "remarks.py",
    "hashing.py", "jsonutil.py", "loans.py", "regions.py", "source.py", "trace_runtime.py", "elaborate.py", "elaborate_types.py",
    "elaborate_protocol.py", "elaborate_whnf.py", "elaborate_patterns.py", "elaborate_proofs.py", "elaborate_holes.py",
    "elaborate_statements.py", "elaborate_strings.py", "elaborate_solver.py", "elaborate_intrinsics.py",
    "elaborate_borrows.py", "elaborate_declarations.py", "elaborate_contract_lints.py", "elaborate_descriptor_lints.py",
    "elaborate_flow_lints.py", "elaborate_resource_lints.py", "graded_source.py", "source_file.py",
    "package_navigation.py",
    "proof_certificates.py",
)

__all__ = [
    "MAX_CONSTANT_NAT",
    "MAX_DEPTH",
    "MAX_NAT_BITS",
    "MAX_OUTPUT_BYTES",
    "MAX_PATTERN_NAT",
    "MAX_REDUCTIONS",
    "MAX_STRING_BYTES",
    "MAX_UNIVERSE",
    "MAX_WORK",
    "Elaboration",
    "Node",
    "_Elaborator",
    "_Protocol",
    "_checked_elaboration",
    "elaborate",
    "elaborate_package",
    "evaluate",
]


class _Elaborator(
    _WhnfMixin,
    _BorrowMixin,
    _PatternsMixin,
    _ProofsMixin,
    _StatementsMixin,
    _StringsMixin,
    _SolverMixin,
    _IntrinsicsMixin,
    _ContractLintsMixin,
    _DeclarationsMixin,
):
    def __init__(self, protocol: _Protocol) -> None:
        self.protocol = protocol
        self.hole_inspection: HoleInspection | None = None
        self.navigation: Navigation | None = None
        self.checked_grade_annotations: set[int] = set()
        self.checked_caller_required: dict[str, str] = {}
        self.graded_box_type: str | None = None
        self.graded_box_domain: str | None = None
        self.checked_receivers: dict[tuple[int, ...], loans._Receiver | None] = {}
        self.checked_scalar_calls: set[tuple[int, ...]] = set()
        self.scalar_callables: set[str] = set()
        self.require_word_proofs = False
        self.word_proofs: dict[tuple[int, int, str], str] = {}
        self.inline_assertions: list[tuple[tuple[int, int], str]] = []
        self.contextual_literal_types: dict[int, str] = {}
        self.integer_operations: dict[int, tuple[str, str]] = {}
        self.serial = 0
        self.binder_stride = 1
        self.work = MAX_WORK
        self.reductions = MAX_REDUCTIONS
        self.metas: list[_Meta] = []
        self.decl_first_meta = 0
        self.whnf_cache: dict[int, tuple[_Term, _Term]] = {}
        self.types: dict[int, _Term] = {}
        # Callable parameter labels are source metadata, never CIC constructors.
        self.parameter_names: dict[int, str] = {}
        self.argument_labels: dict[int, str] = {}
        self.constructor_suggestions: dict[int, str] = {}
        self.semantic_lints: dict[tuple[str, int], str] = {}
        self.flow_lint_observations: dict[tuple[str, int], str | None] = {}
        self.out_lint_candidates: dict[tuple[int, int], int] = {}
        self.nullary_parameters: set[int] = set()
        self.constant_parameters: set[int] = set()
        self.readonly_span_vars: set[int] = set()
        self.ref_parameters: set[int] = set()
        self.out_parameters: set[int] = set()
        self.owned_parameters: set[int] = set()
        self.out_param_names: set[str] = set()
        self.uninitialized_out_params: set[str] = set()
        self.callable_ref_updates: dict[str, tuple[tuple[int, ...], dict[int, _Term]]] = {}
        self.callable_source_names: dict[str, str] = {}
        self.declaration_sites: dict[str, int] = {}
        self.call_declarations: dict[int, int] = {}
        self.recursive_declarations: set[int] = set()
        self.callable_has_effects: set[str] = set()
        self.callable_effect_calls: dict[str, set[_Term]] = {}
        self.callable_effect_writes: dict[str, set[int]] = {}
        self.callable_effect_reads: dict[str, set[int]] = {}
        self.callable_callback_effects: dict[str, set[int]] = {}
        self.callable_effect_arities: dict[str, int] = {}
        self.definition_effect_parameters: dict[int, int] | None = None
        self.definition_callback_uses: set[int] = set()
        self.definition_effects_closed = False
        self.inferred_effect_calls: set[_Term] | None = None
        self.runtime_reads: set[str] = set()
        self.runtime_writes: set[str] = set()
        self.result_bindings: dict[int, set[str]] = {}
        self.checked_resource_consumers: set[str] = set()
        self.untracked_effect_functions: set[str] = set()
        self.active_effect_calls: set[_Term] | None = None
        self.callable_ensures: dict[
            str, list[tuple[tuple[int, ...], tuple[tuple[int, int], ...], int | None, _Term]]
        ] = {}
        self.last_call_updates: list[tuple[Node, _Binding, _Term | None]] = []
        self.guard_value = False
        self.static_forbidden: set[int] | None = None
        self.freeze_checks: dict[tuple[str, str, str], None] = {}
        self.freeze_check_bytes = 0
        self.globals: dict[str, _Binding] = {}
        self.constants: dict[str, _Binding] = {}
        self.definitions: dict[str, _Term] = {}
        self.records: dict[str, _RecordInfo] = {}
        self.records_by_type: dict[str, _RecordInfo] = {}
        self.records_by_ctor: dict[str, _RecordInfo] = {}
        self.record_projections: dict[str, tuple[_RecordInfo, int]] = {}
        self.unions: dict[str, _UnionInfo] = {}
        self.unions_by_type: dict[str, _UnionInfo] = {}
        self.union_ctors: dict[str, tuple[_UnionInfo, _UnionCtor]] = {}
        self.unions_by_ctor: dict[str, tuple[_UnionInfo, _UnionCtor]] = {}
        self.interfaces: dict[str, _InterfaceInfo] = {}
        self.impls: dict[str, list[_ImplInstance]] = {}
        self.active_interface_witnesses: dict[tuple[str, tuple[_Term, ...]], dict[str, _Binding]] = {}
        self.active_interface_ensures: dict[tuple[str, tuple[_Term, ...]], dict[str, tuple[tuple[int, ...], tuple[_Term, ...]]]] = {}
        self.callable_where_constraints: dict[str, tuple[tuple[int, ...], tuple[tuple[str, tuple[_Term, ...]], ...]]] = {}
        self.var_preconditions: dict[int, list[tuple[tuple[int, ...], _Term]]] = {}
        self.fn_contracts: dict[int, _FnContract] = {}
        self.expected_call_type: _Term | None = None
        self.module_name: str = ""
        self.package_instance: str | None = None
        self.package_edition = "math-1"
        self.nominal_owners: dict[str, str] = {}
        self.local_instances: list[tuple[str, _ImplInstance]] = []
        self.emission_prefix = "holdfast"
        self.public_symbols: set[str] = set()
        self.internal_symbols: set[str] = set()
        self.sealed_bodies: set[str] = set()
        self.imported_postconditions: dict[str, tuple[str, ...]] = {}
        self.sealed_updates: dict[str, tuple[tuple[int, ...], dict[int, _Term]]] = {}
        self.private_symbols: set[str] = set()
        self.available_modules: dict[str, _Elaborator] = {}
        self.grade_exports: dict[str, graded_source.GradeExport] = {}
        self.imported_modules: set[str] = set()
        self.module_aliases: set[str] = set()
        self.interfaces_by_identity: dict[str, _InterfaceInfo] = {}
        self.inaccessible_private_symbols: dict[str, str] = {}
        self.builtin_unions: set[str] = {"Result", "ArithmeticError", "ConversionError"}
        self.builtin_union_ctors: set[str] = {
            "Err", "Ok", "Overflow", "ZeroDivisor", "InvalidShift", "OutOfRange",
        }
        self.active_facts: list[_Term] = []
        self.callable_preconditions: dict[str, list[tuple[tuple[int, ...], _Term]]] = {}
        self.fix_names: dict[int, str] = {}
        self.current_rec_var: _Term | None = None
        self.current_rec_name: str | None = None
        self.current_rec_generics: list[_Term] = []
        self.current_rec_params: list[_Term] = []
        self.current_rec_witnesses: list[_Term] = []
        self.current_rec_candidates: list[tuple[int, int]] = []
        self.current_rec_used: bool = False
        self.smaller_vars: dict[int, set[int]] = {}
        self.current_return_type: _Term | None = None
        self.mutable_locals: set[str] = set()
        self.entry_env: dict[str, _Binding] = {}
        self.post_env: dict[str, _Binding] = {}
        self.final_ref_bindings: dict[str, _Binding] = {}
        self.final_return_facts: list[_Term] = []
        self.in_post_env_theorem: bool = False
        self.used_domain_solver_in_proof: bool = False
        self.final_theorem_facts: tuple[_Binding, ...] = ()
        self.frozen_collections: set[str] = set()
        self.lifted_invariants: dict[str, set[str]] = {}
        self.active_lift_scopes: int = 0
        self._in_lifted_target_assignment: str | None = None
        self.in_loop_depth: int = 0
        self.active_regions: set[str] = set()
        self.in_executable_function = False
        self.in_inline_proof = False
        self.ghost_parameters: set[int] = set()
        self.specification_values: dict[str, str] = {}
        self.phase_uses: list[tuple[Node, str]] = []
        self.static_effect_sites: list[Node] = []
        self.nonstatic_callables: set[str] = set()
        self.slice_views: dict[str, str] = {}
        self.slice_view_own_updates: dict[str, set[int]] = {}
        self.restored_view_terms: set[_Term] = set()
        self.local_borrows: dict[str, tuple[str, str, tuple[str, ...]]] = {}
        self.indexed_local_borrows: dict[str, _IndexedLocalBorrow] = {}
        self.indexed_borrow_peers: list[_IndexedBorrowPeer] = []
        self.indexed_borrow_serial: int = 0
        self.readonly_in_params: set[str] = set()
        self.pi_hr_regions: dict[int, tuple[frozenset[str], tuple[str | None, ...], str | None]] = {}
        self.var_hr_regions: dict[int, tuple[frozenset[str], tuple[str | None, ...], str | None]] = {}
        self.param_type_regions: dict[int, str] = {}
        self.scoped_term_regions: dict[int, str] = {}
        self.local_value_regions: dict[str, tuple[int, str]] = {}
        self.scoped_hr_regions: set[str] = set()
        self.hr_region_serial: int = 0
        self.active_lambda_outer_mutables: set[str] = set()
        self.output: list[str] = []
        self.site: Node | None = None
        self._init_borrow_state()
        self._builtins()

    def fail(self, kind: str, message: str, node: Node | None = None) -> HoldFastError:
        return self.protocol.error(kind, message, self.site if node is None else node)

    def tick(self, reduction: bool = False) -> None:
        self.work -= 1
        if reduction:
            self.reductions -= 1
        if self.work < 0 or self.reductions < 0:
            raise self.fail("limit", "elaboration work or definitional reduction budget exhausted")

    def fresh(self, value_type: _Term) -> _Term:
        index = self.serial
        self.serial += self.binder_stride
        self.types[index] = value_type
        return _term("var", value=index)

    def restore_metas(self, saved: list[_Meta]) -> None:
        """Restore inference state without retaining reductions from abandoned solutions."""
        unchanged = self.metas == saved
        self.metas = saved
        if not unchanged:
            self.whnf_cache.clear()
        self.decl_first_meta = next(
            (index for index, meta in enumerate(saved) if meta.solution is None), len(saved)
        )

    def pi(self, domain: _Term, codomain: _Term, *, nullary: bool = False) -> _Term:
        variable = self.fresh(domain)
        if nullary:
            self.nullary_parameters.add(cast("int", variable.value))
        return _term("pi", domain, codomain, value=variable.value)

    def _builtins(self) -> None:
        def bind(name: str, value_type: _Term, generics: int = 0) -> None:
            self.globals[name] = _Binding(_constant(name), value_type, generics)
            self.constants[name] = self.globals[name]

        for name in ("Nat", "bool", "char", "Unit"):
            bind(name, _SORT)
        for spec in _INT_SPECS.values():
            bind(spec.name, _SORT)
        self.globals["byte"] = self.globals["u8"]
        for alias_name, target_name in _NUMERICS_ALIASES.items():
            self.globals[f"HoldFast.Numerics.{alias_name}"] = self.globals[target_name]
        bind("Prop", _SORT)
        bind("Succ", self.pi(_NAT, _NAT))
        a = self.fresh(_SORT)
        b = self.fresh(_SORT)
        n = self.fresh(_NAT)
        x = self.fresh(a)
        y = self.fresh(a)
        z = self.fresh(a)

        def telescope(parameters: tuple[_Term, ...], result: _Term) -> _Term:
            for parameter in reversed(parameters):
                result = _term("pi", self.types[cast("int", parameter.value)], result, value=parameter.value)
            return result

        def eq(left: _Term, right: _Term) -> _Term:
            return _apps(_constant("Eq"), a, left, right)

        bind("Eq", telescope((a, x, y), _PROP), 1)
        self.constants["Refl"] = _Binding(_constant("Refl"), telescope((a, x), eq(x, x)), 1)
        self.constants["Symm"] = _Binding(
            _constant("Symm"), telescope((a, x, y), self.pi(eq(x, y), eq(y, x))), 3
        )
        self.constants["Trans"] = _Binding(
            _constant("Trans"), telescope((a, x, y, z), self.pi(eq(x, y), self.pi(eq(y, z), eq(x, z)))), 4
        )
        f = self.fresh(self.pi(a, b))
        congr_result = _apps(_constant("Eq"), b, _app(f, x), _app(f, y))
        self.constants["Congr"] = _Binding(
            _constant("Congr"), telescope((a, b, x, y, f), self.pi(eq(x, y), congr_result)), 4
        )
        bind("Fst", telescope((a, b), self.pi(_term("prod", a, b), a)), 2)
        bind("Snd", telescope((a, b), self.pi(_term("prod", a, b), b)), 2)
        bind("Vec", telescope((a, n), _SORT))
        bind("Fin", telescope((n,), _SORT))
        vec = _apps(_constant("Vec"), a, n)
        fin = _app(_constant("Fin"), n)
        successor = _app(_constant("Succ"), n)
        bind("VNil", telescope((a,), self.pi(_UNIT, _apps(_constant("Vec"), a, _term("nat", value=0)), nullary=True)), 1)
        bind("VCons", telescope((a, n), self.pi(a, self.pi(vec, _apps(_constant("Vec"), a, successor)))), 2)
        bind("FZero", telescope((n,), self.pi(_UNIT, _app(_constant("Fin"), successor), nullary=True)), 1)
        bind("FSucc", telescope((n,), self.pi(fin, _app(_constant("Fin"), successor))), 1)
        bind("At", telescope((a, n), self.pi(vec, self.pi(fin, a))), 2)
        self.constants["FiniteOffset"] = _Binding(
            _constant("FiniteOffset"), telescope((n,), self.pi(_NAT, _app(_constant("Fin"), successor)))
        )
        self.constants["Vec_At_Nat"] = _Binding(
            _constant("Vec_At_Nat"), telescope((a, n), self.pi(a, self.pi(_NAT, self.pi(vec, a)))), 2
        )
        self.constants["Vec_Update"] = _Binding(
            _constant("Vec_Update"), telescope((a, n), self.pi(_NAT, self.pi(a, self.pi(vec, vec)))), 2
        )
        vec_nat = _apps(_constant("Vec"), _NAT, n)
        tb = _app(_constant("TextBuilder"), n)
        bind("ByteLength", telescope((n,), self.pi(vec_nat, _NAT)), 1)
        bind("TextBuilder", telescope((n,), _SORT))
        bind("EmptyBuilder", telescope((n,), self.pi(_UNIT, tb, nullary=True)), 1)
        bind("Fits", telescope((n,), self.pi(tb, _BOOL)), 1)
        bind("Written", telescope((n,), self.pi(tb, _NAT)), 1)
        byte_sequence = _app(_constant("Seq"), _NAT)
        bind("WrittenBytes", telescope((n,), self.pi(tb, byte_sequence)), 1)
        bind("ValidUtf8", self.pi(byte_sequence, _BOOL))
        self.constants["TextBuilderVal"] = _Binding(
            _constant("TextBuilderVal"), telescope((n,), self.pi(_BOOL, self.pi(byte_sequence, tb))), 1
        )
        self.constants["nat_hex_bytes"] = _Binding(
            _constant("nat_hex_bytes"), self.pi(_NAT, self.pi(_BOOL, self.pi(_NAT, byte_sequence)))
        )
        self.constants["FormatStep"] = _Binding(
            _constant("FormatStep"), telescope((n,), self.pi(tb, self.pi(byte_sequence, tb))), 1
        )
        for name in ("+", "*", "-", "/", "%", "Nat.SaturatingSub"):
            bind(name, self.pi(_NAT, self.pi(_NAT, _NAT)))
        self.definitions["Nat.SaturatingSub"] = _constant("-")
        lhs, rhs = self.fresh(_NAT), self.fresh(_NAT)
        nat_binary_arguments = (cast("int", lhs.value), cast("int", rhs.value))
        nonzero = _apps(_constant("ne_nat"), rhs, _term("nat", value=0))
        self.callable_preconditions["-"] = [(nat_binary_arguments, _apps(_constant("<="), rhs, lhs))]
        self.callable_preconditions["/"] = [(nat_binary_arguments, nonzero)]
        self.callable_preconditions["%"] = [(nat_binary_arguments, nonzero)]
        for name in ("<=", "<", ">=", ">"):
            bind(name, self.pi(_NAT, self.pi(_NAT, _BOOL)))
        for name in ("&&", "||", "==>", "<==>"):
            bind(name, self.pi(_BOOL, self.pi(_BOOL, _BOOL)))
        bind("!", self.pi(_BOOL, _BOOL))
        for name, domain in (
            ("eq_nat", _NAT),
            ("ne_nat", _NAT),
            ("eq_bool", _BOOL),
            ("ne_bool", _BOOL),
            ("eq_unit", _UNIT),
            ("ne_unit", _UNIT),
            ("char_eq", _CHAR),
            ("char_ne", _CHAR),
            ("char_lt", _CHAR),
            ("char_le", _CHAR),
            ("char_gt", _CHAR),
            ("char_ge", _CHAR),
        ):
            bind(name, self.pi(domain, self.pi(domain, _BOOL)))
        self.constants["char_to_nat"] = _Binding(_constant("char_to_nat"), self.pi(_CHAR, _NAT))
        self.constants["char_to_u32"] = _Binding(
            _constant("char_to_u32"), self.pi(_CHAR, _INT_SPECS["u32"].const)
        )
        self.constants["char_from_u8"] = _Binding(_constant("char_from_u8"), self.pi(_U8, _CHAR))
        bind("Span", telescope((a,), _SORT))
        span_a = _app(_constant("Span"), a)
        self.constants["Span_Base"] = _Binding(_constant("Span_Base"), telescope((a,), self.pi(span_a, _USIZE)), 1)
        self.constants["Span_Length"] = _Binding(_constant("Span_Length"), telescope((a,), self.pi(span_a, _USIZE)), 1)
        self.constants["Span_Tag"] = _Binding(_constant("Span_Tag"), telescope((a,), self.pi(span_a, _BOOL)), 1)
        self.constants["Span_PermRead"] = _Binding(_constant("Span_PermRead"), telescope((a,), self.pi(span_a, _BOOL)), 1)
        self.constants["Span_PermWrite"] = _Binding(_constant("Span_PermWrite"), telescope((a,), self.pi(span_a, _BOOL)), 1)
        self.constants["Span_CanRead"] = _Binding(_constant("Span_CanRead"), telescope((a,), self.pi(span_a, _BOOL)), 1)
        self.constants["Span_CanWrite"] = _Binding(_constant("Span_CanWrite"), telescope((a,), self.pi(span_a, _BOOL)), 1)
        self.constants["Span_AllocZeroed"] = _Binding(
            _constant("Span_AllocZeroed"),
            telescope((a,), self.pi(_USIZE, self.pi(_USIZE, span_a))),
            1,
        )
        self.constants["Span_ReadOnly"] = _Binding(
            _constant("Span_ReadOnly"),
            telescope((a,), self.pi(span_a, span_a)),
            1,
        )
        self.constants["Span_Invalidate"] = _Binding(
            _constant("Span_Invalidate"),
            telescope((a,), self.pi(span_a, span_a)),
            1,
        )
        self.constants["Span_Disjoint"] = _Binding(
            _constant("Span_Disjoint"),
            telescope((a,), self.pi(span_a, self.pi(span_a, _BOOL))),
            1,
        )
        self.constants["Span_Read"] = _Binding(
            _constant("Span_Read"),
            telescope((a,), self.pi(span_a, self.pi(_USIZE, a))),
            1,
        )
        self.constants["Span_Write"] = _Binding(
            _constant("Span_Write"),
            telescope((a,), self.pi(span_a, self.pi(_USIZE, self.pi(a, span_a)))),
            1,
        )
        self.constants["Span_Fill"] = _Binding(
            _constant("Span_Fill"),
            telescope((a,), self.pi(span_a, self.pi(_USIZE, self.pi(_USIZE, self.pi(a, span_a))))),
            1,
        )
        self.constants["Span_Slice"] = _Binding(
            _constant("Span_Slice"),
            telescope((a,), self.pi(span_a, self.pi(_USIZE, self.pi(_USIZE, span_a)))),
            1,
        )
        self.constants["Span_CopyPrefix"] = _Binding(
            _constant("Span_CopyPrefix"),
            telescope((a,), self.pi(span_a, self.pi(span_a, self.pi(_USIZE, span_a)))),
            1,
        )
        self.constants["Span_Restore"] = _Binding(
            _constant("Span_Restore"),
            telescope((a,), self.pi(span_a, self.pi(span_a, span_a))),
            1,
        )
        self.constants["Span_ReplaceStore"] = _Binding(
            _constant("Span_ReplaceStore"), telescope((a,), self.pi(span_a, self.pi(span_a, span_a))), 1,
        )
        bind("Seq", telescope((a,), _SORT))
        seq_a = _app(_constant("Seq"), a)
        self.constants["Seq_Empty"] = _Binding(_constant("Seq_Empty"), telescope((a,), seq_a), 1)
        self.constants["Seq_Cons"] = _Binding(
            _constant("Seq_Cons"), telescope((a,), self.pi(a, self.pi(seq_a, seq_a))), 1
        )
        self.constants["Seq_Singleton"] = _Binding(
            _constant("Seq_Singleton"), telescope((a,), self.pi(a, seq_a)), 1
        )
        self.constants["Seq_Count"] = _Binding(
            _constant("Seq_Count"), telescope((a,), self.pi(seq_a, _NAT)), 1
        )
        self.constants["Seq_At"] = _Binding(
            _constant("Seq_At"), telescope((a,), self.pi(a, self.pi(seq_a, self.pi(_NAT, a)))), 1
        )
        self.constants["Seq_Update"] = _Binding(
            _constant("Seq_Update"), telescope((a,), self.pi(seq_a, self.pi(_NAT, self.pi(a, seq_a)))), 1
        )
        self.constants["Seq_Append"] = _Binding(
            _constant("Seq_Append"), telescope((a,), self.pi(seq_a, self.pi(seq_a, seq_a))), 1
        )
        self.constants["Seq_Take"] = _Binding(
            _constant("Seq_Take"), telescope((a,), self.pi(seq_a, self.pi(_NAT, seq_a))), 1
        )
        self.constants["Seq_Skip"] = _Binding(
            _constant("Seq_Skip"), telescope((a,), self.pi(seq_a, self.pi(_NAT, seq_a))), 1
        )
        self.constants["Seq_Slice"] = _Binding(
            _constant("Seq_Slice"), telescope((a,), self.pi(seq_a, self.pi(_NAT, self.pi(_NAT, seq_a)))), 1
        )
        self.constants["Seq_All"] = _Binding(
            _constant("Seq_All"), telescope((a,), self.pi(seq_a, self.pi(self.pi(a, _BOOL), _BOOL))), 1
        )
        self.constants["Seq_Any"] = _Binding(
            _constant("Seq_Any"), telescope((a,), self.pi(seq_a, self.pi(self.pi(a, _BOOL), _BOOL))), 1
        )
        self.constants["Seq_Eq"] = _Binding(
            _constant("Seq_Eq"),
            telescope((a,), self.pi(self.pi(a, self.pi(a, _BOOL)), self.pi(seq_a, self.pi(seq_a, _BOOL)))),
            1,
        )
        self.constants["nat_to_usize"] = _Binding(
            _constant("nat_to_usize"), self.pi(_NAT, _USIZE), 0
        )
        self.constants["Vec_Model"] = _Binding(
            _constant("Vec_Model"), telescope((a, n), self.pi(vec, seq_a)), 2
        )
        self.constants["Span_Model"] = _Binding(
            _constant("Span_Model"), telescope((a,), self.pi(span_a, _app(_constant("Seq"), _U8))), 1
        )
        bind("Slots", telescope((a, n), _SORT))
        slots_an = _apps(_constant("Slots"), a, n)
        m = self.fresh(_NAT)
        slots_am = _apps(_constant("Slots"), a, m)
        self.constants["Slots_Mk"] = _Binding(
            _constant("Slots_Mk"),
            telescope(
                (a, n),
                self.pi(
                    _USIZE,
                    self.pi(
                        _USIZE,
                        self.pi(
                            _BOOL,
                            self.pi(_BOOL, self.pi(_BOOL, self.pi(seq_a, self.pi(seq_a, slots_an)))),
                        ),
                    ),
                ),
            ),
            2,
        )
        self.constants["Slots_Capacity"] = _Binding(
            _constant("Slots_Capacity"), telescope((a, n), self.pi(slots_an, _USIZE)), 2
        )
        self.constants["Slots_Base"] = _Binding(
            _constant("Slots_Base"), telescope((a, n), self.pi(slots_an, _USIZE)), 2
        )
        self.constants["Slots_LiveCount"] = _Binding(
            _constant("Slots_LiveCount"), telescope((a, n), self.pi(slots_an, _USIZE)), 2
        )
        self.constants["Slots_Tag"] = _Binding(
            _constant("Slots_Tag"), telescope((a, n), self.pi(slots_an, _BOOL)), 2
        )
        self.constants["Slots_PermRead"] = _Binding(
            _constant("Slots_PermRead"), telescope((a, n), self.pi(slots_an, _BOOL)), 2
        )
        self.constants["Slots_PermWrite"] = _Binding(
            _constant("Slots_PermWrite"), telescope((a, n), self.pi(slots_an, _BOOL)), 2
        )
        self.constants["Slots_CanRead"] = _Binding(
            _constant("Slots_CanRead"), telescope((a, n), self.pi(slots_an, _BOOL)), 2
        )
        self.constants["Slots_CanWrite"] = _Binding(
            _constant("Slots_CanWrite"), telescope((a, n), self.pi(slots_an, _BOOL)), 2
        )
        self.constants["Slots_RepModel"] = _Binding(
            _constant("Slots_RepModel"), telescope((a, n), self.pi(slots_an, seq_a)), 2
        )
        self.constants["Slots_Model"] = _Binding(
            _constant("Slots_Model"), telescope((a, n), self.pi(slots_an, seq_a)), 2
        )
        self.constants["Slots_AllocVacant"] = _Binding(
            _constant("Slots_AllocVacant"), telescope((a, n), self.pi(_USIZE, slots_an)), 2
        )
        self.constants["Slots_Write"] = _Binding(
            _constant("Slots_Write"),
            telescope((a, n), self.pi(slots_an, self.pi(_USIZE, self.pi(a, slots_an)))),
            2,
        )
        self.constants["Slots_Read"] = _Binding(
            _constant("Slots_Read"),
            telescope((a, n), self.pi(a, self.pi(slots_an, self.pi(_USIZE, a)))),
            2,
        )
        self.constants["Slots_LivePrefix"] = _Binding(
            _constant("Slots_LivePrefix"),
            telescope((a, n), self.pi(slots_an, self.pi(_USIZE, _BOOL))),
            2,
        )
        self.constants["Slots_VacantRange"] = _Binding(
            _constant("Slots_VacantRange"),
            telescope((a, n), self.pi(slots_an, self.pi(_USIZE, self.pi(_USIZE, _BOOL)))),
            2,
        )
        self.constants["Slots_Disjoint"] = _Binding(
            _constant("Slots_Disjoint"),
            telescope((a, n, m), self.pi(slots_an, self.pi(slots_am, _BOOL))),
            3,
        )
        self.constants["Slots_RepEqual"] = _Binding(
            _constant("Slots_RepEqual"),
            telescope((a, n, m), self.pi(self.pi(a, self.pi(a, _BOOL)), self.pi(slots_an, self.pi(slots_am, self.pi(_USIZE, _BOOL))))),
            3,
        )
        self.constants["Slots_CopyRepresentation"] = _Binding(
            _constant("Slots_CopyRepresentation"),
            telescope((a, n, m), self.pi(slots_an, self.pi(slots_am, self.pi(_USIZE, slots_am)))),
            3,
        )
        self.constants["Slots_TransferSource"] = _Binding(
            _constant("Slots_TransferSource"),
            telescope((a, n), self.pi(slots_an, self.pi(_USIZE, slots_an))),
            2,
        )
        self.constants["Slots_TransferDest"] = _Binding(
            _constant("Slots_TransferDest"),
            telescope((a, n), self.pi(slots_an, self.pi(_USIZE, slots_an))),
            2,
        )
        self.constants["Slots_TransferType"] = _Binding(
            _constant("Slots_TransferType"),
            telescope(
                (a, n, m),
                self.pi(slots_an, self.pi(slots_am, self.pi(_USIZE, _term("prod", slots_an, slots_am)))),
            ),
            3,
        )
        self.constants["PrefixModel"] = _Binding(
            _constant("PrefixModel"),
            telescope((a, n), self.pi(slots_an, self.pi(_USIZE, seq_a))),
            2,
        )
        self.constants["NatFold"] = _Binding(
            _constant("NatFold"),
            telescope((a,), self.pi(self.pi(_NAT, self.pi(a, a)), self.pi(a, self.pi(_NAT, a)))),
            1,
        )
        self._register_builtin_unions()
        self._register_int_constants()
        self._register_borrow_builtins(bind)

    def _register_builtin_unions(self) -> None:
        # ArithmeticError { Overflow(); ZeroDivisor(); InvalidShift(); }
        ae_type_const = "holdfast_ArithmeticError"
        ae_rep_type = _term("sum", _UNIT, _term("sum", _UNIT, _UNIT))
        ae_type_binding = _Binding(_constant(ae_type_const), _SORT, 0)
        self.globals["ArithmeticError"] = ae_type_binding
        self.constants[ae_type_const] = ae_type_binding
        ae_ctors: list[_UnionCtor] = []
        for idx, cname in enumerate(("Overflow", "ZeroDivisor", "InvalidShift")):
            c_const = f"holdfast_ArithmeticError_{cname}"
            u_var = self.fresh(_UNIT)
            self.nullary_parameters.add(cast("int", u_var.value))
            c_sig = _term("pi", _UNIT, _constant(ae_type_const), value=u_var.value)
            c_binding = _Binding(_constant(c_const), c_sig, 0)
            self.globals[cname] = c_binding
            self.constants[c_const] = c_binding
            ae_ctors.append(_UnionCtor(cname, c_const, c_binding, (), _UNIT, idx))
        ae_info = _UnionInfo(
            "ArithmeticError",
            ae_type_const,
            (),
            tuple(ae_ctors),
            (ae_rep_type, _term("sum", _UNIT, _UNIT), _UNIT),
        )
        self.unions["ArithmeticError"] = ae_info
        self.unions_by_type[ae_type_const] = ae_info
        for uc in ae_ctors:
            self.union_ctors[uc.name] = (ae_info, uc)
            self.unions_by_ctor[uc.ctor_const] = (ae_info, uc)

        # ConversionError { OutOfRange(); }
        ce_type_const = "holdfast_ConversionError"
        ce_type_binding = _Binding(_constant(ce_type_const), _SORT, 0)
        self.globals["ConversionError"] = ce_type_binding
        self.constants[ce_type_const] = ce_type_binding
        oor_const = "holdfast_ConversionError_OutOfRange"
        oor_u = self.fresh(_UNIT)
        self.nullary_parameters.add(cast("int", oor_u.value))
        oor_sig = _term("pi", _UNIT, _constant(ce_type_const), value=oor_u.value)
        oor_binding = _Binding(_constant(oor_const), oor_sig, 0)
        self.globals["OutOfRange"] = oor_binding
        self.constants[oor_const] = oor_binding
        oor_ctor = _UnionCtor("OutOfRange", oor_const, oor_binding, (), _UNIT, 0)
        ce_info = _UnionInfo(
            "ConversionError",
            ce_type_const,
            (),
            (oor_ctor,),
            (_UNIT,),
        )
        self.unions["ConversionError"] = ce_info
        self.unions_by_type[ce_type_const] = ce_info
        self.union_ctors["OutOfRange"] = (ce_info, oor_ctor)
        self.unions_by_ctor[oor_const] = (ce_info, oor_ctor)

        # Result<TValue, TError> { Err(TError Error); Ok(TValue Value); }
        res_type_const = "holdfast_Result"
        tv_var = self.fresh(_SORT)
        te_var = self.fresh(_SORT)
        res_rep = _term("sum", te_var, tv_var)
        res_sig = self.wrap("pi", [tv_var, te_var], _SORT)
        res_type_binding = _Binding(_constant(res_type_const), res_sig, 2)
        self.globals["Result"] = res_type_binding
        self.constants[res_type_const] = res_type_binding
        res_app = _apps(_constant(res_type_const), tv_var, te_var)

        err_fvar = self.fresh(te_var)
        self.parameter_names[cast("int", err_fvar.value)] = "Error"
        err_const = "holdfast_Result_Err"
        err_sig = self.wrap("pi", [tv_var, te_var, err_fvar], res_app)
        err_binding = _Binding(_constant(err_const), err_sig, 2)
        self.globals["Err"] = err_binding
        self.constants[err_const] = err_binding
        err_ctor = _UnionCtor(
            "Err", err_const, err_binding, (_RecordField("Error", err_fvar, te_var, ""),), te_var, 0
        )

        ok_fvar = self.fresh(tv_var)
        self.parameter_names[cast("int", ok_fvar.value)] = "Value"
        ok_const = "holdfast_Result_Ok"
        ok_sig = self.wrap("pi", [tv_var, te_var, ok_fvar], res_app)
        ok_binding = _Binding(_constant(ok_const), ok_sig, 2)
        self.globals["Ok"] = ok_binding
        self.constants[ok_const] = ok_binding
        ok_ctor = _UnionCtor(
            "Ok", ok_const, ok_binding, (_RecordField("Value", ok_fvar, tv_var, ""),), tv_var, 1
        )

        res_info = _UnionInfo(
            "Result",
            res_type_const,
            (tv_var, te_var),
            (err_ctor, ok_ctor),
            (res_rep, tv_var),
            propagation=(1, 0),
        )
        self.unions["Result"] = res_info
        self.unions_by_type[res_type_const] = res_info
        self.union_ctors["Err"] = (res_info, err_ctor)
        self.union_ctors["Ok"] = (res_info, ok_ctor)
        self.unions_by_ctor[err_const] = (res_info, err_ctor)
        self.unions_by_ctor[ok_const] = (res_info, ok_ctor)

    def _register_int_constants(self) -> None:
        ae_const = _constant("holdfast_ArithmeticError")
        ce_const = _constant("holdfast_ConversionError")
        res_const = _constant("holdfast_Result")
        res_char_conv = _apps(res_const, _CHAR, ce_const)
        byte_sequence = _app(_constant("Seq"), _NAT)
        self.constants["char_try_from_u32"] = _Binding(
            _constant("char_try_from_u32"), self.pi(_INT_SPECS["u32"].const, res_char_conv)
        )
        self.constants["char_try_from_Nat"] = _Binding(
            _constant("char_try_from_Nat"), self.pi(_NAT, res_char_conv)
        )
        for spec in _INT_SPECS.values():
            t = spec.const
            res_arith = _apps(res_const, t, ae_const)
            res_conv = _apps(res_const, t, ce_const)
            for op in (
                "add", "sub", "mul", "div", "rem", "and", "or", "xor",
                "wrap_add", "wrap_sub", "wrap_mul", "sat_add", "sat_sub", "sat_mul",
            ):
                cname = f"int_{op}_{spec.name}"
                self.constants[cname] = _Binding(_constant(cname), self.pi(t, self.pi(t, t)))
            for op in ("neg", "not", "wrap_neg", "sat_neg"):
                cname = f"int_{op}_{spec.name}"
                self.constants[cname] = _Binding(_constant(cname), self.pi(t, t))
            for op in ("eq", "ne", "lt", "le", "gt", "ge"):
                cname = f"int_{op}_{spec.name}"
                self.constants[cname] = _Binding(_constant(cname), self.pi(t, self.pi(t, _BOOL)))
            for op in ("shl", "shr", "wrap_shl"):
                cname = f"int_{op}_{spec.name}"
                self.constants[cname] = _Binding(_constant(cname), self.pi(t, self.pi(_USIZE, t)))
            for op in ("chk_add", "chk_sub", "chk_mul", "chk_div", "chk_rem"):
                cname = f"int_{op}_{spec.name}"
                self.constants[cname] = _Binding(_constant(cname), self.pi(t, self.pi(t, res_arith)))
            cname_cneg = f"int_chk_neg_{spec.name}"
            self.constants[cname_cneg] = _Binding(_constant(cname_cneg), self.pi(t, res_arith))
            for op in ("chk_shl", "chk_shr"):
                cname = f"int_{op}_{spec.name}"
                self.constants[cname] = _Binding(_constant(cname), self.pi(t, self.pi(_USIZE, res_arith)))
            hex_bytes = f"int_hex_bytes_{spec.name}"
            self.constants[hex_bytes] = _Binding(
                _constant(hex_bytes), self.pi(_NAT, self.pi(_BOOL, self.pi(t, byte_sequence)))
            )
            cname_nat = f"int_to_nat_{spec.name}"
            self.constants[cname_nat] = _Binding(_constant(cname_nat), self.pi(t, _NAT))
            cname_tf_nat = f"int_try_from_Nat_{spec.name}"
            self.constants[cname_tf_nat] = _Binding(_constant(cname_tf_nat), self.pi(_NAT, res_conv))
            for src in _INT_SPECS.values():
                cname_from = f"int_from_{src.name}_{spec.name}"
                self.constants[cname_from] = _Binding(_constant(cname_from), self.pi(src.const, t))
                cname_tf = f"int_try_from_{src.name}_{spec.name}"
                self.constants[cname_tf] = _Binding(_constant(cname_tf), self.pi(src.const, res_conv))

    def _int_spec(self, type_term: _Term) -> _IntSpec | None:
        resolved = self.whnf(type_term)
        if resolved.kind == "const" and isinstance(resolved.value, str):
            return _INT_SPECS.get(resolved.value)
        return None

    def meta(self, value_type: _Term, environment: dict[str, _Binding]) -> _Term:
        index = len(self.metas)
        scope: set[int] = set()
        for binding in environment.values():
            scope.update(self.free(binding.term))
        self.metas.append(_Meta(value_type, frozenset(scope)))
        return _term("meta", value=index)

    def resolve(self, term: _Term) -> _Term:
        self.tick()
        if term.kind == "meta":
            solution = self.metas[cast("int", term.value)].solution
            if solution is not None:
                return self.resolve(solution)
        return term

    def substitute(
        self,
        term: _Term,
        variable: int,
        replacement: _Term,
        memo: dict[int, tuple[_Term, _Term]] | None = None,
    ) -> _Term:
        if memo is None:
            memo = {}
        tid = id(term)
        if tid in memo:
            return memo[tid][1]
        self.tick()
        resolved = self.resolve(term)
        if resolved.kind == "var" and resolved.value == variable:
            memo[tid] = (term, replacement)
            return replacement
        if resolved.kind in {"pi", "lam"} and resolved.value == variable:
            new_dom = self.substitute(resolved.args[0], variable, replacement, memo)
            res = (
                resolved
                if new_dom is resolved.args[0]
                else _term(resolved.kind, new_dom, resolved.args[1], value=resolved.value)
            )
            memo[tid] = (term, res)
            return res
        if resolved.kind == "let" and resolved.value == variable:
            new_dom = self.substitute(resolved.args[0], variable, replacement, memo)
            new_val = self.substitute(resolved.args[1], variable, replacement, memo)
            res = (
                resolved
                if (new_dom is resolved.args[0] and new_val is resolved.args[1])
                else _term("let", new_dom, new_val, resolved.args[2], value=resolved.value)
            )
            memo[tid] = (term, res)
            return res
        if resolved.kind == "fix" and resolved.value == variable:
            new_sig = self.substitute(resolved.args[0], variable, replacement, memo)
            res = (
                resolved
                if new_sig is resolved.args[0]
                else _term(
                    "fix",
                    new_sig,
                    resolved.args[1],
                    resolved.args[2],
                    resolved.args[3],
                    value=resolved.value,
                )
            )
            memo[tid] = (term, res)
            return res
        if not resolved.args:
            memo[tid] = (term, resolved)
            return resolved
        new_args = tuple(self.substitute(value, variable, replacement, memo) for value in resolved.args)
        if all(na is oa for na, oa in zip(new_args, resolved.args, strict=True)):
            memo[tid] = (term, resolved)
            return resolved
        res = _Term(resolved.kind, resolved.value, new_args)
        memo[tid] = (term, res)
        return res

    def free(
        self, term: _Term, memo: dict[int, tuple[_Term, frozenset[int]]] | None = None
    ) -> set[int]:
        if memo is None:
            memo = {}
        tid = id(term)
        if tid in memo:
            return set(memo[tid][1])
        self.tick()
        term = self.resolve(term)
        if term.kind == "var":
            fset = frozenset({cast("int", term.value)})
            memo[tid] = (term, fset)
            return set(fset)
        result: set[int] = set()
        for argument in term.args:
            result.update(self.free(argument, memo))
        if term.kind in {"pi", "lam", "let", "fix"}:
            result.discard(cast("int", term.value))
        memo[tid] = (term, frozenset(result))
        return result


    def reset_budget(self) -> None:
        self.work = MAX_WORK
        self.reductions = MAX_REDUCTIONS

    def natural_limit(self) -> int:
        return MAX_CONSTANT_NAT if self.static_forbidden is not None else (1 << MAX_NAT_BITS) - 1


    def unify(self, left: _Term, right: _Term) -> None:
        self.tick()
        left, right = self.whnf(left), self.whnf(right)
        if (left.kind == right.kind and left.kind in {"pi", "lam"}
                and (cast("int", left.value) in self.nullary_parameters)
                != (cast("int", right.value) in self.nullary_parameters)):
            raise self.fail("type", "zero-parameter and explicit-parameter callables have different source arities")
        if (left.kind == right.kind and left.kind in {"pi", "lam"}
                and (cast("int", left.value) in self.constant_parameters)
                != (cast("int", right.value) in self.constant_parameters)):
            raise self.fail("type", "callable constant-parameter requirements differ")
        if left.kind == right.kind == "pi" and any(
            (cast("int", left.value) in mode) != (cast("int", right.value) in mode)
            for mode in (self.readonly_span_vars, self.ref_parameters, self.out_parameters, self.owned_parameters)
        ):
            raise self.fail("type", "callable parameter ownership or loan modes differ")
        if (left.kind == right.kind == "pi" and left.value != right.value
                and (cast("int", left.value) in self.fn_contracts or cast("int", right.value) in self.fn_contracts)):
            raise self.fail("unsupported", "adapting higher-order callback contracts requires a direct checked wrapper")
        if left == right:
            return
        # Decimal literals abbreviate constructor chains; expose one successor
        # when an inferred predecessor is constrained by a concrete index.
        for literal, successor in ((left, right), (right, left)):
            if (literal.kind == "nat" and cast("int", literal.value) > 0
                    and successor.kind == "app" and successor.args[0] == _constant("Succ")):
                self.unify(_term("nat", value=cast("int", literal.value) - 1), successor.args[1])
                return
        if right.kind == "meta" and left.kind != "meta":
            left, right = right, left
        if left.kind == "meta":
            index = cast("int", left.value)
            if self.occurs(index, right):
                raise self.fail("type", "infinite type or cyclic dependent inference (occurs check)")
            record = self.metas[index]
            if not self.free(right) <= record.scope:
                raise self.fail("type", "inference would let a local dependent value escape its scope")
            # Narrow nested unsolved variables too: a future solution cannot escape indirectly.
            self.restrict(right, record.scope)
            self.unify(record.type, self.infer(right))
            record.solution = right
            return
        if left.kind != right.kind or left.value != right.value:
            if left.kind == right.kind and left.kind in {"pi", "lam"}:
                self.unify(left.args[0], right.args[0])
                aligned = self.substitute(right.args[1], cast("int", right.value), _term("var", value=left.value))
                self.unify(left.args[1], aligned)
                return
            raise self.fail("type", "terms or dependent indices are not definitionally equal")
        if len(left.args) != len(right.args):
            raise self.fail("type", "incompatible type constructors")
        for first, second in zip(left.args, right.args, strict=True):
            self.unify(first, second)

    def restrict(self, term: _Term, scope: frozenset[int]) -> None:
        term = self.resolve(term)
        if term.kind == "meta":
            record = self.metas[cast("int", term.value)]
            record.scope = record.scope & scope
        for child in term.args:
            self.restrict(child, scope)

    def infer(self, term: _Term) -> _Term:
        self.tick()
        term = self.resolve(term)
        kind = term.kind
        if kind == "meta":
            return self.metas[cast("int", term.value)].type
        if kind == "var":
            return self.types[cast("int", term.value)]
        if kind == "sort":
            return _term("sort", value=max(0, cast("int", term.value) + 1))
        if kind == "const":
            if term.value == "Prop":
                return _SORT
            return self.constants[cast("str", term.value)].type
        if kind == "nat":
            return _NAT
        if kind == "int":
            return term.args[0]
        if kind == "bool":
            return _BOOL
        if kind == "char":
            return _CHAR
        if kind == "unit":
            return _UNIT
        if kind == "static":
            return term.args[0]
        if kind == "let":
            return self.substitute(self.infer(term.args[2]), cast("int", term.value), term.args[1])
        if kind == "pi":
            domain = self.sort(term.args[0])
            result = self.sort(term.args[1])
            return _term("sort", value=-1 if result == -1 else max(domain, result))
        if kind == "lam":
            return _term("pi", term.args[0], self.infer(term.args[1]), value=term.value)
        if kind == "app":
            function_type = self.whnf(self.infer(term.args[0]))
            if function_type.kind != "pi":
                raise self.fail("type", "application requires a function")
            self.unify(self.infer(term.args[1]), function_type.args[0])
            return self.substitute(function_type.args[1], cast("int", function_type.value), term.args[1])
        if kind == "fix":
            return term.args[0]
        if kind in {"prod", "sum"}:
            return _term("sort", value=max(self.sort(term.args[0]), self.sort(term.args[1]), 0))
        if kind == "sigT":
            return _term("sort", value=max(self.sort(term.args[0]), self.sort(term.args[1].args[1]), 0))
        if kind == "pair":
            return _term("prod", term.args[0], term.args[1])
        if kind == "existT":
            return _term("sigT", term.args[0], term.args[1])
        if kind == "projT1":
            return term.args[0]
        if kind == "projT2":
            p1 = _term("projT1", term.args[0], term.args[1], term.args[2])
            return self.substitute(term.args[1].args[1], cast("int", term.args[1].value), p1)
        if kind == "ex":
            self.sort(term.args[0])
            if self.whnf(self.infer(term.args[1].args[1])) != _PROP:
                raise self.fail("type", "existential quantifier body must be a proposition")
            return _PROP
        if kind == "ex_intro":
            return _term("ex", term.args[0], term.args[1])
        if kind in {"inl", "inr"}:
            return _term("sum", term.args[0], term.args[1])
        if kind == "if":
            return term.args[0]
        if kind in {"bool_match", "unit_match", "pair_match", "sigT_match", "nat_match", "sum_match"}:
            return self.substitute(term.args[0].args[1], cast("int", term.args[0].value), term.args[1])
        raise self.fail("type", "cannot infer internal term")

    def sort(self, term: _Term) -> int:
        value_type = self.whnf(self.infer(term))
        if value_type.kind != "sort":
            raise self.fail("type", "expected a type or proposition")
        level = cast("int", value_type.value)
        if level > MAX_UNIVERSE + 1:
            raise self.fail("limit", "universe formation exceeds the supported hierarchy")
        return level

    def node(self, raw: object, kind: str | None = None) -> Node:
        if not isinstance(raw, dict) or not isinstance(raw.get("kind"), str):
            raise self.fail("protocol", "expected a syntax node")
        node = cast("Node", raw)
        if kind is not None and node["kind"] != kind:
            raise self.fail("protocol", f"expected a '{kind}' node", node)
        return node

    def nodes(self, raw: object) -> list[Node]:
        if not isinstance(raw, list):
            raise self.fail("protocol", "expected a syntax-node list")
        return [self.node(value) for value in raw]

    def name(self, raw: object) -> str:
        if (not isinstance(raw, dict) or not isinstance(raw.get("text"), str)
                or not _IDENTIFIER.fullmatch(raw["text"])):
            raise self.fail("protocol", "expected a located name")
        return cast("str", raw["text"])

    def lifetime_name(self, raw: object) -> str:
        if (not isinstance(raw, dict) or not isinstance(raw.get("text"), str)
                or not re.fullmatch(r"'[A-Za-z_][A-Za-z_0-9]*", raw["text"])):
            raise self.fail("protocol", "expected a located region lifetime name")
        return cast("str", raw["text"])

    def _extract_regions(self, generic_nodes: list[Node]) -> tuple[list[Node], set[str]]:
        non_region: list[Node] = []
        regions: set[str] = set()
        for gnode in generic_nodes:
            self.node(gnode, "generic_parameter")
            if gnode["mode"] == "region":
                if gnode["type"] is not None:
                    raise self.fail("protocol", "region generic parameter cannot carry a type bound", gnode)
                rname = self.lifetime_name(gnode["name"])
                if rname in regions or rname == "'_":
                    raise self.fail("name", f"duplicate or invalid region parameter '{rname}'", gnode)
                regions.add(rname)
            else:
                non_region.append(gnode)
        return non_region, regions

    def _term_contains_restored_view(self, term: _Term) -> bool:
        if not self.restored_view_terms:
            return False
        w = self.whnf(term)
        if w in self.restored_view_terms:
            return True
        if w.kind == "app":
            head, args = self.spine(w)
            if head == _constant("Span_Restore") and len(args) == 3:
                return self._term_contains_restored_view(args[1])
            if head in {_constant("Span_Read"), _constant("Span_Length")}:
                return False
        return any(self._term_contains_restored_view(child) for child in w.args)

    def operator(self, raw: object) -> str:
        if not isinstance(raw, dict) or not isinstance(raw.get("text"), str) or raw["text"] not in _OPERATORS:
            raise self.fail("protocol", "expected a supported located operator")
        return cast("str", raw["text"])

    def no_roles(self, node: Node, *roles: str) -> None:
        for role in roles:
            value = node.get(role)
            if role == "grade" and id(node) in self.checked_grade_annotations:
                continue
            if value is not None and value != []:
                raise self.fail("unsupported", f"'{role}' requires the full frontend", node)

    def bind_local(self, environment: dict[str, _Binding], name: str, binding: _Binding) -> None:
        if "." in name or (name != "_" and name in environment):
            raise self.fail("name", f"duplicate or invalid local binding '{name}'")
        if name != "_":
            environment[name] = binding

    def instantiate(self, binding: _Binding, environment: dict[str, _Binding],
                    arguments: list[Node] | None = None) -> _Binding:
        term, value_type = binding.term, binding.type
        if arguments is not None:
            filtered_args: list[Node] = []
            for arg in arguments:
                if arg["kind"] == "lifetime":
                    lt_name = self.lifetime_name(arg["name"])
                    if lt_name != "'_" and lt_name not in self.active_regions:
                        raise self.fail("name", f"unknown region '{lt_name}'", arg)
                else:
                    filtered_args.append(arg)
            arguments = filtered_args
        if arguments is not None and len(arguments) != binding.generics:
            raise self.fail("type", f"expected {binding.generics} explicit generic arguments, got {len(arguments)}")
        for index in range(binding.generics):
            value_type = self.whnf(value_type)
            if value_type.kind != "pi":
                raise self.fail("type", "invalid generic telescope")
            domain = value_type.args[0]
            if arguments is None:
                argument = self.meta(domain, environment)
            else:
                argument = self.argument(arguments[index], domain, environment)
            term = _app(term, argument)
            value_type = self.substitute(value_type.args[1], cast("int", value_type.value), argument)
        return _Binding(term, value_type)

    def lookup(self, name: str, environment: dict[str, _Binding], *, raw: bool = False) -> _Binding:
        binding = environment.get(name, self.globals.get(name))
        if binding is None:
            if name in self.inaccessible_private_symbols:
                mod = self.inaccessible_private_symbols[name]
                raise self.fail("name", f"cannot access private declaration '{name}' of module '{mod}'")
            raise self.fail("name", f"unknown or forward name '{name}'")
        if self.static_forbidden is not None and id(binding) in self.static_forbidden:
            raise self.fail("type", f"constant initializer depends on nonstatic binding '{name}'")
        if (binding.term.kind == "const" and (requirement := self.checked_caller_required.get(str(binding.term.value))) is not None
                and not self.checked_grade_annotations):
            if requirement == "box":
                raise self.fail("grade", f"'{name}' uses a graded Box interface and requires a checked caller")
            raise self.fail("grade", f"'{name}' accepts a graded callback and requires a checked caller")
        if name in self.indexed_local_borrows and self.in_executable_function and not self.in_inline_proof:
            self._check_indexed_local_borrow_access(name, environment, self.site)
        return binding if raw else self.instantiate(binding, environment)

    def argument(self, node: Node, expected: _Term, environment: dict[str, _Binding]) -> _Term:
        self.site = node
        if node["kind"] == "type_argument":
            value = self.type(self.node(node["type"]), environment)
            if self.whnf(expected) == _NAT and self.whnf(self.infer(value)) == _USIZE:
                value = self.whnf(_app(_constant("int_to_nat_usize"), value))
            if self.whnf(expected) == _NAT:
                self._check_dependent_type_no_shared_mut(node, value, environment)
            self.unify(self.infer(value), expected)
            return value
        if node["kind"] in {"type", "function_type", "group_type", "tuple_type", "computed_type"}:
            if node["kind"] == "type" and self.name(node["name"]) == "_" and not self.nodes(node["arguments"]):
                return self.meta(expected, environment)
            value = self.type(node, environment, require_sort=False)
            if self.whnf(expected) == _NAT and self.whnf(self.infer(value)) == _USIZE:
                value = self.whnf(_app(_constant("int_to_nat_usize"), value))
            if self.whnf(expected) == _NAT:
                self._check_dependent_type_no_shared_mut(node, value, environment)
            self.unify(self.infer(value), expected)
            return value
        if self.whnf(expected) == _NAT and not self._is_unsuffixed_int_expr(node):
            expr_b = self.expression(node, environment)
            self._check_dependent_type_no_shared_mut(node, expr_b.term, environment)
            if self.whnf(expr_b.type) == _USIZE:
                return self.whnf(_app(_constant("int_to_nat_usize"), expr_b.term))
            self.unify(expr_b.type, expected)
            return expr_b.term
        checked_val = self.check(node, expected, environment)
        if self.whnf(expected) == _NAT:
            self._check_dependent_type_no_shared_mut(node, checked_val, environment)
        return checked_val

    def static_argument(self, node: Node, expected: _Term, environment: dict[str, _Binding],
                        *, type_syntax: bool = False) -> _Term:
        """Check the complete source dependency graph before reducing an argument."""
        previous = self.static_forbidden
        self.static_forbidden = (set() if previous is None else previous) | {
            id(binding) for binding in environment.values() if not binding.constant}
        try:
            value = self.argument(node, expected, environment) if type_syntax else self.check(node, expected, environment)
            self.complete(value)
            available = set().union(*(self.free(binding.term) for binding in environment.values()
                                      if binding.constant))
            vector = self._static_vector(expected)
            dependencies = self.free(value)
            if vector is not None:
                self._check_freezable_type(expected)
                dependencies.update(self.free(expected))
            self._classify_phase("", node, executable=True)
            if not dependencies <= available:
                raise self.fail("type", "constant parameter requires a static argument", node)
            expected_whnf = self.whnf(expected)
            if vector is not None or self._static_scalar_kind(expected_whnf) is not None:
                marked = _term("static", expected, value)
                return marked if dependencies else self.whnf(marked)
            return value
        finally:
            self.static_forbidden = previous

    def specialize(self, term: _Term, depth: int = 0) -> _Term:
        """Instantiate logical templates while preserving deferred static demands."""
        self.tick(True)
        if depth > MAX_DEPTH:
            raise self.fail("limit", "static specialization exceeds its nesting budget")
        term = self.resolve(term)
        if term.kind == "fix":
            return term
        if term.kind == "let":
            return _term("let", term.args[0], term.args[1], self.specialize(term.args[2], depth + 1), value=term.value)
        if term.kind == "static":
            if not self.free(term):
                return self.whnf(term)
            value = self.specialize(term.args[1], depth + 1)
            marked = _term("static", term.args[0], value)
            return marked if self.free(marked) else self.whnf(marked)
        if term.kind == "const" and term.value in self.definitions:
            if self.definitions[term.value].kind == "fix":
                return term
            return self.specialize(self.definitions[term.value], depth + 1)
        if term.kind == "app":
            function = self.specialize(term.args[0], depth + 1)
            argument = self.specialize(term.args[1], depth + 1)
            if function.kind == "let":
                body = self.specialize(_app(function.args[2], argument), depth + 1)
                return _term("let", function.args[0], function.args[1], body, value=function.value)
            if function.kind == "lam":
                return self.specialize(self.substitute(function.args[1], cast("int", function.value), argument), depth + 1)
            result = _app(function, argument)
            reduced = self.whnf(result)
            return result if reduced == result else self.specialize(reduced, depth + 1)
        specialized = _Term(term.kind, term.value, tuple(self.specialize(child, depth + 1) for child in term.args))
        if term.kind in {"if", "bool_match", "unit_match", "pair_match", "sigT_match", "nat_match", "sum_match", "projT1", "projT2"}:
            reduced = self.whnf(specialized)
            return specialized if reduced == specialized else self.specialize(reduced, depth + 1)
        return specialized

    def _is_result(self, value_type: _Term) -> bool:
        return self.spine(self.whnf(value_type))[0] == _constant("holdfast_Result")

    def _result_paths(self, name: str, value_type: _Term) -> set[str]:
        """Return the verdict obligations transferred by a whole-value use."""
        self.tick()
        value_type = self.whnf(value_type)
        head, args = self.spine(value_type)
        if head == _constant("holdfast_Result"):
            nested = any(self._result_paths("", arg) for arg in args)
            return {name, f"{name}.*"} if nested else {name}
        if value_type.kind == "prod":
            return {path for i, part in enumerate(value_type.args)
                    for path in self._result_paths(f"{name}.{i + 1}", part)}
        if head.kind != "const":
            return set()
        if record := self.records_by_type.get(str(head.value)):
            return {path for field in record.fields for path in self._result_paths(
                f"{name}.{field.name}", self._instantiate_generic_type(record.generic_vars, args, field.type),
            )}
        if union := self.unions_by_type.get(str(head.value)):
            carries = any(self._result_paths(name, self._instantiate_generic_type(union.generic_vars, args, field.type))
                          for ctor in union.constructors for field in ctor.fields)
            return {f"{name}.*"} if carries else set()
        if head.value in {"Vec", "Seq"} and args and self._result_paths(name, args[0]):
            return {f"{name}.*"}
        return set()

    def _owns_fields(self, value_type: _Term) -> bool:
        self.tick()
        value_type = self.whnf(value_type)
        if value_type.kind == "prod":
            return any(self._owns_fields(t) for t in value_type.args)
        head, args = self.spine(value_type)
        if head.kind != "const":
            # An abstract type can be instantiated with an affine aggregate.
            return head.kind in {"var", "meta"}
        name = str(head.value)
        record = self.records_by_type.get(name)
        union = self.unions_by_type.get(name)
        if record is not None:
            params = record.generic_vars
            fields = record.fields
        elif union is not None:
            params = union.generic_vars
            fields = tuple(field for ctor in union.constructors for field in ctor.fields)
        elif name in {"Seq", "Vec"} and args:
            return self._owns_fields(args[0])
        else:
            return False
        return any(cast("int", field.var.value) in self.owned_parameters
                   or self._owns_fields(self._instantiate_generic_type(params, args, field.type)) for field in fields)

    def _check_value_copy(self, source: Node, value_type: _Term) -> None:
        if (self.in_executable_function and self._unwrap_group(source)["kind"] in {"name", "member", "index"}
                and self._owns_fields(value_type)):
            raise self.fail("type", "copying a value with owned fields requires an explicit whole-value move", source)

    def _extract_type_region(self, type_node: Node) -> str | None:
        cur = type_node
        while cur["kind"] in {"group_type", "type_argument"}:
            cur = self.node(cur["type"])
        if cur["kind"] == "modified_type":
            if cur.get("lifetime") is not None:
                lt_node = self.node(cur["lifetime"], "lifetime")
                return self.lifetime_name(lt_node["name"])
            return self._extract_type_region(self.node(cur["type"]))
        if cur["kind"] == "type":
            for arg in self.nodes(cur["arguments"]):
                if arg["kind"] == "lifetime":
                    return self.lifetime_name(arg["name"])
        return None

    def _contains_span_type(self, ty: _Term) -> bool:
        w = self.whnf(ty)
        head, args = self.spine(w)
        if head == _constant("Span"):
            return True
        if head.kind == "const" and isinstance(head.value, str):
            if rinfo := self.records_by_type.get(head.value):
                return any(
                    self._contains_span_type(self._instantiate_record_type(rinfo, args, rf.type))
                    for rf in rinfo.fields
                )
            if union := self.unions_by_type.get(head.value):
                return any(
                    self._contains_span_type(self._instantiate_generic_type(union.generic_vars, args, f.type))
                    for ctor in union.constructors
                    for f in ctor.fields
                )
        return any(self._contains_span_type(arg) for arg in args)

    def _term_hr_region(self, term: _Term, environment: dict[str, _Binding] | None = None) -> str | None:
        if id(term) in self.scoped_term_regions:
            return self.scoped_term_regions[id(term)]
        w = self.whnf(term)
        if id(w) in self.scoped_term_regions:
            return self.scoped_term_regions[id(w)]
        if environment is not None:
            for k, (reg_tid, reg_tag) in self.local_value_regions.items():
                if k in environment and id(environment[k].term) == reg_tid and self.whnf(environment[k].term) == w:
                    return reg_tag
        if w.kind == "if":
            return self._term_hr_region(w.args[2], environment) or self._term_hr_region(w.args[3], environment)
        if w.kind in {"pair", "existT", "inl", "inr"}:
            for child in w.args[2:]:
                if (reg := self._term_hr_region(child, environment)) is not None:
                    return reg
            return None
        head, args = self.spine(w)
        if head in {_constant("Span_ReadOnly"), _constant("Span_Slice"), _constant("Span_Write"),
                    _constant("Span_Fill"), _constant("Span_Restore")} and len(args) >= 2:
            return self._term_hr_region(args[1], environment)
        if head.kind == "const" and isinstance(head.value, str):
            if record := self.records_by_ctor.get(head.value):
                for child in args[len(record.generic_vars):]:
                    if (reg := self._term_hr_region(child, environment)) is not None:
                        return reg
            if union_ctor := self.unions_by_ctor.get(head.value):
                union, _ = union_ctor
                for child in args[len(union.generic_vars):]:
                    if (reg := self._term_hr_region(child, environment)) is not None:
                        return reg
        return None

    def _is_tracked_span_view_call(self, node: Node) -> bool:
        cur = self._unwrap_group(node)
        while cur["kind"] == "call":
            callee = self._unwrap_group(self.node(cur["callee"]))
            path = self._dotted_member_path(callee)
            if path not in {"Span.ReadOnly", "Span.Slice"}:
                return False
            call_args = self.nodes(cur["arguments"])
            if not call_args:
                return False
            first_arg = self._unwrap_group(self.node(call_args[0]["value"]))
            if first_arg["kind"] == "name":
                return True
            if first_arg["kind"] == "call":
                cur = first_arg
                continue
            return False
        return False

    def _check_argument_mode(self, expected: str | None, actual: object, site: Node) -> None:
        marker = "move" if expected == "owned" else expected
        if actual == marker:
            if self.in_inline_proof and marker in {"ref", "shared_ref", "out", "move"}:
                raise self.fail("type", f"an erased proof cannot pass a '{marker}' argument", site)
            if expected == "in" and self.in_executable_function:
                marked = self._unwrap_group(self.node(site["value"]))
                direct = self._unwrap_group(self.node(marked["value"]))
                if not self._is_tracked_span_view_call(direct):
                    place = direct
                    while place["kind"] in {"member", "index"}:
                        place = self._unwrap_group(self.node(place["value"]))
                    if place["kind"] != "name":
                        raise self.fail("type", "an 'in' loan requires a place; bind the value to a local first", marked)
            return
        if expected is not None:
            article = "an" if expected in {"in", "out", "owned"} else "a"
            marker_article = "an" if marker in {"in", "out"} else "a"
            raise self.fail(
                "type", f"{article} '{expected}' parameter requires {marker_article} '{marker}' call-site argument modifier", site
            )
        article = "an" if actual in {"in", "out"} else "a"
        required = "owned" if actual == "move" else actual
        raise self.fail("type", f"'{actual}' call-site argument modifier requires {article} '{required}' parameter", site)

    def _unresolved_effect_call(self, message: str, site: Node | None) -> None:
        if self.definition_effect_parameters is not None:
            self.definition_effects_closed = False
        else:
            raise self.fail("unsupported", message, site)

    def _pure_callback(self, argument: Node, term: _Term) -> bool:
        value = self.resolve(term)
        if value.kind == "const":
            callee = str(value.value)
            arity = self.callable_effect_arities.get(callee)
            if arity is None:
                return False
            result = self.constants[callee].type
            for _ in range(arity):
                result = self.whnf(result).args[1]
            return (self.whnf(result).kind != "pi" and callee in self.callable_has_effects
                    and not self.callable_callback_effects.get(callee, set())
                    and self.callable_effect_calls.get(callee) == set()
                    and self.callable_effect_reads.get(callee) == self.callable_effect_writes.get(callee) == set())
        source = self._unwrap_group(self.node(argument["value"]))
        if source["kind"] not in {"lambda", "typed_lambda"} or value.kind != "lam":
            return False
        params = self.node(source["signature"]) if source["kind"] == "typed_lambda" else source
        names = {self.name(param["name"]) for param in self.nodes(params["parameters"])}
        body = value
        for _ in range(max(1, len(names))):
            if body.kind != "lam":
                return False
            body = body.args[1]
        if self.whnf(self.infer(body)).kind == "pi":
            return False
        pending = [self.node(source["body"])]
        while pending:
            node = self._unwrap_group(pending.pop())
            if node["kind"] == "binary":
                pending.extend((self.node(node["left"]), self.node(node["right"])))
            elif node["kind"] == "unary" and self.operator(node["operator"]) in {"!", "-", "~"}:
                pending.append(self.node(node["value"]))
            elif node["kind"] == "name" and self.name(node["name"]) in names:
                continue
            elif node["kind"] not in {"bool", "character", "nat", "string", "unit"}:
                return False
        return True

    def _call_arity_matches(self, callee: str, supplied: int, arguments: int) -> bool:
        arity = self.callable_effect_arities.get(callee)
        return arity is None or (supplied == self.constants[callee].generics and arguments == arity)

    def _effect_call_name(self, effect: _Term) -> str:
        target, _ = self.spine(effect)
        if target.kind == "var":
            return self.parameter_names.get(cast("int", target.value), "callable parameter")
        name = str(target.value)
        if (projection := self.record_projections.get(name)) is not None:
            record, index = projection
            return record.fields[index].name
        return self.callable_source_names.get(name, name)

    def _check_call_effects(self, head: _Term, prefix: list[_Term], arguments: list[Node],
                            terms: list[_Term], site: Node | None) -> None:
        if site is not None and not self._static_call_permitted(head, arguments, terms):
            if self.static_forbidden is not None:
                raise self.fail("type", "static evaluation requires a call with an empty effect footprint", site)
            self.static_effect_sites.append(site)
        collecting, bound = self.inferred_effect_calls, self.active_effect_calls
        if collecting is None and bound is None:
            return
        if head.kind != "const":
            ident = cast("int", head.value)
            if head.kind == "var" and ident in self.fn_contracts:
                return
            if collecting is not None:
                formals = self.definition_effect_parameters
                if head.kind == "var" and not prefix and formals is not None and ident in formals:
                    self.definition_callback_uses.add(formals[ident])
                else:
                    self._unresolved_effect_call("private helper with a recursive or indirect call needs explicit effects", site)
            elif head != self.current_rec_var and head.kind == "var" and ident in self.parameter_names:
                name = self.parameter_names[ident]
                if bound is not None and head not in bound:
                    raise self.fail("type", f"callable invokes parameter '{name}' not declared in effects calls(...)", site)
            return
        callee = str(head.value)
        name = self.callable_source_names.get(callee, callee)
        if not self._call_arity_matches(callee, len(prefix), len(terms)):
            self._unresolved_effect_call("partial application or invocation of a returned callable needs a closed callable signature", site)
            return
        if collecting is not None and callee in self.callable_source_names and callee not in self.callable_has_effects:
            self._unresolved_effect_call("private effect inference requires a direct callee with closed effects", site)
            return
        named_in_bound = bound is not None and head in bound
        if bound is not None and callee in self.untracked_effect_functions and not named_in_bound:
            raise self.fail("type", f"callable invokes function '{name}' not declared in effects calls(...)", site)
        required = set() if named_in_bound else set(self.callable_effect_calls.get(callee, ()))
        if any(effect.kind == "app" for effect in required):
            # A callable field's effect is relative to this method's receiver.
            signature = self.constants[callee].type
            for actual in prefix:
                signature = self.whnf(signature)
                if signature.kind != "pi":
                    break
                required = {self.substitute(effect, cast("int", signature.value), actual) for effect in required}
                signature = signature.args[1]
        for index in self.callable_callback_effects.get(callee, set()):
            if index >= min(len(arguments), len(terms)):
                self._unresolved_effect_call("partial application or invocation of a returned callable needs a closed callable signature", site)
                return
            if self._pure_callback(arguments[index], terms[index]):
                continue
            actual = self.resolve(terms[index])
            ident = cast("int", actual.value)
            if actual.kind == "var" and self.definition_effect_parameters is not None and ident in self.definition_effect_parameters:
                self.definition_callback_uses.add(self.definition_effect_parameters[ident])
            elif collecting is not None:
                self._unresolved_effect_call("private effect inference requires a callback with closed, empty effects", site)
                return
            elif ((actual.kind == "var" and ident in self.parameter_names)
                  or (actual.kind == "const" and str(actual.value) in self.callable_source_names)):
                required.add(actual)
            else:
                raise self.fail("unsupported", "callback effects require a known callable or a checked pure lambda", site)
        if collecting is not None:
            collecting.update(required)
        if bound is not None and (missing := required - bound):
            target = min(self._effect_call_name(effect) for effect in missing)
            raise self.fail("type", f"callable transitively invokes '{target}' via '{name}' not declared in effects calls(...)", site)

    def _has_static_effects(self, callee: str) -> bool:
        return (callee in self.nonstatic_callables or bool(self.callable_effect_calls.get(callee))
                or bool(self.callable_effect_reads.get(callee)) or bool(self.callable_effect_writes.get(callee)))

    def _deferred_static_callback(self, value: _Term) -> bool:
        if value.kind != "var":
            return False
        index = cast("int", value.value)
        return (index in self.constant_parameters or index in self.fn_contracts or
                (self.definition_effect_parameters is not None and index in self.definition_effect_parameters) or
                (self.active_effect_calls is not None and value in self.active_effect_calls))

    def _static_call_permitted(self, head: _Term, arguments: list[Node], terms: list[_Term]) -> bool:
        if head.kind == "if":
            self.tick()
            return all(self._static_call_permitted(self.spine(self.resolve(arm))[0], arguments, terms)
                       for arm in head.args[2:])
        if head.kind != "const":
            return head.kind == "lam" or head == self.current_rec_var or self._deferred_static_callback(head)
        callee = str(head.value)
        return (not self._has_static_effects(callee)
                and all(index < min(len(arguments), len(terms)) and
                        (self._pure_callback(arguments[index], terms[index])
                         or self._deferred_static_callback(self.resolve(terms[index])))
                        for index in self.callable_callback_effects.get(callee, ())))

    def apply(self, binding: _Binding, arguments: list[Node], environment: dict[str, _Binding]) -> _Binding:
        call_site = self.site
        term, value_type = binding.term, binding.type
        callee_head, callee_gen_args = self.spine(self.resolve(term))
        fnonce_consume: set[str] = set()
        if callee_head.kind == "var":
            cid = cast("int", callee_head.value)
            cname = self.parameter_names.get(cid)
            if cname is None:
                cname = next((k for k, v in environment.items() if v.term == callee_head), None)
            if cname is not None and cname in self.consumed_fnonce_vars:
                raise self.fail(
                    "type",
                    f"cannot invoke 'FnOnce' callable '{cname}' more than once",
                    call_site,
                )
            if self.var_fn_modes.get(cid) == "FnOnce" and cname is not None:
                fnonce_consume.add(cname)
        for env_k, env_b in environment.items():
            if env_b.term == term and env_k in self.consumed_fnonce_vars:
                raise self.fail(
                    "type",
                    f"cannot invoke 'FnOnce' callable '{env_k}' more than once",
                    call_site,
                )
            if (
                env_b.term == term
                and env_b.term.kind == "var"
                and self.var_fn_modes.get(cast("int", env_b.term.value)) == "FnOnce"
            ):
                fnonce_consume.add(env_k)
        init_vt_w = self.whnf(value_type)
        if init_vt_w.kind == "pi" and self.pi_fn_modes.get(cast("int", init_vt_w.value)) == "FnOnce":
            for env_k, env_b in environment.items():
                if env_b.term == callee_head:
                    if env_k in self.consumed_fnonce_vars:
                        raise self.fail(
                            "type",
                            f"cannot invoke 'FnOnce' callable '{env_k}' more than once",
                            call_site,
                        )
                    fnonce_consume.add(env_k)
        self.consumed_fnonce_vars.update(fnonce_consume)
        call_hr_info = (
            self.var_hr_regions.get(cast("int", callee_head.value))
            if callee_head.kind == "var"
            else None
        ) or (
            self.pi_hr_regions.get(cast("int", init_vt_w.value))
            if init_vt_w.kind == "pi"
            else None
        )
        if callee_head.kind == "const" and str(callee_head.value) in self.specification_values and call_site is not None:
            self.phase_uses.append((call_site, self.specification_values[str(callee_head.value)]))
        is_rec_call = (
            self.current_rec_var is not None
            and callee_head == self.current_rec_var
        )
        if (self.in_executable_function or self.inferred_effect_calls is not None) and callee_head.kind == "const":
            for idx in self.callable_effect_reads.get(str(callee_head.value), set()):
                if idx < len(arguments):
                    self._note_runtime_access(arguments[idx], self.runtime_reads)
        specializing = False
        specialized_term = term
        runtime_arguments: list[tuple[_Term, _Term]] = []
        future = self.whnf(value_type)
        protects_runtime = False
        while future.kind == "pi":
            protects_runtime = protects_runtime or cast("int", future.value) in self.constant_parameters
            future = self.whnf(future.args[1])
        val_args: list[_Term] = []
        loan_targets: dict[int, tuple[Node, _Term]] = {}
        indices: dict[int, _Term] = {}
        shared_indices: dict[int, _Term] = {}
        by_value: list[tuple[Node, _Term]] = []
        runtime_domains: list[tuple[Node, _Term, bool]] = []
        seen_loan_names: set[str] = set()
        all_arg_var_names: set[str] = set()
        out_loan_names: set[str] = set()
        if not arguments:
            if is_rec_call:
                raise self.fail("type", f"zero-parameter declaration '{self.current_rec_name}' cannot be structurally recursive")
            value_type = self.whnf(value_type)
            if value_type.kind != "pi" or cast("int", value_type.value) not in self.nullary_parameters:
                raise self.fail("type", "zero-argument call requires a zero-parameter source callable")
            self.unify(value_type.args[0], _UNIT)
            argument = _term("unit")
            val_args.append(argument)
            term = _app(term, argument)
            specialized_term = _app(specialized_term, argument)
            value_type = self.substitute(value_type.args[1], cast("int", value_type.value), argument)
        else:
            labeled = False
            for idx, node in enumerate(arguments):
                self.node(node, "argument")
                label = node["label"]
                if label is None and labeled:
                    raise self.fail("name", "positional arguments cannot follow a named argument", node)
                labeled = labeled or label is not None
                value_type = self.whnf(value_type)
                if value_type.kind == "meta":
                    domain = self.meta(_SORT, environment)
                    variable = self.fresh(domain)
                    result = self.meta(_SORT, environment)
                    self.unify(value_type, _term("pi", domain, result, value=variable.value))
                    value_type = self.whnf(value_type)
                if value_type.kind != "pi":
                    raise self.fail("type", "too many arguments or a non-callable value", node)
                param_var_id = cast("int", value_type.value)
                if param_var_id in self.nullary_parameters:
                    raise self.fail("type", "a zero-parameter callable accepts no explicit arguments", node)
                if label is not None:
                    spelling = self.name(label)
                    expected = self.argument_labels.get(param_var_id, self.parameter_names.get(param_var_id))
                    if expected is None:
                        raise self.fail("name", "unnamed callable parameters do not accept argument labels", node)
                    if spelling != expected:
                        raise self.fail("name", f"expected argument label '{expected}', got '{spelling}'", node)
                is_out_param = param_var_id in self.out_parameters
                is_ref_param = param_var_id in self.ref_parameters
                is_shared_ref_param = param_var_id in self.shared_ref_parameters
                is_owned_param = param_var_id in self.owned_parameters
                is_in_param = param_var_id in self.readonly_span_vars
                arg_val_node = self._unwrap_group(self.node(node["value"]))
                arg_mod = (
                    cast("Node", arg_val_node["operator"]).get("text")
                    if (
                        arg_val_node["kind"] == "unary"
                        and isinstance(arg_val_node.get("operator"), dict)
                        and cast("Node", arg_val_node["operator"]).get("text") in {"ref", "in", "out", "move", "shared_ref"}
                    )
                    else None
                )
                if arg_val_node["kind"] == "out_variable":
                    arg_mod = "out"
                mode = (
                    "out" if is_out_param
                    else "ref" if is_ref_param
                    else "shared_ref" if is_shared_ref_param
                    else "in" if is_in_param
                    else "owned" if is_owned_param
                    else None
                )
                self._check_argument_mode(mode, arg_mod, node)
                if self.out_lint_candidates and is_ref_param and callee_head.kind == "const":
                    # An initialization loan requires a named place at each call.
                    declaration = self.declaration_sites.get(str(callee_head.value))
                    target = self._unwrap_group(self.node(arg_val_node["value"]))
                    if (declaration is not None and target["kind"] != "name"
                            and (candidate := self.out_lint_candidates.pop((declaration, idx), None)) is not None):
                        self.semantic_lints.pop(("HOLDFAST123", candidate), None)
                if mode is None and self.in_executable_function:
                    by_value.append((node, value_type.args[0]))
                if self.in_executable_function:
                    runtime_domains.append((node, value_type.args[0], mode in {None, "owned"}))
                if param_var_id in self.fn_contracts:
                    if arg_val_node["kind"] not in {"name", "member"}:
                        raise self.fail("unsupported", "contracted Fn arguments require a named checked callable", arg_val_node)
                    offered = self._expression(arg_val_node, environment)
                    self.unify(offered.type, value_type.args[0])
                    self._adapt_scalar_callback(self.fn_contracts[param_var_id], offered, environment, node)
                    argument = offered.term
                    required_static = False
                elif arg_val_node["kind"] == "out_variable":
                    argument = self.fresh(value_type.args[0])
                    loan_targets[idx] = (arg_val_node, value_type.args[0])
                    required_static = False
                elif is_ref_param and self._unwrap_group(self.node(arg_val_node["value"]))["kind"] == "index":
                    target = self._unwrap_group(self.node(arg_val_node["value"]))
                    element, indices[idx] = self._indexed_call_loan(target, environment)
                    self.unify(element.type, value_type.args[0])
                    loan_targets[idx] = (target, value_type.args[0])
                    argument = element.term
                    required_static = False
                elif arg_mod == "out":
                    arg_ident_node = self._unwrap_group(self.node(arg_val_node["value"]))
                    if arg_ident_node["kind"] != "name":
                        raise self.fail("type", "'out' argument target must be a mutable local or loan variable", node)
                    arg_vname = self.name(arg_ident_node["name"])
                    if arg_vname not in self.mutable_locals:
                        raise self.fail("type", f"cannot pass immutable binding '{arg_vname}' as an 'out' argument", node)
                    if arg_vname in self.frozen_collections:
                        raise self.fail(
                            "type",
                            f"cannot mutate collection '{arg_vname}' with 'out' while it is traversed by 'foreach'",
                            node,
                        )
                    if arg_vname in all_arg_var_names:
                        raise self.fail("type", f"overlapping loan for '{arg_vname}' in call", node)
                    seen_loan_names.add(arg_vname)
                    all_arg_var_names.add(arg_vname)
                    out_loan_names.add(arg_vname)
                    target_b = self.lookup(arg_vname, environment)
                    self.site = node
                    self.unify(target_b.type, value_type.args[0])
                    argument = target_b.term
                    loan_targets[idx] = (arg_ident_node, value_type.args[0])
                    required_static = False
                else:
                    arg_ident_node = (
                        self._unwrap_group(self.node(arg_val_node["value"]))
                        if arg_mod in {"ref", "in", "move", "shared_ref"}
                        else arg_val_node
                    )
                    if is_ref_param and arg_ident_node["kind"] != "name":
                        if self._is_tracked_span_view_call(arg_ident_node):
                            pass
                        else:
                            self._resolve_local_borrow_target("ref", arg_ident_node, environment, node)
                            loan_targets[idx] = (arg_ident_node, value_type.args[0])
                    elif is_shared_ref_param and arg_ident_node["kind"] != "name":
                        self._resolve_local_borrow_target("shared_ref", arg_ident_node, environment, node)
                        loan_targets[idx] = (arg_ident_node, value_type.args[0])
                    if arg_ident_node["kind"] == "name":
                        arg_vname = self.name(arg_ident_node["name"])
                        lifted_set = self.lifted_invariants.get(arg_vname)
                        if lifted_set is not None and len(lifted_set) > 0:
                            clause_n = min(lifted_set)
                            raise self.fail(
                                "type",
                                f"cannot pass record '{arg_vname}' to a callable while invariant '{clause_n}' is lifted",
                                node,
                            )
                        if is_shared_ref_param or arg_mod == "shared_ref":
                            if arg_vname in self.readonly_in_params or self._is_readonly_span(environment[arg_vname].term):
                                raise self.fail("type", f"cannot take 'shared ref' borrow of read-only 'in' parameter '{arg_vname}'", node)
                            if arg_vname not in self.mutable_locals and arg_vname not in self.shared_ref_locals:
                                raise self.fail("type", f"cannot pass immutable binding '{arg_vname}' as a 'shared ref' argument", node)
                            seen_loan_names.add(arg_vname)
                            loan_targets[idx] = (arg_ident_node, value_type.args[0])
                        elif is_ref_param or arg_mod == "ref":
                            if arg_vname in self.indexed_local_borrows and self.indexed_local_borrows[arg_vname].mode != "ref":
                                raise self.fail(
                                    "type",
                                    f"cannot borrow shared 'in' borrow '{arg_vname}' as exclusive 'ref' (write-through-shared)",
                                    node,
                                )
                            if arg_vname in self.shared_ref_locals and arg_vname not in self.mutable_locals:
                                raise self.fail(
                                    "type",
                                    f"cannot borrow 'shared ref' binding '{arg_vname}' as exclusive 'ref' (exclusive-from-shared)",
                                    node,
                                )
                            if arg_vname not in self.mutable_locals:
                                raise self.fail("type", f"cannot pass immutable binding '{arg_vname}' as a 'ref' argument", node)
                            if arg_vname in self.frozen_collections:
                                raise self.fail(
                                    "type",
                                    f"cannot mutate collection '{arg_vname}' with 'ref' while it is traversed by 'foreach'",
                                    node,
                                )
                            if arg_vname in all_arg_var_names:
                                raise self.fail("type", f"overlapping loan for '{arg_vname}' in call", node)
                            seen_loan_names.add(arg_vname)
                            loan_targets[idx] = (arg_ident_node, value_type.args[0])
                        elif arg_mod == "move":
                            if arg_vname in all_arg_var_names:
                                raise self.fail(
                                    "type",
                                    f"cannot use or borrow '{arg_vname}' after it was moved in the same call (use-after-owner-move)",
                                    node,
                                )
                            seen_loan_names.add(arg_vname)
                        elif arg_vname in seen_loan_names:
                            raise self.fail("type", f"overlapping loan for '{arg_vname}' in call", node)
                        if not (is_shared_ref_param or arg_mod == "shared_ref"):
                            all_arg_var_names.add(arg_vname)
                    required_static = param_var_id in self.constant_parameters
                    checker = self.static_argument if required_static else self.check
                    check_target = (
                        arg_ident_node
                        if arg_mod in {"ref", "in", "shared_ref"} and arg_ident_node is not arg_val_node
                        else self.node(node["value"])
                    )
                    if arg_mod in {"in", "ref", "shared_ref"}:
                        if (arg_mod in {"in", "shared_ref"} and check_target["kind"] == "index"
                                and self._unwrap_group(self.node(check_target["value"]))["kind"] == "name"):
                            borrowed, index = self._read_indexed_place(check_target, environment)
                            shared_indices[idx] = index.term
                        else:
                            borrowed = self.expression(check_target, environment)
                        self.unify(borrowed.type, value_type.args[0])
                        argument = borrowed.term
                    else:
                        argument = checker(check_target, value_type.args[0], environment)
                val_args.append(argument)
                specializing = specializing or required_static
                if required_static:
                    specialized_term = _app(specialized_term, argument)
                elif protects_runtime:
                    variable = self.fresh(value_type.args[0])
                    runtime_arguments.append((variable, argument))
                    specialized_term = _app(specialized_term, variable)
                else:
                    specialized_term = _app(specialized_term, argument)
                term = _app(term, argument)
                value_type = self.substitute(value_type.args[1], param_var_id, argument)
        self._check_indexed_call_loans(arguments, indices, shared_indices, environment)
        self._check_slice_argument_overlap(arguments, val_args, environment)
        for arg_node, arg_type in by_value:
            if self._owns_fields(arg_type):
                raise self.fail("type", "passing a value with owned fields requires an owned parameter and explicit move", arg_node)
        if self.in_executable_function:
            callee = str(callee_head.value)
            constructor = callee_head.kind == "const" and (callee in self.records_by_ctor or callee in self.unions_by_ctor)
            if not constructor:
                checked = is_rec_call or (callee_head.kind == "const" and callee in self.checked_resource_consumers)
                if not checked and self._owns_fields(value_type):
                    raise self.fail("type", "an affine result requires a callee checked for executable ownership", call_site)
                for site, domain, transfers in runtime_domains:
                    if not checked and self._owns_fields(domain):
                        raise self.fail("type", "an affine argument requires a callee checked for executable ownership", site)
                    if transfers and self._result_paths("", domain) and (not checked
                            or any(self._result_paths("", arg) for arg in callee_gen_args)):
                        raise self.fail("type", "unexamined Result passed to a callable without a checked verdict parameter", site)
        if (
            callee_head.kind == "const"
            and isinstance(callee_head.value, str)
            and callee_head.value in self.records_by_ctor
        ):
            rinfo = self.records_by_ctor[callee_head.value]
            self._check_record_invariants(rinfo, callee_gen_args, term, environment, call_site)
        if callee_head.kind == "const" and callee_head.value in self.callable_preconditions:
            full_args = callee_gen_args + val_args
            for param_ids, req_term in self.callable_preconditions[callee_head.value]:
                if len(full_args) >= len(param_ids):
                    inst_req = req_term
                    for pid, arg_val in zip(param_ids, full_args, strict=False):
                        inst_req = self.substitute(inst_req, pid, arg_val)
                    self._check_precondition_term(inst_req, environment, call_site)
        if callee_head.kind == "var" and cast("int", callee_head.value) in self.var_preconditions:
            full_args_v = callee_gen_args + val_args
            for param_ids, req_term in self.var_preconditions[cast("int", callee_head.value)]:
                if len(full_args_v) >= len(param_ids):
                    inst_req = req_term
                    for pid, arg_val in zip(param_ids, full_args_v, strict=False):
                        inst_req = self.substitute(inst_req, pid, arg_val)
                    self._check_precondition_term(inst_req, environment, call_site)
        if (
            callee_head.kind == "const"
            and isinstance(callee_head.value, str)
            and callee_head.value in self.callable_where_constraints
        ):
            _, w_specs = self.callable_where_constraints[callee_head.value]
            if self.expected_call_type is not None:
                peek_type = value_type
                for _ in w_specs:
                    peek_w = self.whnf(peek_type)
                    if peek_w.kind == "pi":
                        peek_type = peek_w.args[1]
                self._try_unify(peek_type, self.expected_call_type)
            witness_terms = self._resolve_interface_witnesses(
                callee_head.value, callee_gen_args + val_args, environment, call_site
            )
            for w_term in witness_terms:
                value_type = self.whnf(value_type)
                if value_type.kind != "pi":
                    raise self.fail("type", "invalid interface witness telescope", call_site)
                self.unify(self.infer(w_term), value_type.args[0])
                term = _app(term, w_term)
                specialized_term = _app(specialized_term, w_term)
                value_type = self.substitute(value_type.args[1], cast("int", value_type.value), w_term)
        elif is_rec_call and self.current_rec_witnesses:
            for w_term in self.current_rec_witnesses:
                value_type = self.whnf(value_type)
                if value_type.kind != "pi":
                    raise self.fail("type", "invalid recursive interface witness telescope", call_site)
                self.unify(self.infer(w_term), value_type.args[0])
                term = _app(term, w_term)
                specialized_term = _app(specialized_term, w_term)
                value_type = self.substitute(value_type.args[1], cast("int", value_type.value), w_term)
        for vname in out_loan_names:
            self.uninitialized_out_params.discard(vname)
        if (
            self.in_post_env_theorem
            and not protects_runtime
            and callee_head.kind == "const"
            and isinstance(callee_head.value, str)
            and callee_head.value in self.definitions
            and not self._is_prop_type(value_type)
        ):
            term = self._simplify_term_with_facts(term, environment)
        post_loan_terms: dict[int, _Term] = {}
        if loan_targets:
            full_args = callee_gen_args + val_args
            u_param_ids: tuple[int, ...] = ()
            idx_to_term: dict[int, _Term] = {}
            signature_writes = None
            callee = str(callee_head.value)
            is_ctor = callee_head.kind == "const" and (
                callee in self.records_by_ctor or callee in self.unions_by_ctor
            )
            if callee_head.kind == "const" and self._call_arity_matches(callee, len(callee_gen_args), len(val_args)):
                u_param_ids, idx_to_term = self.callable_ref_updates.get(callee, ((), {}))
                signature_writes = set() if is_ctor else self.callable_effect_writes.get(callee)
            for idx, (t_node, t_dom) in loan_targets.items():
                writes = signature_writes is None or idx in signature_writes
                if not writes:
                    upd_term = val_args[idx]
                elif idx in idx_to_term and len(full_args) >= len(u_param_ids):
                    upd_term = idx_to_term[idx]
                    for pid, aval in zip(u_param_ids, full_args, strict=False):
                        upd_term = self.substitute(upd_term, pid, aval)
                    if self.in_post_env_theorem:
                        upd_term = self._simplify_term_with_facts(upd_term, environment)
                elif t_node["kind"] == "out_variable":
                    raise self.fail("unsupported", "'out var' requires a checked callee output value", t_node)
                else:
                    upd_term = self.fresh(t_dom)
                post_loan_terms[idx] = upd_term
                self._record_call_update(t_node, _Binding(upd_term, t_dom), writes=writes, index=indices.get(idx))
        if (
            callee_head.kind == "const"
            and isinstance(callee_head.value, str)
            and callee_head.value in self.callable_ensures
        ):
            full_args = callee_gen_args + val_args
            for e_param_ids, post_loan_pairs, res_var_id, ens_term in self.callable_ensures[callee_head.value]:
                if len(full_args) >= len(e_param_ids):
                    inst_ens = ens_term
                    for pid, aval in zip(e_param_ids, full_args, strict=False):
                        inst_ens = self.substitute(inst_ens, pid, aval)
                    if res_var_id is not None:
                        inst_ens = self.substitute(inst_ens, res_var_id, term)
                    for p_idx, post_vid in post_loan_pairs:
                        replacement = post_loan_terms.get(
                            p_idx, val_args[p_idx] if p_idx < len(val_args) else _term("var", value=post_vid)
                        )
                        inst_ens = self.substitute(inst_ens, post_vid, replacement)
                    if self.whnf(inst_ens) != _term("bool", value=1):
                        self.active_facts.append(inst_ens)
        if callee_head.kind == "var" and (contract := self.fn_contracts.get(cast("int", callee_head.value))) is not None:
            for post in contract.ensures:
                fact = self.substitute(post, contract.argument, val_args[0])
                self.active_facts.append(self.substitute(fact, contract.result, term))
        self._check_call_effects(callee_head, callee_gen_args, arguments, val_args, call_site)
        if is_rec_call:
            self.current_rec_used = True
            if len(callee_gen_args) != len(self.current_rec_generics):
                raise self.fail("type", "recursive call requires full generic instantiation")
            for g_arg, g_param in zip(callee_gen_args, self.current_rec_generics, strict=True):
                if not self._try_unify(g_arg, g_param):
                    raise self.fail("type", "polymorphic recursion with varying generic arguments is not supported")
            if len(val_args) != len(self.current_rec_params) or not self.current_rec_params:
                raise self.fail("type", f"recursive call to '{self.current_rec_name}' must supply all parameters")
            decreasing_indices = {
                i
                for i, pv in enumerate(self.current_rec_params)
                if (
                    self.resolve(val_args[i]).kind == "var"
                    and cast("int", self.resolve(val_args[i]).value)
                    in self.smaller_vars.get(cast("int", pv.value), set())
                )
            }
            self.current_rec_candidates = [
                (p_idx, p_var_id)
                for p_idx, p_var_id in self.current_rec_candidates
                if p_idx in decreasing_indices
            ]
            if not self.current_rec_candidates:
                raise self.fail(
                    "type",
                    f"recursive call to '{self.current_rec_name}' must pass a structurally smaller pattern binder for its decreasing parameter",
                )
        if protects_runtime:
            term = self.specialize(specialized_term) if specializing else specialized_term
            for variable, argument in reversed(runtime_arguments):
                term = _term("let", self.types[cast("int", variable.value)], argument, term, value=variable.value)
        if callee_head.kind == "const" and isinstance(callee_head.value, str) and call_site is not None:
            mapped_ret_reg, has_prophecy_ret = self._check_call_regions(
                callee_head.value, arguments, environment, call_site
            )
            if mapped_ret_reg is not None:
                self.scoped_term_regions[id(term)] = mapped_ret_reg
            if has_prophecy_ret:
                sig = self.fn_region_signatures[callee_head.value]
                prop_owners: list[str] = []
                for pidx in sig.prophecy_param_indices:
                    if pidx < len(arguments):
                        an = self._unwrap_group(self.node(arguments[pidx]["value"]))
                        if (
                            an["kind"] == "unary"
                            and isinstance(an.get("operator"), dict)
                            and cast("Node", an["operator"]).get("text") == "ref"
                        ):
                            an = self._unwrap_group(self.node(an["value"]))
                        if an["kind"] == "name":
                            prop_owners.append(self.name(an["name"]))
                if prop_owners:
                    vt_head, _ = self.spine(self.whnf(value_type))
                    is_res_wrapped = vt_head == _constant("holdfast_Result")
                    self._record_prophecy_call_result(term, value_type, tuple(prop_owners), is_res_wrapped)
        if call_hr_info is not None:
            hr_regions, _, hr_result_region = call_hr_info
            if hr_result_region is not None and hr_result_region in hr_regions:
                self.hr_region_serial += 1
                hr_tag = f"__hr_{self.hr_region_serial}"
                self.scoped_hr_regions.add(hr_tag)
                self.scoped_term_regions[id(term)] = hr_tag
        return _Binding(term, value_type)

    def _scalar_callback_contract(self, node: Node, domain: _Term) -> _FnContract:
        parameters = self.nodes(node["parameters"])
        effects = self.nodes(node["effects"])
        if (len(parameters) != 1 or parameters[0]["name"] is None or node["generics"]
                or self.node(parameters[0]["type"])["kind"] == "modified_type" or parameters[0].get("const")
                or any(t not in {_NAT, _BOOL, _CHAR} and self._int_spec(t) is None for t in domain.args)):
            raise self.fail("unsupported", "contracted Fn requires one named scalar value parameter and a scalar result", node)
        if (len(effects) != 1 or effects[0]["kind"] != "type"
                or self.name(effects[0]["name"]) != "none" or effects[0]["arguments"]):
            raise self.fail("unsupported", "contracted Fn parameters require an explicit effects(none) bound", node)
        name = self.name(parameters[0]["name"])
        if name == "result":
            raise self.fail("name", "contracted Fn reserves 'result' for its postcondition", parameters[0])
        argument = cast("int", domain.value)
        env = {name: _Binding(_term("var", value=argument), domain.args[0])}
        result = self.fresh(domain.args[1])
        pre: list[_Term] = []
        post: list[_Term] = []
        for clause in self.nodes(node["contracts"]):
            if clause["role"] not in {"requires", "ensures"}:
                raise self.fail("unsupported", "contracted Fn supports requires and ensures", clause)
            pred = self.node(clause["value"])
            pending = [pred]
            while pending:
                part = self._unwrap_group(pending.pop())
                if part["kind"] == "binary":
                    pending.extend((self.node(part["left"]), self.node(part["right"])))
                elif part["kind"] == "unary" and self.operator(part["operator"]) == "!":
                    pending.append(self.node(part["value"]))
                elif part["kind"] == "name" and self.name(part["name"]) not in (
                    {name, "result"} if clause["role"] == "ensures" else {name}
                ):
                    raise self.fail("unsupported", "contracted Fn predicates may name only their argument and result", part)
                elif part["kind"] not in {"name", "bool", "nat", "character"}:
                    raise self.fail("unsupported", "contracted Fn predicates require scalar expressions", part)
            if clause["role"] == "requires":
                pre.append(self.check(pred, _BOOL, env))
            else:
                post.append(self.check(pred, _BOOL, {**env, "result": _Binding(result, domain.args[1])}))
        return _FnContract(argument, cast("int", result.value), tuple(pre), tuple(post))

    def _adapt_scalar_callback(self, wanted: _FnContract, offered: _Binding,
                               environment: dict[str, _Binding], site: Node) -> None:
        term = self.resolve(offered.term)
        signature = self.whnf(offered.type)
        x, y = (self.fresh(t) for t in signature.args)
        if term.kind == "var" and (formal := self.fn_contracts.get(cast("int", term.value))) is not None:
            given_pre = [self.substitute(p, formal.argument, x) for p in formal.requires]
            given_post = [self.substitute(self.substitute(p, formal.argument, x), formal.result, y) for p in formal.ensures]
        elif term.kind == "const" and self._pure_callback(site, term):
            given_pre = [self.substitute(p, ids[0], x) for ids, p in self.callable_preconditions.get(str(term.value), [])]
            given_post = []
            for ids, _, result_id, p in self.callable_ensures.get(str(term.value), []):
                fact = self.substitute(p, ids[0], x)
                given_post.append(fact if result_id is None else self.substitute(fact, result_id, y))
        else:
            raise self.fail("type", "callback must have a checked effects(none) bound", site)
        old_facts = self.active_facts
        self.active_facts = [*old_facts, *(self.substitute(p, wanted.argument, x) for p in wanted.requires)]
        try:
            for p in given_pre:
                self._check_precondition_term(p, environment, site)
            self.active_facts.extend(given_post)
            for p in wanted.ensures:
                goal = self.substitute(self.substitute(p, wanted.argument, x), wanted.result, y)
                if not self._prove_bool_precondition(goal, environment):
                    raise self.fail("type", "callback guarantees do not establish the required Fn postcondition", site)
        finally:
            self.active_facts = old_facts

    def telescope(self, generic_nodes: list[Node], parameter_nodes: list[Node],
                  environment: dict[str, _Binding], *, unit: bool = False,
                  callback_contracts: bool = False) -> tuple[list[_Term], dict[str, _Binding]]:
        extended = dict(environment)
        variables: list[_Term] = []
        for node in generic_nodes:
            self.site = node
            self.node(node, "generic_parameter")
            mode = node["mode"]
            if mode == "region":
                if node["type"] is not None:
                    raise self.fail("protocol", "region generic parameter cannot carry a type bound", node)
                rname = self.lifetime_name(node["name"])
                if rname == "'_":
                    raise self.fail("name", f"invalid region parameter '{rname}'", node)
                self.active_regions.add(rname)
                continue
            checked_grade = mode == "grade" and id(node) in self.checked_grade_annotations
            if not checked_grade and (not isinstance(mode, str) or mode not in {"type", "ghost"}):
                raise self.fail("unsupported", f"generic mode '{mode}' requires the full frontend")
            if mode == "ghost" and node["type"] is None:
                raise self.fail("protocol", "ghost binder lacks its type")
            domain = (_NAT if checked_grade else _SORT if node["type"] is None
                      else self.type(self.node(node["type"]), extended))
            if mode == "type" and self.whnf(domain).kind != "sort":
                raise self.fail("type", "a type generic requires a universe kind")
            variable = self.fresh(domain)
            if mode == "ghost" or checked_grade:
                self.ghost_parameters.add(cast("int", variable.value))
            variables.append(variable)
            self.bind_local(extended, self.name(node["name"]), _Binding(variable, domain))
        used_labels: set[str] = set()
        for node in parameter_nodes:
            self.site = node
            if node["kind"] != "parameter":
                raise self.fail("protocol", "invalid parameter role")
            self.no_roles(node, "grade")
            param_type_node = self.node(node["type"])
            is_readonly_span = (
                param_type_node["kind"] == "modified_type"
                and param_type_node.get("modifier") == "in"
            )
            is_ref_param = (
                param_type_node["kind"] == "modified_type"
                and param_type_node.get("modifier") == "ref"
            )
            is_shared_ref_param = (
                param_type_node["kind"] == "modified_type"
                and param_type_node.get("modifier") == "shared_ref"
            )
            is_out_param = (
                param_type_node["kind"] == "modified_type"
                and param_type_node.get("modifier") == "out"
            )
            is_owned_param = (
                param_type_node["kind"] == "modified_type"
                and param_type_node.get("modifier") == "owned"
            )
            annotated_fn = (callback_contracts and param_type_node["kind"] == "function_type"
                            and bool(param_type_node["effects"] or param_type_node["contracts"]))
            source_type = {**param_type_node, "effects": [], "contracts": []} if annotated_fn else param_type_node
            domain = self.type(source_type, extended, allow_out=True)
            variable = self.fresh(domain)
            dom_w = self.whnf(domain)
            if dom_w.kind == "pi":
                if cast("int", dom_w.value) in self.pi_hr_regions:
                    self.var_hr_regions[cast("int", variable.value)] = self.pi_hr_regions[cast("int", dom_w.value)]
                if cast("int", dom_w.value) in self.pi_fn_modes:
                    self.var_fn_modes[cast("int", variable.value)] = self.pi_fn_modes[cast("int", dom_w.value)]
            if (p_reg := self._extract_type_region(param_type_node)) is not None:
                self.param_type_regions[cast("int", variable.value)] = p_reg
            p_mod = (
                cast("str | None", param_type_node.get("modifier"))
                if param_type_node["kind"] == "modified_type"
                else None
            )
            if p_mod is not None or p_reg is not None:
                self.var_region_mode[cast("int", variable.value)] = (p_mod or "", p_reg)
            if annotated_fn:
                if node.get("const", False):
                    raise self.fail("unsupported", "contracted Fn parameters must be runtime parameters", node)
                contract = self._scalar_callback_contract(param_type_node, domain)
                identity = cast("int", variable.value)
                self.fn_contracts[identity] = contract
                self.var_preconditions[identity] = [((contract.argument,), p) for p in contract.requires]
            variables.append(variable)
            if is_readonly_span:
                self.readonly_span_vars.add(cast("int", variable.value))
            if is_ref_param:
                self.ref_parameters.add(cast("int", variable.value))
            if is_shared_ref_param:
                self.shared_ref_parameters.add(cast("int", variable.value))
            if is_out_param:
                self.out_parameters.add(cast("int", variable.value))
            if is_owned_param:
                self.owned_parameters.add(cast("int", variable.value))
            static = cast("bool", node.get("const", False))
            if static and is_out_param:
                raise self.fail("type", "constant parameter cannot be an 'out' loan", node)
            if static and is_owned_param:
                raise self.fail("type", "constant parameter cannot be an 'owned' consuming parameter", node)
            if static:
                self.constant_parameters.add(cast("int", variable.value))
            if node["name"] is not None:
                name = self.name(node["name"])
                self.parameter_names[cast("int", variable.value)] = name
                label = self.name(node.get("label", node["name"]))
                if label in used_labels:
                    raise self.fail("name", f"duplicate argument label '{label}'", node)
                used_labels.add(label)
                if "label" in node:
                    self.argument_labels[cast("int", variable.value)] = label
                if is_readonly_span:
                    self.readonly_in_params.add(name)
                if is_ref_param or is_out_param:
                    self.mutable_locals.add(name)
                if is_shared_ref_param:
                    self.shared_ref_locals.add(name)
                self.local_type_regions[name] = self._extract_type_region_qual(param_type_node)
                if is_out_param:
                    self.out_param_names.add(name)
                    self.uninitialized_out_params.add(name)
                self.bind_local(extended, name, _Binding(variable, domain, constant=static))
                if self.navigation is not None and "span" in cast("Node", node["name"]):
                    self.navigation.declare(self.module_name, node["name"], "parameter", binding=variable.value)
            elif is_out_param:
                raise self.fail("type", "'out' parameter requires a parameter name", node)
        if unit and not parameter_nodes:
            variable = self.fresh(_UNIT)
            self.nullary_parameters.add(cast("int", variable.value))
            variables.append(variable)
        return variables, extended

    def _is_supported_loan_type(self, ty: _Term) -> bool:
        inner_w = self.whnf(ty)
        return inner_w not in (_PROP, _UNIT) and inner_w.kind not in {"pi", "sort"}

    def wrap(self, kind: str, variables: list[_Term], result: _Term) -> _Term:
        for variable in reversed(variables):
            result = _term(kind, self.types[cast("int", variable.value)], result, value=variable.value)
        return result

    def type(
        self,
        node: Node,
        environment: dict[str, _Binding],
        *,
        require_sort: bool = True,
        allow_out: bool = False,
    ) -> _Term:
        self.tick()
        self.site = node
        kind = node["kind"]
        if kind == "type":
            name = self.name(node["name"])
            raw_arguments = self.nodes(node["arguments"])
            arguments: list[Node] = []
            for arg in raw_arguments:
                if arg["kind"] == "lifetime":
                    lt_name = self.lifetime_name(arg["name"])
                    if lt_name != "'_" and lt_name not in self.active_regions:
                        raise self.fail("name", f"unknown region '{lt_name}'", arg)
                else:
                    arguments.append(arg)
            if name == "_" and not arguments:
                result = self.meta(_SORT, environment)
            elif name == "Type":
                if not arguments:
                    result = _SORT
                elif len(arguments) == 1 and arguments[0]["kind"] == "nat":
                    level = int(cast("str", arguments[0]["value"]).replace("_", ""))
                    if not 0 <= level <= MAX_UNIVERSE:
                        raise self.fail("limit", f"Type level must be between 0 and {MAX_UNIVERSE}")
                    result = _term("sort", value=level)
                else:
                    raise self.fail("unsupported", "only numeric Type<n> universe levels are supported")
            elif name == "Prop":
                if arguments:
                    raise self.fail("type", "Prop takes no type arguments")
                result = _PROP
            else:
                parts = name.split(".")
                if (assoc_t := self._try_resolve_assoc_type(name, raw_arguments, arguments, environment)) is not None:
                    result = assoc_t
                elif (
                    len(parts) > 1
                    and not arguments
                    and name not in environment
                    and name not in self.globals
                    and (parts[0] in environment or parts[0] in self.globals)
                ):
                    curr = self.lookup(parts[0], environment)
                    curr_head, _ = self.spine(self.whnf(curr.type))
                    if curr_head.kind == "const" and isinstance(curr_head.value, str) and curr_head.value in self.records_by_type:
                        for seg in parts[1:]:
                            curr = self._project_member(curr, seg, node, environment)
                        result = curr.term
                    else:
                        binding = self.lookup(name, environment, raw=True)
                        result = binding.term
                else:
                    if name in {"LocalCell", "BorrowCell"}:
                        self._ensure_cell_prelude(name)
                    binding = self.lookup(name, environment, raw=True)
                    result, value_type = binding.term, binding.type
                    for argument in arguments:
                        value_type = self.whnf(value_type)
                        if value_type.kind != "pi":
                            raise self.fail("type", f"too many arguments to '{name}'")
                        value = (self.static_argument(argument, value_type.args[0], environment, type_syntax=True)
                                 if cast("int", value_type.value) in self.constant_parameters else
                                 self.argument(argument, value_type.args[0], environment))
                        result = _app(result, value)
                        value_type = self.substitute(value_type.args[1], cast("int", value_type.value), value)
        elif kind in {"group_type", "type_argument"}:
            result = self.type(self.node(node["type"]), environment, require_sort=require_sort, allow_out=allow_out)
        elif kind == "tuple_type":
            values = [self.type(value, environment) for value in self.nodes(node["types"])]
            if len(values) < 2:
                raise self.fail("protocol", "a product type requires at least two components")
            result = values[-1]
            for value in reversed(values[:-1]):
                result = _term("prod", value, result)
        elif kind == "computed_type":
            result = self.expression(self.node(node["value"]), environment).term
        elif kind == "function_type":
            eff_nodes = self.nodes(node["effects"])
            allow_none_eff = (
                len(eff_nodes) == 1
                and eff_nodes[0]["kind"] == "type"
                and self.name(eff_nodes[0]["name"]) == "none"
                and not eff_nodes[0]["arguments"]
            )
            self.no_roles(node, "captures", "contracts")
            fn_mode = cast("str", node["mode"])
            if fn_mode == "Fn":
                if not allow_none_eff:
                    self.no_roles(node, "effects")
            elif fn_mode in {"FnMut", "FnOnce"}:
                if self.in_callable_signature_kind in {"definition", "theorem", "lemma", "property", "constant"}:
                    raise self.fail("unsupported", "only pure Fn callable types are supported")
            else:
                raise self.fail("unsupported", "only pure Fn callable types are supported")
            fn_generics = self.nodes(node["generics"])
            fn_params = self.nodes(node["parameters"])
            _, hr_regions = self._extract_regions(fn_generics)
            prev_active_regions = set(self.active_regions)
            prev_readonly_in = set(self.readonly_in_params)
            prev_mutable = set(self.mutable_locals)
            prev_out = set(self.out_param_names)
            prev_uninit = set(self.uninitialized_out_params)
            prev_shared = set(self.shared_ref_locals)
            try:
                variables, extended = self.telescope(fn_generics, fn_params, environment, unit=True)
                param_regions = tuple(self._extract_type_region(self.node(p["type"])) for p in fn_params)
                result_node = self.node(node["result"])
                result_region = self._extract_type_region(result_node)
                result = self.wrap("pi", variables, self.type(result_node, extended))
            finally:
                self.active_regions = prev_active_regions
                self.readonly_in_params = prev_readonly_in
                self.mutable_locals = prev_mutable
                self.out_param_names = prev_out
                self.uninitialized_out_params = prev_uninit
                self.shared_ref_locals = prev_shared
            if result.kind == "pi":
                self.pi_fn_modes[cast("int", result.value)] = fn_mode
            if hr_regions and result.kind == "pi":
                self.pi_hr_regions[cast("int", result.value)] = (
                    frozenset(hr_regions),
                    param_regions,
                    result_region,
                )
        elif kind == "modified_type":
            modifier = node.get("modifier")
            lt_name: str | None = None
            if node.get("lifetime") is not None:
                if modifier not in {"in", "ref", "shared_ref"}:
                    raise self.fail(
                        "unsupported",
                        "explicit loan lifetimes are only supported on 'in', 'ref', and 'shared_ref' modifiers",
                        node,
                    )
                lt_node = self.node(node["lifetime"], "lifetime")
                lt_name = self.lifetime_name(lt_node["name"])
                if lt_name != "'_" and lt_name not in self.active_regions:
                    raise self.fail("name", f"unknown region '{lt_name}'", lt_node)
            if modifier == "out":
                if not allow_out:
                    raise self.fail("type", "'out' type modifier is only permitted on callable parameters", node)
                inner_type = self.type(self.node(node["type"]), environment, require_sort=require_sort)
                inner_w = self.whnf(inner_type)
                if inner_w in (_PROP, _UNIT) or inner_w.kind in {"pi", "sort"}:
                    raise self.fail("type", "'out' parameter requires a runtime value type", node)
                result = inner_type
            elif modifier == "owned":
                if not allow_out:
                    raise self.fail(
                        "type",
                        "'owned' type modifier is only permitted on callable parameters and data fields",
                        node,
                    )
                inner_type = self.type(self.node(node["type"]), environment, require_sort=require_sort)
                inner_w = self.whnf(inner_type)
                if inner_w in (_PROP, _UNIT) or inner_w.kind in {"pi", "sort"}:
                    raise self.fail("type", "'owned' parameter requires a runtime value type", node)
                result = inner_type
            elif modifier in {"in", "ref", "shared_ref"}:
                inner_type = self.type(self.node(node["type"]), environment, require_sort=require_sort)
                if not self._is_supported_loan_type(inner_type):
                    raise self.fail(
                        "type",
                        f"modifier '{modifier}' requires a runtime value type",
                        node,
                    )
                if modifier == "ref" and self._prophecy_type_active(lt_name):
                    owner_pack = cast("_Term", self.current_fn_ref_owner_type)
                    result = _term("prod", inner_type, self.pi(inner_type, owner_pack))
                else:
                    result = inner_type
            else:
                raise self.fail("unsupported", f"type modifier '{modifier}' requires the full frontend", node)
        else:
            raise self.fail("unsupported", f"'{kind}' is not a supported mathematical type")
        if require_sort:
            self.sort(result)
        return result

    def check(self, node: Node, expected: _Term, environment: dict[str, _Binding]) -> _Term:
        self.site = node
        if node["kind"] == "hole" and self.hole_inspection is not None:
            return self.hole_inspection.observe(node, expected, environment).term
        if node["kind"] == "guard_scope":
            return self.check(self.node(node["value"]), expected, self._guard_environment(node, environment))
        if node["kind"] == "expression_body":
            return self.check(self.node(node["value"]), expected, environment)
        if node["kind"] == "group":
            return self.check(self.node(node["value"]), expected, environment)
        if (prophecy := self._build_ref_return_lens(node, expected, environment)) is not None:
            return prophecy.term
        if node["kind"] not in {"lambda", "typed_lambda", "block"} and (
            self._is_propagatable_union(expected)
            or (self.current_return_type is not None and expected == self.current_return_type)
        ):
            split_prop = self._split_first_propagate(node)
            if split_prop is not None:
                prop_node, rebuild = split_prop
                return self._elaborate_propagate(
                    prop_node,
                    environment,
                    expected,
                    lambda temp_name, _ok_b, ok_env: self.check(
                        rebuild(
                            {
                                "kind": "name",
                                "span": prop_node["span"],
                                "name": {"text": temp_name, "span": prop_node["span"]},
                            }
                        ),
                        expected,
                        ok_env,
                    ),
                )
        if node["kind"] in {"lambda", "typed_lambda"}:
            return self.lambda_(node, environment, expected).term
        if node["kind"] == "block":
            return self.block(node, environment, expected).term
        if node["kind"] == "let_expression":
            return self.check(self.node(node["body"]), expected, self.local(self.node(node["binding"]), environment))
        if node["kind"] == "if_expression":
            return self.if_expression(node, environment, expected).term
        if node["kind"] == "with_expression":
            return self.with_expression(node, environment, expected).term
        if node["kind"] == "match_expression":
            return self.match(node, environment, expected, expression_arms=True).term
        if node["kind"] == "tuple":
            expected_normal = self.whnf(expected)
            if expected_normal.kind == "prod":
                values = self.nodes(node["values"])
                if len(values) < 2:
                    raise self.fail("protocol", "a product requires at least two components")
                first = self.check(values[0], expected_normal.args[0], environment)
                if len(values) == 2:
                    second = self.check(values[1], expected_normal.args[1], environment)
                else:
                    rest = {"kind": "tuple", "span": node["span"], "values": values[1:]}
                    second = self.check(rest, expected_normal.args[1], environment)
                return _term("pair", expected_normal.args[0], expected_normal.args[1], first, second)
        if node["kind"] == "nat" and node["suffix"] == "":
            spec = self._int_spec(expected)
            if spec is not None:
                mag = _parse_numeric_magnitude(cast("str", node["value"]))
                if not spec.min_val <= mag <= spec.max_val:
                    raise self.fail(
                        "type",
                        f"integer literal {mag} is out of range for '{spec.name}' ({spec.min_val}..{spec.max_val})",
                        node,
                    )
                self.contextual_literal_types[cast("list[int]", node["span"])[0]] = spec.name
                return _int_term(spec, mag)
        if node["kind"] == "unary" and self._int_spec(expected) is not None:
            res_u = self._elaborate_unary(node, environment, expected_int=expected)
            self.site = node
            self.unify(res_u.type, expected)
            return res_u.term
        if node["kind"] == "binary" and self._int_spec(expected) is not None:
            res_b = self._elaborate_binary(node, environment, expected_int=expected)
            self.site = node
            self.unify(res_b.type, expected)
            return res_b.term
        prev_expected_call = self.expected_call_type
        if node["kind"] == "call":
            self.expected_call_type = expected
        try:
            value = self.expression(node, environment)
        finally:
            self.expected_call_type = prev_expected_call
        self.site = node
        self.unify(value.type, expected)
        self._check_value_copy(node, value.type)
        return value.term

    def lambda_(self, node: Node, environment: dict[str, _Binding], expected: _Term | None = None) -> _Binding:
        parameter_role = "lambda_parameter"
        lambda_regions: set[str] = set()
        decl_result_region: str | None = None
        decl_param_regions: list[str | None] = []
        expected_w = self.whnf(expected) if expected is not None else None
        expected_hr = (
            self.pi_hr_regions.get(cast("int", expected_w.value))
            if expected_w is not None and expected_w.kind == "pi"
            else None
        )
        lambda_fn_mode = (
            self.pi_fn_modes.get(cast("int", expected_w.value), "Fn")
            if expected_w is not None and expected_w.kind == "pi"
            else "Fn"
        )
        if node["kind"] == "typed_lambda":
            parameter_role = "parameter"
            signature = self.type(self.node(node["signature"]), environment)
            if expected is not None:
                self.unify(signature, expected)
            signature_node = self.node(node["signature"], "function_type")
            lambda_fn_mode = cast("str", signature_node["mode"])
            gen_nodes = self.nodes(signature_node["generics"])
            non_region_gens, lambda_regions = self._extract_regions(gen_nodes)
            if non_region_gens:
                raise self.fail("unsupported", "generic lambda telescopes require explicit declarations", node)
            decl_param_regions = [
                self._extract_type_region(self.node(p["type"])) for p in self.nodes(signature_node["parameters"])
            ]
            decl_result_region = self._extract_type_region(self.node(signature_node["result"]))
            node = {"kind": "lambda", "parameters": signature_node["parameters"], "body": node["body"], "span": node["span"]}
            expected = signature
        parameters = self.nodes(node["parameters"])
        variables: list[_Term] = []
        param_regions_by_vid: dict[int, str] = {}
        extended = dict(environment)
        current = expected
        prev_active_regions = set(self.active_regions)
        prev_readonly_in = set(self.readonly_in_params)
        prev_ret = self.current_return_type
        prev_outer_mutables = set(self.active_lambda_outer_mutables)
        prev_lambda_mode = self.active_lambda_fn_mode
        is_hr_lambda = bool(lambda_regions) or expected_hr is not None
        self.active_regions.update(lambda_regions)
        self.active_lambda_fn_mode = lambda_fn_mode
        if is_hr_lambda and lambda_fn_mode == "Fn":
            self.active_lambda_outer_mutables = set(self.mutable_locals)
        else:
            self.active_lambda_outer_mutables = set()
        try:
            if not parameters:
                variable = self.fresh(_UNIT)
                self.nullary_parameters.add(cast("int", variable.value))
                variables.append(variable)
                if current is not None:
                    current = self.whnf(current)
                    if current.kind != "pi":
                        raise self.fail("type", "lambda requires a callable expected type", node)
                    if cast("int", current.value) not in self.nullary_parameters:
                        raise self.fail("type", "an empty lambda requires a zero-parameter source interface", node)
                    self.unify(current.args[0], _UNIT)
                    current = self.substitute(current.args[1], cast("int", current.value), variable)
            for p_idx, parameter in enumerate(parameters):
                self.site = parameter
                if parameter["kind"] != parameter_role:
                    raise self.fail("protocol", "invalid lambda parameter syntax role")
                self.no_roles(parameter, "grade")
                annotation = parameter["type"]
                if annotation is None and parameter_role != "lambda_parameter":
                    raise self.fail("protocol", "a declared callable parameter requires a type")
                domain = (self.meta(_SORT, extended) if annotation is None
                          else self.type(self.node(annotation), extended))
                expected_pi = None if current is None else self.whnf(current)
                is_in_param = (
                    annotation is not None
                    and self.node(annotation)["kind"] == "modified_type"
                    and self.node(annotation).get("modifier") == "in"
                )
                if expected_pi is not None:
                    if expected_pi.kind != "pi":
                        raise self.fail("type", "lambda has more parameters than its expected type")
                    if cast("int", expected_pi.value) in self.nullary_parameters:
                        raise self.fail("type", "an explicit lambda parameter cannot satisfy a zero-parameter source interface")
                    self.unify(domain, expected_pi.args[0])
                    if cast("int", expected_pi.value) in self.readonly_span_vars:
                        is_in_param = True
                variable = self.fresh(domain)
                variables.append(variable)
                if is_in_param:
                    self.readonly_span_vars.add(cast("int", variable.value))
                if p_idx < len(decl_param_regions) and decl_param_regions[p_idx] is not None:
                    param_regions_by_vid[cast("int", variable.value)] = cast("str", decl_param_regions[p_idx])
                static = cast("bool", parameter.get("const", False))
                if expected_pi is not None:
                    expected_static = cast("int", expected_pi.value) in self.constant_parameters
                    if annotation is None:
                        static = expected_static
                    elif static != expected_static:
                        raise self.fail("type", "lambda constant-parameter requirement differs from its expected type")
                if static:
                    self.constant_parameters.add(cast("int", variable.value))
                name = self.name(parameter["name"])
                self.parameter_names[cast("int", variable.value)] = name
                if is_in_param:
                    self.readonly_in_params.add(name)
                self.bind_local(extended, name, _Binding(variable, domain, constant=static))
                if expected_pi is not None:
                    current = self.substitute(expected_pi.args[1], cast("int", expected_pi.value), variable)
            body_node = self.node(node["body"])
            if current is None:
                body = self.block(body_node, extended) if body_node["kind"] == "block" else self.expression(body_node, extended)
            else:
                self.current_return_type = current
                body = _Binding(self.check(body_node, current, extended), current)
            body_free = self.free(body.term)
            if lambda_regions and decl_result_region is not None and decl_result_region not in lambda_regions:
                for pvid, preg in param_regions_by_vid.items():
                    if preg in lambda_regions and pvid in body_free:
                        raise self.fail(
                            "type",
                            f"cannot escape higher-ranked region '{preg}' into outer region '{decl_result_region}'",
                            node,
                        )
            if expected_hr is not None:
                hr_regions, _, exp_res_reg = expected_hr
                if (
                    exp_res_reg is not None
                    and exp_res_reg not in hr_regions
                    and decl_result_region is not None
                    and decl_result_region in lambda_regions
                ):
                    raise self.fail(
                        "type",
                        f"cannot escape higher-ranked region '{decl_result_region}' into outer region '{exp_res_reg}'",
                        node,
                    )
                if exp_res_reg is not None and exp_res_reg in hr_regions:
                    if decl_result_region is not None and decl_result_region not in lambda_regions:
                        raise self.fail(
                            "type",
                            f"cannot escape outer region '{decl_result_region}' into higher-ranked callback result",
                            node,
                        )
                    param_ids = {cast("int", v.value) for v in variables}
                    captured_free = body_free - param_ids
                    for env_k, env_b in environment.items():
                        if (
                            env_b.term.kind == "var"
                            and cast("int", env_b.term.value) in captured_free
                            and self._contains_borrow_or_region_type(env_b.type, env_k)
                        ):
                            raise self.fail(
                                "type",
                                f"cannot capture or escape outer region binding '{env_k}' in higher-ranked callback",
                                node,
                            )
            lam_term = self.wrap("lam", variables, body.term)
            pi_type = self.wrap("pi", variables, body.type)
            if pi_type.kind == "pi":
                self.pi_fn_modes[cast("int", pi_type.value)] = lambda_fn_mode
            if lambda_regions and pi_type.kind == "pi":
                self.pi_hr_regions[cast("int", pi_type.value)] = (
                    frozenset(lambda_regions),
                    tuple(decl_param_regions),
                    decl_result_region,
                )
            return _Binding(lam_term, pi_type)
        finally:
            self.active_regions = prev_active_regions
            self.readonly_in_params = prev_readonly_in
            self.current_return_type = prev_ret
            self.active_lambda_outer_mutables = prev_outer_mutables
            self.active_lambda_fn_mode = prev_lambda_mode



# A rendered word contains one closing parenthesis per nibble and one for its constructor.
_WORD_LITERAL = re.compile("|".join(
    rf"\(@holdfast_mk_int \([0-9]+ : Corelib\.Init\.Datatypes\.nat\) (?:\(holdfast_x[0-9a-f] ){{{n}}}holdfast_bnil\){{{n + 1}}}"
    for n in sorted({spec.bits // 4 for spec in _INT_SPECS.values()})
))


def _proof_module_body(output: list[str]) -> tuple[str, int]:
    body = "\n\n".join(output)
    if len(body) < MAX_SOURCE_BYTES:
        return body, 0
    counts = Counter(match.group() for match in _WORD_LITERAL.finditer(body))
    shared = {term: f"holdfast_word_literal_{index}" for index, (term, count) in enumerate(counts.items())
              if count > 2}
    if not shared:
        return body, 0
    definitions = "\n".join(f"Local Definition {name} := {term}." for term, name in shared.items())
    rewritten = _WORD_LITERAL.sub(lambda match: shared.get(match.group(), match.group()), body)
    return definitions + "\n\n" + rewritten, len(shared) + 1


def _checked_elaboration(
    source: bytes,
    parsed: object,
    *,
    available_modules: dict[str, _Elaborator] | None = None,
    package_scope: PackageScope | None = None,
    navigation: Navigation | None = None,
    require_word_proofs: bool = False,
    phase: Callable[[str], AbstractContextManager[object]] = nullcontext,
    origins: list[GallinaOrigin] | None = None,
) -> tuple[CheckedElaboration, _Elaborator]:
    protocol = _Protocol(source)
    try:
        snapshot = copy.deepcopy(parsed)
        root = protocol.decode(snapshot)
        elaborator = _Elaborator(protocol)
        elaborator.require_word_proofs = require_word_proofs
        module = elaborator.name(root["name"])
        elaborator.module_name = module
        elaborator.navigation = navigation
        generated_module = gallina_module_name(module)
        if available_modules is not None:
            module_key = module.encode("ascii").hex()
            if package_scope is not None:
                elaborator.package_instance = package_scope.instance
                elaborator.package_edition = package_scope.edition
                module_key = f"{package_scope.instance}_{module_key}"
                # Keep prelude binders shared. User binders from each locked module
                # occupy a disjoint sequence independent of graph traversal order.
                namespace = int.from_bytes(hashlib.sha256(module_key.encode("ascii")).digest())
                elaborator.binder_stride = 1 << 256
                if any(mod.serial % elaborator.binder_stride == namespace for mod in available_modules.values()):
                    raise protocol.error("name", "locked modules have a conflicting binder namespace")
                elaborator.serial = elaborator.binder_stride + namespace
            else:
                elaborator.serial = max((mod.serial for mod in available_modules.values()), default=elaborator.serial)
            elaborator.emission_prefix = f"holdfast_m{module_key}"
            generated_module = "HoldFastPackage_" + module_key
            elaborator.available_modules = dict(available_modules)
        if protocol.holes:
            elaborator.navigation = None
            elaborator.hole_inspection = HoleInspection(elaborator)
            raise elaborator.hole_inspection.refusal(elaborator.nodes(root["declarations"]))
        chunk_origins: dict[int, tuple[tuple[int, int], tuple[int, int], str]] = {}
        declarations: list[tuple[int, int]] = []
        imported_grade_exports = {name: export for mod in elaborator.available_modules.values()
                                  for name, export in mod.grade_exports.items()}
        for mod in elaborator.available_modules.values():
            elaborator.checked_caller_required.update(mod.checked_caller_required)
        imported_boxes = {
            mod.graded_box_type: graded_source.GradeDomain(mod.graded_box_domain)
            for mod in elaborator.available_modules.values()
            if mod.graded_box_type is not None and mod.graded_box_domain is not None
        }

        def resolve_grade_import(name: str) -> tuple[str, graded_source.GradeExport] | None:
            binding = elaborator.globals.get(name)
            if binding is None or binding.term.kind != "const":
                return None
            identity = str(binding.term.value)
            export = imported_grade_exports.get(identity)
            return (identity, export) if export is not None else None

        def resolve_box_import(name: str) -> graded_source.GradeDomain | None:
            record = elaborator.records.get(name)
            if record is None:
                return None
            return imported_boxes.get(record.type_const)

        with phase("resolve-and-elaborate"), ExitStack() as grade_stack:
            grade_replay = graded_source.ModuleReplay(
                Path(__file__).resolve().parents[2], protocol, root, grade_stack, resolve_box=resolve_box_import
            )
            for declaration in elaborator.nodes(root["declarations"]):
                first = len(elaborator.output)
                elaborator.checked_grade_annotations, caller_requirement = grade_replay.check(
                    declaration, resolve_grade_import
                )
                elaborator.declaration(declaration)
                if caller_requirement is not None:
                    name = elaborator.name(declaration["name"])
                    elaborator.checked_caller_required[str(elaborator.globals[name].term.value)] = caller_requirement
                if declaration is grade_replay.box and grade_replay.box_domain is not None:
                    box_record = elaborator.records.get("Box")
                    if box_record is not None and declaration["modifiers"] == ["public"]:
                        elaborator.graded_box_type = box_record.type_const
                        elaborator.graded_box_domain = grade_replay.box_domain.value
                if elaborator.freeze_checks:
                    elaborator.output.append("\n".join(
                        f"Definition {elaborator.emission_prefix}_freeze_check_{first}_{index} : "
                        f"@eq {domain} {original} {frozen} := eq_refl."
                        for index, (domain, original, frozen) in enumerate(elaborator.freeze_checks)))
                    elaborator.freeze_checks.clear()
                if origins is not None:
                    start, end = cast("list[int]", declaration["span"])
                    declarations.append((start, end))
                    for index in range(first, len(elaborator.output)):
                        chunk_origins[index] = ((start, end), (start, end), "declaration")
            owner = 0
            for assertion_span, witness in elaborator.inline_assertions:
                if origins is not None:
                    while declarations[owner][1] <= assertion_span[0]:
                        owner += 1
                    chunk_origins[len(elaborator.output)] = (assertion_span, declarations[owner], "inline-assertion")
                elaborator.output.append(witness)
            if elaborator.word_proofs:
                elaborator.output.append(_WORD_REPLAY_PRELUDE)
                if origins is not None:
                    owner = 0
                    for offset, (start, end, _) in sorted(enumerate(elaborator.word_proofs), key=lambda item: item[1][0]):
                        while owner < len(declarations) and declarations[owner][1] <= start:
                            owner += 1
                        if owner == len(declarations) or not declarations[owner][0] <= start < end <= declarations[owner][1]:
                            raise protocol.error("protocol", "word proof origin outside its declaration")
                        chunk_origins[len(elaborator.output) + offset] = ((start, end), declarations[owner], "word-equation")
                elaborator.output.extend(elaborator.word_proofs.values())
        elaborator.checked_grade_annotations.clear()
        elaborator.grade_exports = {str(elaborator.globals[name].term.value): export
                                    for name, export in grade_replay.exports.items()}
        source_digest = hashlib.sha256(source).hexdigest()
        with phase("generate-gallina"):
            # REUSE-IgnoreStart
            header = ("(* SPDX-License-Identifier: Apache-2.0 *)\n"
                       # REUSE-IgnoreEnd
                       "(* HoldFast mathematical elaboration: unqualified kernel proposal. "
                       f"Source SHA256: {source_digest} *)\n"
                      + "".join(grade_replay.receipts) + f"Module {generated_module}.\n\n" + _PRELUDE + "\n")
            body, hoisted_lines = _proof_module_body(elaborator.output)
            gallina = header + body + f"\n\nEnd {generated_module}.\n"
        if len(gallina.encode("utf-8")) > MAX_OUTPUT_BYTES:
            raise protocol.error("limit", "generated Gallina exceeds the output bound")
        if origins is not None:
            line = header.count("\n") + hoisted_lines
            for index, chunk in enumerate(elaborator.output):
                count = chunk.count("\n") + 1
                if index in chunk_origins:
                    origins.append(GallinaOrigin(line, count, *chunk_origins[index]))
                line += count + 1
        return CheckedElaboration(module, gallina, source_digest, CheckedElaboration.encode_syntax(snapshot),
                                  MappingProxyType(elaborator.contextual_literal_types.copy()),
                                  MappingProxyType(elaborator.call_declarations.copy()),
                                  recursive_declarations=frozenset(elaborator.recursive_declarations),
                                  constructor_suggestions=MappingProxyType(elaborator.constructor_suggestions.copy()),
                                  semantic_lints=MappingProxyType(elaborator.semantic_lints | {
                                      site: message for site, message in elaborator.flow_lint_observations.items()
                                      if message is not None
                                  }),
                                  integer_operations=MappingProxyType(elaborator.integer_operations.copy())), elaborator
    except RecursionError as error:
        raise protocol.error("limit", "elaboration nesting exceeds the host stack bound") from error


def elaborate(
    source: bytes,
    parsed: object,
    *,
    imports: Sequence[tuple[bytes, object]] | None = None,
    require_word_proofs: bool = False,
) -> CheckedElaboration:
    """Check an exact-source schema-2 AST and propose a complete bounded CIC file."""
    if imports is None or not imports:
        return _checked_elaboration(source, parsed, require_word_proofs=require_word_proofs)[0]
    protocol = _Protocol(source)
    module = _Elaborator(protocol).name(protocol.decode(parsed)["name"])
    return elaborate_package([*imports, (source, parsed)], require_word_proofs=require_word_proofs)[module]


def elaborate_package(modules: Sequence[tuple[bytes, object]], *, require_word_proofs: bool = False,
                      scopes: dict[str, PackageScope] | None = None, output_limit: int | None = None,
                      navigation: Navigation | None = None) -> dict[str, CheckedElaboration]:
    """Check a linked module graph in dependency order, with one owner per import path."""
    decoded: dict[str, tuple[bytes, object, _Protocol, Node, list[tuple[str, Node]]]] = {}
    order_names: list[str] = []
    for src, parsed in modules:
        protocol = _Protocol(src)
        root = protocol.decode(parsed)
        probe = _Elaborator(protocol)
        mod_name = probe.name(root["name"])
        if mod_name in decoded:
            previous = hashlib.sha256(decoded[mod_name][0]).hexdigest()
            current = hashlib.sha256(src).hexdigest()
            raise protocol.error("name", f"duplicate module '{mod_name}' in package (source SHA256 {previous} and {current})", root)
        deps = [
            (probe.name(decl["name"]), decl)
            for decl in probe.nodes(root["declarations"])
            if decl["kind"] == "import"
        ]
        decoded[mod_name] = (src, parsed, protocol, root, deps)
        order_names.append(mod_name)

    active: list[str] = []
    visited: set[str] = set()
    topo: list[str] = []

    def visit(mod_name: str) -> None:
        active.append(mod_name)
        _, _, proto, _, deps = decoded[mod_name]
        for dep_name, imp_node in deps:
            if dep_name in active:
                cycle = " -> ".join([*active[active.index(dep_name):], dep_name])
                raise proto.error("name", f"circular module import: {cycle}", imp_node)
            if dep_name in decoded and dep_name not in visited:
                visit(dep_name)
        active.pop()
        visited.add(mod_name)
        topo.append(mod_name)

    if scopes is not None and scopes.keys() != decoded.keys():
        raise ValueError("manifest module names differ from source declarations")
    for mname in order_names:
        if scopes is not None:
            for dependency, site in decoded[mname][4]:
                if dependency != "HoldFast.Numerics" and dependency not in scopes[mname].modules:
                    raise decoded[mname][2].error("name", f"module '{mname}' has no declared dependency on '{dependency}'", site)
        if mname not in visited:
            visit(mname)

    available: dict[str, _Elaborator] = {}
    elaborations: dict[str, CheckedElaboration] = {}
    package_instances: dict[str, list[_ImplInstance]] = {}
    instance_variable_types: dict[int, _Term] = {}
    generated_size = 0
    for mname in topo:
        src, parsed, _, _, _ = decoded[mname]
        try:
            elab, elaborator = _checked_elaboration(src, parsed, available_modules=available, require_word_proofs=require_word_proofs,
                                                    package_scope=scopes[mname] if scopes is not None else None,
                                                    navigation=navigation)
            if scopes is not None:
                # Compare instances from siblings even when no module imports them together.
                elaborator.types.update(instance_variable_types)
                for interface, instance in elaborator.local_instances:
                    prior = package_instances.setdefault(interface, [])
                    if any(elaborator._impl_instances_overlap(other, instance) for other in prior):
                        raise elaborator.fail("type", f"overlapping instances for '{interface}' in locked closure")
                    prior.append(instance)
                    for variable in instance.generic_vars:
                        key = cast("int", variable.value)
                        instance_variable_types[key] = elaborator.types[key]
            if output_limit is not None:
                generated_size += len(elab.gallina.encode("utf-8"))
                if generated_size > output_limit:
                    raise elaborator.fail("limit", "combined package Gallina exceeds the output budget")
        except HoldFastError as error:
            raise HoldFastError(error.kind, error.line, error.column, f"module '{mname}': {error.message}") from error
        available[mname] = elaborator
        elaborations[mname] = elab

    return elaborations


def check_client_upgrade(
    baseline: tuple[bytes, object], candidate: tuple[bytes, object],
    clients: Sequence[tuple[bytes, object]], dependencies: Sequence[tuple[bytes, object]] = (),
) -> dict[str, object]:
    """Elaborate the same importing clients and fixed dependencies against two module revisions."""
    def describe(module: tuple[bytes, object]) -> tuple[str, set[str]]:
        source, parsed = module
        protocol = _Protocol(source)
        ast = protocol.decode(parsed)
        probe = _Elaborator(protocol)
        return probe.name(ast["name"]), {
            probe.name(decl["name"]) for decl in probe.nodes(ast["declarations"]) if decl["kind"] == "import"
        }

    owner, _ = describe(baseline)
    if describe(candidate)[0] != owner:
        raise HoldFastError("name", 1, 1, "upgrade revisions must declare the same module")
    if not clients:
        raise HoldFastError("name", 1, 1, "an upgrade requires at least one dependent client")
    fixed = [*dependencies, *clients]
    described = [describe(module) for module in fixed]
    graph = dict(described)
    client_names = [name for name, _ in described[len(dependencies):]]
    for client in client_names:
        pending = list(graph[client])
        seen: set[str] = set()
        while pending:
            current = pending.pop()
            if current == owner:
                break
            if current not in seen:
                seen.add(current)
                pending.extend(graph.get(current, ()))
        else:
            raise HoldFastError("name", 1, 1, f"client '{client}' does not import '{owner}' directly or transitively")
    for phase, revision in (("baseline", baseline), ("candidate", candidate)):
        try:
            elaborate_package([revision, *fixed])
        except HoldFastError as error:
            raise HoldFastError(error.kind, error.line, error.column, f"{phase} replay: {error.message}") from error
    return {
        "status": "clients-elaborated", "module": owner, "clients": sorted(client_names),
        "baseline_sha256": hashlib.sha256(baseline[0]).hexdigest(),
        "candidate_sha256": hashlib.sha256(candidate[0]).hexdigest(),
        "fixed_sources_sha256": {
            name: hashlib.sha256(module[0]).hexdigest()
            for (name, _), module in zip(described, fixed, strict=True)
        },
    }


def _console_initializer(elaborator: _Elaborator, protocol: _Protocol, parsed: object,
                         prefix_bytes: int, expression_bytes: int) -> Node:
    root = protocol.decode(parsed)
    declarations = elaborator.nodes(root["declarations"])
    if len(declarations) != 1 or declarations[0]["kind"] != "constant":
        raise HoldFastError("syntax", 3, 1, "expected exactly one constant initializer")
    declaration = declarations[0]
    name = elaborator.name(declaration["name"])
    value = elaborator.node(declaration["value"])
    if (name != "__holdfast_console_result"
            or declaration["span"] != [len(b"module Playground;\n"), len(protocol.source)]
            or not prefix_bytes <= cast("list[int]", value["span"])[0]
            < cast("list[int]", value["span"])[1] <= prefix_bytes + expression_bytes):
        raise HoldFastError("syntax", 3, 1, "expected exactly one complete constant initializer")
    return declaration


def _console_value(elaborator: _Elaborator, declaration: Node,
                   value_type: ValueType) -> StaticEvaluation:
    result, _ = elaborator.constant_value(declaration, {})
    normalized = elaborator.whnf(result.term)
    expected = "nat" if value_type == "Nat" else "bool"
    if normalized.kind != expected or elaborator.free(normalized):
        raise HoldFastError("inference", 1, 1, "constant did not reduce to a closed typed value")
    return StaticEvaluation(value_type, cast("int", normalized.value) if value_type == "Nat"
                            else bool(normalized.value))


def evaluate(source: bytes, parsed: object, expression: str, value_type: ValueType,
             *, parse: Callable[[bytes], object]) -> StaticEvaluation:
    """Reduce one source-bound console constant in the checked module's environment.

    The [mathematical console contract](../../docs/tooling/elaboration-prototype.md#commands-and-acceptance)
    uses the native parser and bounded constant reducer.
    """
    _, elaborator = _checked_elaboration(source, parsed)
    if value_type not in {"Nat", "bool"}:
        raise HoldFastError("type", 1, 1, "expression: expected Nat or bool result type")
    try:
        raw = expression.encode("utf-8")
    except UnicodeEncodeError as error:
        raise HoldFastError("encoding", 1, 1, "expression: invalid Unicode text") from error
    if len(raw) > 4096:
        raise HoldFastError("limit", 1, 1, "expression: exceeds 4096 UTF-8 bytes")
    prefix = f"module Playground;\npublic const {value_type} __holdfast_console_result =\n".encode()
    probe = prefix + raw + b"\n;"
    protocol = _Protocol(probe)
    try:
        declaration = _console_initializer(elaborator, protocol, parse(probe), len(prefix), len(raw))
    except HoldFastError as error:
        lines = expression.replace("\r\n", "\n").replace("\r", "\n").split("\n")
        line = max(1, error.line - 2)
        column = error.column if line <= len(lines) else len(lines[-1]) + 1
        line = min(line, len(lines))
        column = min(column, len(lines[line - 1]) + 1)
        raise HoldFastError(error.kind, line, column, f"expression: {error.message}") from error
    except RecursionError as error:
        raise HoldFastError("limit", 1, 1, "expression: syntax nesting exceeds the host stack bound") from error
    elaborator.protocol = protocol
    # The probe is a different source buffer and has its own byte coordinates.
    elaborator.phase_uses.clear()
    elaborator.static_effect_sites.clear()
    try:
        return _console_value(elaborator, declaration, value_type)
    except HoldFastError as error:
        raise HoldFastError(error.kind, 1, 1, f"expression: {error.message}") from error
    except RecursionError as error:
        raise HoldFastError("limit", 1, 1, "expression: elaboration nesting exceeds the host stack bound") from error
