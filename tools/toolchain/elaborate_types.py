# SPDX-License-Identifier: Apache-2.0
"""Core terms, fixed-width integer specifications, bindings, and Gallina prelude for HoldFast elaboration."""

import json
from collections.abc import Mapping
from dataclasses import dataclass, field

from toolchain.ast import MAX_LITERAL_DIGITS

MAX_DEPTH = 128
MAX_WORK = 200_000
MAX_REDUCTIONS = 20_000
MAX_OUTPUT_BYTES = 4_194_304
MAX_UNIVERSE = 8
MAX_NAT_BITS = 4096
MAX_CONSTANT_NAT = 10 ** MAX_LITERAL_DIGITS - 1
MAX_PATTERN_NAT = 64
MAX_STRING_BYTES = 256
MAX_STATIC_VECTOR_SLOTS = 64


@dataclass(frozen=True)
class Elaboration:
    module: str
    gallina: str


@dataclass(frozen=True)
class GallinaOrigin:
    """A group of final Gallina lines and the source spans responsible for it."""

    first_line: int
    line_count: int
    source: tuple[int, int]
    declaration: tuple[int, int]
    stage: str


@dataclass(frozen=True)
class CheckedElaboration(Elaboration):
    source_sha256: str
    syntax: bytes
    contextual_literal_types: Mapping[int, str]
    call_declarations: Mapping[int, int]
    recursive_declarations: frozenset[int]
    constructor_suggestions: Mapping[int, str]
    redundant_ref_ensures: Mapping[int, str]
    integer_operations: Mapping[int, tuple[str, str]]

    @staticmethod
    def encode_syntax(parsed: object) -> bytes:
        return json.dumps(parsed, ensure_ascii=True, allow_nan=False, sort_keys=True, separators=(",", ":")).encode("ascii")


type Node = dict[str, object]



@dataclass(frozen=True)
class _Term:
    kind: str
    value: str | int = ""
    args: tuple[_Term, ...] = ()


def _term(kind: str, *args: _Term, value: str | int = "") -> _Term:
    return _Term(kind, value, tuple(args))


def _app(function: _Term, argument: _Term) -> _Term:
    return _term("app", function, argument)


def _apps(function: _Term, *arguments: _Term) -> _Term:
    for argument in arguments:
        function = _app(function, argument)
    return function


def _constant(name: str) -> _Term:
    return _term("const", value=name)


_NAT = _constant("Nat")
_BOOL = _constant("bool")
_CHAR = _constant("char")
_UNIT = _constant("Unit")
_SORT = _term("sort", value=0)
_PROP = _term("sort", value=-1)


@dataclass(frozen=True)
class _IntSpec:
    name: str
    tag: int
    bits: int
    signed: bool
    min_val: int
    max_val: int
    const: _Term


_INT_SPECS: dict[str, _IntSpec] = {
    "u8": _IntSpec("u8", 0, 8, False, 0, (1 << 8) - 1, _constant("u8")),
    "u16": _IntSpec("u16", 1, 16, False, 0, (1 << 16) - 1, _constant("u16")),
    "u32": _IntSpec("u32", 2, 32, False, 0, (1 << 32) - 1, _constant("u32")),
    "u64": _IntSpec("u64", 3, 64, False, 0, (1 << 64) - 1, _constant("u64")),
    "usize": _IntSpec("usize", 4, 64, False, 0, (1 << 64) - 1, _constant("usize")),
    "i8": _IntSpec("i8", 5, 8, True, -(1 << 7), (1 << 7) - 1, _constant("i8")),
    "i16": _IntSpec("i16", 6, 16, True, -(1 << 15), (1 << 15) - 1, _constant("i16")),
    "i32": _IntSpec("i32", 7, 32, True, -(1 << 31), (1 << 31) - 1, _constant("i32")),
    "i64": _IntSpec("i64", 8, 64, True, -(1 << 63), (1 << 63) - 1, _constant("i64")),
}
_U8 = _INT_SPECS["u8"].const
_USIZE = _INT_SPECS["usize"].const
_NUMERICS_ALIASES: dict[str, str] = {
    "int": "i32",
    "uint": "u32",
    "long": "i64",
    "ulong": "u64",
}
_INT_INTRINSICS = {
    "ShiftLeft",
    "ShiftRight",
    "WrappingAdd",
    "WrappingSub",
    "WrappingMul",
    "WrappingNeg",
    "WrappingShiftLeft",
    "SaturatingAdd",
    "SaturatingSub",
    "SaturatingMul",
    "SaturatingNeg",
    "CheckedAdd",
    "CheckedSub",
    "CheckedMul",
    "CheckedNeg",
    "CheckedDiv",
    "CheckedRem",
    "CheckedShiftLeft",
    "CheckedShiftRight",
}


def _parse_numeric_magnitude(value: str) -> int:
    cleaned = value.replace("_", "")
    if cleaned.startswith(("0x", "0X")):
        return int(cleaned, 16)
    if cleaned.startswith(("0b", "0B")):
        return int(cleaned, 2)
    return int(cleaned, 10)


def _allows_from_conversion(src: _IntSpec, dst: _IntSpec) -> bool:
    if src.name == dst.name:
        return True
    if src.name == "usize" or dst.name == "usize":
        return dst.name == "usize" and src.name in {"u8", "u16", "u32"}
    return src.min_val >= dst.min_val and src.max_val <= dst.max_val


def _wrap_int(spec: _IntSpec, val: int) -> int:
    u = val & ((1 << spec.bits) - 1)
    if spec.signed and (u & (1 << (spec.bits - 1))):
        return u - (1 << spec.bits)
    return u


def _clamp_int(spec: _IntSpec, val: int) -> int:
    return min(spec.max_val, max(spec.min_val, val))


def _trunc_div(a: int, b: int) -> int:
    q = abs(a) // abs(b)
    return -q if (a < 0) != (b < 0) else q


def _trunc_rem(a: int, b: int) -> int:
    return a - _trunc_div(a, b) * b


def _int_term(spec: _IntSpec, value: int) -> _Term:
    return _term("int", spec.const, value=value)


@dataclass
class _Meta:
    type: _Term
    scope: frozenset[int]
    solution: _Term | None = None


@dataclass(frozen=True)
class _FnContract:
    argument: int
    result: int
    requires: tuple[_Term, ...]
    ensures: tuple[_Term, ...]


@dataclass(frozen=True)
class _Binding:
    term: _Term
    type: _Term
    generics: int = 0
    constant: bool = False


@dataclass(frozen=True)
class _Pat:
    kind: str
    node: Node
    names: tuple[str, ...] = ()
    value: bool | str | int = False
    args: tuple[_Pat, ...] = ()


@dataclass(frozen=True)
class _Row:
    patterns: tuple[_Pat, ...]
    bindings: tuple[tuple[str, _Binding], ...]
    arm: Node
    arm_index: int = 0


@dataclass(frozen=True)
class _RecordField:
    name: str
    var: _Term
    type: _Term
    proj_const: str
    readonly_span: bool = False


@dataclass(frozen=True)
class _RecordProperty:
    name: str
    self_var: _Term
    type: _Term
    prop_const: str
    private_to: str | None = None


@dataclass(frozen=True)
class _RecordInvariant:
    name: str
    self_var: _Term
    term: _Term
    type: _Term
    node: Node


@dataclass(frozen=True)
class _RecordMethod:
    returns_receiver_loan: bool
    name: str
    method_const: str
    binding: _Binding
    method_generics: int
    param_labels: tuple[str | None, ...]
    nullary: bool = False
    private_to: str | None = None


@dataclass
class _RecordInfo:
    name: str
    type_const: str
    ctor_const: str
    ctor_binding: _Binding
    generic_vars: tuple[_Term, ...]
    fields: tuple[_RecordField, ...]
    properties: dict[str, _RecordProperty]
    is_dependent: bool = False
    tail_sig_types: tuple[_Term, ...] = ()
    invariants: tuple[_RecordInvariant, ...] = ()
    methods: dict[str, _RecordMethod] = field(default_factory=dict)


@dataclass(frozen=True)
class _UnionCtor:
    name: str
    ctor_const: str
    ctor_binding: _Binding
    fields: tuple[_RecordField, ...]
    payload_type: _Term
    index: int
    is_dependent: bool = False
    tail_sig_types: tuple[_Term, ...] = ()


@dataclass(frozen=True)
class _UnionInfo:
    name: str
    type_const: str
    generic_vars: tuple[_Term, ...]
    constructors: tuple[_UnionCtor, ...]
    suffix_types: tuple[_Term, ...]
    propagation: tuple[int, int] | None = None


@dataclass(frozen=True)
class _InterfaceMethodSpec:
    returns_receiver_loan: bool
    name: str
    method_generics: int
    generic_vars: tuple[_Term, ...]
    param_vars: tuple[_Term, ...]
    param_labels: tuple[str | None, ...]
    param_modifiers: tuple[str | None, ...]
    return_type: _Term
    signature: _Term
    self_var: _Term
    nullary: bool
    preconditions: tuple[tuple[tuple[int, ...], _Term], ...]
    ensures_props: tuple[_Term, ...]


@dataclass(frozen=True)
class _InterfaceLawSpec:
    name: str
    kind: str
    param_vars: tuple[_Term, ...]
    req_props: tuple[_Term, ...]
    ensures_props: tuple[_Term, ...]


@dataclass(frozen=True)
class _InterfaceInfo:
    name: str
    generic_vars: tuple[_Term, ...]
    methods: dict[str, _InterfaceMethodSpec]
    laws: dict[str, _InterfaceLawSpec]


@dataclass(frozen=True)
class _ImplInstance:
    generic_vars: tuple[_Term, ...]
    target_types: tuple[_Term, ...]
    where_constraints: tuple[tuple[str, tuple[_Term, ...]], ...]
    methods: dict[str, _Binding]


@dataclass(frozen=True)
class PackageScope:
    """Exact package instance, available modules and importing source edition."""

    instance: str
    modules: frozenset[str]
    edition: str = "math-1"





_GALLINA = {
    "Nat": "Corelib.Init.Datatypes.nat", "bool": "Corelib.Init.Datatypes.bool",
    "char": "holdfast_char",
    "Unit": "Corelib.Init.Datatypes.unit", "Prop": "Prop",
    "char_eq": "holdfast_char_eq", "char_ne": "holdfast_char_ne",
    "char_lt": "holdfast_char_lt", "char_le": "holdfast_char_le",
    "char_gt": "holdfast_char_gt", "char_ge": "holdfast_char_ge",
    "char_to_nat": "holdfast_char_to_nat", "char_to_u32": "holdfast_char_to_u32",
    "char_from_u8": "holdfast_char_from_u8",
    "char_try_from_u32": "holdfast_char_try_from_u32",
    "char_try_from_Nat": "holdfast_char_try_from_Nat",
    "eq_unit": "holdfast_eq_unit", "ne_unit": "holdfast_ne_unit",
    "u8": "(holdfast_int (0 : Corelib.Init.Datatypes.nat))",
    "u16": "(holdfast_int (1 : Corelib.Init.Datatypes.nat))",
    "u32": "(holdfast_int (2 : Corelib.Init.Datatypes.nat))",
    "u64": "(holdfast_int (3 : Corelib.Init.Datatypes.nat))",
    "usize": "(holdfast_int (4 : Corelib.Init.Datatypes.nat))",
    "i8": "(holdfast_int (5 : Corelib.Init.Datatypes.nat))",
    "i16": "(holdfast_int (6 : Corelib.Init.Datatypes.nat))",
    "i32": "(holdfast_int (7 : Corelib.Init.Datatypes.nat))",
    "i64": "(holdfast_int (8 : Corelib.Init.Datatypes.nat))",
    "holdfast_ArithmeticError": "holdfast_ArithmeticError",
    "holdfast_ArithmeticError_Overflow": "holdfast_ArithmeticError_Overflow",
    "holdfast_ArithmeticError_ZeroDivisor": "holdfast_ArithmeticError_ZeroDivisor",
    "holdfast_ArithmeticError_InvalidShift": "holdfast_ArithmeticError_InvalidShift",
    "holdfast_ConversionError": "holdfast_ConversionError",
    "holdfast_ConversionError_OutOfRange": "holdfast_ConversionError_OutOfRange",
    "holdfast_Result": "holdfast_Result",
    "holdfast_Result_Ok": "holdfast_Result_Ok",
    "holdfast_Result_Err": "holdfast_Result_Err",
    "Succ": "Corelib.Init.Datatypes.S", "Eq": "Corelib.Init.Logic.eq",
    "Refl": "Corelib.Init.Logic.eq_refl", "Symm": "Corelib.Init.Logic.eq_sym",
    "Trans": "Corelib.Init.Logic.eq_trans", "Congr": "holdfast_Congr",
    "Fst": "Corelib.Init.Datatypes.fst", "Snd": "Corelib.Init.Datatypes.snd",
    "Vec": "holdfast_Vec", "VNil": "holdfast_VNil", "VCons": "holdfast_VCons", "ByteLength": "holdfast_ByteLength",
    "Vec_At_Nat": "holdfast_Vec_At_Nat", "Vec_Update": "holdfast_Vec_Update",
    "TextBuilder": "holdfast_TextBuilder", "TextBuilderVal": "holdfast_text_builder",
    "EmptyBuilder": "holdfast_EmptyBuilder", "FormatStep": "holdfast_FormatStep",
    "Fits": "holdfast_Fits", "Written": "holdfast_Written",
    "Fin": "holdfast_Fin", "FZero": "holdfast_FZero", "FSucc": "holdfast_FSucc", "At": "holdfast_At",
    "FiniteOffset": "holdfast_finite_offset",
    "Span": "holdfast_Span",
    "Span_Base": "holdfast_Span_Base",
    "Span_Length": "holdfast_Span_Length",
    "Span_Tag": "holdfast_Span_Tag",
    "Span_PermRead": "holdfast_Span_PermRead",
    "Span_PermWrite": "holdfast_Span_PermWrite",
    "Span_CanRead": "holdfast_Span_CanRead",
    "Span_CanWrite": "holdfast_Span_CanWrite",
    "Span_AllocZeroed": "holdfast_Span_AllocZeroed",
    "Span_ReadOnly": "holdfast_Span_ReadOnly",
    "Span_Invalidate": "holdfast_Span_Invalidate",
    "Span_Disjoint": "holdfast_Span_Disjoint",
    "Span_Read": "holdfast_Span_Read",
    "Span_Write": "holdfast_Span_Write",
    "Span_Fill": "holdfast_Span_Fill",
    "Span_Slice": "holdfast_Span_Slice",
    "Span_CopyPrefix": "holdfast_Span_CopyPrefix",
    "Span_Restore": "holdfast_Span_Restore",
    "nat_to_usize": "holdfast_nat_to_usize",
    "nat_hex_bytes": "holdfast_nat_hex_bytes", "ValidUtf8": "holdfast_ValidUtf8",
    "WrittenBytes": "holdfast_WrittenBytes",
    "Seq": "holdfast_Seq",
    "Seq_Empty": "holdfast_Seq_Empty",
    "Seq_Cons": "holdfast_Seq_Cons",
    "Seq_Singleton": "holdfast_Seq_Singleton",
    "Seq_Count": "holdfast_Seq_Count",
    "Seq_At": "holdfast_Seq_At",
    "Seq_Update": "holdfast_Seq_Update",
    "Seq_Append": "holdfast_Seq_Append",
    "Seq_Take": "holdfast_Seq_Take",
    "Seq_Skip": "holdfast_Seq_Skip",
    "Seq_Slice": "holdfast_Seq_Slice",
    "Seq_All": "holdfast_Seq_All",
    "Seq_Any": "holdfast_Seq_Any",
    "Seq_Eq": "holdfast_Seq_Eq",
    "Vec_Model": "holdfast_Vec_Model",
    "Span_Model": "holdfast_Span_Model",
    "Slots": "holdfast_Slots",
    "Slots_Mk": "holdfast_Slots_Mk",
    "Slots_Base": "holdfast_Slots_Base",
    "Slots_Capacity": "holdfast_Slots_Capacity",
    "Slots_LiveCount": "holdfast_Slots_LiveCount",
    "Slots_Tag": "holdfast_Slots_Tag",
    "Slots_PermRead": "holdfast_Slots_PermRead",
    "Slots_PermWrite": "holdfast_Slots_PermWrite",
    "Slots_CanRead": "holdfast_Slots_CanRead",
    "Slots_CanWrite": "holdfast_Slots_CanWrite",
    "Slots_RepModel": "holdfast_Slots_RepModel",
    "Slots_Model": "holdfast_Slots_Model",
    "Slots_AllocVacant": "holdfast_Slots_AllocVacant",
    "Slots_Write": "holdfast_Slots_Write",
    "Slots_Read": "holdfast_Slots_Read",
    "Slots_LivePrefix": "holdfast_Slots_LivePrefix",
    "Slots_VacantRange": "holdfast_Slots_VacantRange",
    "Slots_Disjoint": "holdfast_Slots_Disjoint",
    "Slots_RepEqual": "holdfast_Slots_RepEqual",
    "Slots_CopyRepresentation": "holdfast_Slots_CopyRepresentation",
    "Slots_TransferSource": "holdfast_Slots_TransferSource",
    "Slots_TransferDest": "holdfast_Slots_TransferDest",
    "Slots_TransferType": "holdfast_Slots_TransferType",
    "PrefixModel": "holdfast_PrefixModel",
    "NatFold": "holdfast_NatFold",
    "+": "Corelib.Init.Nat.add", "*": "Corelib.Init.Nat.mul", "-": "Corelib.Init.Nat.sub",
    "Nat.SaturatingSub": "Corelib.Init.Nat.sub",
    "/": "Corelib.Init.Nat.div", "%": "Corelib.Init.Nat.modulo",
    "<=": "Corelib.Init.Nat.leb", "<": "Corelib.Init.Nat.ltb", ">=": "holdfast_ge", ">": "holdfast_gt",
    "eq_nat": "Corelib.Init.Nat.eqb", "ne_nat": "holdfast_ne_nat",
    "eq_bool": "holdfast_eq_bool", "ne_bool": "holdfast_ne_bool",
    "&&": "holdfast_and", "||": "holdfast_or", "!": "holdfast_not", "==>": "holdfast_implies", "<==>": "holdfast_eq_bool",
    "holdfast_false_elim": "holdfast_false_elim",
    "holdfast_false_true_elim": "holdfast_false_true_elim",
    "holdfast_and_intro": "holdfast_and_intro",
    "holdfast_Slots_vacant_after_copy": "holdfast_Slots_vacant_after_copy",
    "holdfast_Slots_vacant_after_move": "holdfast_Slots_vacant_after_move",
    "holdfast_Slots_vacant_shrink": "holdfast_Slots_vacant_shrink",
    "holdfast_Seq_take_idempotent": "holdfast_Seq_take_idempotent",
    "holdfast_Slots_live_after_copy": "holdfast_Slots_live_after_copy",
    "holdfast_and_left": "holdfast_and_left",
    "holdfast_and_right": "holdfast_and_right",
    "holdfast_or_false_l": "holdfast_or_false_l",
    "holdfast_or_false_r": "holdfast_or_false_r",
    "holdfast_eq_bool_refl": "holdfast_eq_bool_refl",
    "holdfast_eq_bool_of_eq": "holdfast_eq_bool_of_eq",
    "holdfast_eq_bool_true": "holdfast_eq_bool_true",
    "holdfast_int_eq_refl": "holdfast_int_eq_refl",
    "holdfast_int_eq_of_eq": "holdfast_int_eq_of_eq",
    "holdfast_int_eq_true": "holdfast_int_eq_true",
    "holdfast_int_le_of_gt_false": "holdfast_int_le_of_gt_false",
    "holdfast_Span_Store": "holdfast_Span_Store",
    "holdfast_bs_empty": "holdfast_bs_empty",
    "holdfast_bs_slice": "holdfast_bs_slice",
    "holdfast_bs_fill": "holdfast_bs_fill",
    "holdfast_bs_write": "holdfast_bs_write",
    "holdfast_bs_copy": "holdfast_bs_copy",
    "holdfast_store_lookup": "holdfast_store_lookup",
    "holdfast_store_slice_offset": "holdfast_store_slice_offset",
    "holdfast_bs_shift": "holdfast_bs_shift",
    "holdfast_Span_Read_write_same": "holdfast_Span_Read_write_same",
    "holdfast_Span_Read_write_other_ne": "holdfast_Span_Read_write_other_ne",
    "holdfast_store_read_aligned_copy": "holdfast_store_read_aligned_copy",
    "holdfast_store_fill_byte": "holdfast_store_fill_byte",
    "holdfast_usize_zero_le": "holdfast_usize_zero_le",
    "holdfast_extent_bound": "holdfast_extent_bound",
    "holdfast_store_lookup_write_ge": "holdfast_store_lookup_write_ge",
    "holdfast_usize_le_refl": "holdfast_usize_le_refl",
    "holdfast_store_lookup_fill_ge": "holdfast_store_lookup_fill_ge",
    "holdfast_store_lookup_copy_ge": "holdfast_store_lookup_copy_ge",
    "holdfast_nat_add_assoc": "holdfast_nat_add_assoc",
    "holdfast_nat_leb_trans": "holdfast_nat_leb_trans",
    "holdfast_nat_leb_succ_self": "holdfast_nat_leb_succ_self",
    "holdfast_nat_leb_of_ltb_false": "holdfast_nat_leb_of_ltb_false",
    "holdfast_nat_ltb_of_leb_false": "holdfast_nat_ltb_of_leb_false",
    "holdfast_gt_add_pos": "holdfast_gt_add_pos",
    "holdfast_int_add_assoc": "holdfast_int_add_assoc",
    **{
        f"int_{op}_{spec.name}": f"(holdfast_int_{op} ({spec.tag} : Corelib.Init.Datatypes.nat))"
        for spec in _INT_SPECS.values()
        for op in (
            "add", "sub", "mul", "div", "rem", "neg",
            "and", "or", "xor", "not",
            "shl", "shr", "eq", "ne", "lt", "le", "gt", "ge",
            "wrap_add", "wrap_sub", "wrap_mul", "wrap_neg", "wrap_shl",
            "sat_add", "sat_sub", "sat_mul", "sat_neg",
            "chk_add", "chk_sub", "chk_mul", "chk_div",
            "chk_rem", "chk_neg", "chk_shl", "chk_shr",
            "to_nat", "try_from_Nat", "hex_bytes",
        )
    },
    **{
        f"int_from_{src.name}_{dst.name}": (
            f"(holdfast_int_from ({src.tag} : Corelib.Init.Datatypes.nat) ({dst.tag} : Corelib.Init.Datatypes.nat))"
        )
        for src in _INT_SPECS.values()
        for dst in _INT_SPECS.values()
    },
    **{
        f"int_try_from_{src.name}_{dst.name}": (
            f"(holdfast_int_try_from ({src.tag} : Corelib.Init.Datatypes.nat) ({dst.tag} : Corelib.Init.Datatypes.nat))"
        )
        for src in _INT_SPECS.values()
        for dst in _INT_SPECS.values()
    },
}

_PRELUDE = """From Corelib Require Import Init.Datatypes Init.Nat Init.Logic Init.Specif.

Universe holdfast_u0 holdfast_u1 holdfast_u2 holdfast_u3 holdfast_u4 holdfast_u5 holdfast_u6 holdfast_u7 holdfast_u8 holdfast_u9.
Constraint holdfast_u0 < holdfast_u1.
Constraint holdfast_u1 < holdfast_u2.
Constraint holdfast_u2 < holdfast_u3.
Constraint holdfast_u3 < holdfast_u4.
Constraint holdfast_u4 < holdfast_u5.
Constraint holdfast_u5 < holdfast_u6.
Constraint holdfast_u6 < holdfast_u7.
Constraint holdfast_u7 < holdfast_u8.
Constraint holdfast_u8 < holdfast_u9.

Definition holdfast_not (a : bool) : bool := if a then false else true.
Definition holdfast_and (a b : bool) : bool := if a then b else false.
Definition holdfast_or (a b : bool) : bool := if a then true else b.
Definition holdfast_implies (a b : bool) : bool := if a then b else true.
Definition holdfast_eq_bool (a b : bool) : bool := if a then b else holdfast_not b.
Definition holdfast_ne_bool (a b : bool) : bool := holdfast_not (holdfast_eq_bool a b).
Definition holdfast_eq_unit (_ _ : unit) : bool := true.
Definition holdfast_ne_unit (_ _ : unit) : bool := false.
Definition holdfast_ne_nat (a b : nat) : bool := holdfast_not (Corelib.Init.Nat.eqb a b).
Definition holdfast_ge (a b : nat) : bool := Corelib.Init.Nat.leb b a.
Definition holdfast_gt (a b : nat) : bool := Corelib.Init.Nat.ltb b a.

Inductive holdfast_bits : Type@{holdfast_u0} :=
| holdfast_bnil : holdfast_bits
| holdfast_bcons : bool -> holdfast_bits -> holdfast_bits.

Abbreviation holdfast_0 x := (holdfast_bcons Corelib.Init.Datatypes.false x) (only parsing).
Abbreviation holdfast_1 x := (holdfast_bcons Corelib.Init.Datatypes.true x) (only parsing).
Abbreviation holdfast_x0 x := (holdfast_0 (holdfast_0 (holdfast_0 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_x1 x := (holdfast_0 (holdfast_0 (holdfast_0 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_x2 x := (holdfast_0 (holdfast_0 (holdfast_1 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_x3 x := (holdfast_0 (holdfast_0 (holdfast_1 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_x4 x := (holdfast_0 (holdfast_1 (holdfast_0 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_x5 x := (holdfast_0 (holdfast_1 (holdfast_0 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_x6 x := (holdfast_0 (holdfast_1 (holdfast_1 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_x7 x := (holdfast_0 (holdfast_1 (holdfast_1 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_x8 x := (holdfast_1 (holdfast_0 (holdfast_0 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_x9 x := (holdfast_1 (holdfast_0 (holdfast_0 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_xa x := (holdfast_1 (holdfast_0 (holdfast_1 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_xb x := (holdfast_1 (holdfast_0 (holdfast_1 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_xc x := (holdfast_1 (holdfast_1 (holdfast_0 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_xd x := (holdfast_1 (holdfast_1 (holdfast_0 (holdfast_1 x)))) (only parsing).
Abbreviation holdfast_xe x := (holdfast_1 (holdfast_1 (holdfast_1 (holdfast_0 x)))) (only parsing).
Abbreviation holdfast_xf x := (holdfast_1 (holdfast_1 (holdfast_1 (holdfast_1 x)))) (only parsing).

Fixpoint holdfast_bits_eqb (a b : holdfast_bits) : bool :=
  match a, b with
  | holdfast_bnil, holdfast_bnil => true
  | holdfast_bcons x xs, holdfast_bcons y ys => holdfast_and (holdfast_eq_bool x y) (holdfast_bits_eqb xs ys)
  | _, _ => false
  end.

Definition holdfast_xorb (a b : bool) : bool := if a then holdfast_not b else b.

Fixpoint holdfast_bits_xor (a b : holdfast_bits) : holdfast_bits :=
  match a, b with
  | holdfast_bcons x xs, holdfast_bcons y ys => holdfast_bcons (holdfast_xorb x y) (holdfast_bits_xor xs ys)
  | _, _ => holdfast_bnil
  end.

Fixpoint holdfast_bits_and (a b : holdfast_bits) : holdfast_bits :=
  match a, b with
  | holdfast_bcons x xs, holdfast_bcons y ys => holdfast_bcons (holdfast_and x y) (holdfast_bits_and xs ys)
  | _, _ => holdfast_bnil
  end.

Fixpoint holdfast_bits_or (a b : holdfast_bits) : holdfast_bits :=
  match a, b with
  | holdfast_bcons x xs, holdfast_bcons y ys => holdfast_bcons (holdfast_or x y) (holdfast_bits_or xs ys)
  | _, _ => holdfast_bnil
  end.

Fixpoint holdfast_bits_not (a : holdfast_bits) : holdfast_bits :=
  match a with
  | holdfast_bcons x xs => holdfast_bcons (holdfast_not x) (holdfast_bits_not xs)
  | holdfast_bnil => holdfast_bnil
  end.

Fixpoint holdfast_bits_ult (a b : holdfast_bits) : bool :=
  match a, b with
  | _, holdfast_bnil => false
  | holdfast_bnil, holdfast_bcons _ _ => true
  | holdfast_bcons x xs, holdfast_bcons y ys =>
      if holdfast_eq_bool x y then holdfast_bits_ult xs ys else y
  end.

Fixpoint holdfast_bits_ule (a b : holdfast_bits) : bool :=
  match a, b with
  | holdfast_bnil, _ => true
  | holdfast_bcons _ _, holdfast_bnil => false
  | holdfast_bcons x xs, holdfast_bcons y ys =>
      if holdfast_eq_bool x y then holdfast_bits_ule xs ys else y
  end.

Fixpoint holdfast_bits_rev_acc (a acc : holdfast_bits) : holdfast_bits :=
  match a with
  | holdfast_bnil => acc
  | holdfast_bcons x xs => holdfast_bits_rev_acc xs (holdfast_bcons x acc)
  end.

Definition holdfast_bits_rev (a : holdfast_bits) : holdfast_bits :=
  holdfast_bits_rev_acc a holdfast_bnil.

Fixpoint holdfast_bits_add_lsb (a b : holdfast_bits) (carry : bool) : holdfast_bits :=
  match a, b with
  | holdfast_bcons x xs, holdfast_bcons y ys =>
      let sum := holdfast_xorb (holdfast_xorb x y) carry in
      let next_carry := holdfast_or (holdfast_and x y) (holdfast_and (holdfast_xorb x y) carry) in
      holdfast_bcons sum (holdfast_bits_add_lsb xs ys next_carry)
  | _, _ => holdfast_bnil
  end.

Definition holdfast_bits_add (a b : holdfast_bits) : holdfast_bits :=
  holdfast_bits_rev (holdfast_bits_add_lsb (holdfast_bits_rev a) (holdfast_bits_rev b) false).

Fixpoint holdfast_bits_sub_lsb (a b : holdfast_bits) (borrow : bool) : holdfast_bits :=
  match a, b with
  | holdfast_bcons x xs, holdfast_bcons y ys =>
      let diff := holdfast_xorb (holdfast_xorb x y) borrow in
      let next_borrow := holdfast_or (holdfast_and (holdfast_not x) y) (holdfast_and (holdfast_not (holdfast_xorb x y)) borrow) in
      holdfast_bcons diff (holdfast_bits_sub_lsb xs ys next_borrow)
  | _, _ => holdfast_bnil
  end.

Definition holdfast_bits_sub (a b : holdfast_bits) : holdfast_bits :=
  holdfast_bits_rev (holdfast_bits_sub_lsb (holdfast_bits_rev a) (holdfast_bits_rev b) false).

Definition holdfast_tag_bits (tag : nat) : nat :=
  match tag with
  | O => 8
  | S O => 16
  | S (S O) => 32
  | S (S (S O)) => 64
  | S (S (S (S O))) => 64
  | S (S (S (S (S O)))) => 8
  | S (S (S (S (S (S O))))) => 16
  | S (S (S (S (S (S (S O)))))) => 32
  | _ => 64
  end.

Inductive holdfast_word : nat -> Type@{holdfast_u0} :=
| holdfast_wnil : holdfast_word O
| holdfast_wcons : forall n, bool -> holdfast_word n -> holdfast_word (S n).

Fixpoint holdfast_word_bits {n : nat} (w : holdfast_word n) : holdfast_bits :=
  match w with
  | holdfast_wnil => holdfast_bnil
  | holdfast_wcons _ b tail => holdfast_bcons b (holdfast_word_bits tail)
  end.

Fixpoint holdfast_bits_word (n : nat) (bs : holdfast_bits) : holdfast_word n :=
  match n with
  | O => holdfast_wnil
  | S k => match bs with
           | holdfast_bnil => holdfast_wcons k false (holdfast_bits_word k holdfast_bnil)
           | holdfast_bcons b tail => holdfast_wcons k b (holdfast_bits_word k tail)
           end
  end.

Inductive holdfast_int (tag : nat) : Type@{holdfast_u0} :=
| holdfast_word_int : holdfast_word (holdfast_tag_bits tag) -> holdfast_int tag.

Definition holdfast_mk_int (tag : nat) (bs : holdfast_bits) : holdfast_int tag :=
  holdfast_word_int tag (holdfast_bits_word (holdfast_tag_bits tag) bs).
Definition holdfast_int_bits (tag : nat) (x : holdfast_int tag) : holdfast_bits :=
  match x with holdfast_word_int _ w => holdfast_word_bits w end.

Lemma holdfast_word_roundtrip : forall n (w : holdfast_word n),
  holdfast_bits_word n (holdfast_word_bits w) = w.
Proof. intros n w; induction w; simpl; congruence. Qed.

Definition holdfast_tag_signed (tag : nat) : bool :=
  Corelib.Init.Nat.leb 5 tag.

Fixpoint holdfast_bits_len (a : holdfast_bits) : nat :=
  match a with
  | holdfast_bnil => O
  | holdfast_bcons _ xs => S (holdfast_bits_len xs)
  end.

Fixpoint holdfast_bits_pad (n : nat) (fill : bool) (a : holdfast_bits) : holdfast_bits :=
  match n with
  | O => a
  | S k => holdfast_bcons fill (holdfast_bits_pad k fill a)
  end.

Definition holdfast_bits_head (a : holdfast_bits) : bool :=
  match a with
  | holdfast_bcons x _ => x
  | holdfast_bnil => false
  end.

Definition holdfast_bits_tail (a : holdfast_bits) : holdfast_bits :=
  match a with
  | holdfast_bcons _ xs => xs
  | holdfast_bnil => holdfast_bnil
  end.

Fixpoint holdfast_bits_snoc (a : holdfast_bits) (x : bool) : holdfast_bits :=
  match a with
  | holdfast_bnil => holdfast_bcons x holdfast_bnil
  | holdfast_bcons y ys => holdfast_bcons y (holdfast_bits_snoc ys x)
  end.

Fixpoint holdfast_bits_init (a : holdfast_bits) : holdfast_bits :=
  match a with
  | holdfast_bnil => holdfast_bnil
  | holdfast_bcons x xs =>
      match xs with
      | holdfast_bnil => holdfast_bnil
      | holdfast_bcons _ _ => holdfast_bcons x (holdfast_bits_init xs)
      end
  end.

Fixpoint holdfast_bits_fill (a : holdfast_bits) (b : bool) : holdfast_bits :=
  match a with
  | holdfast_bnil => holdfast_bnil
  | holdfast_bcons _ xs => holdfast_bcons b (holdfast_bits_fill xs b)
  end.

Definition holdfast_bits_zero_like (a : holdfast_bits) : holdfast_bits :=
  holdfast_bits_fill a false.

Definition holdfast_bits_is_zero (a : holdfast_bits) : bool :=
  holdfast_bits_eqb a (holdfast_bits_zero_like a).

Definition holdfast_bits_neg (a : holdfast_bits) : holdfast_bits :=
  holdfast_bits_sub (holdfast_bits_zero_like a) a.

Definition holdfast_bits_shl1 (a : holdfast_bits) : holdfast_bits :=
  match a with
  | holdfast_bnil => holdfast_bnil
  | holdfast_bcons _ xs => holdfast_bits_snoc xs false
  end.

Definition holdfast_bits_shr1 (fill : bool) (a : holdfast_bits) : holdfast_bits :=
  match a with
  | holdfast_bnil => holdfast_bnil
  | holdfast_bcons _ _ => holdfast_bcons fill (holdfast_bits_init a)
  end.

Fixpoint holdfast_bits_shl_n (k : nat) (a : holdfast_bits) : holdfast_bits :=
  match k with
  | O => a
  | S j => holdfast_bits_shl_n j (holdfast_bits_shl1 a)
  end.

Fixpoint holdfast_bits_shr_n (k : nat) (fill : bool) (a : holdfast_bits) : holdfast_bits :=
  match k with
  | O => a
  | S j => holdfast_bits_shr_n j fill (holdfast_bits_shr1 fill a)
  end.

Fixpoint holdfast_bits_mul_acc (b a acc : holdfast_bits) : holdfast_bits :=
  match b with
  | holdfast_bnil => acc
  | holdfast_bcons x xs =>
      let shifted := holdfast_bits_shl1 acc in
      holdfast_bits_mul_acc xs a (if x then holdfast_bits_add shifted a else shifted)
  end.

Definition holdfast_bits_mul (a b : holdfast_bits) : holdfast_bits :=
  holdfast_bits_mul_acc b a (holdfast_bits_zero_like a).

Fixpoint holdfast_bits_divmod_acc (n d r qrev : holdfast_bits) : @prod holdfast_bits holdfast_bits :=
  match n with
  | holdfast_bnil => @pair holdfast_bits holdfast_bits (holdfast_bits_rev qrev) r
  | holdfast_bcons x xs =>
      let shifted := holdfast_bits_snoc (holdfast_bits_tail r) x in
      if holdfast_bits_ule d shifted
      then holdfast_bits_divmod_acc xs d (holdfast_bits_sub shifted d) (holdfast_bcons true qrev)
      else holdfast_bits_divmod_acc xs d shifted (holdfast_bcons false qrev)
  end.

Definition holdfast_bits_udivmod (n d : holdfast_bits) : @prod holdfast_bits holdfast_bits :=
  let result :=
    holdfast_bits_divmod_acc n (holdfast_bcons false d) (holdfast_bcons false (holdfast_bits_zero_like n)) holdfast_bnil
  in
  @pair holdfast_bits holdfast_bits
    (@fst holdfast_bits holdfast_bits result) (holdfast_bits_tail (@snd holdfast_bits holdfast_bits result)).

Definition holdfast_bits_extend (signed : bool) (a : holdfast_bits) : holdfast_bits :=
  holdfast_bits_pad (holdfast_bits_len a) (holdfast_and signed (holdfast_bits_head a)) a.

Fixpoint holdfast_bits_take_lsb (n : nat) (fill : bool) (a : holdfast_bits) : holdfast_bits :=
  match n with
  | O => holdfast_bnil
  | S k =>
      match a with
      | holdfast_bnil => holdfast_bcons fill (holdfast_bits_take_lsb k fill holdfast_bnil)
      | holdfast_bcons x xs => holdfast_bcons x (holdfast_bits_take_lsb k fill xs)
      end
  end.

Definition holdfast_bits_resize (n : nat) (fill : bool) (a : holdfast_bits) : holdfast_bits :=
  holdfast_bits_rev (holdfast_bits_take_lsb n fill (holdfast_bits_rev a)).

Definition holdfast_bits_max (signed : bool) (a : holdfast_bits) : holdfast_bits :=
  if signed then holdfast_bcons false (holdfast_bits_fill (holdfast_bits_tail a) true) else holdfast_bits_fill a true.

Definition holdfast_bits_min (signed : bool) (a : holdfast_bits) : holdfast_bits :=
  if signed then holdfast_bcons true (holdfast_bits_zero_like (holdfast_bits_tail a)) else holdfast_bits_zero_like a.

Definition holdfast_bits_add_overflows (signed : bool) (a b sum : holdfast_bits) : bool :=
  if signed
  then holdfast_and (holdfast_eq_bool (holdfast_bits_head a) (holdfast_bits_head b))
                (holdfast_ne_bool (holdfast_bits_head sum) (holdfast_bits_head a))
  else holdfast_bits_ult sum a.

Definition holdfast_bits_sub_overflows (signed : bool) (a b diff : holdfast_bits) : bool :=
  if signed
  then holdfast_and (holdfast_ne_bool (holdfast_bits_head a) (holdfast_bits_head b))
                (holdfast_ne_bool (holdfast_bits_head diff) (holdfast_bits_head a))
  else holdfast_bits_ult a b.

Definition holdfast_bits_mul_overflows (signed : bool) (a b : holdfast_bits) : bool :=
  holdfast_not
    (holdfast_bits_eqb
      (holdfast_bits_extend signed (holdfast_bits_mul a b))
      (holdfast_bits_mul (holdfast_bits_extend signed a) (holdfast_bits_extend signed b))).

Fixpoint holdfast_bits_to_nat_acc (bs : holdfast_bits) (acc : nat) : nat :=
  match bs with
  | holdfast_bnil => acc
  | holdfast_bcons b rest =>
      holdfast_bits_to_nat_acc rest (Corelib.Init.Nat.add (Corelib.Init.Nat.mul 2 acc) (if b then 1 else 0))
  end.

Fixpoint holdfast_nat_to_bits_lsb (w n : nat) : holdfast_bits :=
  match w with
  | O => holdfast_bnil
  | S k => holdfast_bcons (Corelib.Init.Nat.odd n) (holdfast_nat_to_bits_lsb k (Corelib.Init.Nat.div2 n))
  end.

Definition holdfast_nat_to_bits (w n : nat) : holdfast_bits :=
  holdfast_bits_rev (holdfast_nat_to_bits_lsb w n).

Fixpoint holdfast_nat_shr_n (k n : nat) : nat :=
  match k with
  | O => n
  | S j => holdfast_nat_shr_n j (Corelib.Init.Nat.div2 n)
  end.

Definition holdfast_nat_fits (w n : nat) : bool :=
  Corelib.Init.Nat.eqb (holdfast_nat_shr_n w n) O.

Definition holdfast_ArithmeticError : Type@{holdfast_u0} :=
  @sum unit (@sum unit unit).
Definition holdfast_ArithmeticError_Overflow (_ : unit) : holdfast_ArithmeticError :=
  @inl unit (@sum unit unit) tt.
Definition holdfast_ArithmeticError_ZeroDivisor (_ : unit) : holdfast_ArithmeticError :=
  @inr unit (@sum unit unit) (@inl unit unit tt).
Definition holdfast_ArithmeticError_InvalidShift (_ : unit) : holdfast_ArithmeticError :=
  @inr unit (@sum unit unit) (@inr unit unit tt).

Definition holdfast_ConversionError : Type@{holdfast_u0} := unit.
Definition holdfast_ConversionError_OutOfRange (_ : unit) : holdfast_ConversionError := tt.

Definition holdfast_Result (TValue TError : Type@{holdfast_u0}) : Type@{holdfast_u0} :=
  @sum TError TValue.
Definition holdfast_Result_Err (TValue TError : Type@{holdfast_u0}) (e : TError) : holdfast_Result TValue TError :=
  @inl TError TValue e.
Definition holdfast_Result_Ok (TValue TError : Type@{holdfast_u0}) (v : TValue) : holdfast_Result TValue TError :=
  @inr TError TValue v.

Fixpoint holdfast_bits_zero (a : holdfast_bits) : bool :=
  match a with holdfast_bnil => true | holdfast_bcons x rest => if x then false else holdfast_bits_zero rest end.

Definition holdfast_int_add (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  if holdfast_bits_zero (holdfast_bits_rev (holdfast_int_bits tag b)) then a
  else holdfast_mk_int tag (holdfast_bits_add (holdfast_int_bits tag a) (holdfast_int_bits tag b)).
Definition holdfast_int_sub (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_sub (holdfast_int_bits tag a) (holdfast_int_bits tag b)).
Definition holdfast_int_negative (tag : nat) (bs : holdfast_bits) : bool :=
  holdfast_and (holdfast_tag_signed tag) (holdfast_bits_head bs).
Definition holdfast_int_magnitude (tag : nat) (bs : holdfast_bits) : holdfast_bits :=
  if holdfast_int_negative tag bs then holdfast_bits_neg bs else bs.
Definition holdfast_int_mul (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_mul (holdfast_int_bits tag a) (holdfast_int_bits tag b)).
Definition holdfast_int_div (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  if holdfast_bits_is_zero y then holdfast_mk_int tag (holdfast_bits_zero_like x) else
  let q := @fst holdfast_bits holdfast_bits
    (holdfast_bits_udivmod (holdfast_int_magnitude tag x) (holdfast_int_magnitude tag y)) in
  holdfast_mk_int tag
    (if holdfast_xorb (holdfast_int_negative tag x) (holdfast_int_negative tag y) then holdfast_bits_neg q else q).
Definition holdfast_int_rem (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  if holdfast_bits_is_zero y then a else
  let r := @snd holdfast_bits holdfast_bits
    (holdfast_bits_udivmod (holdfast_int_magnitude tag x) (holdfast_int_magnitude tag y)) in
  holdfast_mk_int tag (if holdfast_int_negative tag x then holdfast_bits_neg r else r).
Definition holdfast_int_neg (tag : nat) (a : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_neg (holdfast_int_bits tag a)).
Definition holdfast_int_and (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_and (holdfast_int_bits tag a) (holdfast_int_bits tag b)).
Definition holdfast_int_or (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_or (holdfast_int_bits tag a) (holdfast_int_bits tag b)).
Definition holdfast_int_xor (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_xor (holdfast_int_bits tag a) (holdfast_int_bits tag b)).
Definition holdfast_int_not (tag : nat) (a : holdfast_int tag) : holdfast_int tag :=
  holdfast_mk_int tag (holdfast_bits_not (holdfast_int_bits tag a)).
Definition holdfast_shift_amount (tag : nat) (count : holdfast_int (4 : nat)) : option nat :=
  let c := holdfast_int_bits (4 : nat) count in
  if holdfast_bits_ult c (holdfast_nat_to_bits (holdfast_bits_len c) (holdfast_tag_bits tag))
  then Some (holdfast_bits_to_nat_acc c O)
  else None.
Definition holdfast_int_shl (tag : nat) (a : holdfast_int tag) (count : holdfast_int (4 : nat)) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  match holdfast_shift_amount tag count with
  | Some k => holdfast_mk_int tag (holdfast_bits_shl_n k x)
  | None => holdfast_mk_int tag (holdfast_bits_zero_like x)
  end.
Definition holdfast_int_shr (tag : nat) (a : holdfast_int tag) (count : holdfast_int (4 : nat)) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let fill := holdfast_int_negative tag x in
  match holdfast_shift_amount tag count with
  | Some k => holdfast_mk_int tag (holdfast_bits_shr_n k fill x)
  | None => holdfast_mk_int tag (holdfast_bits_fill x fill)
  end.
Definition holdfast_int_eq (tag : nat) (a b : holdfast_int tag) : bool :=
  holdfast_bits_eqb (holdfast_int_bits tag a) (holdfast_int_bits tag b).
Definition holdfast_int_ne (tag : nat) (a b : holdfast_int tag) : bool :=
  holdfast_not (holdfast_int_eq tag a b).
Definition holdfast_int_key (tag : nat) (a : holdfast_int tag) : holdfast_bits :=
  let bs := holdfast_int_bits tag a in
  if holdfast_tag_signed tag
  then match bs with
       | holdfast_bcons msb rest => holdfast_bcons (holdfast_not msb) rest
       | holdfast_bnil => holdfast_bnil
       end
  else bs.
Definition holdfast_int_lt (tag : nat) (a b : holdfast_int tag) : bool :=
  holdfast_bits_ult (holdfast_int_key tag a) (holdfast_int_key tag b).
Definition holdfast_int_le (tag : nat) (a b : holdfast_int tag) : bool :=
  holdfast_bits_ule (holdfast_int_key tag a) (holdfast_int_key tag b).
Definition holdfast_int_gt (tag : nat) (a b : holdfast_int tag) : bool :=
  holdfast_bits_ult (holdfast_int_key tag b) (holdfast_int_key tag a).
Definition holdfast_int_ge (tag : nat) (a b : holdfast_int tag) : bool :=
  holdfast_bits_ule (holdfast_int_key tag b) (holdfast_int_key tag a).
Definition holdfast_int_wrap_add (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_int_add tag a b.
Definition holdfast_int_wrap_sub (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_int_sub tag a b.
Definition holdfast_int_wrap_mul (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  holdfast_int_mul tag a b.
Definition holdfast_int_wrap_neg (tag : nat) (a : holdfast_int tag) : holdfast_int tag :=
  holdfast_int_neg tag a.
Definition holdfast_int_wrap_shl (tag : nat) (a : holdfast_int tag) (count : holdfast_int (4 : nat)) : holdfast_int tag :=
  holdfast_int_shl tag a count.
Definition holdfast_int_sat_add (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  let s := holdfast_tag_signed tag in
  let r := holdfast_bits_add x y in
  holdfast_mk_int tag
    (if holdfast_bits_add_overflows s x y r
     then (if holdfast_int_negative tag x then holdfast_bits_min s x else holdfast_bits_max s x)
     else r).
Definition holdfast_int_sat_sub (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  let s := holdfast_tag_signed tag in
  let r := holdfast_bits_sub x y in
  holdfast_mk_int tag
    (if holdfast_bits_sub_overflows s x y r
     then (if s then (if holdfast_bits_head x then holdfast_bits_min s x else holdfast_bits_max s x)
           else holdfast_bits_min s x)
     else r).
Definition holdfast_int_sat_mul (tag : nat) (a b : holdfast_int tag) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  let s := holdfast_tag_signed tag in
  holdfast_mk_int tag
    (if holdfast_bits_mul_overflows s x y
     then (if holdfast_xorb (holdfast_int_negative tag x) (holdfast_int_negative tag y)
           then holdfast_bits_min s x else holdfast_bits_max s x)
     else holdfast_bits_mul x y).
Definition holdfast_int_sat_neg (tag : nat) (a : holdfast_int tag) : holdfast_int tag :=
  let x := holdfast_int_bits tag a in
  let s := holdfast_tag_signed tag in
  holdfast_mk_int tag
    (if s
     then (if holdfast_bits_eqb x (holdfast_bits_min s x) then holdfast_bits_max s x else holdfast_bits_neg x)
     else holdfast_bits_zero_like x).
Definition holdfast_int_ok (tag : nat) (x : holdfast_bits) : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  holdfast_Result_Ok (holdfast_int tag) holdfast_ArithmeticError (holdfast_mk_int tag x).
Definition holdfast_int_err (tag : nat) (e : holdfast_ArithmeticError)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  holdfast_Result_Err (holdfast_int tag) holdfast_ArithmeticError e.
Definition holdfast_int_chk_add (tag : nat) (a b : holdfast_int tag)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  let r := holdfast_bits_add x y in
  if holdfast_bits_add_overflows (holdfast_tag_signed tag) x y r
  then holdfast_int_err tag (holdfast_ArithmeticError_Overflow tt)
  else holdfast_int_ok tag r.
Definition holdfast_int_chk_sub (tag : nat) (a b : holdfast_int tag)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  let r := holdfast_bits_sub x y in
  if holdfast_bits_sub_overflows (holdfast_tag_signed tag) x y r
  then holdfast_int_err tag (holdfast_ArithmeticError_Overflow tt)
  else holdfast_int_ok tag r.
Definition holdfast_int_chk_mul (tag : nat) (a b : holdfast_int tag)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  if holdfast_bits_mul_overflows (holdfast_tag_signed tag) x y
  then holdfast_int_err tag (holdfast_ArithmeticError_Overflow tt)
  else holdfast_int_ok tag (holdfast_bits_mul x y).
Definition holdfast_int_chk_div (tag : nat) (a b : holdfast_int tag)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  let x := holdfast_int_bits tag a in
  let y := holdfast_int_bits tag b in
  let s := holdfast_tag_signed tag in
  if holdfast_bits_is_zero y then holdfast_int_err tag (holdfast_ArithmeticError_ZeroDivisor tt) else
  if holdfast_and s (holdfast_and (holdfast_bits_eqb x (holdfast_bits_min s x)) (holdfast_bits_eqb y (holdfast_bits_fill y true)))
  then holdfast_int_err tag (holdfast_ArithmeticError_Overflow tt)
  else holdfast_Result_Ok (holdfast_int tag) holdfast_ArithmeticError (holdfast_int_div tag a b).
Definition holdfast_int_chk_rem (tag : nat) (a b : holdfast_int tag)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  if holdfast_bits_is_zero (holdfast_int_bits tag b)
  then holdfast_int_err tag (holdfast_ArithmeticError_ZeroDivisor tt)
  else holdfast_Result_Ok (holdfast_int tag) holdfast_ArithmeticError (holdfast_int_rem tag a b).
Definition holdfast_int_chk_neg (tag : nat) (a : holdfast_int tag)
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  let x := holdfast_int_bits tag a in
  let s := holdfast_tag_signed tag in
  if (if s then holdfast_bits_eqb x (holdfast_bits_min s x) else holdfast_not (holdfast_bits_is_zero x))
  then holdfast_int_err tag (holdfast_ArithmeticError_Overflow tt)
  else holdfast_int_ok tag (holdfast_bits_neg x).
Definition holdfast_int_chk_shl (tag : nat) (a : holdfast_int tag) (count : holdfast_int (4 : nat))
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  let x := holdfast_int_bits tag a in
  match holdfast_shift_amount tag count with
  | None => holdfast_int_err tag (holdfast_ArithmeticError_InvalidShift tt)
  | Some k =>
      let r := holdfast_bits_shl_n k x in
      if holdfast_bits_eqb (holdfast_bits_shr_n k (holdfast_int_negative tag r) r) x
      then holdfast_int_ok tag r
      else holdfast_int_err tag (holdfast_ArithmeticError_Overflow tt)
  end.
Definition holdfast_int_chk_shr (tag : nat) (a : holdfast_int tag) (count : holdfast_int (4 : nat))
    : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError :=
  match holdfast_shift_amount tag count with
  | None => holdfast_int_err tag (holdfast_ArithmeticError_InvalidShift tt)
  | Some _ => holdfast_Result_Ok (holdfast_int tag) holdfast_ArithmeticError (holdfast_int_shr tag a count)
  end.
Definition holdfast_int_to_nat (tag : nat) (a : holdfast_int tag) : nat :=
  let bs := holdfast_int_bits tag a in
  if holdfast_int_negative tag bs then O else holdfast_bits_to_nat_acc bs O.
Definition holdfast_nat_hex_width (minimum value : nat) : nat :=
  Nat.max minimum (S (Nat.div (Nat.log2 value) 4)).

Fixpoint holdfast_significant_bits (bs : holdfast_bits) : nat :=
  match bs with
  | holdfast_bnil => O
  | holdfast_bcons true tail => S (holdfast_bits_len tail)
  | holdfast_bcons false tail => holdfast_significant_bits tail
  end.

Definition holdfast_int_hex_width (tag minimum : nat) (value : holdfast_int tag) : nat :=
  Nat.max minimum (S (Nat.div (Nat.pred (holdfast_significant_bits (holdfast_int_bits tag value))) 4)).

Definition holdfast_int_from (src dst : nat) (x : holdfast_int src) : holdfast_int dst :=
  let bs := holdfast_int_bits src x in
  holdfast_mk_int dst (holdfast_bits_resize (holdfast_tag_bits dst) (holdfast_int_negative src bs) bs).
Definition holdfast_int_try_from (src dst : nat) (x : holdfast_int src)
    : holdfast_Result (holdfast_int dst) holdfast_ConversionError :=
  let c := holdfast_int_from src dst x in
  if holdfast_and
       (holdfast_int_eq src (holdfast_int_from dst src c) x)
       (holdfast_eq_bool (holdfast_int_negative src (holdfast_int_bits src x)) (holdfast_int_negative dst (holdfast_int_bits dst c)))
  then holdfast_Result_Ok (holdfast_int dst) holdfast_ConversionError c
  else holdfast_Result_Err (holdfast_int dst) holdfast_ConversionError (holdfast_ConversionError_OutOfRange tt).
Definition holdfast_int_try_from_Nat (dst : nat) (n : nat)
    : holdfast_Result (holdfast_int dst) holdfast_ConversionError :=
  let w := holdfast_tag_bits dst in
  if holdfast_nat_fits (if holdfast_tag_signed dst then Corelib.Init.Nat.pred w else w) n
  then holdfast_Result_Ok (holdfast_int dst) holdfast_ConversionError (holdfast_mk_int dst (holdfast_nat_to_bits w n))
  else holdfast_Result_Err (holdfast_int dst) holdfast_ConversionError (holdfast_ConversionError_OutOfRange tt).

Definition holdfast_char_scalar_bits (bs : holdfast_bits) : bool :=
  holdfast_and
    (holdfast_bits_ule bs (holdfast_x0 (holdfast_x0 (holdfast_x1 (holdfast_x0 (holdfast_xf (holdfast_xf (holdfast_xf (holdfast_xf holdfast_bnil)))))))))
    (holdfast_or
      (holdfast_bits_ult bs (holdfast_x0 (holdfast_x0 (holdfast_x0 (holdfast_x0 (holdfast_xd (holdfast_x8 (holdfast_x0 (holdfast_x0 holdfast_bnil)))))))))
      (holdfast_bits_ult (holdfast_x0 (holdfast_x0 (holdfast_x0 (holdfast_x0 (holdfast_xd (holdfast_xf (holdfast_xf (holdfast_xf holdfast_bnil)))))))) bs)).

Definition holdfast_valid_scalar (n : nat) : bool :=
  holdfast_and (holdfast_nat_fits 32 n) (holdfast_char_scalar_bits (holdfast_nat_to_bits 32 n)).

Inductive holdfast_char : Type@{holdfast_u0} :=
| holdfast_scalar : forall n, holdfast_valid_scalar n = true -> holdfast_char.

Definition holdfast_mk_char (n : nat) : holdfast_char :=
  match holdfast_valid_scalar n as b return (holdfast_valid_scalar n = b -> holdfast_char) with
  | true => fun valid => holdfast_scalar n valid
  | false => fun _ => holdfast_scalar O eq_refl
  end eq_refl.

Definition holdfast_char_code (c : holdfast_char) : nat :=
  match c with
  | holdfast_scalar n _ => n
  end.

Lemma holdfast_char_wellformed : forall c, holdfast_valid_scalar (holdfast_char_code c) = true.
Proof. intros [n valid]; exact valid. Qed.

Definition holdfast_char_eq (a b : holdfast_char) : bool :=
  Corelib.Init.Nat.eqb (holdfast_char_code a) (holdfast_char_code b).
Definition holdfast_char_ne (a b : holdfast_char) : bool :=
  holdfast_not (holdfast_char_eq a b).
Definition holdfast_char_lt (a b : holdfast_char) : bool :=
  Corelib.Init.Nat.ltb (holdfast_char_code a) (holdfast_char_code b).
Definition holdfast_char_le (a b : holdfast_char) : bool :=
  Corelib.Init.Nat.leb (holdfast_char_code a) (holdfast_char_code b).
Definition holdfast_char_gt (a b : holdfast_char) : bool :=
  Corelib.Init.Nat.ltb (holdfast_char_code b) (holdfast_char_code a).
Definition holdfast_char_ge (a b : holdfast_char) : bool :=
  Corelib.Init.Nat.leb (holdfast_char_code b) (holdfast_char_code a).
Definition holdfast_char_to_nat (c : holdfast_char) : nat :=
  holdfast_char_code c.
Definition holdfast_char_to_u32 (c : holdfast_char) : holdfast_int (2 : nat) :=
  holdfast_mk_int (2 : nat) (holdfast_nat_to_bits 32 (holdfast_char_code c)).
Definition holdfast_char_from_u8 (b : holdfast_int (0 : nat)) : holdfast_char :=
  holdfast_mk_char (holdfast_bits_to_nat_acc (holdfast_int_bits (0 : nat) b) O).
Definition holdfast_char_try_from_u32 (v : holdfast_int (2 : nat))
    : holdfast_Result holdfast_char holdfast_ConversionError :=
  let bs := holdfast_int_bits (2 : nat) v in
  if holdfast_char_scalar_bits bs
  then holdfast_Result_Ok holdfast_char holdfast_ConversionError (holdfast_mk_char (holdfast_bits_to_nat_acc bs O))
  else holdfast_Result_Err holdfast_char holdfast_ConversionError (holdfast_ConversionError_OutOfRange tt).
Definition holdfast_char_try_from_Nat (n : nat)
    : holdfast_Result holdfast_char holdfast_ConversionError :=
  if holdfast_valid_scalar n
  then holdfast_Result_Ok holdfast_char holdfast_ConversionError (holdfast_mk_char n)
  else holdfast_Result_Err holdfast_char holdfast_ConversionError (holdfast_ConversionError_OutOfRange tt).

Definition holdfast_u8_zero : holdfast_int (0 : nat) :=
  holdfast_mk_int (0 : nat) (holdfast_bits_pad 8 false holdfast_bnil).

Definition holdfast_usize_zero : holdfast_int (4 : nat) :=
  holdfast_mk_int (4 : nat) (holdfast_bits_pad 64 false holdfast_bnil).

Definition holdfast_false_elim (P : Type@{holdfast_u0}) (h : @Corelib.Init.Logic.eq bool true false) : P :=
  match h in (@Corelib.Init.Logic.eq _ _ b) return (if b then unit else P) with
  | @Corelib.Init.Logic.eq_refl _ _ => tt
  end.

Definition holdfast_false_true_elim (P : Type@{holdfast_u0}) (h : @Corelib.Init.Logic.eq bool false true) : P :=
  holdfast_false_elim P (@Corelib.Init.Logic.eq_sym bool false true h).

Definition holdfast_and_intro (a b : bool)
    (ha : @Corelib.Init.Logic.eq bool a true)
    (hb : @Corelib.Init.Logic.eq bool b true)
    : @Corelib.Init.Logic.eq bool (holdfast_and a b) true :=
  @Corelib.Init.Logic.eq_trans bool (holdfast_and a b) (holdfast_and true b) true
    (@Corelib.Init.Logic.f_equal bool bool (fun x : bool => holdfast_and x b) a true ha)
    hb.

Definition holdfast_and_left (a b : bool)
    (h : @Corelib.Init.Logic.eq bool (holdfast_and a b) true)
    : @Corelib.Init.Logic.eq bool a true :=
  match a as a0 return (@Corelib.Init.Logic.eq bool (holdfast_and a0 b) true -> @Corelib.Init.Logic.eq bool a0 true) with
  | true => fun _ => @Corelib.Init.Logic.eq_refl bool true
  | false => fun h0 => h0
  end h.

Definition holdfast_and_right (a b : bool)
    (h : @Corelib.Init.Logic.eq bool (holdfast_and a b) true)
    : @Corelib.Init.Logic.eq bool b true :=
  match a as a0 return (@Corelib.Init.Logic.eq bool (holdfast_and a0 b) true -> @Corelib.Init.Logic.eq bool b true) with
  | true => fun h0 => h0
  | false => fun h0 => holdfast_false_true_elim (@Corelib.Init.Logic.eq bool b true) h0
  end h.

Definition holdfast_or_false_l (a b : bool)
    (h : @Corelib.Init.Logic.eq bool (holdfast_or a b) false)
    : @Corelib.Init.Logic.eq bool a false :=
  match a as a0 return (@Corelib.Init.Logic.eq bool (holdfast_or a0 b) false -> @Corelib.Init.Logic.eq bool a0 false) with
  | true => fun h0 => holdfast_false_elim (@Corelib.Init.Logic.eq bool true false) h0
  | false => fun _ => @Corelib.Init.Logic.eq_refl bool false
  end h.

Definition holdfast_or_false_r (a b : bool)
    (h : @Corelib.Init.Logic.eq bool (holdfast_or a b) false)
    : @Corelib.Init.Logic.eq bool b false :=
  match a as a0 return (@Corelib.Init.Logic.eq bool (holdfast_or a0 b) false -> @Corelib.Init.Logic.eq bool b false) with
  | true => fun h0 => holdfast_false_elim (@Corelib.Init.Logic.eq bool b false) h0
  | false => fun h0 => h0
  end h.

Definition holdfast_eq_bool_refl (b : bool) : @Corelib.Init.Logic.eq bool (holdfast_eq_bool b b) true :=
  match b as b0 return (@Corelib.Init.Logic.eq bool (holdfast_eq_bool b0 b0) true) with
  | true => @Corelib.Init.Logic.eq_refl bool true
  | false => @Corelib.Init.Logic.eq_refl bool true
  end.

Definition holdfast_eq_bool_of_eq (a b : bool) (p : @Corelib.Init.Logic.eq bool a b)
    : @Corelib.Init.Logic.eq bool (holdfast_eq_bool a b) true :=
  match p in (@Corelib.Init.Logic.eq _ _ b') return (@Corelib.Init.Logic.eq bool (holdfast_eq_bool a b') true) with
  | @Corelib.Init.Logic.eq_refl _ _ => holdfast_eq_bool_refl a
  end.

Definition holdfast_eq_bool_true (a b : bool) (h : @Corelib.Init.Logic.eq bool (holdfast_eq_bool a b) true)
    : @Corelib.Init.Logic.eq bool a b :=
  match a as a0, b as b0 return (@Corelib.Init.Logic.eq bool (holdfast_eq_bool a0 b0) true -> @Corelib.Init.Logic.eq bool a0 b0) with
  | true, true => fun _ => @Corelib.Init.Logic.eq_refl bool true
  | true, false => fun h0 => @Corelib.Init.Logic.eq_sym bool false true h0
  | false, true => fun h0 => h0
  | false, false => fun _ => @Corelib.Init.Logic.eq_refl bool false
  end h.

Fixpoint holdfast_bits_eqb_refl (a : holdfast_bits) {struct a} : @Corelib.Init.Logic.eq bool (holdfast_bits_eqb a a) true :=
  match a as a0 return (@Corelib.Init.Logic.eq bool (holdfast_bits_eqb a0 a0) true) with
  | holdfast_bnil => @Corelib.Init.Logic.eq_refl bool true
  | holdfast_bcons x xs => holdfast_and_intro (holdfast_eq_bool x x) (holdfast_bits_eqb xs xs) (holdfast_eq_bool_refl x) (holdfast_bits_eqb_refl xs)
  end.

Fixpoint holdfast_bits_eqb_true (a b : holdfast_bits) {struct a}
    : @Corelib.Init.Logic.eq bool (holdfast_bits_eqb a b) true -> @Corelib.Init.Logic.eq holdfast_bits a b :=
  match a as a0, b as b0 return (@Corelib.Init.Logic.eq bool (holdfast_bits_eqb a0 b0) true -> @Corelib.Init.Logic.eq holdfast_bits a0 b0) with
  | holdfast_bnil, holdfast_bnil => fun _ => @Corelib.Init.Logic.eq_refl holdfast_bits holdfast_bnil
  | holdfast_bnil, holdfast_bcons y ys => fun h => holdfast_false_true_elim (@Corelib.Init.Logic.eq holdfast_bits holdfast_bnil (holdfast_bcons y ys)) h
  | holdfast_bcons x xs, holdfast_bnil => fun h => holdfast_false_true_elim (@Corelib.Init.Logic.eq holdfast_bits (holdfast_bcons x xs) holdfast_bnil) h
  | holdfast_bcons x xs, holdfast_bcons y ys => fun h =>
      match holdfast_eq_bool_true x y (holdfast_and_left (holdfast_eq_bool x y) (holdfast_bits_eqb xs ys) h) in (@Corelib.Init.Logic.eq _ _ y0)
        return (@Corelib.Init.Logic.eq holdfast_bits (holdfast_bcons x xs) (holdfast_bcons y0 ys)) with
      | @Corelib.Init.Logic.eq_refl _ _ =>
          @Corelib.Init.Logic.f_equal holdfast_bits holdfast_bits (holdfast_bcons x) xs ys
            (holdfast_bits_eqb_true xs ys (holdfast_and_right (holdfast_eq_bool x y) (holdfast_bits_eqb xs ys) h))
      end
  end.

Definition holdfast_int_eq_refl (tag : nat) (x : holdfast_int tag)
    : @Corelib.Init.Logic.eq bool (holdfast_int_eq tag x x) true :=
  holdfast_bits_eqb_refl (holdfast_int_bits tag x).

Definition holdfast_int_eq_of_eq (tag : nat) (x y : holdfast_int tag)
    (p : @Corelib.Init.Logic.eq (holdfast_int tag) x y)
    : @Corelib.Init.Logic.eq bool (holdfast_int_eq tag x y) true :=
  match p in (@Corelib.Init.Logic.eq _ _ y') return (@Corelib.Init.Logic.eq bool (holdfast_int_eq tag x y') true) with
  | @Corelib.Init.Logic.eq_refl _ _ => holdfast_int_eq_refl tag x
  end.

Lemma holdfast_int_eq_true (tag : nat) (x y : holdfast_int tag)
    (h : holdfast_int_eq tag x y = true) : x = y.
Proof.
  destruct x as [a], y as [b].
  apply (holdfast_bits_eqb_true (holdfast_word_bits a) (holdfast_word_bits b)) in h.
  apply (f_equal (holdfast_bits_word (holdfast_tag_bits tag))) in h.
  rewrite !holdfast_word_roundtrip in h. now subst.
Qed.

Definition holdfast_int_ne_false (tag : nat) (x y : holdfast_int tag)
    (h : @Corelib.Init.Logic.eq bool (holdfast_int_ne tag x y) true)
    : @Corelib.Init.Logic.eq bool (holdfast_int_eq tag x y) false :=
  match holdfast_int_eq tag x y as b return (@Corelib.Init.Logic.eq bool (holdfast_not b) true -> @Corelib.Init.Logic.eq bool b false) with
  | true => fun h0 => @Corelib.Init.Logic.eq_sym bool false true h0
  | false => fun _ => @Corelib.Init.Logic.eq_refl bool false
  end h.

Definition holdfast_int_eq_sym_false (tag : nat) (x y : holdfast_int tag)
    (h : @Corelib.Init.Logic.eq bool (holdfast_int_eq tag x y) false)
    : @Corelib.Init.Logic.eq bool (holdfast_int_eq tag y x) false :=
  match holdfast_int_eq tag y x as b return (@Corelib.Init.Logic.eq bool (holdfast_int_eq tag y x) b -> @Corelib.Init.Logic.eq bool b false) with
  | true => fun hyx =>
      holdfast_false_elim (@Corelib.Init.Logic.eq bool true false)
        (@Corelib.Init.Logic.eq_trans bool true (holdfast_int_eq tag x y) false
          (@Corelib.Init.Logic.eq_sym bool (holdfast_int_eq tag x y) true
            (holdfast_int_eq_of_eq tag x y (@Corelib.Init.Logic.eq_sym (holdfast_int tag) y x (holdfast_int_eq_true tag y x hyx))))
          h)
  | false => fun _ => @Corelib.Init.Logic.eq_refl bool false
  end (@Corelib.Init.Logic.eq_refl bool (holdfast_int_eq tag y x)).

Fixpoint holdfast_bits_ult_ule_false (P : Type@{holdfast_u0}) (a b : holdfast_bits) {struct a}
    : @Corelib.Init.Logic.eq bool (holdfast_bits_ult a b) true ->
      @Corelib.Init.Logic.eq bool (holdfast_bits_ule b a) true -> P :=
  match a as a0, b as b0 return (@Corelib.Init.Logic.eq bool (holdfast_bits_ult a0 b0) true -> @Corelib.Init.Logic.eq bool (holdfast_bits_ule b0 a0) true -> P) with
  | holdfast_bnil, holdfast_bnil => fun h1 _ => holdfast_false_true_elim P h1
  | holdfast_bnil, holdfast_bcons _ _ => fun _ h2 => holdfast_false_true_elim P h2
  | holdfast_bcons _ _, holdfast_bnil => fun h1 _ => holdfast_false_true_elim P h1
  | holdfast_bcons x xs, holdfast_bcons y ys =>
      match x as x0, y as y0 return (@Corelib.Init.Logic.eq bool (if holdfast_eq_bool x0 y0 then holdfast_bits_ult xs ys else y0) true -> @Corelib.Init.Logic.eq bool (if holdfast_eq_bool y0 x0 then holdfast_bits_ule ys xs else x0) true -> P) with
      | true, true => fun h1 h2 => holdfast_bits_ult_ule_false P xs ys h1 h2
      | false, false => fun h1 h2 => holdfast_bits_ult_ule_false P xs ys h1 h2
      | true, false => fun h1 _ => holdfast_false_true_elim P h1
      | false, true => fun _ h2 => holdfast_false_true_elim P h2
      end
  end.

Fixpoint holdfast_bits_ult_ule_trans (a b c : holdfast_bits) {struct a}
    : @Corelib.Init.Logic.eq bool (holdfast_bits_ult a b) true ->
      @Corelib.Init.Logic.eq bool (holdfast_bits_ule b c) true ->
      @Corelib.Init.Logic.eq bool (holdfast_bits_ult a c) true :=
  match a as a0, b as b0, c as c0 return (@Corelib.Init.Logic.eq bool (holdfast_bits_ult a0 b0) true -> @Corelib.Init.Logic.eq bool (holdfast_bits_ule b0 c0) true -> @Corelib.Init.Logic.eq bool (holdfast_bits_ult a0 c0) true) with
  | holdfast_bnil, holdfast_bnil, _ => fun h1 _ => holdfast_false_true_elim _ h1
  | holdfast_bcons _ _, holdfast_bnil, _ => fun h1 _ => holdfast_false_true_elim _ h1
  | holdfast_bnil, holdfast_bcons _ _, holdfast_bnil => fun _ h2 => holdfast_false_true_elim _ h2
  | holdfast_bnil, holdfast_bcons _ _, holdfast_bcons _ _ => fun _ _ => @Corelib.Init.Logic.eq_refl bool true
  | holdfast_bcons _ _, holdfast_bcons _ _, holdfast_bnil => fun _ h2 => holdfast_false_true_elim _ h2
  | holdfast_bcons x xs, holdfast_bcons y ys, holdfast_bcons z zs =>
      match x as x0, y as y0, z as z0 return (@Corelib.Init.Logic.eq bool (if holdfast_eq_bool x0 y0 then holdfast_bits_ult xs ys else y0) true -> @Corelib.Init.Logic.eq bool (if holdfast_eq_bool y0 z0 then holdfast_bits_ule ys zs else z0) true -> @Corelib.Init.Logic.eq bool (if holdfast_eq_bool x0 z0 then holdfast_bits_ult xs zs else z0) true) with
      | true, true, true => fun h1 h2 => holdfast_bits_ult_ule_trans xs ys zs h1 h2
      | false, false, false => fun h1 h2 => holdfast_bits_ult_ule_trans xs ys zs h1 h2
      | false, false, true => fun _ _ => @Corelib.Init.Logic.eq_refl bool true
      | false, true, true => fun _ _ => @Corelib.Init.Logic.eq_refl bool true
      | true, false, false => fun h1 _ => holdfast_false_true_elim _ h1
      | true, false, true => fun h1 _ => holdfast_false_true_elim _ h1
      | false, true, false => fun _ h2 => holdfast_false_true_elim _ h2
      | true, true, false => fun _ h2 => holdfast_false_true_elim _ h2
      end
  end.

Fixpoint holdfast_bits_ule_of_ult_false (a b : holdfast_bits) {struct a}
    : @Corelib.Init.Logic.eq bool (holdfast_bits_ult b a) false ->
      @Corelib.Init.Logic.eq bool (holdfast_bits_ule a b) true :=
  match a as a0, b as b0 return (@Corelib.Init.Logic.eq bool (holdfast_bits_ult b0 a0) false -> @Corelib.Init.Logic.eq bool (holdfast_bits_ule a0 b0) true) with
  | holdfast_bnil, _ => fun _ => @Corelib.Init.Logic.eq_refl bool true
  | holdfast_bcons _ _, holdfast_bnil => fun h => holdfast_false_elim (@Corelib.Init.Logic.eq bool false true) h
  | holdfast_bcons x xs, holdfast_bcons y ys =>
      match x as x0, y as y0 return (@Corelib.Init.Logic.eq bool (if holdfast_eq_bool y0 x0 then holdfast_bits_ult ys xs else x0) false -> @Corelib.Init.Logic.eq bool (if holdfast_eq_bool x0 y0 then holdfast_bits_ule xs ys else y0) true) with
      | true, true => fun h => holdfast_bits_ule_of_ult_false xs ys h
      | false, false => fun h => holdfast_bits_ule_of_ult_false xs ys h
      | false, true => fun _ => @Corelib.Init.Logic.eq_refl bool true
      | true, false => fun h => holdfast_false_elim (@Corelib.Init.Logic.eq bool false true) h
      end
  end.

Definition holdfast_int_le_of_gt_false (tag : nat) (x y : holdfast_int tag)
    (h : @Corelib.Init.Logic.eq bool (holdfast_int_gt tag x y) false)
    : @Corelib.Init.Logic.eq bool (holdfast_int_le tag x y) true :=
  holdfast_bits_ule_of_ult_false (holdfast_int_key tag x) (holdfast_int_key tag y) h.

Definition holdfast_extent_end (base len : holdfast_int (4 : nat)) : holdfast_int (4 : nat) :=
  if holdfast_int_eq (4 : nat) base holdfast_usize_zero then len else holdfast_int_add (4 : nat) base len.

Lemma holdfast_usize_le_refl (x : holdfast_int (4 : nat)) : holdfast_int_le (4 : nat) x x = true.
Proof.
  destruct x as [w]. change (holdfast_bits_ule (holdfast_word_bits w) (holdfast_word_bits w) = true).
  generalize (holdfast_word_bits w); intro xs.
  induction xs as [|b xs IH]. reflexivity. destruct b; exact IH.
Qed.

Definition holdfast_in_extent (addr base len : holdfast_int (4 : nat)) : bool :=
  holdfast_and
    (holdfast_int_le (4 : nat) base addr)
    (holdfast_int_lt (4 : nat) addr (holdfast_extent_end base len)).

Inductive holdfast_ByteStore : Type@{holdfast_u0} :=
| holdfast_bs_empty : holdfast_ByteStore
| holdfast_bs_slice : holdfast_int (4 : nat) -> holdfast_int (4 : nat) -> holdfast_ByteStore -> holdfast_ByteStore
| holdfast_bs_fill : holdfast_int (4 : nat) -> holdfast_int (4 : nat) -> holdfast_int (0 : nat) -> holdfast_ByteStore -> holdfast_ByteStore
| holdfast_bs_write : holdfast_int (4 : nat) -> holdfast_int (0 : nat) -> holdfast_ByteStore -> holdfast_ByteStore
| holdfast_bs_copy : holdfast_int (4 : nat) -> holdfast_int (4 : nat) -> holdfast_int (4 : nat) -> holdfast_ByteStore -> holdfast_ByteStore -> holdfast_ByteStore.

Fixpoint holdfast_store_lookup (st : holdfast_ByteStore) (addr : holdfast_int (4 : nat)) {struct st} : holdfast_int (0 : nat) :=
  match st with
  | holdfast_bs_empty => holdfast_u8_zero
  | holdfast_bs_slice off _ parent_st =>
      holdfast_store_lookup parent_st (holdfast_int_add (4 : nat) off addr)
  | holdfast_bs_fill base len val rest =>
      if holdfast_in_extent addr base len then val else holdfast_store_lookup rest addr
  | holdfast_bs_write waddr val rest =>
      if holdfast_int_eq (4 : nat) addr waddr then val else holdfast_store_lookup rest addr
  | holdfast_bs_copy dbase sbase count src_st rest =>
      if holdfast_in_extent addr dbase count then
        holdfast_store_lookup src_st (holdfast_int_add (4 : nat) sbase (holdfast_int_sub (4 : nat) addr dbase))
      else
        holdfast_store_lookup rest addr
  end.

Fixpoint holdfast_store_slice_offset (st : holdfast_ByteStore) {struct st} : holdfast_int (4 : nat) :=
  match st with
  | holdfast_bs_empty => holdfast_usize_zero
  | holdfast_bs_slice off _ _ => off
  | holdfast_bs_fill _ _ _ rest => holdfast_store_slice_offset rest
  | holdfast_bs_write _ _ rest => holdfast_store_slice_offset rest
  | holdfast_bs_copy _ _ _ _ rest => holdfast_store_slice_offset rest
  end.

Fixpoint holdfast_bs_shift (off : holdfast_int (4 : nat)) (st : holdfast_ByteStore) {struct st} : holdfast_ByteStore :=
  match st with
  | holdfast_bs_empty => holdfast_bs_empty
  | holdfast_bs_slice _ _ parent_st => parent_st
  | holdfast_bs_fill foff len val rest =>
      holdfast_bs_fill (holdfast_int_add (4 : nat) off foff) len val (holdfast_bs_shift off rest)
  | holdfast_bs_write widx val rest =>
      holdfast_bs_write (holdfast_int_add (4 : nat) off widx) val (holdfast_bs_shift off rest)
  | holdfast_bs_copy doff soff count src_st rest =>
      holdfast_bs_copy (holdfast_int_add (4 : nat) off doff) soff count src_st (holdfast_bs_shift off rest)
  end.

Inductive holdfast_Span (A : Type@{holdfast_u0}) : Type@{holdfast_u0} :=
| holdfast_mk_span :
    holdfast_int (4 : nat) ->
    holdfast_int (4 : nat) ->
    bool ->
    bool ->
    bool ->
    holdfast_ByteStore ->
    holdfast_Span A.

Definition holdfast_Span_Base (A : Type@{holdfast_u0}) (s : holdfast_Span A) : holdfast_int (4 : nat) :=
  match s with
  | holdfast_mk_span _ base _ _ _ _ _ => base
  end.

Definition holdfast_Span_Length (A : Type@{holdfast_u0}) (s : holdfast_Span A) : holdfast_int (4 : nat) :=
  match s with
  | holdfast_mk_span _ _ len _ _ _ _ => len
  end.

Definition holdfast_Span_Tag (A : Type@{holdfast_u0}) (s : holdfast_Span A) : bool :=
  match s with
  | holdfast_mk_span _ _ _ tag _ _ _ => tag
  end.

Definition holdfast_Span_PermRead (A : Type@{holdfast_u0}) (s : holdfast_Span A) : bool :=
  match s with
  | holdfast_mk_span _ _ _ _ pr _ _ => pr
  end.

Definition holdfast_Span_PermWrite (A : Type@{holdfast_u0}) (s : holdfast_Span A) : bool :=
  match s with
  | holdfast_mk_span _ _ _ _ _ pw _ => pw
  end.

Definition holdfast_Span_Store (A : Type@{holdfast_u0}) (s : holdfast_Span A) : holdfast_ByteStore :=
  match s with
  | holdfast_mk_span _ _ _ _ _ _ st => st
  end.

Definition holdfast_Span_CanRead (A : Type@{holdfast_u0}) (s : holdfast_Span A) : bool :=
  holdfast_and (holdfast_Span_PermRead A s) (holdfast_Span_Tag A s).

Definition holdfast_Span_CanWrite (A : Type@{holdfast_u0}) (s : holdfast_Span A) : bool :=
  holdfast_and (holdfast_Span_PermWrite A s) (holdfast_Span_Tag A s).

Definition holdfast_Span_AllocZeroed (A : Type@{holdfast_u0}) (base cap : holdfast_int (4 : nat)) : holdfast_Span A :=
  holdfast_mk_span A base cap true true true holdfast_bs_empty.

Definition holdfast_Span_ReadOnly (A : Type@{holdfast_u0}) (s : holdfast_Span A) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_Span_Base A s)
    (holdfast_Span_Length A s)
    (holdfast_Span_Tag A s)
    (holdfast_Span_PermRead A s)
    false
    (holdfast_Span_Store A s).

Definition holdfast_Span_Invalidate (A : Type@{holdfast_u0}) (s : holdfast_Span A) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_Span_Base A s)
    (holdfast_Span_Length A s)
    false
    false
    false
    (holdfast_Span_Store A s).

Definition holdfast_extents_disjoint (a alen b blen : holdfast_int (4 : nat)) : bool :=
  if holdfast_int_eq 4 alen holdfast_usize_zero then true else
  if holdfast_int_eq 4 blen holdfast_usize_zero then true else
  if holdfast_int_le 4 a b then holdfast_int_le 4 alen (holdfast_int_sub 4 b a)
  else holdfast_int_le 4 blen (holdfast_int_sub 4 a b).

Definition holdfast_Span_Disjoint (A : Type@{holdfast_u0}) (a b : holdfast_Span A) : bool :=
  holdfast_extents_disjoint (holdfast_Span_Base A a) (holdfast_Span_Length A a)
    (holdfast_Span_Base A b) (holdfast_Span_Length A b).

Definition holdfast_Span_Read (A : Type@{holdfast_u0}) (s : holdfast_Span A) (idx : holdfast_int (4 : nat)) : holdfast_int (0 : nat) :=
  holdfast_store_lookup (holdfast_Span_Store A s) idx.

Definition holdfast_Span_Write (A : Type@{holdfast_u0}) (s : holdfast_Span A) (idx : holdfast_int (4 : nat)) (val : holdfast_int (0 : nat)) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_Span_Base A s)
    (holdfast_Span_Length A s)
    (holdfast_Span_Tag A s)
    (holdfast_Span_PermRead A s)
    (holdfast_Span_PermWrite A s)
    (holdfast_bs_write idx val (holdfast_Span_Store A s)).

Definition holdfast_Span_Fill (A : Type@{holdfast_u0}) (s : holdfast_Span A) (off count : holdfast_int (4 : nat)) (val : holdfast_int (0 : nat)) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_Span_Base A s)
    (holdfast_Span_Length A s)
    (holdfast_Span_Tag A s)
    (holdfast_Span_PermRead A s)
    (holdfast_Span_PermWrite A s)
    (holdfast_bs_fill off count val (holdfast_Span_Store A s)).

Definition holdfast_Span_Slice (A : Type@{holdfast_u0}) (s : holdfast_Span A) (off count : holdfast_int (4 : nat)) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_int_add (4 : nat) (holdfast_Span_Base A s) off)
    count
    (holdfast_Span_Tag A s)
    (holdfast_Span_PermRead A s)
    (holdfast_Span_PermWrite A s)
    (holdfast_bs_slice off count (holdfast_Span_Store A s)).

Definition holdfast_Span_CopyPrefix (A : Type@{holdfast_u0}) (dst src : holdfast_Span A) (count : holdfast_int (4 : nat)) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_Span_Base A dst)
    (holdfast_Span_Length A dst)
    (holdfast_Span_Tag A dst)
    (holdfast_Span_PermRead A dst)
    (holdfast_Span_PermWrite A dst)
    (holdfast_bs_copy holdfast_usize_zero holdfast_usize_zero count (holdfast_Span_Store A src) (holdfast_Span_Store A dst)).

Definition holdfast_Span_Restore (A : Type@{holdfast_u0}) (parent view : holdfast_Span A) : holdfast_Span A :=
  holdfast_mk_span A
    (holdfast_Span_Base A parent)
    (holdfast_Span_Length A parent)
    (holdfast_Span_Tag A parent)
    (holdfast_Span_PermRead A parent)
    (holdfast_Span_PermWrite A parent)
    (holdfast_bs_shift (holdfast_store_slice_offset (holdfast_Span_Store A view)) (holdfast_Span_Store A view)).

Definition holdfast_Span_Read_write_same (A : Type@{holdfast_u0}) (s : holdfast_Span A) (idx : holdfast_int (4 : nat)) (val : holdfast_int (0 : nat))
    : @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
        (holdfast_Span_Read A (holdfast_Span_Write A s idx val) idx)
        val :=
  @Corelib.Init.Logic.f_equal bool (holdfast_int (0 : nat))
    (fun b : bool => if b then val else holdfast_store_lookup (holdfast_Span_Store A s) idx)
    (holdfast_int_eq (4 : nat) idx idx)
    true
    (holdfast_int_eq_refl (4 : nat) idx).

Definition holdfast_Span_Read_write_other_ne (A : Type@{holdfast_u0}) (s : holdfast_Span A) (widx ridx : holdfast_int (4 : nat)) (val : holdfast_int (0 : nat))
    (hne : @Corelib.Init.Logic.eq bool (holdfast_int_ne (4 : nat) widx ridx) true)
    : @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
        (holdfast_Span_Read A (holdfast_Span_Write A s widx val) ridx)
        (holdfast_Span_Read A s ridx) :=
  @Corelib.Init.Logic.f_equal bool (holdfast_int (0 : nat))
    (fun b : bool => if b then val else holdfast_store_lookup (holdfast_Span_Store A s) ridx)
    (holdfast_int_eq (4 : nat) ridx widx)
    false
    (holdfast_int_eq_sym_false (4 : nat) widx ridx (holdfast_int_ne_false (4 : nat) widx ridx hne)).

Definition holdfast_int_lt_ge_false (P : Type@{holdfast_u0}) (a b c : holdfast_int (4 : nat))
    (hab : @Corelib.Init.Logic.eq bool (holdfast_int_lt (4 : nat) a b) true)
    (hcb : @Corelib.Init.Logic.eq bool (holdfast_int_ge (4 : nat) c b) true)
    (hca : @Corelib.Init.Logic.eq bool (holdfast_int_eq (4 : nat) c a) true) : P :=
  holdfast_bits_ult_ule_false P (holdfast_int_bits (4 : nat) a) (holdfast_int_bits (4 : nat) b) hab
    (match holdfast_int_eq_true (4 : nat) c a hca in (@Corelib.Init.Logic.eq _ _ a0)
       return (@Corelib.Init.Logic.eq bool (holdfast_int_ge (4 : nat) a0 b) true) with
     | @Corelib.Init.Logic.eq_refl _ _ => hcb
     end).

Definition holdfast_store_lookup_write_ge (widx hi idx : holdfast_int (4 : nat)) (val : holdfast_int (0 : nat)) (rest : holdfast_ByteStore)
    (hw : @Corelib.Init.Logic.eq bool (holdfast_int_lt (4 : nat) widx hi) true)
    (hge : @Corelib.Init.Logic.eq bool (holdfast_int_ge (4 : nat) idx hi) true)
    : @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
        (holdfast_store_lookup (holdfast_bs_write widx val rest) idx)
        (holdfast_store_lookup rest idx) :=
  match holdfast_int_eq (4 : nat) idx widx as b
    return (@Corelib.Init.Logic.eq bool (holdfast_int_eq (4 : nat) idx widx) b ->
            @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
              (if b then val else holdfast_store_lookup rest idx)
              (holdfast_store_lookup rest idx)) with
  | true => fun heq =>
      holdfast_int_lt_ge_false
        (@Corelib.Init.Logic.eq (holdfast_int (0 : nat)) val (holdfast_store_lookup rest idx))
        widx hi idx hw hge heq
  | false => fun _ => @Corelib.Init.Logic.eq_refl (holdfast_int (0 : nat)) (holdfast_store_lookup rest idx)
  end (@Corelib.Init.Logic.eq_refl bool (holdfast_int_eq (4 : nat) idx widx)).

Lemma holdfast_word_bits_length : forall n (w : holdfast_word n), holdfast_bits_len (holdfast_word_bits w) = n.
Proof. intros n w; induction w; simpl; congruence. Qed.

Definition holdfast_in_extent_ge_elim (P : Type@{holdfast_u0}) (base len hi idx : holdfast_int (4 : nat))
    (hbound : @Corelib.Init.Logic.eq bool (holdfast_int_le (4 : nat) (holdfast_extent_end base len) hi) true)
    (hge : @Corelib.Init.Logic.eq bool (holdfast_int_ge (4 : nat) idx hi) true)
    (hext : @Corelib.Init.Logic.eq bool (holdfast_in_extent idx base len) true) : P :=
  holdfast_bits_ult_ule_false P (holdfast_int_bits (4 : nat) idx) (holdfast_int_bits (4 : nat) hi)
    (holdfast_bits_ult_ule_trans
      (holdfast_int_bits (4 : nat) idx)
      (holdfast_int_bits (4 : nat) (holdfast_extent_end base len))
      (holdfast_int_bits (4 : nat) hi)
      (holdfast_and_right
        (holdfast_int_le (4 : nat) base idx)
        (holdfast_int_lt (4 : nat) idx (holdfast_extent_end base len))
        hext)
      hbound)
    hge.

Definition holdfast_store_lookup_fill_ge (base len hi idx : holdfast_int (4 : nat)) (val : holdfast_int (0 : nat)) (rest : holdfast_ByteStore)
    (hbound : @Corelib.Init.Logic.eq bool (holdfast_int_le (4 : nat) (holdfast_extent_end base len) hi) true)
    (hge : @Corelib.Init.Logic.eq bool (holdfast_int_ge (4 : nat) idx hi) true)
    : @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
        (holdfast_store_lookup (holdfast_bs_fill base len val rest) idx)
        (holdfast_store_lookup rest idx) :=
  match holdfast_in_extent idx base len as b
    return (@Corelib.Init.Logic.eq bool (holdfast_in_extent idx base len) b ->
            @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
              (if b then val else holdfast_store_lookup rest idx)
              (holdfast_store_lookup rest idx)) with
  | true => fun hext =>
      holdfast_in_extent_ge_elim
        (@Corelib.Init.Logic.eq (holdfast_int (0 : nat)) val (holdfast_store_lookup rest idx))
        base len hi idx hbound hge hext
  | false => fun _ => @Corelib.Init.Logic.eq_refl (holdfast_int (0 : nat)) (holdfast_store_lookup rest idx)
  end (@Corelib.Init.Logic.eq_refl bool (holdfast_in_extent idx base len)).

Definition holdfast_store_lookup_copy_ge (dbase sbase count hi idx : holdfast_int (4 : nat)) (src_st rest : holdfast_ByteStore)
    (hbound : @Corelib.Init.Logic.eq bool (holdfast_int_le (4 : nat) (holdfast_extent_end dbase count) hi) true)
    (hge : @Corelib.Init.Logic.eq bool (holdfast_int_ge (4 : nat) idx hi) true)
    : @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
        (holdfast_store_lookup (holdfast_bs_copy dbase sbase count src_st rest) idx)
        (holdfast_store_lookup rest idx) :=
  match holdfast_in_extent idx dbase count as b
    return (@Corelib.Init.Logic.eq bool (holdfast_in_extent idx dbase count) b ->
            @Corelib.Init.Logic.eq (holdfast_int (0 : nat))
              (if b then holdfast_store_lookup src_st (holdfast_int_add (4 : nat) sbase (holdfast_int_sub (4 : nat) idx dbase))
               else holdfast_store_lookup rest idx)
              (holdfast_store_lookup rest idx)) with
  | true => fun hext =>
      holdfast_in_extent_ge_elim
        (@Corelib.Init.Logic.eq (holdfast_int (0 : nat))
          (holdfast_store_lookup src_st (holdfast_int_add (4 : nat) sbase (holdfast_int_sub (4 : nat) idx dbase)))
          (holdfast_store_lookup rest idx))
        dbase count hi idx hbound hge hext
  | false => fun _ => @Corelib.Init.Logic.eq_refl (holdfast_int (0 : nat)) (holdfast_store_lookup rest idx)
  end (@Corelib.Init.Logic.eq_refl bool (holdfast_in_extent idx dbase count)).

Definition holdfast_Congr (A B : Type@{holdfast_u0}) (x y : A) (f : A -> B)
    (p : @Corelib.Init.Logic.eq A x y) : @Corelib.Init.Logic.eq B (f x) (f y) :=
  @Corelib.Init.Logic.f_equal A B f x y p.

Lemma holdfast_freeze_observe (A : Type@{holdfast_u0}) (initial frozen : A)
    (same : initial = frozen) (P : A -> Type@{holdfast_u0}) (observe : forall a, P a) :
    @eq_rect A initial P (observe initial) frozen same = observe frozen.
Proof. destruct same. reflexivity. Qed.

Fixpoint holdfast_Vec (A : Type@{holdfast_u0}) (n : nat) {struct n} : Type@{holdfast_u0} :=
  match n with
  | O => unit
  | S k => @prod A (holdfast_Vec A k)
  end.
Definition holdfast_VNil (A : Type@{holdfast_u0}) (_ : unit) : holdfast_Vec A O := tt.
Definition holdfast_VCons (A : Type@{holdfast_u0}) (n : nat) (x : A) (xs : holdfast_Vec A n)
    : holdfast_Vec A (S n) := @pair A (holdfast_Vec A n) x xs.

Inductive holdfast_Fin : nat -> Type@{holdfast_u0} :=
| holdfast_fzero : forall n : nat, holdfast_Fin (S n)
| holdfast_fsucc : forall n : nat, holdfast_Fin n -> holdfast_Fin (S n).
Definition holdfast_FZero (n : nat) (_ : unit) : holdfast_Fin (S n) := holdfast_fzero n.
Definition holdfast_FSucc (n : nat) (i : holdfast_Fin n) : holdfast_Fin (S n) := holdfast_fsucc n i.
Fixpoint holdfast_finite_offset (n i : nat) {struct n} : holdfast_Fin (S n) :=
  match n as k return holdfast_Fin (S k) with
  | O => holdfast_fzero O
  | S k => match i with
           | O => holdfast_fzero (S k)
           | S j => holdfast_fsucc (S k) (holdfast_finite_offset k j)
           end
  end.
Fixpoint holdfast_lookup (A : Type@{holdfast_u0}) (n : nat) (i : holdfast_Fin n) {struct i}
    : holdfast_Vec A n -> A :=
  match i in holdfast_Fin size return holdfast_Vec A size -> A with
  | holdfast_fzero k => fun v => @fst A (holdfast_Vec A k) v
  | holdfast_fsucc k j => fun v => holdfast_lookup A k j (@snd A (holdfast_Vec A k) v)
  end.
Definition holdfast_At (A : Type@{holdfast_u0}) (n : nat) (xs : holdfast_Vec A n) (i : holdfast_Fin n)
    : A := holdfast_lookup A n i xs.
Fixpoint holdfast_Vec_At_Nat (A : Type@{holdfast_u0}) (n : nat) (d : A) (idx : nat) {struct n}
    : holdfast_Vec A n -> A :=
  match n return holdfast_Vec A n -> A with
  | O => fun _ => d
  | S k => fun v =>
      match idx with
      | O => @fst A (holdfast_Vec A k) v
      | S j => holdfast_Vec_At_Nat A k d j (@snd A (holdfast_Vec A k) v)
      end
  end.
Fixpoint holdfast_Vec_Update (A : Type@{holdfast_u0}) (n : nat) (idx : nat) (val : A) {struct n}
    : holdfast_Vec A n -> holdfast_Vec A n :=
  match n return holdfast_Vec A n -> holdfast_Vec A n with
  | O => fun v => v
  | S k => fun v =>
      match idx with
      | O => @pair A (holdfast_Vec A k) val (@snd A (holdfast_Vec A k) v)
      | S j => @pair A (holdfast_Vec A k) (@fst A (holdfast_Vec A k) v) (holdfast_Vec_Update A k j val (@snd A (holdfast_Vec A k) v))
      end
  end.
Definition holdfast_ByteLength (n : nat) (_ : holdfast_Vec nat n) : nat := n.

Definition holdfast_nat_to_usize (n : nat) : holdfast_int (4 : nat) :=
  holdfast_mk_int (4 : nat) (holdfast_nat_to_bits 64 n).

Inductive holdfast_Seq (A : Type@{holdfast_u0}) : Type@{holdfast_u0} :=
| holdfast_Seq_Empty : holdfast_Seq A
| holdfast_Seq_Cons : A -> holdfast_Seq A -> holdfast_Seq A.

Definition holdfast_Seq_Singleton (A : Type@{holdfast_u0}) (x : A) : holdfast_Seq A :=
  holdfast_Seq_Cons A x (holdfast_Seq_Empty A).

Fixpoint holdfast_Seq_Count (A : Type@{holdfast_u0}) (s : holdfast_Seq A) {struct s} : nat :=
  match s with
  | holdfast_Seq_Empty _ => O
  | holdfast_Seq_Cons _ _ xs => S (holdfast_Seq_Count A xs)
  end.

Fixpoint holdfast_Seq_At (A : Type@{holdfast_u0}) (d : A) (s : holdfast_Seq A) (idx : nat) {struct s} : A :=
  match s with
  | holdfast_Seq_Empty _ => d
  | holdfast_Seq_Cons _ x xs =>
      match idx with
      | O => x
      | S k => holdfast_Seq_At A d xs k
      end
  end.

Fixpoint holdfast_Seq_Update (A : Type@{holdfast_u0}) (s : holdfast_Seq A) (idx : nat) (val : A) {struct s} : holdfast_Seq A :=
  match s with
  | holdfast_Seq_Empty _ => holdfast_Seq_Empty A
  | holdfast_Seq_Cons _ x xs =>
      match idx with
      | O => holdfast_Seq_Cons A val xs
      | S k => holdfast_Seq_Cons A x (holdfast_Seq_Update A xs k val)
      end
  end.

Fixpoint holdfast_Seq_Append (A : Type@{holdfast_u0}) (a b : holdfast_Seq A) {struct a} : holdfast_Seq A :=
  match a with
  | holdfast_Seq_Empty _ => b
  | holdfast_Seq_Cons _ x xs => holdfast_Seq_Cons A x (holdfast_Seq_Append A xs b)
  end.

Inductive holdfast_TextBuilder (capacity : nat) : Type@{holdfast_u0} :=
| holdfast_text_builder : bool -> holdfast_Seq nat -> holdfast_TextBuilder capacity.
Definition holdfast_EmptyBuilder (capacity : nat) (_ : unit) : holdfast_TextBuilder capacity :=
  holdfast_text_builder capacity true (holdfast_Seq_Empty nat).
Definition holdfast_FormatStep (capacity : nat) (builder : holdfast_TextBuilder capacity) (chunk : holdfast_Seq nat)
    : holdfast_TextBuilder capacity :=
  match builder with
  | holdfast_text_builder _ ok used =>
      if holdfast_and ok (Nat.leb (Nat.add (holdfast_Seq_Count nat used) (holdfast_Seq_Count nat chunk)) capacity)
      then holdfast_text_builder capacity true (holdfast_Seq_Append nat used chunk)
      else holdfast_text_builder capacity false used
  end.
Definition holdfast_Fits (capacity : nat) (builder : holdfast_TextBuilder capacity) : bool :=
  match builder with holdfast_text_builder _ ok _ => ok end.
Definition holdfast_WrittenBytes (capacity : nat) (builder : holdfast_TextBuilder capacity) : holdfast_Seq nat :=
  match builder with holdfast_text_builder _ _ used => used end.
Definition holdfast_Written (capacity : nat) (builder : holdfast_TextBuilder capacity) : nat :=
  holdfast_Seq_Count nat (holdfast_WrittenBytes capacity builder).

Fixpoint holdfast_utf8_check (s : holdfast_Seq nat) (remaining low high : nat) {struct s} : bool :=
  match s with
  | holdfast_Seq_Empty _ => Nat.eqb remaining 0
  | holdfast_Seq_Cons _ b tail =>
      match remaining with
      | S k => holdfast_and (holdfast_and (Nat.leb low b) (Nat.leb b high)) (holdfast_utf8_check tail k 128 191)
      | O => if Nat.ltb b 128 then holdfast_utf8_check tail 0 0 0 else
             if Nat.ltb b 194 then false else
             if Nat.ltb b 224 then holdfast_utf8_check tail 1 128 191 else
             if Nat.ltb b 240 then holdfast_utf8_check tail 2
                 (if Nat.eqb b 224 then 160 else 128) (if Nat.eqb b 237 then 159 else 191) else
             if Nat.leb b 244 then holdfast_utf8_check tail 3
                 (if Nat.eqb b 240 then 144 else 128) (if Nat.eqb b 244 then 143 else 191) else false
      end
  end.
Definition holdfast_ValidUtf8 (s : holdfast_Seq nat) := holdfast_utf8_check s 0 0 0.

Fixpoint holdfast_hex_digits (count : nat) (upper : bool) (bs : holdfast_bits) : holdfast_Seq nat :=
  match count with
  | O => holdfast_Seq_Empty nat
  | S k =>
      let step := fun (n : nat) (xs : holdfast_bits) => Nat.add (Nat.double n) (if holdfast_bits_head xs then 1 else 0) in
      let t1 := holdfast_bits_tail bs in let t2 := holdfast_bits_tail t1 in let t3 := holdfast_bits_tail t2 in
      let digit := step (step (step (step 0 bs) t1) t2) t3 in
      let code := if Nat.ltb digit 10 then Nat.add 48 digit else Nat.add (if upper then 55 else 87) digit in
      holdfast_Seq_Cons nat code (holdfast_hex_digits k upper (holdfast_bits_tail t3))
  end.
Definition holdfast_nat_hex_bytes (minimum : nat) (upper : bool) (value : nat) :=
  let n := holdfast_nat_hex_width minimum value in holdfast_hex_digits n upper (holdfast_nat_to_bits (Nat.mul 4 n) value).
Definition holdfast_int_hex_bytes (tag minimum : nat) (upper : bool) (value : holdfast_int tag) :=
  let n := holdfast_int_hex_width tag minimum value in
  holdfast_hex_digits n upper (holdfast_bits_resize (Nat.mul 4 n) false (holdfast_int_bits tag value)).

Fixpoint holdfast_Seq_Take (A : Type@{holdfast_u0}) (s : holdfast_Seq A) (n : nat) {struct n} : holdfast_Seq A :=
  match n with
  | O => holdfast_Seq_Empty A
  | S k =>
      match s with
      | holdfast_Seq_Empty _ => holdfast_Seq_Empty A
      | holdfast_Seq_Cons _ x xs => holdfast_Seq_Cons A x (holdfast_Seq_Take A xs k)
      end
  end.

Fixpoint holdfast_Seq_Skip (A : Type@{holdfast_u0}) (s : holdfast_Seq A) (n : nat) {struct n} : holdfast_Seq A :=
  match n with
  | O => s
  | S k =>
      match s with
      | holdfast_Seq_Empty _ => holdfast_Seq_Empty A
      | holdfast_Seq_Cons _ _ xs => holdfast_Seq_Skip A xs k
      end
  end.

Definition holdfast_Seq_Slice (A : Type@{holdfast_u0}) (s : holdfast_Seq A) (off cnt : nat) : holdfast_Seq A :=
  holdfast_Seq_Take A (holdfast_Seq_Skip A s off) cnt.

Fixpoint holdfast_Seq_All (A : Type@{holdfast_u0}) (s : holdfast_Seq A) (p : A -> bool) {struct s} : bool :=
  match s with
  | holdfast_Seq_Empty _ => true
  | holdfast_Seq_Cons _ x xs => holdfast_and (p x) (holdfast_Seq_All A xs p)
  end.

Fixpoint holdfast_Seq_Any (A : Type@{holdfast_u0}) (s : holdfast_Seq A) (p : A -> bool) {struct s} : bool :=
  match s with
  | holdfast_Seq_Empty _ => false
  | holdfast_Seq_Cons _ x xs => holdfast_or (p x) (holdfast_Seq_Any A xs p)
  end.

Fixpoint holdfast_Seq_Eq (A : Type@{holdfast_u0}) (eqA : A -> A -> bool) (a b : holdfast_Seq A) {struct a} : bool :=
  match a, b with
  | holdfast_Seq_Empty _, holdfast_Seq_Empty _ => true
  | holdfast_Seq_Cons _ x xs, holdfast_Seq_Cons _ y ys => holdfast_and (eqA x y) (holdfast_Seq_Eq A eqA xs ys)
  | _, _ => false
  end.

Fixpoint holdfast_Vec_Model (A : Type@{holdfast_u0}) (n : nat) {struct n} : holdfast_Vec A n -> holdfast_Seq A :=
  match n return holdfast_Vec A n -> holdfast_Seq A with
  | O => fun _ => holdfast_Seq_Empty A
  | S k => fun v => holdfast_Seq_Cons A (@fst A (holdfast_Vec A k) v) (holdfast_Vec_Model A k (@snd A (holdfast_Vec A k) v))
  end.

Fixpoint holdfast_Seq_Tabulate (A : Type@{holdfast_u0}) (n : nat) (f : nat -> A) : holdfast_Seq A :=
  match n with
  | O => holdfast_Seq_Empty A
  | S k => holdfast_Seq_Cons A (f O) (holdfast_Seq_Tabulate A k (fun i => f (S i)))
  end.

Lemma holdfast_Seq_Count_Tabulate : forall (A : Type@{holdfast_u0}) n (f : nat -> A),
  holdfast_Seq_Count A (holdfast_Seq_Tabulate A n f) = n.
Proof. intros A n; induction n; intros f; simpl; auto. Qed.

Lemma holdfast_Seq_At_Tabulate : forall (A : Type@{holdfast_u0}) n (f : nat -> A) (d : A) i,
  holdfast_Seq_At A d (holdfast_Seq_Tabulate A n f) i = if Nat.ltb i n then f i else d.
Proof.
  intros A n; induction n as [|n IH]; intros f d [|i]; simpl; try reflexivity.
  apply (IH (fun j => f (S j)) d i).
Qed.

Definition holdfast_Span_Model (A : Type@{holdfast_u0}) (s : holdfast_Span A) : holdfast_Seq (holdfast_int (0 : nat)) :=
  holdfast_Seq_Tabulate (holdfast_int 0) (holdfast_int_to_nat 4 (holdfast_Span_Length A s))
    (fun i => holdfast_Span_Read A s (holdfast_nat_to_usize i)).

Inductive holdfast_Slots (A : Type@{holdfast_u0}) : nat -> Type@{holdfast_u0} :=
| holdfast_Slots_Mk : forall cap : nat,
    holdfast_int (4 : nat) ->
    holdfast_int (4 : nat) ->
    bool ->
    bool ->
    bool ->
    holdfast_Seq A ->
    holdfast_Seq A ->
    holdfast_Slots A cap.

Definition holdfast_Slots_Capacity (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : holdfast_int 4 :=
  match s with
  | holdfast_Slots_Mk _ stored _ _ _ _ _ _ _ => holdfast_nat_to_usize stored
  end.

Lemma holdfast_Slots_Capacity_index : forall (A : Type@{holdfast_u0}) cap (s : holdfast_Slots A cap),
    holdfast_Slots_Capacity A cap s = holdfast_nat_to_usize cap.
Proof. intros A cap s; destruct s; reflexivity. Qed.

Definition holdfast_Slots_Base (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : holdfast_int (4 : nat) :=
  match s with
  | holdfast_Slots_Mk _ _ base _ _ _ _ _ _ => base
  end.

Definition holdfast_Slots_LiveCount (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : holdfast_int (4 : nat) :=
  match s with
  | holdfast_Slots_Mk _ _ _ live _ _ _ _ _ => live
  end.

Definition holdfast_Slots_Tag (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : bool :=
  match s with
  | holdfast_Slots_Mk _ _ _ _ tag _ _ _ _ => tag
  end.

Definition holdfast_Slots_PermRead (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : bool :=
  match s with
  | holdfast_Slots_Mk _ _ _ _ _ pr _ _ _ => pr
  end.

Definition holdfast_Slots_PermWrite (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : bool :=
  match s with
  | holdfast_Slots_Mk _ _ _ _ _ _ pw _ _ => pw
  end.

Definition holdfast_Slots_RepModel (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : holdfast_Seq A :=
  match s with
  | holdfast_Slots_Mk _ _ _ _ _ _ _ rep _ => rep
  end.

Definition holdfast_Slots_Model (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : holdfast_Seq A :=
  match s with
  | holdfast_Slots_Mk _ _ _ _ _ _ _ _ m => m
  end.

Definition holdfast_Slots_CanRead (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : bool :=
  holdfast_and (holdfast_Slots_Tag A cap s) (holdfast_Slots_PermRead A cap s).

Definition holdfast_Slots_CanWrite (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) : bool :=
  holdfast_and (holdfast_Slots_Tag A cap s) (holdfast_Slots_PermWrite A cap s).

Definition holdfast_Slots_AllocVacant (A : Type@{holdfast_u0}) (cap : nat) (base : holdfast_int (4 : nat)) : holdfast_Slots A cap :=
  holdfast_Slots_Mk A cap base (holdfast_nat_to_usize O) true true true (holdfast_Seq_Empty A) (holdfast_Seq_Empty A).

Definition holdfast_Slots_Write (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) (idx : holdfast_int (4 : nat)) (val : A)
    : holdfast_Slots A cap :=
  let i := holdfast_int_to_nat 4 idx in
  let live := holdfast_Slots_LiveCount A cap s in
  let model := holdfast_Slots_Model A cap s in
  let next := if holdfast_int_eq 4 idx live
              then holdfast_Seq_Append A model (holdfast_Seq_Singleton A val)
              else holdfast_Seq_Update A model i val in
  holdfast_Slots_Mk A cap (holdfast_Slots_Base A cap s)
    (if holdfast_int_eq 4 idx live then holdfast_nat_to_usize (S i) else live)
    (holdfast_Slots_Tag A cap s) (holdfast_Slots_PermRead A cap s) (holdfast_Slots_PermWrite A cap s)
    next next.

Definition holdfast_Slots_Read (A : Type@{holdfast_u0}) (cap : nat) (d : A) (s : holdfast_Slots A cap) (idx : holdfast_int (4 : nat)) : A :=
  holdfast_Seq_At A d (holdfast_Slots_Model A cap s) (holdfast_int_to_nat (4 : nat) idx).

Definition holdfast_Slots_LivePrefix (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) (cnt : holdfast_int (4 : nat)) : bool :=
  holdfast_and (holdfast_Slots_CanRead A cap s)
    (holdfast_and (Nat.leb (holdfast_int_to_nat 4 cnt) cap)
      (holdfast_and (holdfast_int_eq 4 (holdfast_Slots_LiveCount A cap s) cnt)
        (Nat.eqb (holdfast_Seq_Count A (holdfast_Slots_Model A cap s)) (holdfast_int_to_nat 4 cnt)))).

Definition holdfast_Slots_VacantRange (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) (start stop : holdfast_int (4 : nat)) : bool :=
  holdfast_and (holdfast_Slots_CanWrite A cap s)
    (holdfast_and (holdfast_int_le 4 (holdfast_Slots_LiveCount A cap s) start)
      (holdfast_and (holdfast_int_le 4 start stop) (Nat.leb (holdfast_int_to_nat 4 stop) cap))).

Definition holdfast_Slots_Disjoint (A : Type@{holdfast_u0}) (n m : nat) (a : holdfast_Slots A n) (b : holdfast_Slots A m) : bool :=
  let x := holdfast_int_to_nat 4 (holdfast_Slots_Base A n a) in
  let y := holdfast_int_to_nat 4 (holdfast_Slots_Base A m b) in
  holdfast_or (holdfast_or (Nat.eqb n O) (Nat.eqb m O))
    (holdfast_or (Nat.leb (Nat.add x n) y) (Nat.leb (Nat.add y m) x)).

Definition holdfast_Slots_RepEqual (A : Type@{holdfast_u0}) (n m : nat) (same : A -> A -> bool)
    (dst : holdfast_Slots A n) (src : holdfast_Slots A m) (cnt : holdfast_int 4) : bool :=
  let k := holdfast_int_to_nat 4 cnt in
  let rep := holdfast_Seq_Take A (holdfast_Slots_RepModel A n dst) k in
  let model := holdfast_Seq_Take A (holdfast_Slots_Model A m src) k in
  holdfast_and (Nat.eqb (holdfast_Seq_Count A rep) k) (holdfast_Seq_Eq A same rep model).

Definition holdfast_Slots_CopyRepresentation (A : Type@{holdfast_u0}) (n m : nat) (src : holdfast_Slots A n) (dst : holdfast_Slots A m) (cnt : holdfast_int (4 : nat))
    : holdfast_Slots A m :=
  holdfast_Slots_Mk A m
    (holdfast_Slots_Base A m dst)
    (holdfast_nat_to_usize O)
    (holdfast_Slots_Tag A m dst)
    (holdfast_Slots_PermRead A m dst)
    (holdfast_Slots_PermWrite A m dst)
    (holdfast_Seq_Take A (holdfast_Slots_Model A n src) (holdfast_int_to_nat 4 cnt))
    (holdfast_Seq_Empty A).

Definition holdfast_Slots_TransferSource (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) (_ : holdfast_int (4 : nat))
    : holdfast_Slots A cap :=
  holdfast_Slots_Mk A cap
    (holdfast_Slots_Base A cap s)
    (holdfast_nat_to_usize O)
    (holdfast_Slots_Tag A cap s)
    (holdfast_Slots_PermRead A cap s)
    (holdfast_Slots_PermWrite A cap s)
    (holdfast_Seq_Empty A)
    (holdfast_Seq_Empty A).

Definition holdfast_Slots_TransferDest (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) (cnt : holdfast_int (4 : nat))
    : holdfast_Slots A cap :=
  holdfast_Slots_Mk A cap
    (holdfast_Slots_Base A cap s)
    cnt
    (holdfast_Slots_Tag A cap s)
    (holdfast_Slots_PermRead A cap s)
    (holdfast_Slots_PermWrite A cap s)
    (holdfast_Slots_RepModel A cap s)
    (holdfast_Slots_RepModel A cap s).

Lemma holdfast_Seq_Count_take_exact : forall (A : Type@{holdfast_u0}) k (xs : holdfast_Seq A),
  Nat.eqb (holdfast_Seq_Count A xs) k = true ->
  Nat.eqb (holdfast_Seq_Count A (holdfast_Seq_Take A xs k)) k = true.
Proof.
  intros A k. induction k as [|k IH]; intros [|x xs] H; simpl in *;
    try reflexivity; try discriminate. exact (IH xs H).
Qed.

From Stdlib Require Import Arith.PeanoNat Lia.

Lemma holdfast_nat_leb_trans (a b c : nat) :
  Nat.leb a b = true -> Nat.leb b c = true -> Nat.leb a c = true.
Proof. rewrite !Nat.leb_le. apply Nat.le_trans. Qed.

Lemma holdfast_nat_leb_succ_self (a : nat) : Nat.leb a (S a) = true.
Proof. apply Nat.leb_le. apply Nat.le_succ_diag_r. Qed.

Lemma holdfast_nat_leb_of_ltb_false (a b : nat) :
  Nat.ltb a b = false -> Nat.leb b a = true.
Proof. rewrite Nat.ltb_ge, Nat.leb_le. exact (fun h => h). Qed.

Lemma holdfast_nat_ltb_of_leb_false (a b : nat) :
  Nat.leb a b = false -> Nat.ltb b a = true.
Proof. rewrite Nat.leb_gt, Nat.ltb_lt. exact (fun h => h). Qed.
Unset Lia Cache.

Lemma holdfast_bits_value_order : forall xs ys p q,
    holdfast_bits_len xs = holdfast_bits_len ys ->
    (or (Nat.lt p q) (and (p = q) (holdfast_bits_ule xs ys = true))) ->
    Nat.le (holdfast_bits_to_nat_acc xs p) (holdfast_bits_to_nat_acc ys q).
Proof.
  induction xs as [|x xs IH]; intros [|y ys] p q Hlen H; simpl in Hlen; try discriminate.
  - simpl. lia.
  - injection Hlen as Hlen. destruct x, y; cbn [holdfast_bits_to_nat_acc holdfast_bits_ule holdfast_eq_bool] in *;
      apply IH; try exact Hlen; intuition lia.
Qed.

Lemma holdfast_usize_zero_le : forall x, holdfast_int_le 4 holdfast_usize_zero x = true.
Proof.
  assert (H : forall n (w : holdfast_word n),
      holdfast_bits_ule (holdfast_word_bits (holdfast_bits_word n holdfast_bnil)) (holdfast_word_bits w) = true).
  { intros n w; induction w; simpl; [reflexivity | destruct b; simpl; auto]. }
  intros [w]. exact (H 64 w).
Qed.

Lemma holdfast_Slots_vacant_shrink : forall (A : Type@{holdfast_u0}) cap (s : holdfast_Slots A cap) small large,
  holdfast_Slots_VacantRange A cap s holdfast_usize_zero large = true ->
  holdfast_int_le 4 small large = true ->
  holdfast_Slots_VacantRange A cap s holdfast_usize_zero small = true.
Proof.
  intros A cap s small large Hvac Hle. unfold holdfast_Slots_VacantRange in *.
  destruct (holdfast_Slots_CanWrite A cap s), (holdfast_int_le 4 (holdfast_Slots_LiveCount A cap s) holdfast_usize_zero);
    cbn [holdfast_and] in *; try discriminate.
  rewrite holdfast_usize_zero_le in Hvac |- *. cbn [holdfast_and] in *.
  apply Nat.leb_le in Hvac. apply Nat.leb_le. eapply Nat.le_trans; [|exact Hvac].
  change (Nat.le (holdfast_bits_to_nat_acc (holdfast_int_bits 4 small) O) (holdfast_bits_to_nat_acc (holdfast_int_bits 4 large) O)).
  apply holdfast_bits_value_order.
  - destruct small as [ws], large as [wl]. transitivity 64; [apply holdfast_word_bits_length | symmetry; apply holdfast_word_bits_length].
  - right; split; [reflexivity | exact Hle].
Qed.

Lemma holdfast_Slots_vacant_after_copy : forall (A : Type@{holdfast_u0}) n m (src : holdfast_Slots A n)
    (dst : holdfast_Slots A m) k stop,
  holdfast_Slots_VacantRange A m dst holdfast_usize_zero stop = true ->
  holdfast_int_le 4 k stop = true ->
  holdfast_Slots_VacantRange A m
    (holdfast_Slots_TransferDest A m (holdfast_Slots_CopyRepresentation A n m src dst k) k) k stop = true.
Proof.
  intros A n m src dst k stop Hvac Hle. unfold holdfast_Slots_VacantRange in Hvac |- *.
  change (holdfast_and (holdfast_Slots_CanWrite A m dst) (holdfast_and (holdfast_int_le 4 k k)
    (holdfast_and (holdfast_int_le 4 k stop) (Nat.leb (holdfast_int_to_nat 4 stop) m))) = true).
  rewrite holdfast_usize_le_refl, Hle; cbn [holdfast_and].
  destruct (holdfast_Slots_CanWrite A m dst); cbn [holdfast_and] in *; try discriminate.
  exact (holdfast_and_right _ _ (holdfast_and_right _ _ Hvac)).
Qed.

Lemma holdfast_Slots_vacant_after_move : forall (A : Type@{holdfast_u0}) n (s : holdfast_Slots A n) k start stop,
  holdfast_Slots_VacantRange A n s start stop = true ->
  holdfast_Slots_VacantRange A n (holdfast_Slots_TransferSource A n s k) holdfast_usize_zero stop = true.
Proof.
  intros A n s k start stop Hvac. unfold holdfast_Slots_VacantRange in Hvac |- *.
  change (holdfast_and (holdfast_Slots_CanWrite A n s) (holdfast_and (holdfast_int_le 4 holdfast_usize_zero holdfast_usize_zero)
    (holdfast_and (holdfast_int_le 4 holdfast_usize_zero stop) (Nat.leb (holdfast_int_to_nat 4 stop) n))) = true).
  rewrite !holdfast_usize_zero_le; cbn [holdfast_and].
  destruct (holdfast_Slots_CanWrite A n s); cbn [holdfast_and] in *; try discriminate.
  exact (holdfast_and_right _ _ (holdfast_and_right _ _ Hvac)).
Qed.

Lemma holdfast_Seq_take_idempotent : forall (A : Type@{holdfast_u0}) n (xs : holdfast_Seq A),
  holdfast_Seq_Take A (holdfast_Seq_Take A xs n) n = holdfast_Seq_Take A xs n.
Proof.
  intros A n; induction n as [|n IH]; intros [|x xs]; simpl; try reflexivity.
  now rewrite IH.
Qed.

Lemma holdfast_Slots_live_after_copy : forall (A : Type@{holdfast_u0}) n m
    (src : holdfast_Slots A n) (dst : holdfast_Slots A m) k,
  holdfast_Slots_LivePrefix A n src k = true ->
  holdfast_Slots_VacantRange A m dst holdfast_usize_zero k = true ->
  holdfast_Slots_CanRead A m dst = true ->
  holdfast_Slots_LivePrefix A m
    (holdfast_Slots_TransferDest A m (holdfast_Slots_CopyRepresentation A n m src dst k) k) k = true.
Proof.
  intros A n m src dst k Hlive Hvac Hread.
  unfold holdfast_Slots_LivePrefix in Hlive |- *. unfold holdfast_Slots_VacantRange in Hvac.
  apply holdfast_and_intro; [exact Hread |].
  apply holdfast_and_intro; [exact (holdfast_and_right _ _ (holdfast_and_right _ _ (holdfast_and_right _ _ Hvac))) |].
  apply holdfast_and_intro; [exact (holdfast_int_eq_refl 4 k) |].
  apply holdfast_Seq_Count_take_exact. exact (holdfast_and_right _ _ (holdfast_and_right _ _ (holdfast_and_right _ _ Hlive))).
Qed.

Definition holdfast_Slots_TransferType (A : Type@{holdfast_u0}) (n m : nat) (src : holdfast_Slots A n) (dst : holdfast_Slots A m) (cnt : holdfast_int (4 : nat))
    : @prod (holdfast_Slots A n) (holdfast_Slots A m) :=
  @pair (holdfast_Slots A n) (holdfast_Slots A m)
    (holdfast_Slots_TransferSource A n src cnt)
    (holdfast_Slots_TransferDest A m dst cnt).

Definition holdfast_PrefixModel (A : Type@{holdfast_u0}) (cap : nat) (s : holdfast_Slots A cap) (cnt : holdfast_int (4 : nat)) : holdfast_Seq A :=
  holdfast_Seq_Take A (holdfast_Slots_Model A cap s) (holdfast_int_to_nat 4 cnt).

Fixpoint holdfast_NatFold (A : Type@{holdfast_u0}) (step : nat -> A -> A) (initial : A) (n : nat) {struct n} : A :=
  match n with
  | O => initial
  | S k => step k (holdfast_NatFold A step initial k)
  end.

Fixpoint holdfast_nat_add_assoc (a b c : nat) {struct a}
    : @Corelib.Init.Logic.eq nat
        (Corelib.Init.Nat.add (Corelib.Init.Nat.add a b) c)
        (Corelib.Init.Nat.add a (Corelib.Init.Nat.add b c)) :=
  match a as a0 return
    (@Corelib.Init.Logic.eq nat
      (Corelib.Init.Nat.add (Corelib.Init.Nat.add a0 b) c)
      (Corelib.Init.Nat.add a0 (Corelib.Init.Nat.add b c))) with
  | O => @Corelib.Init.Logic.eq_refl nat (Corelib.Init.Nat.add b c)
  | S a' =>
      @Corelib.Init.Logic.f_equal nat nat S
        (Corelib.Init.Nat.add (Corelib.Init.Nat.add a' b) c)
        (Corelib.Init.Nat.add a' (Corelib.Init.Nat.add b c))
        (holdfast_nat_add_assoc a' b c)
  end.

Fixpoint holdfast_gt_add_pos (x k : nat) {struct x}
    : @Corelib.Init.Logic.eq bool (holdfast_gt (Corelib.Init.Nat.add x (S k)) x) true :=
  match x as x0 return (@Corelib.Init.Logic.eq bool (holdfast_gt (Corelib.Init.Nat.add x0 (S k)) x0) true) with
  | O => @Corelib.Init.Logic.eq_refl bool true
  | S x' => holdfast_gt_add_pos x' k
  end.

Lemma holdfast_bits_rev_acc_rev : forall (a acc : holdfast_bits),
  holdfast_bits_rev_acc (holdfast_bits_rev_acc a acc) holdfast_bnil = holdfast_bits_rev_acc acc a.
Proof.
  induction a as [|x xs IH]; intros acc; simpl; [reflexivity | apply IH].
Qed.

Lemma holdfast_bits_rev_rev : forall (a : holdfast_bits), holdfast_bits_rev (holdfast_bits_rev a) = a.
Proof.
  intros a. unfold holdfast_bits_rev. apply holdfast_bits_rev_acc_rev.
Qed.

Lemma holdfast_bits_add_lsb_assoc_gen : forall (a b c : holdfast_bits) (c1 c2 d1 d2 : bool),
  Corelib.Init.Nat.eqb
    (Corelib.Init.Nat.add (if c1 then 1 else 0) (if c2 then 1 else 0))
    (Corelib.Init.Nat.add (if d1 then 1 else 0) (if d2 then 1 else 0)) = true ->
  holdfast_bits_add_lsb (holdfast_bits_add_lsb a b c1) c c2 = holdfast_bits_add_lsb a (holdfast_bits_add_lsb b c d1) d2.
Proof.
  induction a as [|x xs IH]; intros b c c1 c2 d1 d2 Hc;
  destruct b as [|y ys], c as [|z zs]; simpl; try reflexivity.
  destruct x, y, z, c1, c2, d1, d2; simpl in Hc; try discriminate Hc;
  simpl; f_equal; eapply IH; reflexivity.
Qed.

Lemma holdfast_int_width : forall tag (x : holdfast_int tag), holdfast_bits_len (holdfast_int_bits tag x) = holdfast_tag_bits tag.
Proof. intros tag [w]; apply holdfast_word_bits_length. Qed.

Lemma holdfast_bits_roundtrip : forall bs, holdfast_word_bits (holdfast_bits_word (holdfast_bits_len bs) bs) = bs.
Proof. induction bs; simpl; congruence. Qed.

Lemma holdfast_bits_rev_acc_length : forall a acc,
  holdfast_bits_len (holdfast_bits_rev_acc a acc) = Corelib.Init.Nat.add (holdfast_bits_len a) (holdfast_bits_len acc).
Proof.
  induction a as [|x xs IH]; intro acc; simpl; [reflexivity | rewrite IH; simpl].
  generalize (holdfast_bits_len xs) (holdfast_bits_len acc). intros n m; induction n; simpl; congruence.
Qed.

Lemma holdfast_bits_rev_length : forall a, holdfast_bits_len (holdfast_bits_rev a) = holdfast_bits_len a.
Proof.
  intro a; unfold holdfast_bits_rev; rewrite holdfast_bits_rev_acc_length; simpl.
  generalize (holdfast_bits_len a); intro n; induction n; simpl; congruence.
Qed.

Lemma holdfast_bits_add_lsb_length : forall a b c, holdfast_bits_len a = holdfast_bits_len b ->
  holdfast_bits_len (holdfast_bits_add_lsb a b c) = holdfast_bits_len a.
Proof.
  induction a as [|x xs IH]; intros [|y ys] c H; simpl in *; try discriminate; try reflexivity.
  f_equal; apply IH; now injection H.
Qed.

Lemma holdfast_bits_word_exact : forall n bs, holdfast_bits_len bs = n ->
  holdfast_word_bits (holdfast_bits_word n bs) = bs.
Proof. intros n bs H; subst n; apply holdfast_bits_roundtrip. Qed.

Lemma holdfast_bits_zero_right : forall a b, holdfast_bits_zero b = true ->
  holdfast_bits_len a = holdfast_bits_len b -> holdfast_bits_add_lsb a b false = a.
Proof.
  induction a as [|x a IH]; intros [|y b] Hz H; try discriminate; try reflexivity.
  injection H as H. destruct y; [discriminate |]. destruct x;
    cbn [holdfast_bits_add_lsb holdfast_xorb holdfast_or holdfast_and holdfast_not]; f_equal; now apply IH.
Qed.
Lemma holdfast_int_add_bits : forall tag a b, holdfast_int_bits tag (holdfast_int_add tag a b) =
  holdfast_bits_add (holdfast_int_bits tag a) (holdfast_int_bits tag b).
Proof.
  intros tag a b. unfold holdfast_int_add.
  destruct (holdfast_bits_zero (holdfast_bits_rev (holdfast_int_bits tag b))) eqn:Hz.
  - unfold holdfast_bits_add. rewrite holdfast_bits_zero_right by
      (assumption || now rewrite !holdfast_bits_rev_length, !holdfast_int_width).
    symmetry. apply holdfast_bits_rev_rev.
  - apply holdfast_bits_word_exact. unfold holdfast_bits_add.
    rewrite holdfast_bits_rev_length, holdfast_bits_add_lsb_length;
      rewrite !holdfast_bits_rev_length, !holdfast_int_width; reflexivity.
Qed.

Lemma holdfast_bits_sub_lsb_length : forall a b borrow, holdfast_bits_len a = holdfast_bits_len b ->
  holdfast_bits_len (holdfast_bits_sub_lsb a b borrow) = holdfast_bits_len a.
Proof.
  induction a as [|x a IH]; intros [|y b] c H; cbn in *; try discriminate; try reflexivity.
  f_equal. apply IH. now injection H.
Qed.
Lemma holdfast_int_sub_bits : forall tag a b, holdfast_int_bits tag (holdfast_int_sub tag a b) =
  holdfast_bits_sub (holdfast_int_bits tag a) (holdfast_int_bits tag b).
Proof.
  intros tag [a] [b]. change (holdfast_word_bits (holdfast_bits_word (holdfast_tag_bits tag)
    (holdfast_bits_sub (holdfast_word_bits a) (holdfast_word_bits b))) = holdfast_bits_sub (holdfast_word_bits a) (holdfast_word_bits b)).
  apply holdfast_bits_word_exact. unfold holdfast_bits_sub.
  rewrite holdfast_bits_rev_length, holdfast_bits_sub_lsb_length;
    rewrite !holdfast_bits_rev_length, !holdfast_word_bits_length; reflexivity.
Qed.
Lemma holdfast_int_bits_inj : forall tag a b, holdfast_int_bits tag a = holdfast_int_bits tag b -> a = b.
Proof.
  intros tag [a] [b] H. change (holdfast_word_bits a = holdfast_word_bits b) in H.
  apply (f_equal (holdfast_bits_word (holdfast_tag_bits tag))) in H.
  rewrite !holdfast_word_roundtrip in H. now subst.
Qed.
Lemma holdfast_bits_sub_add_lsb : forall a b c, holdfast_bits_len a = holdfast_bits_len b ->
  holdfast_bits_add_lsb b (holdfast_bits_sub_lsb a b c) c = a.
Proof.
  induction a as [|x a IH]; intros [|y b] c H; try discriminate; try reflexivity.
  injection H as H. destruct x, y, c; cbn [holdfast_bits_sub_lsb holdfast_bits_add_lsb
    holdfast_xorb holdfast_or holdfast_and holdfast_not]; f_equal; now apply IH.
Qed.
Lemma holdfast_int_sub_add : forall tag a b, holdfast_int_add tag b (holdfast_int_sub tag a b) = a.
Proof.
  intros tag a b. apply holdfast_int_bits_inj. rewrite holdfast_int_add_bits, holdfast_int_sub_bits.
  unfold holdfast_bits_add, holdfast_bits_sub. rewrite holdfast_bits_rev_rev, holdfast_bits_sub_add_lsb.
  - apply holdfast_bits_rev_rev.
  - now rewrite !holdfast_bits_rev_length, !holdfast_int_width.
Qed.
Lemma holdfast_bits_zero_left : forall a b, holdfast_bits_zero a = true ->
  holdfast_bits_len a = holdfast_bits_len b -> holdfast_bits_add_lsb a b false = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Hz H; try discriminate; try reflexivity.
  injection H as H. destruct x; [discriminate |]. destruct y;
    cbn [holdfast_bits_add_lsb holdfast_xorb holdfast_or holdfast_and holdfast_not]; f_equal; now apply IH.
Qed.
Lemma holdfast_int_usize_zero_left : forall x, holdfast_int_add 4 holdfast_usize_zero x = x.
Proof.
  intro x. apply holdfast_int_bits_inj. rewrite holdfast_int_add_bits. unfold holdfast_bits_add.
  rewrite holdfast_bits_zero_left. apply holdfast_bits_rev_rev. reflexivity.
  now rewrite !holdfast_bits_rev_length, !holdfast_int_width.
Qed.
Lemma holdfast_store_read_aligned_copy : forall base count idx parent rest,
  holdfast_int_ge 4 idx base = true -> holdfast_int_lt 4 idx (holdfast_extent_end base count) = true ->
  holdfast_store_lookup (holdfast_bs_copy base holdfast_usize_zero count (holdfast_bs_slice base count parent) rest) idx =
  holdfast_store_lookup parent idx.
Proof.
  intros base count idx parent rest Hlo Hhi. change (holdfast_int_le 4 base idx = true) in Hlo.
  cbn [holdfast_store_lookup]. unfold holdfast_in_extent. rewrite Hlo, Hhi.
  cbn [holdfast_and]. now rewrite holdfast_int_usize_zero_left, holdfast_int_sub_add.
Qed.
Lemma holdfast_store_fill_byte : forall base count idx val rest,
  holdfast_int_le 4 base idx = true -> holdfast_int_lt 4 idx (holdfast_extent_end base count) = true ->
  holdfast_store_lookup (holdfast_bs_fill base count val rest) idx = val.
Proof.
  intros base count idx val rest Hlo Hhi; cbn [holdfast_store_lookup]; unfold holdfast_in_extent.
  now rewrite Hlo, Hhi.
Qed.

From Stdlib Require Import ZArith.BinInt.

Module HoldFastUnsigned.
Local Open Scope Z_scope.
Definition digit (b : bool) : Z := if b then 1 else 0.
Fixpoint big (xs : holdfast_bits) (prefix : Z) : Z :=
  match xs with
  | holdfast_bnil => prefix
  | holdfast_bcons x rest => big rest (2 * prefix + digit x)
  end.
Fixpoint little (xs : holdfast_bits) : Z :=
  match xs with
  | holdfast_bnil => 0
  | holdfast_bcons x rest => digit x + 2 * little rest
  end.

Lemma unsigned_order : forall a b, holdfast_bits_len a = holdfast_bits_len b ->
  forall p q, big a p <= big b q <-> p < q \\/ (p = q /\\ holdfast_bits_ule a b = true).
Proof.
  induction a as [|x a IH]; intros [|y b] H p q; try discriminate.
  - cbn. lia.
  - injection H as H. cbn [big]. rewrite (IH b H).
    destruct x, y; cbn [digit holdfast_bits_ule holdfast_eq_bool holdfast_not]; intuition (try congruence; lia).
Qed.

Lemma rev_value : forall xs acc, little (holdfast_bits_rev_acc xs acc) = big xs (little acc).
Proof.
  induction xs as [|x xs IH]; intro acc; [reflexivity |].
  cbn [holdfast_bits_rev_acc big]. rewrite IH. cbn [little]. f_equal. lia.
Qed.

Lemma value_nonnegative : forall xs p, 0 <= p -> 0 <= big xs p.
Proof.
  induction xs as [|x xs IH]; intros p H; cbn [big]; [assumption |].
  apply IH. destruct x; cbn [digit]; lia.
Qed.

Lemma little_sum_bound : forall a b c, holdfast_bits_len a = holdfast_bits_len b ->
  little (holdfast_bits_add_lsb a b c) <= little a + little b + digit c.
Proof.
  induction a as [|x a IH]; intros [|y b] c H; try discriminate.
  - destruct c; reflexivity || (cbn [little holdfast_bits_add_lsb digit]; lia).
  - injection H as H. cbn [holdfast_bits_add_lsb little].
    pose proof (IH b (holdfast_or (holdfast_and x y) (holdfast_and (holdfast_xorb x y) c)) H) as K.
    destruct x, y, c; cbn [holdfast_xorb holdfast_or holdfast_and holdfast_not digit] in *; lia.
Qed.

Definition value (x : holdfast_int 4) : Z := big (holdfast_int_bits 4 x) 0.
Lemma order : forall a b, holdfast_int_le 4 a b = true <-> value a <= value b.
Proof.
  intros a b. unfold value.
  change (holdfast_bits_ule (holdfast_int_bits 4 a) (holdfast_int_bits 4 b) = true <->
    big (holdfast_int_bits 4 a) 0 <= big (holdfast_int_bits 4 b) 0).
  rewrite unsigned_order by now rewrite !holdfast_int_width.
  intuition lia.
Qed.
Lemma sum_bound : forall a b, value (holdfast_int_add 4 a b) <= value a + value b.
Proof.
  intros a b. unfold value. rewrite holdfast_int_add_bits. unfold holdfast_bits_add.
  change 0 with (little holdfast_bnil). rewrite <- !rev_value.
  unfold holdfast_bits_rev. rewrite holdfast_bits_rev_acc_rev. cbn [holdfast_bits_rev_acc].
  pose proof (little_sum_bound (holdfast_bits_rev (holdfast_int_bits 4 a))
    (holdfast_bits_rev (holdfast_int_bits 4 b)) false) as H.
  assert (Hlen : holdfast_bits_len (holdfast_bits_rev (holdfast_int_bits 4 a)) =
    holdfast_bits_len (holdfast_bits_rev (holdfast_int_bits 4 b))) by now rewrite !holdfast_bits_rev_length, !holdfast_int_width.
  specialize (H Hlen). cbn [digit] in H. unfold holdfast_bits_rev in *; lia.
Qed.
End HoldFastUnsigned.

Lemma holdfast_extent_bound : forall base count limit hi,
  holdfast_int_le 4 count limit = true ->
  Z.leb (Z.add (HoldFastUnsigned.value base) (HoldFastUnsigned.value limit)) (HoldFastUnsigned.value hi) = true ->
  holdfast_int_le 4 (holdfast_extent_end base count) hi = true.
Proof.
  intros base count limit hi Hcount Hmax.
  apply HoldFastUnsigned.order in Hcount. apply Z.leb_le in Hmax. apply HoldFastUnsigned.order.
  unfold holdfast_extent_end. destruct (holdfast_int_eq 4 base holdfast_usize_zero).
  - pose proof (HoldFastUnsigned.value_nonnegative (holdfast_int_bits 4 base) 0%Z ltac:(lia)).
    unfold HoldFastUnsigned.value in *; lia.
  - pose proof (HoldFastUnsigned.sum_bound base count); lia.
Qed.

Definition holdfast_int_agrees (tag : nat) (checked : holdfast_Result (holdfast_int tag) holdfast_ArithmeticError)
    (ordinary : holdfast_int tag) : bool :=
  match checked with inl _ => false | inr word => holdfast_int_eq tag word ordinary end.

Lemma holdfast_int_agrees_sound : forall tag checked ordinary,
  holdfast_int_agrees tag checked ordinary = true ->
  checked = holdfast_Result_Ok (holdfast_int tag) holdfast_ArithmeticError ordinary.
Proof.
  intros tag [e|x] ordinary H; [discriminate |].
  cbn [holdfast_int_agrees] in H. apply holdfast_int_eq_true in H. now subst.
Qed.

Definition holdfast_checked_wrap_shl tag (x : holdfast_int tag) (count : holdfast_int 4) :=
  match holdfast_shift_amount tag count with
  | None => holdfast_int_err tag (holdfast_ArithmeticError_InvalidShift tt)
  | Some _ => holdfast_Result_Ok (holdfast_int tag) holdfast_ArithmeticError (holdfast_int_wrap_shl tag x count)
  end.

Fixpoint holdfast_bits_every (shape : holdfast_bits) (test : holdfast_bits -> bool) : bool :=
  match shape with
  | holdfast_bnil => test holdfast_bnil
  | holdfast_bcons _ rest => holdfast_and
       (holdfast_bits_every rest (fun xs => test (holdfast_bcons false xs)))
       (holdfast_bits_every rest (fun xs => test (holdfast_bcons true xs)))
  end.
Lemma holdfast_bits_every_sound : forall shape bs test,
  holdfast_bits_len bs = holdfast_bits_len shape -> holdfast_bits_every shape test = true -> test bs = true.
Proof.
  induction shape as [|a tail IH]; intros [|b bs] test Hlen H; simpl in *; try discriminate.
  - exact H.
  - injection Hlen as Hlen. destruct b.
    + apply (IH bs (fun xs => test (holdfast_bcons true xs)) Hlen); exact (holdfast_and_right _ _ H).
    + apply (IH bs (fun xs => test (holdfast_bcons false xs)) Hlen); exact (holdfast_and_left _ _ H).
Qed.

Lemma holdfast_every_word_sound : forall tag (test : holdfast_int tag -> bool),
  holdfast_bits_every (holdfast_int_bits tag (holdfast_mk_int tag holdfast_bnil))
    (fun bits => test (holdfast_mk_int tag bits)) = true ->
  forall x, test x = true.
Proof.
  intros tag test H [w].
  pose proof (holdfast_bits_every_sound (holdfast_int_bits tag (holdfast_mk_int tag holdfast_bnil))
    (holdfast_word_bits w) (fun bits => test (holdfast_mk_int tag bits))) as specialize_word.
  assert (Hlen : holdfast_bits_len (holdfast_word_bits w) =
    holdfast_bits_len (holdfast_int_bits tag (holdfast_mk_int tag holdfast_bnil)))
    by now rewrite holdfast_word_bits_length, holdfast_int_width.
  specialize (specialize_word Hlen H). unfold holdfast_mk_int in specialize_word.
  now rewrite holdfast_word_roundtrip in specialize_word.
Qed.

Lemma holdfast_int_add_assoc : forall (tag : nat) (a b c : holdfast_int tag),
  holdfast_int_add tag (holdfast_int_add tag a b) c = holdfast_int_add tag a (holdfast_int_add tag b c).
Proof.
  intros tag a b c. apply holdfast_int_bits_inj. rewrite !holdfast_int_add_bits.
  unfold holdfast_bits_add. rewrite !holdfast_bits_rev_rev. f_equal.
  eapply holdfast_bits_add_lsb_assoc_gen. reflexivity.
Qed.
"""

_WORD_REPLAY_PRELUDE = r"""
Module HoldFastWordReplay.
Import HoldFastUnsigned.
Local Open Scope Z_scope.

Definition unsigned tag (x : holdfast_int tag) := big (holdfast_int_bits tag x) 0.
Fixpoint capacity (n : nat) : Z :=
  match n with O => 1 | S k => 2 * capacity k end.

Lemma little_range : forall a, 0 <= little a < capacity (holdfast_bits_len a).
Proof.
  induction a as [|x a IH]; [cbn; lia |].
  destruct x; cbn [little digit holdfast_bits_len capacity]; lia.
Qed.
Lemma range : forall tag x, 0 <= unsigned tag x < capacity (holdfast_tag_bits tag).
Proof.
  intros tag x. pose proof (little_range (holdfast_bits_rev (holdfast_int_bits tag x))) as H.
  rewrite holdfast_bits_rev_length, holdfast_int_width in H. unfold holdfast_bits_rev in H.
  rewrite rev_value in H. exact H.
Qed.
Lemma ult_complement : forall a b, holdfast_bits_ult a b = negb (holdfast_bits_ule b a).
Proof.
  induction a as [|x a IH]; intros [|y b]; try reflexivity.
  destruct x, y; cbn [holdfast_bits_ult holdfast_bits_ule holdfast_eq_bool holdfast_not]; auto.
Qed.
Lemma bits_le : forall a b, holdfast_bits_len a = holdfast_bits_len b ->
  (holdfast_bits_ule a b = true <-> big a 0 <= big b 0).
Proof. intros a b H. rewrite unsigned_order by assumption. intuition lia. Qed.
Lemma bits_lt : forall a b, holdfast_bits_len a = holdfast_bits_len b ->
  (holdfast_bits_ult a b = true <-> big a 0 < big b 0).
Proof.
  intros a b H. rewrite ult_complement. pose proof (bits_le b a (eq_sym H)).
  destruct (holdfast_bits_ule b a); cbn; intuition (try discriminate; lia).
Qed.
Lemma le : forall tag a b, holdfast_tag_signed tag = false ->
  (holdfast_int_le tag a b = true <-> unsigned tag a <= unsigned tag b).
Proof.
  intros tag a b H. unfold holdfast_int_le, holdfast_int_key, unsigned. rewrite H.
  apply bits_le. now rewrite !holdfast_int_width.
Qed.
Lemma lt : forall tag a b, holdfast_tag_signed tag = false ->
  (holdfast_int_lt tag a b = true <-> unsigned tag a < unsigned tag b).
Proof.
  intros tag a b H. unfold holdfast_int_lt, holdfast_int_key, unsigned. rewrite H.
  apply bits_lt. now rewrite !holdfast_int_width.
Qed.

Lemma little_sum : forall a b c, holdfast_bits_len a = holdfast_bits_len b ->
  little a + little b + digit c < capacity (holdfast_bits_len a) ->
  little (holdfast_bits_add_lsb a b c) = little a + little b + digit c.
Proof.
  induction a as [|x a IH]; intros [|y b] c L H; try discriminate.
  - destruct c; cbn in *; lia.
  - injection L as L. cbn [holdfast_bits_add_lsb little holdfast_bits_len capacity] in *.
    destruct x, y, c; cbn [holdfast_xorb holdfast_or holdfast_and holdfast_not digit] in *;
      rewrite IH by (exact L || (cbn [digit]; lia)); cbn [digit]; lia.
Qed.
Lemma sum : forall tag a b,
  unsigned tag a + unsigned tag b < capacity (holdfast_tag_bits tag) ->
  unsigned tag (holdfast_int_add tag a b) = unsigned tag a + unsigned tag b.
Proof.
  intros tag a b H. unfold unsigned in *. rewrite holdfast_int_add_bits. unfold holdfast_bits_add.
  change 0 with (little holdfast_bnil). rewrite <- !rev_value. unfold holdfast_bits_rev.
  rewrite holdfast_bits_rev_acc_rev. cbn [holdfast_bits_rev_acc]. rewrite little_sum.
  - cbn [digit]. lia.
  - change (holdfast_bits_len (holdfast_bits_rev (holdfast_int_bits tag a)) = holdfast_bits_len (holdfast_bits_rev (holdfast_int_bits tag b))). now rewrite !holdfast_bits_rev_length, !holdfast_int_width.
  - rewrite !rev_value, holdfast_bits_rev_acc_length, holdfast_int_width, Nat.add_0_r.
    cbn [little digit]. lia.
Qed.
Lemma add_ok : forall tag a b, holdfast_tag_signed tag = false ->
  unsigned tag a + unsigned tag b < capacity (holdfast_tag_bits tag) ->
  holdfast_int_chk_add tag a b = holdfast_Result_Ok _ _ (holdfast_int_add tag a b).
Proof.
  intros tag a b S H. pose proof (sum tag a b H) as E.
  unfold holdfast_int_chk_add, holdfast_bits_add_overflows. rewrite S, <- holdfast_int_add_bits.
  destruct (holdfast_bits_ult _ _) eqn:K.
  - apply bits_lt in K; [|now rewrite !holdfast_int_width].
    pose proof (range tag b). unfold unsigned in *. lia.
  - unfold holdfast_int_ok. destruct (holdfast_int_add tag a b) as [w]. cbn [holdfast_int_bits].
    unfold holdfast_mk_int. now rewrite holdfast_word_roundtrip.
Qed.
Lemma sub_ok : forall tag a b, holdfast_tag_signed tag = false -> unsigned tag b <= unsigned tag a ->
  holdfast_int_chk_sub tag a b = holdfast_Result_Ok _ _ (holdfast_int_sub tag a b).
Proof.
  intros tag a b S H. unfold holdfast_int_chk_sub, holdfast_bits_sub_overflows. rewrite S.
  destruct (holdfast_bits_ult _ _) eqn:K; [|reflexivity].
  apply bits_lt in K; [|now rewrite !holdfast_int_width]. unfold unsigned in H. lia.
Qed.

Definition half tag := capacity (Nat.pred (holdfast_tag_bits tag)).
Definition signed tag x := big (holdfast_int_key tag x) 0 - half tag.

Lemma key_length : forall tag x, holdfast_bits_len (holdfast_int_key tag x) = holdfast_tag_bits tag.
Proof.
  intros tag x. pose proof (holdfast_int_width tag x) as L.
  unfold holdfast_int_key. destruct (holdfast_tag_signed tag); [destruct (holdfast_int_bits tag x) |]; exact L.
Qed.
Lemma signed_le : forall tag a b,
  holdfast_int_le tag a b = true <-> signed tag a <= signed tag b.
Proof. intros. unfold holdfast_int_le, signed. rewrite bits_le by now rewrite !key_length. lia. Qed.
Lemma signed_lt : forall tag a b,
  holdfast_int_lt tag a b = true <-> signed tag a < signed tag b.
Proof. intros. unfold holdfast_int_lt, signed. rewrite bits_lt by now rewrite !key_length. lia. Qed.

Lemma big_prefix : forall xs p, big xs p = big xs 0 + capacity (holdfast_bits_len xs) * p.
Proof.
  induction xs as [|x xs IH]; intro p; cbn [big capacity holdfast_bits_len]; [lia |].
  rewrite (IH (2 * p + digit x)), (IH (2 * 0 + digit x)). nia.
Qed.
Lemma big_range : forall xs, 0 <= big xs 0 < capacity (holdfast_bits_len xs).
Proof.
  intro xs. pose proof (little_range (holdfast_bits_rev xs)) as R.
  rewrite holdfast_bits_rev_length in R. unfold holdfast_bits_rev in R. now rewrite rev_value in R.
Qed.
Lemma signed_parts : forall tag x, holdfast_tag_signed tag = true ->
  - half tag <= signed tag x < half tag /\
  (if holdfast_bits_head (holdfast_int_bits tag x)
   then unsigned tag x = signed tag x + 2 * half tag /\ signed tag x < 0
   else unsigned tag x = signed tag x /\ 0 <= signed tag x).
Proof.
  intros tag x S. pose proof (holdfast_int_width tag x) as W.
  unfold signed, unsigned, half, holdfast_int_key. rewrite S, <- W.
  destruct (holdfast_int_bits tag x) as [|b xs].
  - destruct tag as [|[|[|[|[|[|[|[|tag]]]]]]]]; discriminate W.
  - pose proof (big_range xs) as R. destruct b;
      cbn [holdfast_bits_head holdfast_not big digit holdfast_bits_len Nat.pred];
      rewrite !Z.mul_0_r, !Z.add_0_l; rewrite (big_prefix xs 1); lia.
Qed.
Lemma full_capacity : forall tag, capacity (holdfast_tag_bits tag) = 2 * half tag.
Proof. intro tag. unfold half. destruct tag as [|[|[|[|[|[|[|[|tag]]]]]]]]; reflexivity. Qed.

Lemma little_sum_cases : forall a b c, holdfast_bits_len a = holdfast_bits_len b ->
  let actual := little (holdfast_bits_add_lsb a b c) in
  let total := little a + little b + digit c in
  actual = total \/ actual = total - capacity (holdfast_bits_len a).
Proof.
  induction a as [|x a IH]; intros [|y b] c L; try discriminate.
  - destruct c; cbn; intuition lia.
  - injection L as L. cbn [holdfast_bits_add_lsb little capacity holdfast_bits_len].
    specialize (IH b (holdfast_or (holdfast_and x y) (holdfast_and (holdfast_xorb x y) c)) L).
    destruct x, y, c; cbn [holdfast_xorb holdfast_or holdfast_and holdfast_not digit] in *; intuition lia.
Qed.
Lemma sum_cases : forall tag a b,
  let total := unsigned tag a + unsigned tag b in
  let actual := unsigned tag (holdfast_int_add tag a b) in
  actual = total \/ actual = total - 2 * half tag.
Proof.
  intros tag a b. cbv zeta. unfold unsigned. rewrite holdfast_int_add_bits.
  unfold holdfast_bits_add. change 0 with (little holdfast_bnil). rewrite <- !rev_value.
  unfold holdfast_bits_rev. rewrite holdfast_bits_rev_acc_rev. cbn [holdfast_bits_rev_acc].
  pose proof (little_sum_cases (holdfast_bits_rev (holdfast_int_bits tag a))
    (holdfast_bits_rev (holdfast_int_bits tag b)) false ltac:(now rewrite !holdfast_bits_rev_length, !holdfast_int_width)) as H.
  cbv zeta in H. rewrite holdfast_bits_rev_length, holdfast_int_width, full_capacity in H.
  cbn [digit] in H. unfold holdfast_bits_rev in H. lia.
Qed.
Lemma signed_add_ok : forall tag a b, holdfast_tag_signed tag = true ->
  - half tag <= signed tag a + signed tag b < half tag ->
  holdfast_int_chk_add tag a b = holdfast_Result_Ok _ _ (holdfast_int_add tag a b).
Proof.
  intros tag a b S B. pose proof (sum_cases tag a b) as E. cbv zeta in E.
  pose proof (signed_parts tag a S) as A. pose proof (signed_parts tag b S) as D.
  pose proof (signed_parts tag (holdfast_int_add tag a b) S) as R.
  unfold holdfast_int_chk_add, holdfast_bits_add_overflows. rewrite S, <- holdfast_int_add_bits.
  assert (K : holdfast_and (holdfast_eq_bool (holdfast_bits_head (holdfast_int_bits tag a)) (holdfast_bits_head (holdfast_int_bits tag b)))
    (holdfast_ne_bool (holdfast_bits_head (holdfast_int_bits tag (holdfast_int_add tag a b))) (holdfast_bits_head (holdfast_int_bits tag a))) = false).
  { destruct (holdfast_bits_head (holdfast_int_bits tag a)), (holdfast_bits_head (holdfast_int_bits tag b)),
      (holdfast_bits_head (holdfast_int_bits tag (holdfast_int_add tag a b))); try reflexivity; intuition lia. }
  rewrite K. unfold holdfast_int_ok. destruct (holdfast_int_add tag a b) as [w]. cbn [holdfast_int_bits].
  unfold holdfast_mk_int. now rewrite holdfast_word_roundtrip.
Qed.
Lemma signed_sub_ok : forall tag a b, holdfast_tag_signed tag = true ->
  - half tag <= signed tag a - signed tag b < half tag ->
  holdfast_int_chk_sub tag a b = holdfast_Result_Ok _ _ (holdfast_int_sub tag a b).
Proof.
  intros tag a b S B. pose proof (sum_cases tag b (holdfast_int_sub tag a b)) as E.
  cbv zeta in E. rewrite holdfast_int_sub_add in E.
  pose proof (signed_parts tag a S) as A. pose proof (signed_parts tag b S) as D.
  pose proof (signed_parts tag (holdfast_int_sub tag a b) S) as R.
  unfold holdfast_int_chk_sub, holdfast_bits_sub_overflows. rewrite S, <- holdfast_int_sub_bits.
  assert (K : holdfast_and (holdfast_ne_bool (holdfast_bits_head (holdfast_int_bits tag a)) (holdfast_bits_head (holdfast_int_bits tag b)))
    (holdfast_ne_bool (holdfast_bits_head (holdfast_int_bits tag (holdfast_int_sub tag a b))) (holdfast_bits_head (holdfast_int_bits tag a))) = false).
  { destruct (holdfast_bits_head (holdfast_int_bits tag a)), (holdfast_bits_head (holdfast_int_bits tag b)),
      (holdfast_bits_head (holdfast_int_bits tag (holdfast_int_sub tag a b))); try reflexivity; intuition lia. }
  rewrite K. unfold holdfast_int_ok. destruct (holdfast_int_sub tag a b) as [w]. cbn [holdfast_int_bits].
  unfold holdfast_mk_int. now rewrite holdfast_word_roundtrip.
Qed.
Lemma zero_value : forall bs, big (holdfast_bits_zero_like bs) 0 = 0.
Proof.
  induction bs; [reflexivity |].
  change (big (holdfast_bits_zero_like bs) 0 = 0). exact IHbs.
Qed.
Lemma nonzero : forall tag x, unsigned tag x <> 0 ->
  holdfast_bits_is_zero (holdfast_int_bits tag x) = false.
Proof.
  intros tag x H. unfold holdfast_bits_is_zero.
  destruct (holdfast_bits_eqb _ _) eqn:E; [|reflexivity].
  apply holdfast_bits_eqb_true in E. exfalso. apply H. unfold unsigned.
  rewrite E at 1. apply zero_value.
Qed.
Lemma rem_ok : forall tag a b, unsigned tag b <> 0 ->
  holdfast_int_chk_rem tag a b = holdfast_Result_Ok _ _ (holdfast_int_rem tag a b).
Proof. intros tag a b H. unfold holdfast_int_chk_rem. now rewrite nonzero. Qed.
Lemma div_ok : forall tag a b, holdfast_tag_signed tag = false -> unsigned tag b <> 0 ->
  holdfast_int_chk_div tag a b = holdfast_Result_Ok _ _ (holdfast_int_div tag a b).
Proof. intros tag a b S H. unfold holdfast_int_chk_div. now rewrite nonzero, S. Qed.
Lemma fill_value : forall xs bit p, big (holdfast_bits_fill xs bit) p =
  capacity (holdfast_bits_len xs) * p + (if bit then capacity (holdfast_bits_len xs) - 1 else 0).
Proof.
  induction xs as [|x xs IH]; intros bit p;
    cbn [holdfast_bits_fill holdfast_bits_len big capacity]; [destruct bit; lia |].
  rewrite IH. destruct bit; cbn [digit]; nia.
Qed.
Lemma min_value : forall xs, holdfast_bits_len xs <> O ->
  big (holdfast_bits_min true xs) 0 = capacity (Nat.pred (holdfast_bits_len xs)).
Proof.
  intros [|x xs] H; [contradiction |]. unfold holdfast_bits_min, holdfast_bits_zero_like.
  cbn [holdfast_bits_tail holdfast_bits_len big Nat.pred]. rewrite fill_value. cbn [digit]; nia.
Qed.
Lemma signed_min_excluded : forall tag x,
  unsigned tag x <> capacity (Nat.pred (holdfast_tag_bits tag)) ->
  holdfast_bits_eqb (holdfast_int_bits tag x) (holdfast_bits_min true (holdfast_int_bits tag x)) = false.
Proof.
  intros tag x H. destruct (holdfast_bits_eqb _ _) eqn:E; [|reflexivity].
  apply holdfast_bits_eqb_true in E. exfalso. apply H. unfold unsigned.
  rewrite E at 1. rewrite min_value, holdfast_int_width; [reflexivity |].
  rewrite holdfast_int_width. destruct tag as [|[|[|[|[|[|[|[|tag]]]]]]]]; discriminate.
Qed.
Lemma signed_div_ok : forall tag a b, holdfast_tag_signed tag = true -> unsigned tag b <> 0 ->
  (unsigned tag a <> capacity (Nat.pred (holdfast_tag_bits tag)) \/ unsigned tag b <> capacity (holdfast_tag_bits tag) - 1) ->
  holdfast_int_chk_div tag a b = holdfast_Result_Ok _ _ (holdfast_int_div tag a b).
Proof.
  intros tag a b S N [A|B]; unfold holdfast_int_chk_div; rewrite nonzero by exact N; rewrite S.
  - now rewrite signed_min_excluded.
  - destruct (holdfast_bits_eqb _ (holdfast_bits_fill _ true)) eqn:E.
    + apply holdfast_bits_eqb_true in E. exfalso. apply B. unfold unsigned.
      rewrite E at 1. rewrite fill_value, holdfast_int_width. lia.
    + destruct (holdfast_bits_eqb (holdfast_int_bits tag a) (holdfast_bits_min true (holdfast_int_bits tag a))); reflexivity.
Qed.
Lemma signed_neg_ok : forall tag a, holdfast_tag_signed tag = true ->
  unsigned tag a <> capacity (Nat.pred (holdfast_tag_bits tag)) ->
  holdfast_int_chk_neg tag a = holdfast_Result_Ok _ _ (holdfast_int_neg tag a).
Proof. intros tag a S H. unfold holdfast_int_chk_neg. now rewrite S, signed_min_excluded. Qed.
Lemma ne : forall tag a b, holdfast_int_ne tag a b = true -> unsigned tag a <> unsigned tag b.
Proof.
  intros tag a b H E. unfold holdfast_int_ne, holdfast_int_eq in H.
  pose proof (holdfast_int_width tag a) as A. pose proof (holdfast_int_width tag b) as B.
  assert (L : holdfast_bits_len (holdfast_int_bits tag a) = holdfast_bits_len (holdfast_int_bits tag b)) by congruence.
  assert (K : forall x y, holdfast_bits_ule x y = true -> holdfast_bits_ule y x = true -> holdfast_bits_eqb x y = true).
  { induction x as [|p x IH]; intros [|q y] P Q; try discriminate; try reflexivity.
    destruct p, q; cbn in *; intuition. }
  rewrite K in H; [discriminate | apply bits_le | apply bits_le]; try congruence;
    unfold unsigned in E; lia.
Qed.
Lemma eqv : forall tag a b, holdfast_int_eq tag a b = true -> unsigned tag a = unsigned tag b.
Proof. intros tag a b H. apply holdfast_int_eq_true in H. now subst. Qed.
Lemma signed_eqv : forall tag a b, holdfast_int_eq tag a b = true -> signed tag a = signed tag b.
Proof. intros tag a b H. apply holdfast_int_eq_true in H. now subst. Qed.
Lemma signed_ne : forall tag a b, holdfast_tag_signed tag = true ->
  holdfast_int_ne tag a b = true -> signed tag a <> signed tag b.
Proof.
  intros tag a b S H E. apply (ne tag a b H).
  pose proof (signed_parts tag a S). pose proof (signed_parts tag b S).
  destruct (holdfast_bits_head (holdfast_int_bits tag a)), (holdfast_bits_head (holdfast_int_bits tag b)); intuition lia.
Qed.
Lemma shift_amount : forall tag c,
  unsigned 4 c < big (holdfast_nat_to_bits 64 (holdfast_tag_bits tag)) 0 ->
  exists k, holdfast_shift_amount tag c = Some k.
Proof.
  intros tag c H. unfold holdfast_shift_amount. rewrite holdfast_int_width.
  assert (L : forall width n, holdfast_bits_len (holdfast_nat_to_bits width n) = width).
  { intros width n. unfold holdfast_nat_to_bits. rewrite holdfast_bits_rev_length. revert n.
    induction width; intros; cbn [holdfast_nat_to_bits_lsb holdfast_bits_len]; auto. }
  rewrite (proj2 (bits_lt _ _ ltac:(rewrite holdfast_int_width, L; reflexivity)) H). eexists; reflexivity.
Qed.
Lemma shr_ok : forall tag a c,
  unsigned 4 c < big (holdfast_nat_to_bits 64 (holdfast_tag_bits tag)) 0 ->
  holdfast_int_chk_shr tag a c = holdfast_Result_Ok _ _ (holdfast_int_shr tag a c).
Proof. intros tag a c H. destruct (shift_amount tag c H) as [k E]. unfold holdfast_int_chk_shr. now rewrite E. Qed.
Lemma wrap_shl_ok : forall tag a c,
  unsigned 4 c < big (holdfast_nat_to_bits 64 (holdfast_tag_bits tag)) 0 ->
  holdfast_checked_wrap_shl tag a c = holdfast_Result_Ok _ _ (holdfast_int_wrap_shl tag a c).
Proof. intros tag a c H. destruct (shift_amount tag c H) as [k E]. unfold holdfast_checked_wrap_shl. now rewrite E. Qed.
End HoldFastWordReplay.
"""
