# SPDX-License-Identifier: Apache-2.0
"""Replay returned views and their owner states on source control-flow paths."""

import re
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.elaborate import elaborate


def _replay_view_proof(gallina: str, proof: str, module: str, theorems: list[str]) -> None:
    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "view return depended on a solver assumption")
    exports = [*solver_ledger.math_exports(gallina), *theorems]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory(prefix="holdfast-view-return-") as tmp:
        unit = Path(tmp) / f"{module}.v"
        unit.write_text(gallina + proof + audit, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", unit.name], cwd=tmp, capture_output=True,
                                encoding="utf-8", timeout=180, check=False)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(exports), f"HoldFast_{module}", entries)


def _conditional_view_return() -> None:
    source = (TOOLS / "tests" / "fixtures" / "conditional-view-return.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        disjoint = source.replace(b"i < 4usize", b"i < 4usize && i != 0usize").replace(
            b"        return Ok", b"        values[0usize] = 9u8;\n        return Ok",
        )
        wide = disjoint.replace(b"i < 4usize && i != 0usize", b"i < 3usize && i > 0usize").replace(
            b"i, 1usize", b"i, 2usize",
        )
        for candidate in (disjoint, wide):
            elaborate(candidate, parser.parse_source(compiled, candidate, surface=True))
        direct_slice = source.replace(b"Span.ReadOnly(Span.Slice(values, i, 1usize))", b"Span.Slice(values, i, 1usize)")
        conflict = "cannot prove returned slice is disjoint from an update to 'values'"
        for candidate, update, message in (
            (source, b"Span.Restore(ref values, selected);", "already restored"),
            (source, b"values[i] = 9u8;", conflict),
            (direct_slice, b"values[i] = 9u8;", conflict),
        ):
            invalid = candidate.replace(b"        return Ok", b"        " + update + b"\n        return Ok")
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="the returned view outlived a conflicting owner update") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            return_line = next(number for number, line in enumerate(invalid.splitlines(), 1) if b"return Ok" in line)
            ensure(error.kind == "type" and error.line == return_line and message in error.message,
                   f"wrong refusal for an invalid returned view: {error}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_InspectOrReset) :", gallina, re.MULTILINE)
    [projection] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_ConditionalViewReturn.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition observed_byte values i :=
  match {client} values i with
  | inr loan => Some (trial_read ({projection} loan) (trial_index 0))
  | inl _ => None
  end.
Local Definition in_bounds i := holdfast_int_lt 4 i (trial_index 4).

Theorem conditional_view_and_writeback : forall values i,
  (in_bounds i = true ->
    observed_byte values i = Some (trial_read values i) /\
    {client}_post_values values i = values) /\
  (in_bounds i = false ->
    observed_byte values i = None /\
    trial_read ({client}_post_values values i) (trial_index 0) = trial_byte 8) /\
  (forall k, holdfast_int_ne 4 (trial_index 0) k = true ->
    trial_read ({client}_post_values values i) k = trial_read values k).
Proof.
  intros values i.
  unfold observed_byte, {client}, {client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:decision
  end.
  all: match type of decision with
       | _ = ?outcome => change (in_bounds i = outcome) in decision
       end; rewrite decision.
  - split; [| split; [discriminate | reflexivity]]. intros _. split; reflexivity.
  - split; [discriminate | split].
    + intros _. split; [reflexivity | apply holdfast_Span_Read_write_same].
    + intros k outside. now apply holdfast_Span_Read_write_other_ne.
Qed.

Local Definition trial_span :=
  holdfast_Span_Write _ (holdfast_mk_span (holdfast_int 0) (trial_index 11)
    (trial_index 4) true true true holdfast_bs_empty) (trial_index 3) (trial_byte 42).
Example conditional_view_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\
  holdfast_Span_CanWrite _ trial_span = true /\
  holdfast_Span_Length _ trial_span = trial_index 4 /\
  observed_byte trial_span (trial_index 3) = Some (trial_byte 42) /\
  observed_byte trial_span (trial_index 4) = None.
Proof. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "ConditionalViewReturn", [
        "conditional_view_and_writeback", "conditional_view_entry_is_inhabited",
    ])


def _joined_view_return() -> None:
    source = (TOOLS / "tests" / "fixtures" / "joined-view-return.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        before_borrow = source.replace(b"        let selected", b"        if (i == 0usize) { values[i] = 7u8; }\n        let selected")
        elaborate(before_borrow, parser.parse_source(compiled, before_borrow, surface=True))
        for candidate, write, conflict in (
            (source, b"values[1usize] = 8u8;", b"values[0usize] = 8u8;"),
            (source, b"values[0usize] = 9u8;", b"values[i] = 9u8;"),
            (before_borrow, b"values[0usize] = 9u8;", b"values[i] = 9u8;"),
        ):
            invalid = candidate.replace(write, conflict)
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="a join hid a write into the returned view") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            return_line = next(number for number, line in enumerate(invalid.splitlines(), 1) if b"return Ok" in line)
            ensure(error.kind == "type" and error.line == return_line
                   and "cannot prove returned slice is disjoint from an update to 'values'" in error.message,
                   f"wrong refusal for an overlapping branch write: {error}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_InspectAndPatch) :", gallina, re.MULTILINE)
    [projection] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_JoinedViewReturn.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition observed_byte values i :=
  match {client} values i with
  | inr loan => Some (trial_read ({projection} loan) (trial_index 0))
  | inl _ => None
  end.
Local Definition in_bounds i := holdfast_int_lt 4 i (trial_index 4).
Local Definition index_zero i := holdfast_int_eq 4 i (trial_index 0).
Local Definition written_index i := trial_index (if index_zero i then 1 else 0).
Local Definition written_byte i := trial_byte (if index_zero i then 8 else 9).

Theorem joined_view_and_writeback : forall values i,
  (in_bounds i = true ->
    observed_byte values i = Some (trial_read values i) /\
    trial_read ({client}_post_values values i) (written_index i) = written_byte i /\
    (forall k, holdfast_int_ne 4 (written_index i) k = true ->
      trial_read ({client}_post_values values i) k = trial_read values k)) /\
  (in_bounds i = false -> observed_byte values i = None /\ {client}_post_values values i = values).
Proof.
  intros values i. unfold observed_byte, {client}, {client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:decision
  end.
  all: match type of decision with
       | _ = ?outcome => change (in_bounds i = outcome) in decision
       end; rewrite decision.
  - split; [|discriminate]. intros _. split; [reflexivity|].
    match goal with
    | |- context [if ?guard then _ else _] => destruct guard eqn:zero
    end.
    all: match type of zero with
         | _ = ?outcome => change (index_zero i = outcome) in zero
         end; unfold written_index, written_byte; rewrite zero;
      split; [apply holdfast_Span_Read_write_same | intros k outside; now apply holdfast_Span_Read_write_other_ne].
  - split; [discriminate | intros _; split; reflexivity].
Qed.

Local Definition trial_span :=
  holdfast_Span_Write _ (holdfast_mk_span (holdfast_int 0) (trial_index 11)
    (trial_index 4) true true true holdfast_bs_empty) (trial_index 0) (trial_byte 42).
Example joined_view_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\
  holdfast_Span_CanWrite _ trial_span = true /\
  holdfast_Span_Length _ trial_span = trial_index 4 /\
  observed_byte trial_span (trial_index 0) = Some (trial_byte 42) /\
  observed_byte trial_span (trial_index 4) = None.
Proof. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "JoinedViewReturn", ["joined_view_and_writeback", "joined_view_entry_is_inhabited"])


def _loop_view_return() -> None:
    source = (TOOLS / "tests" / "fixtures" / "loop-view-return.hf").read_bytes()
    loop_start = source.index(b"        foreach")
    loop_end = source.index(b"        return Ok", loop_start)
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        empty = source[:loop_start] + b"        Span.Fill(ref values, 3usize, n, 9u8);\n" + source[loop_end:]
        empty = empty.replace(b"n <= 3usize", b"n == 0usize")
        after_view = source[:loop_start] + b"        Span.Fill(ref values, 1usize, 3usize, 9u8);\n" + source[loop_end:]
        after_view = after_view.replace(b"3usize, 1usize", b"0usize, 1usize")
        for valid in (empty, after_view):
            elaborate(valid, parser.parse_source(compiled, valid, surface=True))
        for invalid in (
            source.replace(b"n <= 3usize", b"n <= 4usize"),
            source.replace(b"3usize, 1usize", b"2usize, 2usize"),
            after_view.replace(b"1usize, 3usize, 9u8", b"0usize, 3usize, 9u8"),
        ):
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="a fill overlapped the returned view") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            return_line = next(number for number, line in enumerate(invalid.splitlines(), 1) if b"return Ok" in line)
            ensure(error.kind == "type" and error.line == return_line
                   and "cannot prove returned slice is disjoint from an update to 'values'" in error.message,
                   f"wrong refusal for an overlapping fill: {error}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_InspectAndFill) :", gallina, re.MULTILINE)
    [projection] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_LoopViewReturn.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition observed_byte values n :=
  match {client} values n with
  | inr loan => Some (trial_read ({projection} loan) (trial_index 0))
  | inl _ => None
  end.
Local Definition valid_count n := holdfast_int_le 4 n (trial_index 3).
Local Definition expected_byte values n k :=
  if holdfast_int_lt 4 k n then trial_byte 9 else trial_read values k.

Theorem loop_view_and_writeback : forall values n,
  (valid_count n = true ->
    observed_byte values n = Some (trial_read values (trial_index 3)) /\
    observed_byte values n = Some (trial_read ({client}_post_values values n) (trial_index 3)) /\
    (forall k, trial_read ({client}_post_values values n) k = expected_byte values n k)) /\
  (valid_count n = false -> observed_byte values n = None /\ {client}_post_values values n = values).
Proof.
  intros values n. unfold observed_byte, {client}, {client}_post_values. cbv beta.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:decision
  end.
  all: match type of decision with
       | _ = ?outcome => change (valid_count n = outcome) in decision
       end; rewrite decision.
  - split; [|discriminate]. intros _. split; [reflexivity|]. split.
    + change (Some (trial_read values (trial_index 3)) =
        Some (trial_read (holdfast_Span_Fill _ values holdfast_usize_zero n (trial_byte 9)) (trial_index 3))).
      symmetry. apply (f_equal (@Some _)).
      apply (holdfast_store_lookup_fill_ge _ _ (trial_index 3)); [exact decision|reflexivity].
    + intros k. unfold expected_byte.
      change ((if holdfast_in_extent k holdfast_usize_zero n then trial_byte 9 else trial_read values k) =
        if holdfast_int_lt 4 k n then trial_byte 9 else trial_read values k).
      unfold holdfast_in_extent. now rewrite holdfast_usize_zero_le.
  - split; [discriminate|intros _; split; reflexivity].
Qed.

Local Definition trial_span :=
  holdfast_Span_Write _ (holdfast_mk_span (holdfast_int 0) (trial_index 11)
    (trial_index 4) true true true holdfast_bs_empty) (trial_index 3) (trial_byte 42).
Example loop_view_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\
  holdfast_Span_CanWrite _ trial_span = true /\
  holdfast_Span_Length _ trial_span = trial_index 4 /\
  observed_byte trial_span (trial_index 0) = Some (trial_byte 42) /\
  observed_byte trial_span (trial_index 3) = Some (trial_byte 42) /\
  observed_byte trial_span (trial_index 4) = None.
Proof. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "LoopViewReturn", ["loop_view_and_writeback", "loop_view_entry_is_inhabited"])


def cases() -> list[Case]:
    return [
        Case("conditional view return and sibling owner writeback", _conditional_view_return, lane="toolchain"),
        Case("returned view and branch-specific owner writeback at a join", _joined_view_return, lane="toolchain"),
        Case("returned view and disjoint symbolic loop writeback", _loop_view_return, lane="toolchain"),
    ]
