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


def _lending_span_iteration() -> None:
    source = (TOOLS / "tests" / "fixtures" / "lending-span-iteration.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        bounded = source.replace(b"    requires values.CanRead",
                                 b"    requires values.Length == 4usize\n    requires values.CanRead")
        aliased = bounded.replace(b"    var visits", b"    let savedView = Span.ReadOnly(values);\n    var visits")
        owner_reused = bounded.replace(b"public Nat ", b"public byte ").replace(b"return visits;", b"return values[0usize];")
        view = b"Span.ReadOnly(Span.Slice(values, 0usize, 1usize))"
        earlier_use = owner_reused.replace(
            b"    var visits",
            b"    var before = 0u8;\n    { let selected = " + view + b"; before = selected[0usize]; }\n    var visits",
        ).replace(b"return values[0usize];", b"return before;")
        for valid in (owner_reused, earlier_use):
            elaborate(valid, parser.parse_source(compiled, valid, surface=True))
        for candidate, marker, message in (
            (bounded, b"let observed = values[0usize];", "cannot access suspended Span owner 'values'"),
            (aliased, b"let observed = savedView[0usize];", "cannot access suspended Span owner 'values'"),
        ):
            invalid = candidate.replace(b"        element =", b"        " + marker + b"\n        element =")
            with raises(HoldFastError, msg="a competing read bypassed the active element loan") as failure:
                elaborate(invalid, parser.parse_source(compiled, invalid, surface=True))
            error = failure.exception
            read_line = next(number for number, line in enumerate(invalid.splitlines(), 1) if marker in line)
            ensure(error.kind == "type" and error.line == read_line and message in error.message,
                   f"wrong refusal for conflicting access during lending: {error}")
        for invalid, message in (
            (source.replace(b" && values.CanWrite", b""), "Span.CanWrite"),
            (source.replace(b"in values) {", b"in values) invariant visits == 0 {"),
             "could not be established on loop inductive step"),
            (source.replace(b"writes(values)", b"none").replace(b"if (element == 0u8) 9u8 else 1u8", b"element"),
             "write"),
            (owner_reused.replace(b"    var visits", b"    let selected = " + view + b";\n    var visits")
             .replace(b"return values[0usize];", b"return selected[0usize];"),
             "cannot establish exclusive iteration of 'values' with retained Span views or aliases (selected)"),
        ):
            with raises(HoldFastError, msg="a loan was lent without a permission or invariant") as failure:
                elaborate(invalid, parser.parse_source(compiled, invalid, surface=True))
            ensure(failure.exception.kind == "type" and message in failure.exception.message,
                   f"wrong refusal for lending iteration: {failure.exception}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_RewriteElements) :", gallina, re.MULTILINE)
    proof = rf"""
From Stdlib Require Import Arith.PeanoNat Lists.List.
Import HoldFast_LendingSpanIteration ListNotations.
Local Definition trial_word := holdfast_int 0.
Local Definition trial_span := holdfast_Span trial_word.
Local Definition trial_index := holdfast_nat_to_usize.
Local Definition trial_byte n := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read trial_word.
Local Definition trial_length values := holdfast_int_to_nat 4 (holdfast_Span_Length trial_word values).
Local Definition trial_rewrite value :=
  if holdfast_int_eq 0 value (trial_byte 0) then trial_byte 9 else trial_byte 1.
Local Definition trial_step i values :=
  holdfast_Span_Write trial_word values (trial_index i) (trial_rewrite (trial_read values (trial_index i))).
Local Fixpoint trial_prefix values n :=
  match n with
  | O => values
  | S i => trial_step i (trial_prefix values i)
  end.
Local Definition trial_state values n :=
  holdfast_NatFold (trial_span * (nat * unit))
    (fun i state => (trial_step i (fst state), (fst (snd state) + 1, tt))) (values, (0, tt)) n.
Local Lemma trial_state_correct : forall values n,
  trial_state values n = (trial_prefix values n, (n, tt)).
Proof.
  intros values n. induction n as [|n IH]; [reflexivity|].
  change ((trial_step n (fst (trial_state values n)), (fst (snd (trial_state values n)) + 1, tt)) =
          (trial_step n (trial_prefix values n), (S n, tt))).
  rewrite IH. cbn [fst snd]. now rewrite Nat.add_1_r.
Qed.
Theorem lending_iteration_count_and_writeback : forall values,
  {client} values = trial_length values /\
  (forall k, trial_read ({client}_post_values values) k = trial_read (trial_prefix values (trial_length values)) k).
Proof.
  intros values. split.
  - change (fst (snd (trial_state values (trial_length values))) = trial_length values).
    now rewrite trial_state_correct.
  - intros k. change (trial_read (fst (trial_state values (trial_length values))) k =
                       trial_read (trial_prefix values (trial_length values)) k).
    now rewrite trial_state_correct.
Qed.
Local Lemma trial_prefix_frame : forall values n k,
  (forall i, i < n -> holdfast_int_ne 4 (trial_index i) k = true) ->
  trial_read (trial_prefix values n) k = trial_read values k.
Proof.
  intros values n. induction n as [|n IH]; intros k separate; [reflexivity|].
  change (trial_read (trial_step n (trial_prefix values n)) k = trial_read values k).
  unfold trial_step, trial_read. rewrite holdfast_Span_Read_write_other_ne.
  - apply IH. intros i earlier. apply separate. now apply Nat.lt_lt_succ_r.
  - apply separate, Nat.lt_succ_diag_r.
Qed.
Theorem lending_iteration_frame : forall values k,
  (forall i, i < trial_length values -> holdfast_int_ne 4 (trial_index i) k = true) ->
  trial_read ({client}_post_values values) k = trial_read values k.
Proof.
  intros values k separate. rewrite (proj2 (lending_iteration_count_and_writeback values)). now apply trial_prefix_frame.
Qed.
Local Definition trial_values (a b c d n : nat) :=
  let initial := holdfast_mk_span trial_word (trial_index 17) (trial_index n) true true true holdfast_bs_empty in
  let write s i v := holdfast_Span_Write trial_word s (trial_index i) (trial_byte v) in
  write (write (write (write initial 0 a) 1 b) 2 c) 3 d.
Local Definition trial_observe a b c d n :=
  let values := trial_values a b c d n in
  let post := {client}_post_values values in
  ({client} values, map (fun i => holdfast_int_to_nat 0 (trial_read post (trial_index i))) [0; 1; 2; 3]).
Example lending_prefix_observations :
  map (trial_observe 0 2 0 4) [0; 1; 2; 3; 4] =
    [(0, [0; 2; 0; 4]); (1, [9; 2; 0; 4]); (2, [9; 1; 0; 4]); (3, [9; 1; 9; 4]); (4, [9; 1; 9; 1])] /\
  map (trial_observe 1 0 3 0) [0; 1; 2; 3; 4] =
    [(0, [1; 0; 3; 0]); (1, [1; 0; 3; 0]); (2, [1; 9; 3; 0]); (3, [1; 9; 1; 0]); (4, [1; 9; 1; 9])].
Proof. vm_compute. split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "LendingSpanIteration", [
        "lending_iteration_count_and_writeback", "lending_iteration_frame", "lending_prefix_observations",
    ])


def cases() -> list[Case]:
    return [
        Case("conditional view return and sibling owner writeback", _conditional_view_return, lane="toolchain"),
        Case("returned view and branch-specific owner writeback at a join", _joined_view_return, lane="toolchain"),
        Case("returned view and disjoint symbolic loop writeback", _loop_view_return, lane="toolchain"),
        Case("scoped lending and symbolic Span element writeback", _lending_span_iteration, lane="toolchain"),
    ]
