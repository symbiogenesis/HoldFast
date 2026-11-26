# SPDX-License-Identifier: Apache-2.0
"""Replay shared views and their owner states on source control-flow paths."""

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


def _branch_view_last_use() -> None:
    source = (TOOLS / "tests" / "fixtures" / "branch-view-last-use.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        for read, site, prefix in (
            (b"selected[0usize]", b"selected[0usize]", b""),
            (b"Span.Read(selected, 0usize)", b"Span.Read", b""),
            (b"selected.Model[0usize]", b"selected.Model", b""),
            (b"ReadElement(in selected[0usize])", b"selected[0usize]",
             b"private byte ReadElement(in byte value) { return value; }\n\n"),
        ):
            candidate = source.replace(b"selected[0usize]", read).replace(
                b"public byte ObserveAndWrite", prefix + b"public byte ObserveAndWrite",
            )
            elaborate(candidate, parser.parse_source(compiled, candidate, surface=True))
            for invalid, access in (
                (candidate.replace(
                    b"        let observed = " + read + b";\n        values[i] = 9u8;",
                    b"        values[i] = 9u8;\n        let observed = " + read + b";",
                ), b"let observed = " + read),
                (candidate.replace(b"values[0usize] = 8u8;", b"values[i] = 8u8;"), b"return " + read),
            ):
                tree = parser.parse_source(compiled, invalid, surface=True)
                with raises(HoldFastError, msg="a read through an overlapping branch write was accepted") as failure:
                    elaborate(invalid, tree)
                error = failure.exception
                line, row = next((n, row) for n, row in enumerate(invalid.splitlines(), 1) if access in row)
                ensure(error.kind == "type" and (error.line, error.column) == (line, row.index(site) + 1)
                       and "cannot prove Span view read is disjoint from an update to 'values'" in error.message,
                       f"wrong refusal for a live slice read: {error}")

        whole = source.replace(b"Span.ReadOnly(Span.Slice(values, i, 1usize))", b"Span.ReadOnly(values)").replace(
            b"selected[0usize]", b"selected[i]",
        )
        valid_whole = whole.replace(b"        values[0usize] = 8u8;\n", b"")
        elaborate(valid_whole, parser.parse_source(compiled, valid_whole, surface=True))
        with raises(HoldFastError, msg="a live read-only view of the full owner survived an overlapping write") as failure:
            elaborate(whole, parser.parse_source(compiled, whole, surface=True))
        ensure(failure.exception.kind == "type"
               and "cannot prove Span view read is disjoint from an update to 'values'" in failure.exception.message,
               f"wrong refusal for a live full-owner view: {failure.exception}")

        live_read = b"        return selected[0usize];"
        iteration = source.replace(live_read, b"""        var observed = 0u8;
        foreach (let element in selected) {
            observed = element;
        }
        return observed;""")
        copy = source.replace(
            b"ref Span<byte> values, usize i", b"ref Span<byte> values, ref Span<byte> dest, usize i",
        ).replace(b"effects writes(values)", b"effects writes(values, dest)").replace(
            b"    requires i < 4usize",
            b"    requires i < 4usize\n    requires dest.CanRead && dest.CanWrite\n"
            b"    requires dest.Length == 1usize\n    requires Span.Disjoint(values, dest)",
        ).replace(live_read, b"        Span.CopyPrefix(ref dest, selected, 1usize);\n        return dest[0usize];")
        for candidate, access in ((iteration, b"in selected"), (copy, b"Span.CopyPrefix")):
            elaborate(candidate, parser.parse_source(compiled, candidate, surface=True))
            invalid = candidate.replace(b"values[0usize] = 8u8;", b"values[i] = 8u8;")
            with raises(HoldFastError, msg="a range read ignored an overlapping owner write") as failure:
                elaborate(invalid, parser.parse_source(compiled, invalid, surface=True))
            error = failure.exception
            line = next(n for n, row in enumerate(invalid.splitlines(), 1) if access in row)
            ensure(error.kind == "type" and error.line == line
                   and "cannot prove Span view read is disjoint from an update to 'values'" in error.message,
                   f"wrong refusal for a live Span view in a range read: {error}")

        constant = b"""module GlobalIndexedBorrow;
private const Vec<Nat,1> Tag = "A";
private Nat ReadElement(in Nat value) { return value; }
public Nat ReadTag() { return ReadElement(in Tag[0]); }
"""
        elaborate(constant, parser.parse_source(compiled, constant, surface=True))

    [client] = re.findall(r"^Definition (holdfast_d\d+_ObserveAndWrite) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_BranchViewLastUse.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition trial_write := holdfast_Span_Write (holdfast_int 0).
Local Definition nonzero i := holdfast_int_ne 4 i (trial_index 0).

Theorem branch_view_observation_and_restoration : forall values i read_first,
  {client} values i read_first = trial_read values i /\
  {client}_post_values values i read_first =
    if read_first then trial_write values i (trial_byte 9)
    else if nonzero i then trial_write values (trial_index 0) (trial_byte 8)
    else values.
Proof.
  intros values i read_first.
  unfold {client}, {client}_post_values, nonzero. cbv beta.
  destruct read_first; split; try reflexivity.
  match goal with
  | |- context [if ?guard then _ else _] => destruct guard eqn:decision
  end.
  all: try reflexivity.
  all: match type of decision with
       | _ = ?outcome => change (holdfast_int_ne 4 i (trial_index 0) = outcome) in decision
       end; rewrite decision; reflexivity.
Qed.

Theorem branch_view_frame : forall values i read_first k,
  (read_first = true -> holdfast_int_ne 4 i k = true) ->
  (read_first = false -> nonzero i = true -> holdfast_int_ne 4 (trial_index 0) k = true) ->
  trial_read ({client}_post_values values i read_first) k = trial_read values k.
Proof.
  intros values i read_first k after_read before_read.
  rewrite (proj2 (branch_view_observation_and_restoration values i read_first)).
  destruct read_first.
  - apply holdfast_Span_Read_write_other_ne. now apply after_read.
  - destruct (nonzero i) eqn:separate.
    + apply holdfast_Span_Read_write_other_ne. now apply before_read.
    + reflexivity.
Qed.

Local Definition trial_span :=
  trial_write (holdfast_mk_span (holdfast_int 0) (trial_index 11)
    (trial_index 4) true true true holdfast_bs_empty) (trial_index 2) (trial_byte 42).
Example branch_view_entry_is_inhabited :
  holdfast_Span_CanRead _ trial_span = true /\
  holdfast_Span_CanWrite _ trial_span = true /\
  holdfast_Span_Length _ trial_span = trial_index 4 /\
  holdfast_int_lt 4 (trial_index 2) (trial_index 4) = true /\
  {client} trial_span (trial_index 2) true = trial_byte 42 /\
  {client} trial_span (trial_index 2) false = trial_byte 42 /\
  trial_read ({client}_post_values trial_span (trial_index 2) true) (trial_index 2) = trial_byte 9 /\
  trial_read ({client}_post_values trial_span (trial_index 2) false) (trial_index 0) = trial_byte 8.
Proof. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "BranchViewLastUse", [
        "branch_view_observation_and_restoration", "branch_view_frame", "branch_view_entry_is_inhabited",
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


def _correlated_view_return() -> None:
    source = b"""module CorrelatedViewReturn;

public record ByteView<region 'owner>(in<'owner> Span<byte> Bytes);

public ByteView<'owner> PatchOther<region 'owner>(ref<'owner> Span<byte> values, bool first)
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
    return ByteView(in selected);
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        for invalid in (
            source.replace(b"values[1usize] = 8u8;", b"values[0usize] = 8u8;"),
            source.replace(b"values[0usize] = 9u8;", b"values[1usize] = 9u8;"),
            source.replace(b"bool first)", b"bool first, bool patchFirst)").replace(b"    if (first)", b"    if (patchFirst)"),
        ):
            tree = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="an overlapping branch write invalidated the selected view") as failure:
                elaborate(invalid, tree)
            error = failure.exception
            return_line = next(n for n, line in enumerate(invalid.splitlines(), 1) if b"return ByteView" in line)
            ensure(error.kind == "type" and error.line == return_line
                   and "cannot prove returned slice is disjoint from an update to 'values'" in error.message,
                   f"wrong refusal for an overlapping returned view: {error}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_PatchOther) :", gallina, re.MULTILINE)
    [projection] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_CorrelatedViewReturn.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition view_index (first : bool) := trial_index (if first then 0 else 1).
Local Definition write_index (first : bool) := trial_index (if first then 1 else 0).
Local Definition write_byte (first : bool) := trial_byte (if first then 8 else 9).

Theorem correlated_view_and_writeback : forall values first,
  let view := {projection} ({client} values first) in
  let post := {client}_post_values values first in
  holdfast_Span_Base _ view = holdfast_int_add 4 (holdfast_Span_Base _ post) (view_index first) /\
  holdfast_Span_Length _ view = trial_index 1 /\
  trial_read view (trial_index 0) = trial_read post (view_index first) /\
  trial_read post (write_index first) = write_byte first /\
  (forall k, holdfast_int_ne 4 (write_index first) k = true -> trial_read post k = trial_read values k).
Proof.
  intros values [];
    unfold {client}, {client}_post_values, {projection}, view_index, write_index, write_byte;
    cbv beta iota zeta.
  all: split; [reflexivity |]; split; [reflexivity |]; split.
  1,3: match goal with
       | |- _ = ?post_read =>
         lazymatch post_read with
         | trial_read _ ?index => change (trial_read values index = post_read)
         end
       end; symmetry; apply holdfast_Span_Read_write_other_ne; reflexivity.
  all: split; [apply holdfast_Span_Read_write_same | intros k outside; now apply holdfast_Span_Read_write_other_ne].
Qed.

Local Definition initial_span :=
  holdfast_Span_Write _
    (holdfast_Span_Write _ (holdfast_mk_span (holdfast_int 0) (trial_index 11)
      (trial_index 4) true true true holdfast_bs_empty) (trial_index 0) (trial_byte 3))
    (trial_index 1) (trial_byte 4).
Example correlated_view_observations :
  holdfast_Span_CanRead _ initial_span = true /\
  holdfast_Span_CanWrite _ initial_span = true /\
  holdfast_Span_Length _ initial_span = trial_index 4 /\
  trial_read ({projection} ({client} initial_span true)) (trial_index 0) = trial_byte 3 /\
  trial_read ({projection} ({client} initial_span false)) (trial_index 0) = trial_byte 4 /\
  trial_read ({client}_post_values initial_span true) (trial_index 1) = trial_byte 8 /\
  trial_read ({client}_post_values initial_span false) (trial_index 0) = trial_byte 9.
Proof. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "CorrelatedViewReturn", [
        "correlated_view_and_writeback", "correlated_view_observations",
    ])


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


def _lending_span_break() -> None:
    source = (TOOLS / "tests" / "fixtures" / "lending-span-break.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        bounded = source.replace(b"    requires values.CanRead",
                                 b"    requires values.Length == 4usize\n    requires values.CanRead")
        aliased = bounded.replace(b"    var visits", b"    let savedView = Span.ReadOnly(values);\n    var visits")
        owner_reused = bounded.replace(b"public Nat ", b"public byte ").replace(b"return visits;", b"return values[0usize];")
        view = b"Span.ReadOnly(Span.Slice(values, 0usize, 1usize))"
        elaborate(owner_reused, parser.parse_source(compiled, owner_reused, surface=True))
        for candidate, marker, message in (
            (bounded, b"let observed = values[0usize];", "cannot access suspended Span owner 'values'"),
            (aliased, b"let observed = savedView[0usize];", "cannot access suspended Span owner 'values'"),
        ):
            invalid = candidate.replace(b"        let stop", b"        " + marker + b"\n        let stop")
            with raises(HoldFastError, msg="a competing read bypassed the active element loan") as failure:
                elaborate(invalid, parser.parse_source(compiled, invalid, surface=True))
            error = failure.exception
            read_line = next(number for number, line in enumerate(invalid.splitlines(), 1) if marker in line)
            ensure(error.kind == "type" and error.line == read_line and message in error.message,
                   f"wrong refusal for conflicting access during breaking lending: {error}")
        for invalid, expected_kind, message in (
            (source.replace(b"in values) {", b"in values) invariant visits == 0 {"),
             "type", "could not be established on loop break"),
            (source.replace(b"        if (stop) {\n            break;\n        }",
                            b"        if (stop) {\n            break;\n        }\n        visits += 0;"),
             "unsupported", "a conditional loop exit needs an explicit control-flow result"),
            (owner_reused.replace(b"    var visits", b"    let selected = " + view + b";\n    var visits")
             .replace(b"return values[0usize];", b"return selected[0usize];"),
             "type", "cannot establish exclusive iteration of 'values' with retained Span views or aliases (selected)"),
        ):
            with raises(HoldFastError, msg="invalid break or retained view was accepted") as failure:
                elaborate(invalid, parser.parse_source(compiled, invalid, surface=True))
            ensure(failure.exception.kind == expected_kind and message in failure.exception.message,
                   f"wrong refusal for lending break: {failure.exception}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_RewriteThroughZero) :", gallina, re.MULTILINE)
    proof = rf"""
From Stdlib Require Import Arith.PeanoNat Lists.List.
Import HoldFast_LendingSpanBreak ListNotations.
Local Definition trial_word := holdfast_int 0.
Local Definition trial_span := holdfast_Span trial_word.
Local Definition trial_index := holdfast_nat_to_usize.
Local Definition trial_byte n := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read trial_word.
Local Definition trial_length values := holdfast_int_to_nat 4 (holdfast_Span_Length trial_word values).
Local Definition trial_step i (state : trial_span * (nat * bool)) :=
  if snd (snd state) then state
  else
    (holdfast_Span_Write trial_word (fst state) (trial_index i) (trial_byte 9),
     (fst (snd state) + 1, holdfast_int_eq 0 (trial_read (fst state) (trial_index i)) (trial_byte 0))).
Local Fixpoint trial_prefix values n :=
  match n with
  | O => (values, (0, false))
  | S i => trial_step i (trial_prefix values i)
  end.
Local Definition trial_state values n :=
  holdfast_NatFold (trial_span * (nat * bool)) trial_step (values, (0, false)) n.
Local Lemma trial_state_correct : forall values n,
  trial_state values n = trial_prefix values n.
Proof.
  intros values n. induction n as [|n IH]; [reflexivity|].
  change (trial_step n (trial_state values n) = trial_step n (trial_prefix values n)).
  now rewrite IH.
Qed.
Theorem lending_break_count_and_writeback : forall values,
  {client} values = fst (snd (trial_prefix values (trial_length values))) /\
  (forall k, trial_read ({client}_post_values values) k = trial_read (fst (trial_prefix values (trial_length values))) k).
Proof.
  intros values. split.
  - change (fst (snd (trial_state values (trial_length values))) =
            fst (snd (trial_prefix values (trial_length values)))).
    now rewrite trial_state_correct.
  - intros k. change (trial_read (fst (trial_state values (trial_length values))) k =
                       trial_read (fst (trial_prefix values (trial_length values))) k).
    now rewrite trial_state_correct.
Qed.
Local Lemma trial_prefix_frozen : forall values i d,
  snd (snd (trial_prefix values i)) = true ->
  trial_prefix values (i + d) = trial_prefix values i.
Proof.
  intros values i d stopped. induction d as [|d IH]; [now rewrite Nat.add_0_r|].
  rewrite Nat.add_succ_r.
  change (trial_step (i + d) (trial_prefix values (i + d)) = trial_prefix values i).
  rewrite IH. unfold trial_step. now rewrite stopped.
Qed.
Local Lemma trial_prefix_frame : forall values n k,
  (forall i, i < n -> holdfast_int_ne 4 (trial_index i) k = true) ->
  trial_read (fst (trial_prefix values n)) k = trial_read values k.
Proof.
  intros values n. induction n as [|n IH]; intros k separate; [reflexivity|].
  change (trial_read (fst (trial_step n (trial_prefix values n))) k = trial_read values k).
  unfold trial_step. destruct (snd (snd (trial_prefix values n))); cbn [fst].
  - apply IH. intros i earlier. apply separate. now apply Nat.lt_lt_succ_r.
  - unfold trial_read. rewrite holdfast_Span_Read_write_other_ne.
    + apply IH. intros i earlier. apply separate. now apply Nat.lt_lt_succ_r.
    + apply separate, Nat.lt_succ_diag_r.
Qed.
Theorem lending_break_frame_and_freeze : forall values k,
  ((forall i, i < trial_length values -> holdfast_int_ne 4 (trial_index i) k = true) ->
   trial_read ({client}_post_values values) k = trial_read values k) /\
  (forall i d, snd (snd (trial_prefix values i)) = true ->
   trial_prefix values (i + d) = trial_prefix values i).
Proof.
  intros values k. split.
  - intros separate. rewrite (proj2 (lending_break_count_and_writeback values)). now apply trial_prefix_frame.
  - intros i d stopped. now apply trial_prefix_frozen.
Qed.
Local Definition trial_values (a b c d n : nat) :=
  let initial := holdfast_mk_span trial_word (trial_index 17) (trial_index n) true true true holdfast_bs_empty in
  let write s i v := holdfast_Span_Write trial_word s (trial_index i) (trial_byte v) in
  write (write (write (write initial 0 a) 1 b) 2 c) 3 d.
Local Definition trial_observe a b c d n :=
  let values := trial_values a b c d n in
  let post := {client}_post_values values in
  ({client} values, map (fun i => holdfast_int_to_nat 0 (trial_read post (trial_index i))) [0; 1; 2; 3]).
Example lending_break_observations :
  trial_observe 1 2 3 4 0 = (0, [1; 2; 3; 4]) /\
  trial_observe 0 2 3 4 4 = (1, [9; 2; 3; 4]) /\
  trial_observe 1 0 2 3 4 = (2, [9; 9; 2; 3]) /\
  trial_observe 1 2 3 0 4 = (4, [9; 9; 9; 9]) /\
  trial_observe 1 2 3 4 4 = (4, [9; 9; 9; 9]).
Proof. vm_compute. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "LendingSpanBreak", [
        "lending_break_count_and_writeback", "lending_break_frame_and_freeze", "lending_break_observations",
    ])


def cases() -> list[Case]:
    return [
        Case("conditional view return and sibling owner writeback", _conditional_view_return, lane="toolchain"),
        Case("branch-specific last use of a shared Span view", _branch_view_last_use, lane="toolchain"),
        Case("returned view and branch-specific owner writeback at a join", _joined_view_return, lane="toolchain"),
        Case("conditional view origin and correlated owner writeback", _correlated_view_return, lane="toolchain"),
        Case("returned view and disjoint symbolic loop writeback", _loop_view_return, lane="toolchain"),
        Case("scoped lending and symbolic Span element writeback", _lending_span_iteration, lane="toolchain"),
        Case("scoped lending and early break exits on Span", _lending_span_break, lane="toolchain"),
    ]
