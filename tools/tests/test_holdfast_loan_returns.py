# SPDX-License-Identifier: Apache-2.0
"""Replay shared views and their owner states on source control-flow paths."""

import contextlib
import re
import subprocess
from functools import partial
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import parser, proofenv, rocq_cache, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.elaborate import elaborate


def _replay_view_proof(gallina: str, proof: str, module: str, theorems: list[str], *,
                       batch: rocq_cache.BatchChecker | None = None) -> None:
    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "view return depended on a solver assumption")
    exports = [*solver_ledger.math_exports(gallina), *theorems]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with contextlib.ExitStack() as stack:
        if batch is None:
            directory = Path(stack.enter_context(TemporaryDirectory(prefix="holdfast-view-return-")))
            stem = module
        else:
            directory = batch.work_dir
            stem = batch.unique_stem(module)
        unit = directory / f"{stem}.v"
        unit.write_text(gallina + proof + audit, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", unit.name], cwd=directory, capture_output=True,
                                encoding="utf-8", timeout=180, check=False)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(exports), f"HoldFast_{module}", entries)
        if batch is not None:
            batch.register(stem)
        else:
            rocq_cache.check_kernel(directory, [stem])


def _conditional_view_return(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    ], batch=batch)


def _branch_view_last_use(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    ], batch=batch)


def _joined_view_return(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    _replay_view_proof(gallina, proof, "JoinedViewReturn", [
        "joined_view_and_writeback", "joined_view_entry_is_inhabited",
    ], batch=batch)


def _correlated_view_return(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    ], batch=batch)


def _loop_view_return(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    _replay_view_proof(gallina, proof, "LoopViewReturn", [
        "loop_view_and_writeback", "loop_view_entry_is_inhabited",
    ], batch=batch)


def _lending_span_iteration(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    ], batch=batch)


def _lending_span_break(*, batch: rocq_cache.BatchChecker | None = None) -> None:
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
    ], batch=batch)


def _lending_filter_return(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = (TOOLS / "tests" / "fixtures" / "lending-filter-return.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina

        # 1. Writing to the returned slice index before early return violates disjointness
        overlapping = source.replace(
            b"            return Ok(ByteView(in selected));",
            b"            buf[i] = 9u8;\n            return Ok(ByteView(in selected));",
        )
        with raises(HoldFastError, msg="overlapping write before returned view") as overlap_err:
            elaborate(overlapping, parser.parse_source(compiled, overlapping, surface=True))
        return_line = next(n for n, line in enumerate(overlapping.splitlines(), 1) if b"return Ok" in line)
        ensure(
            overlap_err.exception.kind == "type"
            and overlap_err.exception.line == return_line
            and "cannot prove returned slice is disjoint from an update to 'buf'" in overlap_err.exception.message,
            f"unexpected error for overlapping early-return write: {overlap_err.exception}",
        )

        # 2. Missing write permission on continue-path update is refused
        no_write = source.replace(b"requires buf.CanRead && buf.CanWrite", b"requires buf.CanRead").replace(
            b"        invariant buf.CanWrite\n", b""
        )
        with raises(HoldFastError, msg="missing Span.CanWrite permission") as perm_err:
            elaborate(no_write, parser.parse_source(compiled, no_write, surface=True))
        ensure(
            perm_err.exception.kind == "type" and "Span.CanWrite" in perm_err.exception.message,
            f"unexpected error for missing write permission: {perm_err.exception}",
        )

        # 3. Returning an out-of-bounds slice from the loop body is refused
        oob_slice = source.replace(
            b"if (buf[i] != 0u8) {", b"if (buf[i] != 0u8 && len < 100usize) {"
        ).replace(b"Span.Slice(buf, i, 1usize)", b"Span.Slice(buf, i, 2usize)")
        with raises(HoldFastError, msg="out-of-bounds loop slice") as bounds_err:
            elaborate(oob_slice, parser.parse_source(compiled, oob_slice, surface=True))
        ensure(
            bounds_err.exception.kind == "type" and "slice" in bounds_err.exception.message.lower(),
            f"unexpected error for out-of-bounds slice: {bounds_err.exception}",
        )

    [client] = re.findall(r"^Definition (holdfast_d\d+_FirstNonZeroAndMark) :", gallina, re.MULTILINE)
    [view_ty] = re.findall(r"^Definition (holdfast_d\d+_ByteView) :", gallina, re.MULTILINE)
    [view_ctor] = re.findall(r"^Definition (holdfast_d\d+_ByteView_ctor) :", gallina, re.MULTILINE)
    [projection] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_LendingFilterReturn.
Local Definition trial_word := holdfast_int 4.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_span := holdfast_Span (holdfast_int 0).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition trial_length s := holdfast_int_to_nat 4 (holdfast_Span_Length (holdfast_int 0) s).
Local Definition trial_res := holdfast_Result {view_ty} bool.
Local Definition trial_state_t := (trial_span * (unit + trial_res))%type.
Local Definition observe_res (r : trial_res) : option (nat * nat) :=
  match r with
  | inl _ => None
  | inr v =>
      Some (holdfast_int_to_nat 0 (trial_read ({projection} v) (trial_index 0)),
            holdfast_int_to_nat 4 (holdfast_Span_Length (holdfast_int 0) ({projection} v)))
  end.
Local Definition trial_step (i : nat) (st : trial_state_t) : trial_state_t :=
  match snd st with
  | inr _ => st
  | inl _ =>
      let cur := fst st in
      let idx := holdfast_nat_to_usize (holdfast_int_to_nat 4 (trial_index 0) + i) in
      if holdfast_int_ne 0 (trial_read cur idx) (trial_byte 0)
      then (cur, inr (inr ({view_ctor} (holdfast_Span_ReadOnly (holdfast_int 0) (holdfast_Span_Slice (holdfast_int 0) cur idx (trial_index 1))))))
      else (holdfast_Span_Write (holdfast_int 0) cur idx (trial_byte 9), inl tt)
  end.
Local Fixpoint trial_prefix buf n : trial_state_t :=
  match n with
  | O => (buf, inl tt)
  | S i => trial_step i (trial_prefix buf i)
  end.
Local Definition trial_state buf n :=
  holdfast_NatFold trial_state_t trial_step (buf, inl tt) n.
Local Lemma trial_state_correct : forall buf n,
  trial_state buf n = trial_prefix buf n.
Proof.
  intros buf n. induction n as [|n IH]; [reflexivity|].
  change (trial_step n (trial_state buf n) = trial_step n (trial_prefix buf n)).
  now rewrite IH.
Qed.
Theorem lending_filter_matches_recursive : forall buf,
  let st := trial_prefix buf (trial_length buf) in
  {client} buf = (match snd st with inl _ => inl false | inr r => r end) /\
  (forall k, trial_read ({client}_post_buf buf) k = trial_read (fst st) k).
Proof.
  intros buf.
  assert (Hsub : trial_length buf - holdfast_int_to_nat 4 (trial_index 0) = trial_length buf) by (destruct (trial_length buf); reflexivity).
  unfold {client}, {client}_post_buf. cbv beta.
  split.
  - change (match snd (trial_state buf (trial_length buf - holdfast_int_to_nat 4 (trial_index 0))) with inl _ => inl false | inr r => r end =
            match snd (trial_prefix buf (trial_length buf)) with inl _ => inl false | inr r => r end).
    rewrite Hsub. now rewrite trial_state_correct.
  - intros k. change (trial_read (fst (trial_state buf (trial_length buf - holdfast_int_to_nat 4 (trial_index 0)))) k =
                      trial_read (fst (trial_prefix buf (trial_length buf))) k).
    rewrite Hsub. now rewrite trial_state_correct.
Qed.
Local Lemma trial_prefix_frozen : forall buf i d r,
  snd (trial_prefix buf i) = inr r ->
  trial_prefix buf (i + d) = trial_prefix buf i.
Proof.
  intros buf i d r hit. induction d as [|d IH]; [rewrite <- plus_n_O; reflexivity|].
  rewrite <- plus_n_Sm.
  change (trial_step (i + d) (trial_prefix buf (i + d)) = trial_prefix buf i).
  rewrite IH. unfold trial_step. now rewrite hit.
Qed.
Local Lemma trial_prefix_frame : forall buf n k,
  (forall i, i < n ->
    holdfast_int_ne 4 (holdfast_nat_to_usize (holdfast_int_to_nat 4 (trial_index 0) + i)) k = true) ->
  trial_read (fst (trial_prefix buf n)) k = trial_read buf k.
Proof.
  intros buf n. induction n as [|n IH]; intros k sep; [reflexivity|].
  assert (earlier : forall i, i < n ->
    holdfast_int_ne 4 (holdfast_nat_to_usize (holdfast_int_to_nat 4 (trial_index 0) + i)) k = true)
    by (intros i hi; apply sep; exact (le_S _ _ hi)).
  change (trial_read (fst (trial_step n (trial_prefix buf n))) k = trial_read buf k).
  unfold trial_step. destruct (snd (trial_prefix buf n)) as [[]|r] eqn:Hst.
  - set (cur := fst (trial_prefix buf n)).
    set (idx := holdfast_nat_to_usize (holdfast_int_to_nat 4 (trial_index 0) + n)).
    destruct (holdfast_int_ne 0 (trial_read cur idx) (trial_byte 0)); cbn [fst].
    + exact (IH k earlier).
    + unfold trial_read. rewrite holdfast_Span_Read_write_other_ne.
      * exact (IH k earlier).
      * apply sep. exact (le_n (S n)).
  - exact (IH k earlier).
Qed.
Theorem lending_filter_frame_and_freeze : forall buf k,
  ((forall i, i < trial_length buf ->
    holdfast_int_ne 4 (holdfast_nat_to_usize (holdfast_int_to_nat 4 (trial_index 0) + i)) k = true) ->
   trial_read ({client}_post_buf buf) k = trial_read buf k) /\
  (forall i d r, snd (trial_prefix buf i) = inr r ->
   trial_prefix buf (i + d) = trial_prefix buf i).
Proof.
  intros buf k. split.
  - intros sep. rewrite (proj2 (lending_filter_matches_recursive buf) k). now apply trial_prefix_frame.
  - intros i d r hit. exact (trial_prefix_frozen buf i d r hit).
Qed.
Local Definition trial_buf (a b c d n : nat) :=
  let initial := holdfast_mk_span (holdfast_int 0) (trial_index 19) (trial_index n) true true true holdfast_bs_empty in
  let write s i v := holdfast_Span_Write (holdfast_int 0) s (trial_index i) (trial_byte v) in
  write (write (write (write initial 0 a) 1 b) 2 c) 3 d.
Local Definition trial_observe a b c d n :=
  let buf := trial_buf a b c d n in
  let res := {client} buf in
  let post := {client}_post_buf buf in
  let rd i := holdfast_int_to_nat 0 (trial_read post (trial_index i)) in
  (observe_res res, (rd 0, rd 1, rd 2, rd 3)).
Example lending_filter_observations :
  trial_observe 5 0 0 0 4 = (Some (5, 1), (5, 0, 0, 0)) /\
  trial_observe 0 0 7 3 4 = (Some (7, 1), (9, 9, 7, 3)) /\
  trial_observe 0 0 0 0 4 = (None, (9, 9, 9, 9)) /\
  trial_observe 1 2 3 4 0 = (None, (1, 2, 3, 4)).
Proof. vm_compute. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "LendingFilterReturn", [
        "lending_filter_matches_recursive", "lending_filter_frame_and_freeze", "lending_filter_observations",
    ], batch=batch)


def _subslice_disjoint_writeback(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = (TOOLS / "tests" / "fixtures" / "subslice-disjoint-writeback.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        for invalid, needle, message in (
            (
                source.replace(b"requires (a + m <= b) || (b + n <= a)", b"requires a < buf.Length"),
                b"var right = Span.Slice(buf, b, n);",
                "cannot prove mutable slice 'right' is disjoint from live mutable slice 'left' of 'buf'",
            ),
            (
                source.replace(
                    b"((a + m <= b) || (b + n <= a)) || (m == 0usize || n == 0usize)",
                    b"a < buf.Length",
                ),
                b"let right = ref Span.Slice(buf, b, n);",
                "cannot prove mutable slice 'right' is disjoint from live mutable slice 'left' of 'buf'",
            ),
            (
                source.replace(b"    left[k1] = 11u8;", b"    left[k1] = 11u8;\n    Span.Fill(ref buf, a, m, 99u8);"),
                b"return DualBytes(left[k1], right[k2]);",
                "cannot prove Span view read is disjoint from an update to 'buf'",
            ),
        ):
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="overlapping mutable sub-slice reached Gallina emission") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            target_line = next(num for num, line in enumerate(invalid.splitlines(), 1) if needle in line)
            ensure(error.kind == "type" and error.line == target_line and message in error.message,
                   f"wrong rejection for overlapping mutable sub-slice: {error.line}:{error.column}: {error}")

    [dual_var] = re.findall(r"^Definition (holdfast_d\d+_DualWriteVar) :", gallina, re.MULTILINE)
    [dual_let] = re.findall(r"^Definition (holdfast_d\d+_DualWriteRefLet) :", gallina, re.MULTILINE)
    [zero_fn] = re.findall(r"^Definition (holdfast_d\d+_ZeroLenSlices) :", gallina, re.MULTILINE)
    [left_proj] = re.findall(r"^Definition (holdfast_d\d+_DualBytes_Left) :", gallina, re.MULTILINE)
    [right_proj] = re.findall(r"^Definition (holdfast_d\d+_DualBytes_Right) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_SubsliceDisjointWriteback.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition trial_buf :=
  let initial := holdfast_mk_span (holdfast_int 0) (trial_index 11) (trial_index 8) true true true holdfast_bs_empty in
  let wr s i v := holdfast_Span_Write (holdfast_int 0) s (trial_index i) (trial_byte v) in
  wr (wr (wr (wr (wr (wr (wr (wr initial 0 100) 1 101) 2 102) 3 103) 4 104) 5 105) 6 106) 7 107.
Local Definition observe_span (s : holdfast_Span (holdfast_int 0)) :=
  (holdfast_int_to_nat 0 (trial_read s (trial_index 0)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 1)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 2)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 3)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 4)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 5)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 6)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 7))).
Theorem dual_var_writeback_and_frame :
  let r1 := {dual_var} trial_buf (trial_index 1) (trial_index 2) (trial_index 4) (trial_index 3) (trial_index 1) (trial_index 2) in
  let p1 := {dual_var}_post_buf trial_buf (trial_index 1) (trial_index 2) (trial_index 4) (trial_index 3) (trial_index 1) (trial_index 2) in
  let r2 := {dual_var} trial_buf (trial_index 5) (trial_index 2) (trial_index 1) (trial_index 2) (trial_index 0) (trial_index 1) in
  let p2 := {dual_var}_post_buf trial_buf (trial_index 5) (trial_index 2) (trial_index 1) (trial_index 2) (trial_index 0) (trial_index 1) in
  (holdfast_int_to_nat 0 ({left_proj} r1), holdfast_int_to_nat 0 ({right_proj} r1)) = (33, 44) /\
  observe_span p1 = (100, 101, 33, 103, 104, 105, 44, 107) /\
  (holdfast_int_to_nat 0 ({left_proj} r2), holdfast_int_to_nat 0 ({right_proj} r2)) = (33, 44) /\
  observe_span p2 = (100, 101, 44, 103, 104, 33, 106, 107).
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem dual_ref_let_and_zero_len_writeback :
  let r_let := {dual_let} trial_buf (trial_index 1) (trial_index 2) (trial_index 5) (trial_index 2) (trial_index 0) (trial_index 1) in
  let p_let := {dual_let}_post_buf trial_buf (trial_index 1) (trial_index 2) (trial_index 5) (trial_index 2) (trial_index 0) (trial_index 1) in
  let r_zero := {zero_fn} trial_buf (trial_index 3) (trial_index 2) (trial_index 4) (trial_index 1) in
  let p_zero := {zero_fn}_post_buf trial_buf (trial_index 3) (trial_index 2) (trial_index 4) (trial_index 1) in
  holdfast_int_to_nat 0 r_let = 12 /\
  observe_span p_let = (100, 5, 102, 103, 104, 105, 7, 107) /\
  holdfast_int_to_nat 0 r_zero = 77 /\
  observe_span p_zero = (100, 101, 102, 77, 104, 105, 106, 107).
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem dual_writeback_preserves_metadata : forall buf a m b n k1 k2,
  holdfast_Span_Base _ ({dual_var}_post_buf buf a m b n k1 k2) = holdfast_Span_Base _ buf /\
  holdfast_Span_Length _ ({dual_var}_post_buf buf a m b n k1 k2) = holdfast_Span_Length _ buf /\
  holdfast_Span_Tag _ ({dual_var}_post_buf buf a m b n k1 k2) = holdfast_Span_Tag _ buf.
Proof. intros buf a m b n k1 k2. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "SubsliceDisjointWriteback", [
        "dual_var_writeback_and_frame",
        "dual_ref_let_and_zero_len_writeback",
        "dual_writeback_preserves_metadata",
    ], batch=batch)


def _field_and_multidim_borrows(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = (TOOLS / "tests" / "fixtures" / "field-and-multidim-borrows.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        sibling_valid = source.replace(
            b"    if (resetOther) {\n        rows[j] = Seq.Empty<byte>();\n        return elem;\n    } else {\n        return elem;\n    }",
            b"    if (resetOther) {\n        rows[i] = Seq.Empty<byte>();\n        return 0u8;\n    } else {\n        return elem;\n    }",
        )
        elaborate(sibling_valid, parser.parse_source(compiled, sibling_valid, surface=True))
        for invalid, needle, message in (
            (
                source.replace(b"items[i].Payload = 9u8;", b"items[i].Header = 9u8;"),
                b"return h;",
                "cannot prove indexed borrow 'h' remains valid after update to owner 'items'",
            ),
            (
                source.replace(b"let p = ref items[i].Payload;", b"let p = ref items[i].Header;"),
                b"h = 4u8;",
                "cannot prove indexed borrow 'h' is disjoint from overlapping borrow of 'items'",
            ),
            (
                source.replace(b"requires r1 != r2 || c1 != c2", b"requires r1 < grid.Count"),
                b"return x;",
                "cannot prove indexed borrow 'x' remains valid after update to owner 'grid'",
            ),
            (
                source.replace(b"rows[j] = Seq.Empty<byte>();", b"rows[i] = Seq.Empty<byte>();"),
                b"return elem;",
                "cannot prove indexed borrow 'elem' remains valid after update to owner 'rows'",
            ),
        ):
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="conflicting field/2D/unstable borrow reached Gallina emission") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            target_line = next(num for num, line in enumerate(invalid.splitlines(), 1) if needle in line)
            ensure(error.kind == "type" and error.line == target_line and message in error.message,
                   f"wrong rejection for field/2D/unstable borrow: {error.line}:{error.column}: {error}")

    [entry_ctor] = re.findall(r"^Definition (holdfast_d\d+_Entry_ctor) :", gallina, re.MULTILINE)
    [entry_hdr] = re.findall(r"^Definition (holdfast_d\d+_Entry_Header) :", gallina, re.MULTILINE)
    [entry_pay] = re.findall(r"^Definition (holdfast_d\d+_Entry_Payload) :", gallina, re.MULTILINE)
    [split_fn] = re.findall(r"^Definition (holdfast_d\d+_SplitFieldsWrite) :", gallina, re.MULTILINE)
    [dual_fld] = re.findall(r"^Definition (holdfast_d\d+_DualFieldRefBorrows) :", gallina, re.MULTILINE)
    [grid_fn] = re.findall(r"^Definition (holdfast_d\d+_GridDisjunctiveGuard) :", gallina, re.MULTILINE)
    [dual_grid] = re.findall(r"^Definition (holdfast_d\d+_DualGridRefBorrows) :", gallina, re.MULTILINE)
    [row_fn] = re.findall(r"^Definition (holdfast_d\d+_PathSensitiveRowClear) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_FieldAndMultidimBorrows.
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_seq2 (A : Type) (x y : A) :=
  holdfast_Seq_Append A (holdfast_Seq_Singleton A x) (holdfast_Seq_Singleton A y).
Local Definition default_entry := {entry_ctor} (trial_byte 0) (trial_byte 0).
Local Definition trial_items :=
  trial_seq2 _ ({entry_ctor} (trial_byte 11) (trial_byte 12)) ({entry_ctor} (trial_byte 21) (trial_byte 22)).
Local Definition trial_grid :=
  trial_seq2 _ (trial_seq2 _ (trial_byte 10) (trial_byte 20)) (trial_seq2 _ (trial_byte 30) (trial_byte 40)).
Theorem field_split_and_dual_writeback :
  let r_split := {split_fn} trial_items 0 in
  let p_split := {split_fn}_post_items trial_items 0 in
  let r_dual := {dual_fld} trial_items 1 in
  let p_dual := {dual_fld}_post_items trial_items 1 in
  let e0 := holdfast_Seq_At _ default_entry p_split 0 in
  let e1s := holdfast_Seq_At _ default_entry p_split 1 in
  let e0d := holdfast_Seq_At _ default_entry p_dual 0 in
  let e1 := holdfast_Seq_At _ default_entry p_dual 1 in
  holdfast_int_to_nat 0 r_split = 11 /\
  holdfast_int_to_nat 0 ({entry_hdr} e0) = 11 /\
  holdfast_int_to_nat 0 ({entry_pay} e0) = 9 /\
  holdfast_int_to_nat 0 ({entry_hdr} e1s) = 21 /\
  holdfast_int_to_nat 0 ({entry_pay} e1s) = 22 /\
  holdfast_int_to_nat 0 r_dual = 13 /\
  holdfast_int_to_nat 0 ({entry_hdr} e0d) = 11 /\
  holdfast_int_to_nat 0 ({entry_pay} e0d) = 12 /\
  holdfast_int_to_nat 0 ({entry_hdr} e1) = 4 /\
  holdfast_int_to_nat 0 ({entry_pay} e1) = 9.
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem grid_2d_and_row_clear_replay :
  let read_cell g r c :=
    holdfast_int_to_nat 0 (holdfast_Seq_At _ (trial_byte 0) (holdfast_Seq_At _ (holdfast_Seq_Empty _) g r) c) in
  let r_grid1 := {grid_fn} trial_grid 0 1 0 0 in
  let p_grid1 := {grid_fn}_post_grid trial_grid 0 1 0 0 in
  let r_grid2 := {dual_grid} trial_grid 0 1 1 0 in
  let p_grid2 := {dual_grid}_post_grid trial_grid 0 1 1 0 in
  let r_clear := {row_fn} trial_grid 0 1 true in
  let p_clear := {row_fn}_post_rows trial_grid 0 1 true in
  let r_keep := {row_fn} trial_grid 0 1 false in
  let p_keep := {row_fn}_post_rows trial_grid 0 1 false in
  holdfast_int_to_nat 0 r_grid1 = 20 /\
  (read_cell p_grid1 0 0, read_cell p_grid1 0 1, read_cell p_grid1 1 0, read_cell p_grid1 1 1) = (7, 20, 30, 40) /\
  holdfast_int_to_nat 0 r_grid2 = 10 /\
  (read_cell p_grid2 0 0, read_cell p_grid2 0 1, read_cell p_grid2 1 0, read_cell p_grid2 1 1) = (10, 3, 7, 40) /\
  holdfast_int_to_nat 0 r_clear = 10 /\
  holdfast_Seq_Count _ (holdfast_Seq_At _ (holdfast_Seq_Empty _) p_clear 1) = 0 /\
  read_cell p_clear 0 0 = 10 /\
  holdfast_int_to_nat 0 r_keep = 10 /\
  read_cell p_keep 1 0 = 30.
Proof. vm_compute. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "FieldAndMultidimBorrows", [
        "field_split_and_dual_writeback",
        "grid_2d_and_row_clear_replay",
    ], batch=batch)


def _loop_cursor_reborrow(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = (TOOLS / "tests" / "fixtures" / "loop-cursor-reborrow.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        for invalid, needle, message in (
            (
                source.replace(
                    b"let hit = Span.ReadOnly(Span.Slice(buf, i, 1usize));\n            return Ok(ByteView(in hit));",
                    b"let hit = Span.ReadOnly(Span.Slice(buf, i, 1usize));\n            buf[i] = 7u8;\n            return Ok(ByteView(in hit));",
                ),
                b"return Ok(ByteView(in hit));",
                "cannot prove returned slice is disjoint from an update to 'buf'",
            ),
            (
                source.replace(
                    b"let sub = Span.Slice(buf, i, 1usize);\n            return Ok(ByteView(in Span.ReadOnly(sub)));",
                    b"let sub = Span.Slice(buf, i, 1usize);\n            buf[i] = 7u8;\n            return Ok(ByteView(in Span.ReadOnly(sub)));",
                ),
                b"return Ok(ByteView(in Span.ReadOnly(sub)));",
                "cannot prove returned slice is disjoint from an update to 'buf'",
            ),
            (
                source.replace(
                    b"    let len = buf.Length;\n    foreach (let i in 0usize..len)\n        invariant buf.CanRead\n        invariant buf.CanWrite\n        invariant buf.Length == len\n    {\n        var cell = Span.Slice(buf, i, 1usize);\n        cell[0usize] = 3u8;\n    }\n    return buf[0usize];",
                    b"    let len = buf.Length;\n    let head = Span.ReadOnly(Span.Slice(buf, 0usize, 1usize));\n    foreach (let i in 0usize..len)\n        invariant buf.CanRead\n        invariant buf.CanWrite\n        invariant buf.Length == len\n    {\n        var cell = Span.Slice(buf, i, 1usize);\n        cell[0usize] = 3u8;\n    }\n    return head[0usize];",
                ),
                b"return head[0usize];",
                "cannot prove Span view read is disjoint from an update to 'buf'",
            ),
        ):
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="conflicting loop cursor borrow reached Gallina emission") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            target_line = next(num for num, line in enumerate(invalid.splitlines(), 1) if needle in line)
            ensure(error.kind == "type" and error.line == target_line and message in error.message,
                   f"wrong rejection for loop cursor borrow: {error.line}:{error.column}: {error}")

    [scan_fn] = re.findall(r"^Definition (holdfast_d\d+_ScanMarkAndReturnView) :", gallina, re.MULTILINE)
    [mut_fn] = re.findall(r"^Definition (holdfast_d\d+_ForeachCursorMutReturn) :", gallina, re.MULTILINE)
    [fill_fn] = re.findall(r"^Definition (holdfast_d\d+_ShrinkingCursorFill) :", gallina, re.MULTILINE)
    [view_ty] = re.findall(r"^Definition (holdfast_d\d+_ByteView) :", gallina, re.MULTILINE)
    [view_proj] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_LoopCursorReborrow.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Local Definition trial_buf a b c d :=
  let initial := holdfast_mk_span (holdfast_int 0) (trial_index 23) (trial_index 4) true true true holdfast_bs_empty in
  let wr s i v := holdfast_Span_Write (holdfast_int 0) s (trial_index i) (trial_byte v) in
  wr (wr (wr (wr initial 0 a) 1 b) 2 c) 3 d.
Local Definition observe_span (s : holdfast_Span (holdfast_int 0)) :=
  (holdfast_int_to_nat 0 (trial_read s (trial_index 0)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 1)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 2)),
   holdfast_int_to_nat 0 (trial_read s (trial_index 3))).
Local Definition observe_res (res : bool + {view_ty}) :=
  match res with
  | inr view => Some (holdfast_int_to_nat 0 (trial_read ({view_proj} view) (trial_index 0)))
  | inl _ => None
  end.
Theorem loop_cursor_reborrow_observations :
  let b1 := trial_buf 5 6 7 8 in
  let b2 := trial_buf 5 6 0 8 in
  observe_res ({scan_fn} b1 (trial_byte 7)) = Some 7 /\
  observe_span ({scan_fn}_post_buf b1 (trial_byte 7)) = (1, 1, 7, 8) /\
  observe_res ({scan_fn} b1 (trial_byte 99)) = None /\
  observe_span ({scan_fn}_post_buf b1 (trial_byte 99)) = (1, 1, 1, 1) /\
  observe_res ({mut_fn} b2 (trial_byte 0)) = Some 10 /\
  observe_span ({mut_fn}_post_buf b2 (trial_byte 0)) = (2, 2, 10, 8) /\
  observe_res ({mut_fn} b2 (trial_byte 99)) = None /\
  observe_span ({mut_fn}_post_buf b2 (trial_byte 99)) = (2, 2, 2, 2) /\
  holdfast_int_to_nat 0 ({fill_fn} b1) = 3 /\
  observe_span ({fill_fn}_post_buf b1) = (3, 3, 3, 3).
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem loop_cursor_preserves_metadata : forall buf target,
  holdfast_Span_Length _ ({scan_fn}_post_buf buf target) = holdfast_Span_Length _ buf /\
  holdfast_Span_Length _ ({mut_fn}_post_buf buf target) = holdfast_Span_Length _ buf /\
  holdfast_Span_Length _ ({fill_fn}_post_buf buf) = holdfast_Span_Length _ buf.
Proof. intros buf target. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "LoopCursorReborrow", [
        "loop_cursor_reborrow_observations",
        "loop_cursor_preserves_metadata",
    ], batch=batch)


def _higher_ranked_view_callback(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = (TOOLS / "tests" / "fixtures" / "higher-ranked-view-callback.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        escape_return = source + b"""
public in<'outer> Span<byte> EscapeReturn<region 'outer>(
    in<'outer> Span<byte> buf,
    Fn<region 'fresh>(in<'fresh> Span<byte>) -> in<'fresh> Span<byte> select
)
    requires buf.CanRead
{
    return select(in buf);
}
"""
        for invalid, needle, message in (
            (
                source.replace(
                    b"    let selected = makeView(in buf);",
                    b"    var saved = ByteView(in Span.ReadOnly(buf));\n"
                    b"    saved = makeView(in buf);\n"
                    b"    let selected = makeView(in buf);",
                ),
                b"saved = makeView(in buf);",
                "cannot assign value from higher-ranked callback region to outer binding 'saved'",
            ),
            (
                escape_return,
                b"return select(in buf);",
                "cannot return value borrowing higher-ranked callback region outside its invocation",
            ),
            (
                source.replace(
                    b"Fn<region 'r>(in<'r> Span<byte> s) -> in<'r> Span<byte> => s",
                    b"Fn<region 'r>(in<'r> Span<byte> s) -> in<'r> Span<byte> => buf",
                ),
                b"ApplyFreshRead(in buf, Fn<region 'r>(in<'r> Span<byte> s) -> in<'r> Span<byte> => buf, idx);",
                "cannot capture or escape outer region binding 'buf' in higher-ranked callback",
            ),
            (
                source.replace(
                    b"Fn<region 'fresh>(in<'fresh> Span<byte>) -> in<'fresh> Span<byte> select",
                    b"Fn<region 'fresh>(in<'fresh> Span<byte>) -> in<'outer> Span<byte> select",
                ),
                b"ApplyFreshRead(in buf, Fn<region 'r>(in<'r> Span<byte> s) -> in<'r> Span<byte> => s, idx);",
                "cannot escape higher-ranked region",
            ),
            (
                source.replace(
                    b"    return ApplyFreshRead(in buf, Fn<region 'r>(in<'r> Span<byte> s) -> in<'r> Span<byte> => s, idx);",
                    b"    var count = 0usize;\n"
                    b"    return ApplyFreshRead(in buf, Fn<region 'r>(in<'r> Span<byte> s) -> in<'r> Span<byte> => "
                    b"{ count = 1usize; return s; }, idx);",
                ),
                b"count = 1usize;",
                "cannot mutate outer variable 'count' inside higher-ranked callback",
            ),
        ):
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="escaping higher-ranked callback region reached Gallina emission") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            target_line = next(num for num, line in enumerate(invalid.splitlines(), 1) if needle in line)
            ensure(error.kind == "type" and error.line == target_line and message in error.message,
                   f"wrong rejection for escaping higher-ranked callback: {error.line}:{error.column}: {error}")

    [apply_fresh] = re.findall(r"^Definition (holdfast_d\d+_ApplyFreshRead) :", gallina, re.MULTILINE)
    [apply_id] = re.findall(r"^Definition (holdfast_d\d+_ApplyIdentity) :", gallina, re.MULTILINE)
    [apply_first] = re.findall(r"^Definition (holdfast_d\d+_ApplyFirstByte) :", gallina, re.MULTILINE)
    [apply_bv] = re.findall(r"^Definition (holdfast_d\d+_ApplyByteViewCallback) :", gallina, re.MULTILINE)
    [bv_ctor] = re.findall(r"^Definition (holdfast_d\d+_ByteView_ctor) :", gallina, re.MULTILINE)
    [bv_proj] = re.findall(r"^Definition (holdfast_d\d+_ByteView_Bytes) :", gallina, re.MULTILINE)
    [use_bv] = re.findall(r"^Definition (holdfast_d\d+_UseByteViewIdentity) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_HigherRankedViewCallback.
Local Definition trial_index (n : nat) := holdfast_mk_int 4 (holdfast_nat_to_bits 64 n).
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition trial_read := holdfast_Span_Read (holdfast_int 0).
Theorem higher_ranked_identity_functional : forall buf idx,
  holdfast_Span_CanRead (holdfast_int 0) buf = true ->
  holdfast_int_lt 4 idx (holdfast_Span_Length (holdfast_int 0) buf) = true ->
  {apply_fresh} buf (fun s => s) idx = trial_read buf idx /\
  {apply_id} buf idx = trial_read buf idx /\
  {use_bv} buf idx = trial_read buf idx.
Proof.
  intros buf idx Hread Hlt.
  unfold {apply_id}, {use_bv}, {apply_fresh}, {apply_bv}, {bv_proj}, {bv_ctor}, holdfast_and, trial_read.
  cbv beta.
  simpl fst.
  rewrite Hread, Hlt.
  repeat split; reflexivity.
Qed.
Local Definition trial_buf :=
  let initial := holdfast_mk_span (holdfast_int 0) (trial_index 29) (trial_index 4) true true false holdfast_bs_empty in
  let wr s i v := holdfast_Span_Write (holdfast_int 0) s (trial_index i) (trial_byte v) in
  wr (wr (wr (wr initial 0 41) 1 42) 2 43) 3 44.
Theorem higher_ranked_callback_observations :
  holdfast_int_to_nat 0 ({apply_id} trial_buf (trial_index 2)) = 43 /\
  holdfast_int_to_nat 0 ({apply_first} trial_buf) = 42 /\
  holdfast_int_to_nat 0 ({use_bv} trial_buf (trial_index 3)) = 44.
Proof. vm_compute. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "HigherRankedViewCallback", [
        "higher_ranked_identity_functional",
        "higher_ranked_callback_observations",
    ], batch=batch)


def _two_phase_receiver_replay(*, batch: rocq_cache.BatchChecker | None = None) -> None:
    source = b"""// SPDX-License-Identifier: Apache-2.0
module TwoPhaseReceiver;

public record ByteBox(byte Count, byte Accum);

public interface CounterOps<T> {
    public byte ReadCount(in T self);
    public byte MutateCount(ref T self);
    public Unit Update(ref T self, byte delta);
    public Unit UpdateFromView(ref T self, in byte delta);
}

public impl CounterOps<ByteBox> {
    public byte ReadCount(in ByteBox self) {
        return self.Count;
    }

    public byte MutateCount(ref ByteBox self) {
        self = ByteBox(self.Count.WrappingAdd(2u8), self.Accum);
        return self.Count;
    }

    public Unit Update(ref ByteBox self, byte delta) {
        self = ByteBox(self.Count.WrappingAdd(1u8), self.Accum.WrappingAdd(delta));
        return ();
    }

    public Unit UpdateFromView(ref ByteBox self, in byte delta) {
        self = ByteBox(self.Count.WrappingAdd(1u8), self.Accum.WrappingAdd(delta));
        return ();
    }
}

public interface FieldOps<T> {
    public Unit AddCount(ref T self, in byte count);
}

public impl FieldOps<byte> {
    public Unit AddCount(ref byte self, in byte count) {
        self = self.WrappingAdd(count);
        return ();
    }
}

private byte BumpOther(ref ByteBox other) {
    other = ByteBox(other.Count.WrappingAdd(10u8), other.Accum);
    return other.Count;
}

public ByteBox TwoPhaseSelfRead(ref ByteBox buf) {
    buf.Update(buf.ReadCount());
    return buf;
}

public ByteBox TwoPhaseEffectfulArg(ref ByteBox buf, ref ByteBox other) {
    buf.Update(BumpOther(ref other));
    return buf;
}

public ByteBox TwoPhaseDisjointFieldView(ref ByteBox buf) {
    buf.Accum.AddCount(in buf.Count);
    return buf;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        for old_stmt, new_stmt, column_needle, message in (
            (
                b"    buf.Update(buf.ReadCount());",
                b"    buf.Update(BumpOther(ref buf));",
                b"ref buf",
                "conflicting-receiver-reservation",
            ),
            (
                b"    buf.Update(buf.ReadCount());",
                b"    buf.Update(buf.MutateCount());",
                b"buf.MutateCount()",
                "conflicting-receiver-reservation",
            ),
            (
                b"    buf.Update(buf.ReadCount());",
                b"    buf.UpdateFromView(in buf.Count);",
                b"buf.UpdateFromView",
                "competing-loans",
            ),
            (
                b"    buf.Accum.AddCount(in buf.Count);",
                b"    buf.Accum.AddCount(in buf.Accum);",
                b"buf.Accum.AddCount",
                "competing-loans",
            ),
        ):
            invalid = source.replace(old_stmt, new_stmt)
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="conflicting two-phase receiver access reached Gallina emission") as failure:
                elaborate(invalid, parsed)
            error = failure.exception
            target_line = next(num for num, line in enumerate(invalid.splitlines(), 1) if new_stmt in line)
            target_col = invalid.splitlines()[target_line - 1].index(column_needle) + 1
            ensure(
                error.kind == "type" and (error.line, error.column) == (target_line, target_col) and message in error.message,
                f"wrong rejection for two-phase receiver conflict: {error.line}:{error.column}: {error}",
            )

    [box_ctor] = re.findall(r"^Definition (holdfast_d\d+_ByteBox_ctor) :", gallina, re.MULTILINE)
    [box_cnt] = re.findall(r"^Definition (holdfast_d\d+_ByteBox_Count) :", gallina, re.MULTILINE)
    [box_acc] = re.findall(r"^Definition (holdfast_d\d+_ByteBox_Accum) :", gallina, re.MULTILINE)
    [self_read] = re.findall(r"^Definition (holdfast_d\d+_TwoPhaseSelfRead) :", gallina, re.MULTILINE)
    [eff_arg] = re.findall(r"^Definition (holdfast_d\d+_TwoPhaseEffectfulArg) :", gallina, re.MULTILINE)
    [field_view] = re.findall(r"^Definition (holdfast_d\d+_TwoPhaseDisjointFieldView) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_TwoPhaseReceiver.
Local Definition trial_byte (n : nat) := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition wrap_add := holdfast_int_wrap_add 0.
Theorem two_phase_eval_order_and_post_state : forall buf other,
  let r_self := {self_read} buf in
  let r_eff := {eff_arg} buf other in
  let p_other := {eff_arg}_post_other buf other in
  let r_fld := {field_view} buf in
  r_self = {box_ctor} (wrap_add ({box_cnt} buf) (trial_byte 1)) (wrap_add ({box_acc} buf) ({box_cnt} buf)) /\
  {self_read}_post_buf buf = r_self /\
  p_other = {box_ctor} (wrap_add ({box_cnt} other) (trial_byte 10)) ({box_acc} other) /\
  r_eff = {box_ctor} (wrap_add ({box_cnt} buf) (trial_byte 1))
                     (wrap_add ({box_acc} buf) (wrap_add ({box_cnt} other) (trial_byte 10))) /\
  {eff_arg}_post_buf buf other = r_eff /\
  r_fld = {box_ctor} ({box_cnt} buf) (wrap_add ({box_acc} buf) ({box_cnt} buf)) /\
  {field_view}_post_buf buf = r_fld.
Proof.
  intros buf other.
  repeat split; reflexivity.
Qed.
Theorem two_phase_concrete_observations :
  let b1 := {box_ctor} (trial_byte 5) (trial_byte 100) in
  let o1 := {box_ctor} (trial_byte 7) (trial_byte 50) in
  ({box_cnt} ({self_read} b1), {box_acc} ({self_read} b1)) = (trial_byte 6, trial_byte 105) /\
  ({box_cnt} ({eff_arg} b1 o1), {box_acc} ({eff_arg} b1 o1)) = (trial_byte 6, trial_byte 117) /\
  ({box_cnt} ({eff_arg}_post_other b1 o1), {box_acc} ({eff_arg}_post_other b1 o1)) = (trial_byte 17, trial_byte 50) /\
  ({box_cnt} ({field_view} b1), {box_acc} ({field_view} b1)) = (trial_byte 5, trial_byte 105).
Proof. vm_compute. repeat split; reflexivity. Qed.
"""
    _replay_view_proof(gallina, proof, "TwoPhaseReceiver", [
        "two_phase_eval_order_and_post_state",
        "two_phase_concrete_observations",
    ], batch=batch)


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("conditional view return and sibling owner writeback",
             partial(_conditional_view_return, batch=batch), lane="toolchain"),
        Case("branch-specific last use of a shared Span view",
             partial(_branch_view_last_use, batch=batch), lane="toolchain"),
        Case("returned view and branch-specific owner writeback at a join",
             partial(_joined_view_return, batch=batch), lane="toolchain"),
        Case("conditional view origin and correlated owner writeback",
             partial(_correlated_view_return, batch=batch), lane="toolchain"),
        Case("returned view and disjoint symbolic loop writeback",
             partial(_loop_view_return, batch=batch), lane="toolchain"),
        Case("scoped lending and symbolic Span element writeback",
             partial(_lending_span_iteration, batch=batch), lane="toolchain"),
        Case("scoped lending and early break exits on Span",
             partial(_lending_span_break, batch=batch), lane="toolchain"),
        Case("lending filtering range loop with early borrowed view return",
             partial(_lending_filter_return, batch=batch), lane="toolchain"),
        Case("simultaneous exclusive disjoint sub-slice writeback",
             partial(_subslice_disjoint_writeback, batch=batch), lane="toolchain"),
        Case("same-index disjoint record fields, 2D borrows, and path-sensitive clear",
             partial(_field_and_multidim_borrows, batch=batch), lane="toolchain"),
        Case("loop-carried cursor reborrowing and conditional returned view",
             partial(_loop_cursor_reborrow, batch=batch), lane="toolchain"),
        Case("higher-ranked region-polymorphic view callbacks",
             partial(_higher_ranked_view_callback, batch=batch), lane="toolchain"),
        Case("two-phase receiver elaboration, evaluation order, and Rocq replay",
             partial(_two_phase_receiver_replay, batch=batch), lane="toolchain"),
        Case("kernel check all returned-view proofs with rocqchk", batch.verify_all, lane="toolchain"),
    ]
