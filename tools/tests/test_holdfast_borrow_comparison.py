# SPDX-License-Identifier: Apache-2.0
"""Check the HoldFast endpoint of the nested-row borrowing comparison."""

import re
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.elaborate import elaborate


def _nested_indexed_invalidation() -> None:
    source = (TOOLS / "tests" / "fixtures" / "nested-indexed-invalidation.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina
        for invalid in (
            source.replace(b"ref rows[j]", b"ref rows[i]"),
            source.replace(b" && i != j", b""),
        ):
            parsed = parser.parse_source(compiled, invalid, surface=True)
            with raises(HoldFastError, msg="a clear may invalidate a live shared row loan") as failure:
                elaborate(invalid, parsed)
            [(line, text)] = [(n, row) for n, row in enumerate(invalid.splitlines(), 1) if b"ClearPeer(in rows" in row]
            error = failure.exception
            ensure(error.kind == "type" and (error.line, error.column) == (line, text.index(b"ref rows") + 1)
                   and "cannot prove indexed loan of 'rows' is disjoint from argument 1" in error.message,
                   f"wrong refusal for an overlapping clear: {error}")

    [client] = re.findall(r"^Definition (holdfast_d\d+_ReadAfterClear) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_NestedIndexedInvalidation.
Local Definition byte := holdfast_int 0.
Local Definition row := holdfast_Seq byte.
Local Definition empty := holdfast_Seq_Empty byte.
Local Definition first (xs : row) : holdfast_Result byte bool :=
  match xs with holdfast_Seq_Empty _ => inl false | holdfast_Seq_Cons _ x _ => inr x end.
Local Definition rows (left right frame : row) : holdfast_Vec row 3 :=
  (left, (right, (frame, tt))).

Theorem nested_clear_preserves_peer_and_frame : forall left right frame i j,
  let input := rows left right frame in
  let observed := {client} input i j in
  let restored := {client}_post_rows input i j in
  (match i, j with
   | 0, 1 => (first left, rows left empty frame)
   | 1, 0 => (first right, rows empty right frame)
   | _, _ => (inl false, input)
   end) = (observed, restored).
Proof.
  intros left right frame [|[|i]] [|[|j]]; destruct left, right; reflexivity.
Qed.
"""
    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "nested-row borrowing depended on solver assumptions")
    exports = [*solver_ledger.math_exports(gallina), "nested_clear_preserves_peer_and_frame"]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory(prefix="holdfast-nested-rows-") as tmp:
        unit = Path(tmp) / "NestedRows.v"
        unit.write_text(gallina + proof + audit, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", unit.name], cwd=tmp, capture_output=True,
                                encoding="utf-8", timeout=180, check=False)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(exports), "HoldFast_NestedIndexedInvalidation", entries)


def cases() -> list[Case]:
    return [Case("guarded nested-row invalidation with peer and frame replay", _nested_indexed_invalidation,
                 lane="toolchain")]
