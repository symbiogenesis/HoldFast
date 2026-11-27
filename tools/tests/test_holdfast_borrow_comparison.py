# SPDX-License-Identifier: Apache-2.0
"""Check the HoldFast endpoint of the nested-row borrowing comparison."""

import re
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import ante_borrow_compare, parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError
from toolchain.cli import holdfast_borrow_compare
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


def _check_invalid_direct(compiled: parser.Build, source: bytes, snippet: str, msg: str) -> None:
    parsed = parser.parse_source(compiled, source, surface=True)
    with raises(HoldFastError, msg=msg) as failure:
        elaborate(source, parsed)
    error = failure.exception
    ensure(error.kind == "type" and snippet in error.message, f"unexpected failure for {msg}: {error}")


def _direct_indexed_borrows() -> None:
    source = (TOOLS / "tests" / "fixtures" / "direct-indexed-borrows.hf").read_bytes()
    with parser.cached_build(TOOLS.parent) as compiled:
        gallina = elaborate(source, parser.parse_source(compiled, source, surface=True)).gallina

        # 1. Mutating same index rows[i] then reading selected = in rows[i]
        _check_invalid_direct(
            compiled,
            source.replace(b"rows[j] = Seq.Empty<byte>();", b"rows[i] = Seq.Empty<byte>();"),
            "cannot prove indexed borrow 'selected' remains valid after update to owner 'rows'",
            "mutating same index rows[i] should invalidate later read of selected",
        )
        # 2. Mutating rows[j] without i != j guard then reading selected
        _check_invalid_direct(
            compiled,
            source.replace(b"if (i < 2 && j < 2 && i != j) {", b"if (i < 2 && j < 2) {"),
            "cannot prove indexed borrow 'selected' remains valid after update to owner 'rows'",
            "unguarded rows[j] write should invalidate later read of selected",
        )
        # 3. Simultaneous exclusive local borrows a, b without i != j
        _check_invalid_direct(
            compiled,
            source.replace(
                b"public byte UpdatePairDirect(ref Vec<byte, 3> values, Nat i, Nat j) {\n    if (i < 3 && j < 3 && i != j) {",
                b"public byte UpdatePairDirect(ref Vec<byte, 3> values, Nat i, Nat j) {\n    if (i < 3 && j < 3) {",
            ),
            "cannot prove indexed borrow 'a' is disjoint from overlapping borrow of 'values'",
            "aliasing exclusive local borrows a and b without i != j should fail",
        )
        # 4. Direct assignment through shared 'in' borrow
        _check_invalid_direct(
            compiled,
            source.replace(
                b"        rows[j] = Seq.Empty<byte>();",
                b"        selected = Seq.Empty<byte>();",
            ),
            "write-through-shared",
            "assigning through shared 'in' borrow should be refused",
        )
        # 5. Passing shared 'in' borrow as 'ref' argument
        _check_invalid_direct(
            compiled,
            source.replace(
                b"        rows[j] = Seq.Empty<byte>();",
                b"        TouchRow(ref selected);",
            ),
            "write-through-shared",
            "passing shared 'in' borrow as 'ref' argument should be refused",
        )
        # 6. Exclusive 'ref' indexed borrow of read-only 'in' binding
        _check_invalid_direct(
            compiled,
            source.replace(
                b"public byte ReadSeqDirect(in Seq<byte> xs, Nat i, Nat j) {\n    if (i < xs.Count && j < xs.Count) {\n        let a = in xs[i];",
                b"public byte ReadSeqDirect(in Seq<byte> xs, Nat i, Nat j) {\n    if (i < xs.Count && j < xs.Count) {\n        let a = ref xs[i];",
            ),
            "cannot take exclusive 'ref' borrow of read-only 'in' parameter 'xs'",
            "taking exclusive 'ref' element borrow from read-only 'in' binding should fail",
        )
        # 7. Out-of-bounds indexed local borrow
        _check_invalid_direct(
            compiled,
            source.replace(b"if (i < xs.Count && j < xs.Count) {", b"if (j < xs.Count) {"),
            "cannot prove Seq index is within Seq.Count bounds",
            "out-of-bounds indexed local borrow should fail",
        )
        # 8. Joined branch where else writes values[k] without i != k and a is read after join
        _check_invalid_direct(
            compiled,
            source.replace(b"if (i < 3 && j < 3 && k < 3 && i != k) {", b"if (i < 3 && j < 3 && k < 3) {"),
            "cannot prove indexed borrow 'a' remains valid after update to owner 'values'",
            "unguarded joined branch write should invalidate post-join read of a",
        )

    [read_direct] = re.findall(r"^Definition (holdfast_d\d+_ReadAfterClearDirect) :", gallina, re.MULTILINE)
    [branch_disjoint] = re.findall(r"^Definition (holdfast_d\d+_BranchLastUseOrDisjoint) :", gallina, re.MULTILINE)
    [joined_clear] = re.findall(r"^Definition (holdfast_d\d+_JoinedDisjointClear) :", gallina, re.MULTILINE)
    [update_pair] = re.findall(r"^Definition (holdfast_d\d+_UpdatePairDirect) :", gallina, re.MULTILINE)
    [update_span] = re.findall(r"^Definition (holdfast_d\d+_UpdateSpanPair) :", gallina, re.MULTILINE)
    [read_slots] = re.findall(r"^Definition (holdfast_d\d+_ReadSlotsDirect) :", gallina, re.MULTILINE)
    [read_seq] = re.findall(r"^Definition (holdfast_d\d+_ReadSeqDirect) :", gallina, re.MULTILINE)
    proof = rf"""
Import HoldFast_DirectIndexedBorrows.
Local Definition byte := holdfast_int 0.
Local Definition bconst (n : nat) : byte := holdfast_mk_int 0 (holdfast_nat_to_bits 8 n).
Local Definition row := holdfast_Seq byte.
Local Definition empty := holdfast_Seq_Empty byte.
Local Definition first (xs : row) : holdfast_Result byte bool :=
  match xs with holdfast_Seq_Empty _ => inl false | holdfast_Seq_Cons _ x _ => inr x end.
Local Definition rows (left right frame : row) : holdfast_Vec row 3 :=
  (left, (right, (frame, tt))).
Local Definition vec3 (x y z : byte) : holdfast_Vec byte 3 := (x, (y, (z, tt))).

Theorem direct_clear_preserves_peer_and_frame : forall left right frame i j,
  let input := rows left right frame in
  let observed := {read_direct} input i j in
  let restored := {read_direct}_post_rows input i j in
  (match i, j with
   | 0, 1 => (first left, rows left empty frame)
   | 1, 0 => (first right, rows empty right frame)
   | _, _ => (inl false, input)
   end) = (observed, restored).
Proof.
  intros left right frame [|[|i]] [|[|j]]; destruct left, right; reflexivity.
Qed.

Theorem branch_last_use_or_disjoint_sound : forall x y z,
  let input := vec3 x y z in
  let obs_true := {branch_disjoint} input 0 1 true in
  let post_true := {branch_disjoint}_post_values input 0 1 true in
  let obs_false := {branch_disjoint} input 0 1 false in
  let post_false := {branch_disjoint}_post_values input 0 1 false in
  obs_true = holdfast_int_wrap_add 0 x (bconst 7) /\
  post_true = vec3 (bconst 7) y z /\
  obs_false = bconst 5 /\
  post_false = vec3 (bconst 5) y z.
Proof.
  intros x y z; repeat split; reflexivity.
Qed.

Theorem joined_disjoint_clear_sound : forall x y z,
  let input := vec3 x y z in
  ({joined_clear} input 0 1 2 = x /\
   {joined_clear}_post_values input 0 1 2 = vec3 x (bconst 4) z /\
   {joined_clear} input 0 0 2 = x /\
   {joined_clear}_post_values input 0 0 2 = vec3 x y (bconst 9)).
Proof.
  intros x y z; repeat split; reflexivity.
Qed.

Theorem update_pair_direct_sound : forall x y z,
  let input := vec3 x y z in
  {update_pair} input 0 2 = holdfast_int_add 0 (bconst 11) (bconst 22) /\
  {update_pair}_post_values input 0 2 = vec3 (bconst 11) y (bconst 22).
Proof.
  intros x y z; split; reflexivity.
Qed.

Theorem read_seq_direct_sound : forall a b c : byte,
  let s := holdfast_Seq_Cons byte a (holdfast_Seq_Cons byte b (holdfast_Seq_Cons byte c empty)) in
  {read_seq} s 0 2 = holdfast_int_wrap_add 0 a c.
Proof.
  intros a b c; reflexivity.
Qed.

Definition direct_span_ref : holdfast_Span byte -> _ -> _ -> byte := {update_span}.
Definition direct_slots_ref : holdfast_Slots byte 4 -> _ -> _ -> byte := {read_slots}.
"""
    entries = solver_ledger.ledger(gallina)
    ensure(not entries, "direct-indexed borrowing depended on solver assumptions")
    exports = [
        *solver_ledger.math_exports(gallina),
        "direct_clear_preserves_peer_and_frame",
        "branch_last_use_or_disjoint_sound",
        "joined_disjoint_clear_sound",
        "update_pair_direct_sound",
        "read_seq_direct_sound",
        "direct_span_ref",
        "direct_slots_ref",
    ]
    audit = "".join(f"Print Assumptions {name}.\n" for name in exports)
    with TemporaryDirectory(prefix="holdfast-direct-borrows-") as tmp:
        unit = Path(tmp) / "DirectBorrows.v"
        unit.write_text(gallina + proof + audit, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", unit.name], cwd=tmp, capture_output=True,
                                encoding="utf-8", timeout=180, check=False)
        ensure(replay.returncode == 0, replay.stderr)
        solver_ledger.audit(replay.stdout, len(exports), "HoldFast_DirectIndexedBorrows", entries)


def _pinned_rustc_available() -> list[str] | None:
    compiler = ["rustc", f"+{holdfast_borrow_compare.NIGHTLY}"]
    try:
        version = subprocess.run(
            [*compiler, "-vV"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            timeout=holdfast_borrow_compare.TIMEOUT,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if version.returncode != 0 or f"commit-hash: {holdfast_borrow_compare.REVISION}" not in version.stdout.splitlines():
        return None
    return compiler


def _comparison_fixture_contracts() -> None:
    fixtures = TOOLS / "tests" / "fixtures"
    expected_fixture_cfgs: dict[str, set[str | None]] = {
        "subslice_disjoint_writeback.rs": {"direct", "coincident", None},
        "multidim_index_borrows.rs": {"direct", "coincident", None},
        "exclusive_conditional_return.rs": {None, "live_conflict"},
        "shared_mut_stable_element.rs": {"direct", None},
        "tag_preserving_union_mut.rs": {"direct", "coincident", None},
        "capacity_preserving_push.rs": {"direct", "coincident", None},
        "multi_region_disambiguation.rs": {"unified_region", None},
        "partial_field_move.rs": {"use_moved", None},
    }
    for mode in holdfast_borrow_compare.MODES:
        mode_trials = holdfast_borrow_compare.trials(mode)
        ensure(bool(mode_trials), f"expected non-empty Rust trials for mode {mode}")
        for fixture_name, expected_cfgs in expected_fixture_cfgs.items():
            cfgs = {trial.configuration for trial in mode_trials if trial.fixture == fixture_name}
            ensure(cfgs == expected_cfgs,
                   f"mode {mode} missing expected configurations for {fixture_name}: {cfgs}")
        for trial in mode_trials:
            fixture_path = fixtures / trial.fixture
            ensure(fixture_path.is_file(), f"missing Rust comparison fixture: {fixture_path}")
            source = fixture_path.read_text(encoding="utf-8")
            ensure(source.startswith("// SPDX-License-Identifier: Apache-2.0\n"),
                   f"missing SPDX header in {trial.fixture}")
            for code, marker in trial.expected:
                ensure(bool(re.fullmatch(r"E\d{4}", code)), f"unexpected Rust diagnostic code {code!r}")
                try:
                    holdfast_borrow_compare._marker_line(source, marker)
                except ValueError as exc:
                    raise AssertionError(f"{trial.fixture} ({mode}, {trial.configuration}): {exc}") from exc
            if not trial.expected:
                ensure("fn expected_observations()" in source,
                       f"accepted Rust fixture {trial.fixture} must define expected_observations()")

    mode_trials_by_mode = {
        mode: {(trial.fixture, trial.configuration): trial for trial in holdfast_borrow_compare.trials(mode)}
        for mode in holdfast_borrow_compare.MODES
    }
    for entry in holdfast_borrow_compare.MATRIX_CASES:
        ensure(entry.ante_expected in holdfast_borrow_compare.VERDICTS
               and entry.holdfast_expected in holdfast_borrow_compare.VERDICTS,
               f"invalid matrix verdicts for {entry.case}")
        for mode in holdfast_borrow_compare.MODES:
            ensure((entry.fixture, entry.cfg) in mode_trials_by_mode[mode],
                   f"matrix case {entry.case} missing in Rust mode {mode}")
    synthetic_results: list[dict[str, object]] = [
        {
            "mode": mode,
            "fixture": trial.fixture,
            "cfg": trial.configuration,
            "flags": [],
            "decision": "rejected" if trial.expected else "accepted",
        }
        for mode in holdfast_borrow_compare.MODES
        for trial in holdfast_borrow_compare.trials(mode)
        if not trial.next_solver
    ]
    matrix = holdfast_borrow_compare._comparison_matrix(synthetic_results)
    matrix_cases = matrix["cases"]
    if not isinstance(matrix_cases, list) or len(matrix_cases) != len(holdfast_borrow_compare.MATRIX_CASES):
        raise AssertionError("comparison_matrix did not materialize all MATRIX_CASES")
    by_case = {row["case"]: row for row in matrix_cases if isinstance(row, dict)}
    ensure(by_case["exclusive_conditional_return"]["rust_nll"] == "rejected"
           and by_case["exclusive_conditional_return"]["rust_polonius_legacy"] == "accepted"
           and by_case["exclusive_conditional_return"]["rust_polonius_alpha"] == "accepted"
           and by_case["exclusive_conditional_return"]["ante_expected"] == "unsupported",
           f"unexpected exclusive_conditional_return matrix row: {by_case['exclusive_conditional_return']}")
    ensure(by_case["shared_mut_stable_element"]["rust_nll"] == "rejected"
           and by_case["shared_mut_stable_element"]["rust_polonius_legacy"] == "rejected"
           and by_case["shared_mut_stable_element"]["rust_polonius_alpha"] == "rejected"
           and by_case["shared_mut_stable_element"]["ante_expected"] == "accepted"
           and by_case["shared_mut_stable_element"]["holdfast_expected"] == "rejected",
           f"unexpected shared_mut_stable_element matrix row: {by_case['shared_mut_stable_element']}")

    ensure(len(ante_borrow_compare.TRIALS) >= 4
           and ante_borrow_compare.TRIALS[0].direct == ante_borrow_compare.DIRECT
           and ante_borrow_compare.TRIALS[1].direct == ante_borrow_compare.MULTIDIM_DIRECT,
           "ante_borrow_compare.TRIALS must retain nested_indexed_invalidation.an and multidim_index_borrows.an first")
    wired_directs = {trial.direct for trial in ante_borrow_compare.TRIALS}
    ensure({ante_borrow_compare.BRANCH_VIEW_DIRECT, ante_borrow_compare.LOOP_VIEW_DIRECT}.issubset(wired_directs),
           f"ante_borrow_compare.TRIALS missing branch/loop view trials: {wired_directs}")
    for trial in ante_borrow_compare.TRIALS:
        for required in (trial.direct, trial.rewrite, *((trial.companion_hf,) if trial.companion_hf is not None else ())):
            ensure((fixtures / required).is_file(), f"missing Ante comparison fixture: {required}")
        direct_source = (fixtures / trial.direct).read_text(encoding="utf-8")
        ensure(direct_source.startswith("// SPDX-License-Identifier: Apache-2.0\n"),
               f"missing SPDX header in {trial.direct}")
        selected_lines = [line for line in direct_source.splitlines() if line == trial.invalidation_line]
        ensure(len(selected_lines) == 1,
               f"{trial.direct} must have exactly one {trial.invalidation_line!r} line")
        ensure(trial.invalidation_target in trial.invalidation_line,
               f"{trial.direct}: invalidation_target {trial.invalidation_target!r} missing from invalidation_line")
        ensure(direct_source.count(trial.direct_mutation) == 1,
               f"{trial.direct} must contain {trial.direct_mutation!r} exactly once")
        coincident_source = direct_source.replace(trial.direct_mutation, trial.coincident_mutation)
        ensure(trial.invalidation_line in coincident_source.splitlines(),
               f"{trial.coincident} synthesis must preserve {trial.invalidation_line!r}")
        rewrite_source = (fixtures / trial.rewrite).read_text(encoding="utf-8")
        ensure(rewrite_source.startswith("// SPDX-License-Identifier: Apache-2.0\n"),
               f"missing SPDX header in {trial.rewrite}")
        ensure(f'println "{trial.rewrite_output}"' in rewrite_source,
               f"{trial.rewrite} must print {trial.rewrite_output!r}")

    for modeled_an, snippet in (
        ("shared_mut_stable_element.an", "b.first := 9u8"),
        ("tag_preserving_union_mut.an", "overwrite_payload slot byte"),
        ("capacity_preserving_push.an", "Vec.push buf item"),
    ):
        modeled_source = (fixtures / modeled_an).read_text(encoding="utf-8")
        ensure(modeled_source.startswith("// SPDX-License-Identifier: Apache-2.0\n"),
               f"missing SPDX header in {modeled_an}")
        ensure(snippet in modeled_source, f"{modeled_an} missing expected snippet {snippet!r}")

    compiler = _pinned_rustc_available()
    if compiler is not None:
        with TemporaryDirectory(prefix="holdfast-new-rust-trials-") as tmp:
            work = Path(tmp)
            for name in expected_fixture_cfgs:
                (work / name).write_bytes((fixtures / name).read_bytes())
            observed_results = [
                holdfast_borrow_compare._run_trial(compiler, mode, trial, work, measure=False)
                for mode in holdfast_borrow_compare.MODES
                for trial in holdfast_borrow_compare.trials(mode)
                if trial.fixture in expected_fixture_cfgs
            ]
            p3_verdicts = {
                entry["mode"]: entry["decision"]
                for entry in observed_results
                if entry["fixture"] == "exclusive_conditional_return.rs" and entry["cfg"] is None
            }
            ensure(p3_verdicts == {
                "default": "accepted",
                "off": "rejected",
                "legacy": "accepted",
                "next": "accepted",
            }, f"unexpected Problem Case #3 verdicts: {p3_verdicts}")
            for shared_mode in holdfast_borrow_compare.MODES:
                shared_verdict = next(
                    entry["decision"]
                    for entry in observed_results
                    if entry["fixture"] == "shared_mut_stable_element.rs"
                    and entry["cfg"] == "direct"
                    and entry["mode"] == shared_mode
                )
                ensure(shared_verdict == "rejected",
                       f"shared_mut_stable_element direct must be rejected in mode {shared_mode}")


def cases() -> list[Case]:
    return [
        Case("comparison fixture contracts and markers", _comparison_fixture_contracts, lane="any"),
        Case("guarded nested-row invalidation with peer and frame replay", _nested_indexed_invalidation,
             lane="toolchain"),
        Case("direct local indexed borrows with path-sensitive separation", _direct_indexed_borrows,
             lane="toolchain"),
    ]
