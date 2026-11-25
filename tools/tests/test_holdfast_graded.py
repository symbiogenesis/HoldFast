# SPDX-License-Identifier: Apache-2.0
"""Replay the pure graded kernel trial and audit its principal proofs."""

import shutil
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case
from toolchain import proofenv, solver_ledger

_AUDITED = (
    "check_sound",
    "substitute_telescope_sound",
    "separate_computation_and_type_use",
    "specialize_dependent_function",
    "scale_computation_through_application",
    "reject_wrong_exact_allowance",
    "reject_unbound_type_index",
    "reject_capture_of_nested_type_binder",
    "rewrite_later_telescope_rows",
    "reject_stale_type_use_certificate",
    "reject_stale_substitution_row",
)


def _replay() -> None:
    source = TOOLS / "rocq" / "graded_pure.v"
    launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
    compile_unit = [*launch, "rocq", "c", "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-") as temporary:
        directory = Path(temporary)
        shutil.copyfile(source, directory / source.name)
        subprocess.run([*compile_unit, source.name], cwd=directory, check=True, timeout=180)
        audit = directory / "GradeAudit.v"
        audit.write_text("Require Import graded_pure.\n" + "".join(
            f"Print Assumptions GradedPure.{name}.\n" for name in _AUDITED), encoding="utf-8")
        report = subprocess.run([*compile_unit, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=180)
        solver_ledger.audit(report.stdout, len(_AUDITED), "GradedPure", ())
        subprocess.run([*launch, "rocqchk", "-silent", source.stem], cwd=directory,
                       check=True, timeout=180)


def cases() -> list[Case]:
    return [Case("pure dependent usage and telescope substitution replay", _replay, lane="toolchain")]
