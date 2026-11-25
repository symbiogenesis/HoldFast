# SPDX-License-Identifier: Apache-2.0
"""Replay exact-natural type-use irrelevance and the audio routing comparison."""

import shutil
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case
from toolchain import proofenv, solver_ledger


def _type_irrelevance() -> None:
    audited = ("zero_type_use", "zero_use_preserves_row", "checked_zero_type_use")
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-type-use-") as temporary:
        directory = Path(temporary)
        for name in ("graded_pure.v", "graded_type_irrelevance.v"):
            shutil.copyfile(TOOLS / "rocq" / name, directory / name)
            subprocess.run([*compiler, name], cwd=directory, check=True, timeout=30)
        audit = directory / "TypeUseAudit.v"
        audit.write_text("Require Import graded_type_irrelevance.\n" + "".join(
            f"Print Assumptions GradedTypeIrrelevance.{name}.\n" for name in audited), encoding="utf-8")
        result = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=30)
        solver_ledger.audit(result.stdout, len(audited), "GradedTypeIrrelevance", ())
        subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", "rocqchk",
                        "-silent", "graded_type_irrelevance"], cwd=directory, check=True, timeout=180)


def cases() -> list[Case]:
    return [Case("exact-natural zero type-use substitution law", _type_irrelevance, lane="toolchain")]
