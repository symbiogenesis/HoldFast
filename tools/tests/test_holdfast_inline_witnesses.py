# SPDX-License-Identifier: Apache-2.0
"""Kernel replay of executable assertions whose witnesses erase from the result."""

import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure, raises
from toolchain import elaborate, parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError


def _unused_witness() -> None:
    source = b"""module InlineWitness;
public Nat Observe(Nat n) requires n <= 4 {
    proof { assert (n <= 5) == true; }
    return n;
}
"""
    with parser.cached_build(TOOLS.parent) as compiled:
        def check(program: bytes) -> str:
            return elaborate.elaborate(program, parser.parse_source(compiled, program, surface=True)).gallina

        gallina = check(source)
        for comparison, diagnostic in ((b"n <= 3", "assertion could not be established"),
                                       (b"n < 7", "inline assertion needs a proof")):
            with raises(HoldFastError) as failure:
                check(source.replace(b"n <= 5", comparison))
            ensure(failure.exception.line == 3 and diagnostic in str(failure.exception),
                   f"wrong refusal for inline assertion: {failure.exception}")

    start = source.index(b"assert")
    end = source.index(b";", start) + 1
    [name] = [item for item in solver_ledger.math_exports(gallina) if item.startswith(f"holdfast_assert_{start}_{end}_")]
    module = elaborate.gallina_module_name("InlineWitness")
    consumer = (f"\nExample bound : forall n, Nat.leb n 4 = true -> Nat.leb n 5 = true := {module}.{name}.\n"
                "Print Assumptions bound.\n")
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        target = directory / "Witness.v"
        target.write_text(gallina + consumer, encoding="utf-8")
        launch = ["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--"]
        compile_unit = [*launch, "rocq", "c", "-q", target.name]
        replay = subprocess.run(compile_unit, cwd=directory, capture_output=True, check=True, timeout=180)
        solver_ledger.audit(replay.stdout.decode(), 1, module, ())
        subprocess.run([*launch, "rocqchk", "-silent", "Witness"], cwd=directory, check=True, timeout=180)
        target.write_text(gallina + consumer.replace("n 5 = true", "n 3 = true"), encoding="utf-8")
        rejected = subprocess.run(compile_unit, cwd=directory, capture_output=True, check=False, timeout=180)
        ensure(rejected.returncode != 0 and b"expected to have type" in rejected.stderr,
               "the checked witness satisfied a stronger independent conclusion")


def cases() -> list[Case]:
    return [Case("erased assertion exports its exact conditional proof", _unused_witness, lane="toolchain")]
