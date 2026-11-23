# SPDX-License-Identifier: Apache-2.0
"""Source decisions, erased calls, generated sites and atomic LLVM reports."""

import io
import json
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch

import toolchain
from tests.harness import Case, ensure, raises
from toolchain import remarks
from toolchain.cli import vela
from toolchain.hashing import sha256_bytes

_PRODUCER = "1" * 64
_SOURCE = b"""module Decisions;
public Nat Pick(const Nat factor, Nat value) => factor * value;
public Nat Carry(const Nat n, Nat x) => Pick(n, x);
public Nat Run(Nat x) => Carry(7, x);
"""


def _decisions() -> None:
    exported = remarks.compile_remarks(_SOURCE, "decisions.vela", _PRODUCER)
    ensure(exported.error is None and exported.gallina == toolchain.translate(_SOURCE).gallina,
           "recording changed Gallina or the compiler verdict")
    ensure(exported.gallina is not None, "accepted source has no Gallina")
    body = exported.gallina or ""
    carry, run = body.split("Definition f_Carry", 1)[1].split("Definition f_Run")
    ensure("(f_Pick " in carry and "f_Carry" not in run and "f_Pick" not in run and "(7 :" in run,
           "the symbolically retained or eliminated calls disagree with the output")
    header, missed, generated, outer = exported.yaml.decode().split("--- !")
    info = json.loads(header.removeprefix("# Vela remarks "))
    ensure(info["decision_count"] == 3 and info["source_sha256"] == sha256_bytes(_SOURCE)
           and info["gallina_sha256"] == sha256_bytes(body.encode("ascii")) and info["outcome"] == "emitted",
           "manifest did not bind the complete independent output")
    ensure(missed.startswith("Missed\n") and "Function: f_Carry" in missed and "GeneratedFrom:" not in missed,
           "generic declaration did not retain the symbolic call")
    ensure(generated.startswith("Passed\n") and "Function: f_Run" in generated
           and "Callee: f_Pick" in generated and "GeneratedFrom: f_Carry" in generated
           and "Line: 3, Column: 41" in generated and "Line: 4, Column: 26" in generated,
           "specialized nested call lost its authored and generated origins")
    ensure(outer.startswith("Passed\n") and "Callee: f_Carry" in outer and "GeneratedFrom:" not in outer,
           "outer applied site differs from the actual caller")
    ensure(remarks.compile_remarks(_SOURCE, "decisions.vela", _PRODUCER).yaml == exported.yaml,
           "unchanged compilation was not byte reproducible")


def _refusals() -> None:
    wrong = _SOURCE + b"public Nat Wrong(Nat runtime) => Pick(runtime, 2);\n"
    exported = remarks.compile_remarks(wrong, "unique.vela", _PRODUCER)
    ensure(exported.gallina is None and exported.error is not None and b"--- !Failure" in exported.yaml
           and b"Function: f_Wrong" in exported.yaml and b"runtime binding" in exported.yaml
           and b'"gallina_sha256":null' in exported.yaml, "runtime dependence lost its real refusal")
    with patch.object(toolchain, "MAX_STATIC_WORK", 0):
        limited = remarks.compile_remarks(_SOURCE, "unique.vela", _PRODUCER)
    ensure(limited.error is not None and b"--- !Failure" in limited.yaml and b"budget exhausted" in limited.yaml,
           "actual specialization budget failure was omitted")
    malformed = remarks.compile_remarks(b"module ;", "odd's.vela", _PRODUCER)
    ensure(malformed.gallina is None and malformed.error is not None and b"--- !" not in malformed.yaml,
           "failed parsing fabricated a pass decision")
    named = remarks.compile_remarks(wrong, "odd's.vela", _PRODUCER)
    ensure(b"File: 'odd%27s.vela'" in named.yaml and b"binding 'runtime';" in named.yaml,
           "stock LLVM reader cannot recover the original filename or diagnostic quoting")
    for filename in ("../relative.vela", "line\nbreak", ""):
        with raises(ValueError, msg="accepted an invalid source basename"):
            remarks.compile_remarks(_SOURCE, filename, _PRODUCER)


def _publication() -> None:
    with tempfile.TemporaryDirectory() as temp, redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
        source = Path(temp) / "decisions.vela"
        report = Path(temp) / "remarks.yaml"
        source.write_bytes(_SOURCE)
        write = ["remarks", str(source), "--output", str(report)]
        check = ["remarks-validate", str(source), str(report)]
        with patch.object(vela.compiler_trace, "producer_identity", return_value=_PRODUCER):
            ensure(vela.main(write) == 0 and vela.main(check) == 0, "CLI failed to round-trip the current report")
            valid = report.read_bytes()
            report.write_bytes(valid.replace(b"!Passed", b"!Missed", 1))
            ensure(vela.main(check) == 1, "edited outcome was accepted")
            report.write_bytes(valid)
            with patch.object(remarks, "MAX_DECISIONS", 1):
                ensure(vela.main(write) == 1 and report.read_bytes() == valid,
                       "truncated decisions overwrote the report")
            with patch.object(vela.compiler_trace, "producer_identity", side_effect=(_PRODUCER, "2" * 64)):
                ensure(vela.main(write) == 1 and report.read_bytes() == valid,
                       "producer replacement during publication overwrote the report")
            source.write_bytes(_SOURCE.replace(b"Carry(7", b"Carry(8"))
            ensure(vela.main(check) == 1, "stale source was accepted")
            source.write_bytes(_SOURCE + b"public Nat Bad(Nat x) => Pick(x, x);")
            ensure(vela.main(write) == 1 and b"!Failure" in report.read_bytes() and vela.main(check) == 0,
                   "source refusal lost its evidence or gained a successful compiler verdict")


def cases() -> list[Case]:
    return [Case("real-specialization-and-generated-origins", _decisions),
            Case("checked-call-and-budget-refusals", _refusals),
            Case("bound-atomic-remarks-publication", _publication)]
