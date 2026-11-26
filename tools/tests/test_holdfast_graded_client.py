# SPDX-License-Identifier: Apache-2.0
"""Replay exact-natural type-use irrelevance and the audio routing comparison."""

import contextlib
import io
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from tests.test_holdfast_packages import _write
from toolchain import packages, proofenv, solver_ledger
from toolchain.cli.holdfast_parser import main as parser_main


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


def _parser_command(arguments: list[str]) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(arguments)
    return status, output.getvalue(), error.getvalue()


def _check_audio_route_behavior(directory: Path, name: str, gallina: str) -> None:
    proof = directory / f"{name}.v"
    proof.write_text(gallina + """
Import HoldFast_GradedAudioRoute.
Theorem stereo_route_returns_samples :
  forall (period label_count : nat)
    (stereo : @holdfast_Vec nat ((period + 1) + (period + 1)))
    (labels : @holdfast_Vec nat label_count),
    holdfast_d1_StereoRoute period label_count stereo labels = stereo.
Proof. reflexivity. Qed.
Print Assumptions stereo_route_returns_samples.
""", encoding="utf-8")
    checked = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                             capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
    solver_ledger.audit(checked.stdout, 1, f"{name} behavior", ())


def _audio_route() -> None:
    fixture = TOOLS / "tests" / "fixtures" / "graded-audio-route.hf"
    source = fixture.read_text(encoding="utf-8")
    grade_annotations = re.compile(r" @ NatExact\([0-9]+\)")
    status, output, error = _parser_command(["check-grades", str(fixture), "StereoRoute"])
    ensure(status == 0, error)
    report = json.loads(output)
    binders = report["binders"]
    demands = [(binder["name"], binder["computation"], binder["type"]) for binder in binders]
    ensure(demands == [("period", 0, 4), ("labelCount", 0, 1), ("stereo", 1, 0),
                       ("channelLabels", 0, 0)], f"wrong audio route demands: {demands}")
    period = {"name": "period", "span": binders[0]["span"], "uses": 2}
    label_count = {"name": "labelCount", "span": binders[1]["span"], "uses": 1}
    ensure(binders[2]["annotation_type_uses"] == report["result_type_uses"] == [period],
           "stereo input and result lost their shared period")
    ensure(binders[3]["annotation_type_uses"] == [label_count], "label input lost its independent count")
    ensure(report["dependencies"] == ["RouteInputs"], "audio router must use the parameterized route")

    with tempfile.TemporaryDirectory(prefix="holdfast-audio-route-") as temporary:
        directory = Path(temporary)
        baseline = directory / "AudioRoute.hf"
        baseline_text, annotations = grade_annotations.subn("", source)
        ensure(annotations == 12, "baseline changed the audio route annotation budget")
        baseline.write_text(baseline_text, encoding="utf-8")
        for path, name in ((baseline, "AudioRouteBaseline"), (fixture, "AudioRouteGraded")):
            status, gallina, error = _parser_command(["elaborate", str(path)])
            ensure(status == 0, error)
            _check_audio_route_behavior(directory, name, gallina)

        stale = source.replace("RouteInputs()(period + 1, labelCount)", "RouteInputs()(period, labelCount)")
        graded_stale = directory / "GradedStale.hf"
        graded_stale.write_text(stale, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(graded_stale)])
        ensure(status == 1 and not output and "declared dependent type" in error, error)
        baseline.write_text(grade_annotations.sub("", stale), encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(baseline)])
        ensure(status == 1 and not output and "dependent indices are not definitionally equal" in error, error)

        bad_allowance = source.replace("samples @ NatExact(1)", "samples @ NatExact(0)")
        ensure(grade_annotations.sub("", bad_allowance) == baseline_text, "allowance control changed behavior")
        graded_stale.write_text(bad_allowance, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(graded_stale)])
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)


def _locked_grading() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-package-") as temporary:
        workspace = Path(temporary)
        source = _write(workspace, "main", "v1", {}, "GradedLocked") / "module.hf"
        text = "module GradedLocked;\npublic definition Nat Twice(Nat n @ NatExact(2)) => n + n;\n"
        source.write_text(text, encoding="utf-8")
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]
        status, _, error = _parser_command(lock_command)
        ensure(status == 0, error)
        status, _, error = _parser_command(build_command)
        ensure(status == 0, error)
        checked = bundle.read_bytes()
        emitted = json.loads(checked)["modules"]["GradedLocked"]
        ensure("Graded replay Twice NatExact: SHA256" in emitted, "locked build lost its grade receipt")

        source.write_text(text.replace("NatExact(2)", "NatExact(1)"), encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        status, _, error = _parser_command(lock_command)
        ensure(status == 0, error)
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked, "failed graded build changed the retained bundle")


def _locked_graded_import() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-import-") as temporary:
        workspace = Path(temporary)
        lib = _write(workspace, "library", "v1", {}, "SignedGrade") / "module.hf"
        client = _write(workspace, "main", "v1", {"library": "v1"}, "GradeClient") / "module.hf"
        provider = ("module SignedGrade;\n"
                    "public definition Vec<Nat, (n + n)> Preserve(Nat n @ NatExact(0),\n"
                    "    Vec<Nat, (n + n)> samples @ NatExact(1)) => samples;\n")
        consumer = ("module GradeClient;\nimport SignedGrade as Provider;\n"
                    "public definition Vec<Nat, (n + n)> Route(Nat n @ NatExact(0),\n"
                    "    Vec<Nat, (n + n)> samples @ NatExact(1)) => Provider.Preserve(n, samples);\n")
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]

        def relock() -> None:
            status, _, error = _parser_command(lock_command)
            ensure(status == 0, error)

        def checked_client() -> str:
            relock()
            status, _, error = _parser_command(build_command)
            ensure(status == 0, error)
            emitted = str(json.loads(bundle.read_bytes())["modules"]["GradeClient"])
            return next(line for line in emitted.splitlines() if "Graded replay Route NatExact" in line)

        lib.write_text(provider, encoding="utf-8")
        client.write_text(consumer, encoding="utf-8")
        first = checked_client()
        client.write_text(consumer.replace("as Provider;", "{ Preserve as Keep };")
                          .replace("Provider.Preserve", "Keep"), encoding="utf-8")
        checked_client()
        client.write_text(consumer, encoding="utf-8")
        ensure(checked_client() == first, "identical source closures produced different grade evidence")

        manifest = client.parent / packages.MANIFEST
        original_manifest = manifest.read_text(encoding="utf-8")
        alternative = _write(workspace, "library", "v2", {}, "SignedGrade") / "module.hf"
        alternative.write_text(provider, encoding="utf-8")
        manifest.write_text(original_manifest.replace('library = "v1"', 'library = "v2"'), encoding="utf-8")
        ensure(checked_client() != first, "different provider identity reused the client grade receipt")
        manifest.write_text(original_manifest, encoding="utf-8")
        relock()

        lib.write_text(provider + "\n", encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        ensure(checked_client() != first, "changed provider source did not invalidate the client grade receipt")
        checked = bundle.read_bytes()

        lib.write_text(provider.replace("NatExact", "NatBound"), encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "requires the NatBound grade domain" in error, error)

        lib.write_text(provider, encoding="utf-8")
        client.write_text(consumer.replace("Preserve(n, samples)", "Preserve(n + n, samples)"), encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "computation demand or natural-index checking" in error, error)
        ensure(bundle.read_bytes() == checked, "invalid graded import changed the retained bundle")


def cases() -> list[Case]:
    return [Case("exact-natural zero type-use substitution law", _type_irrelevance, lane="toolchain"),
            Case("paired graded and ordinary audio routing replay", _audio_route, lane="toolchain"),
            Case("default graded replay in a locked package", _locked_grading, lane="toolchain"),
            Case("graded dependent calls through a locked import", _locked_graded_import, lane="toolchain")]
