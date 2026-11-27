# SPDX-License-Identifier: Apache-2.0
"""Replay exact-natural type-use irrelevance and the audio routing comparison."""

import contextlib
import io
import json
import math
import re
import subprocess
import tempfile
import time
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from tests.test_holdfast_packages import _write
from toolchain import packages, proofenv, rocq_cache, solver_ledger
from toolchain.cli.holdfast_parser import main as parser_main

INDEPENDENT_CASES = True


def _type_irrelevance() -> None:
    audited = (
        "zero_type_use",
        "zero_type_var_use",
        "zero_use_preserves_row",
        "checked_zero_type_use",
        "checked_zero_type_var_use",
    )
    compiler = [*proofenv.rocq_command(), "-q"]
    with tempfile.TemporaryDirectory(prefix="holdfast-type-use-") as temporary:
        directory = Path(temporary)
        rocq_cache.materialize_repo_units(
            TOOLS.parent,
            directory,
            ("graded_pure.v", "graded_type_irrelevance.v"),
            compiler=compiler,
        )
        audit = directory / "TypeUseAudit.v"
        audit.write_text("Require Import graded_type_irrelevance.\n" + "".join(
            f"Print Assumptions GradedTypeIrrelevance.{name}.\n" for name in audited), encoding="utf-8")
        result = subprocess.run([*compiler, audit.name], cwd=directory, capture_output=True,
                                text=True, encoding="utf-8", check=True, timeout=30)
        solver_ledger.audit(result.stdout, len(audited), "GradedTypeIrrelevance", ())
        rocq_cache.check_kernel(directory, ["graded_type_irrelevance"])


def _parser_command(arguments: list[str]) -> tuple[int, str, str]:
    output, error = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
        status = parser_main(arguments)
    return status, output.getvalue(), error.getvalue()


def _check_audio_route_behavior(directory: Path, name: str, gallina: str) -> float:
    erased_theorems = [
        line.split()[1] for line in gallina.splitlines()
        if line.startswith("Theorem ") and "_erased_" in line and "_correspondence" in line
    ]
    proof = directory / f"{name}.v"
    unit_text, _ = rocq_cache.use_cached_prelude(gallina + """
Import HoldFast_GradedAudioRoute.
Theorem stereo_route_returns_samples :
  forall (period label_count : nat)
    (stereo : @holdfast_Vec nat ((period + 1) + (period + 1)))
    (labels : @holdfast_Vec nat label_count),
    holdfast_d1_StereoRoute period label_count stereo labels = stereo.
Proof. reflexivity. Qed.
Print Assumptions stereo_route_returns_samples.
""" + "".join(f"Print Assumptions {thm}.\n" for thm in erased_theorems), directory)
    proof.write_text(unit_text, encoding="utf-8")
    started = time.perf_counter()
    checked = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                             capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
    elapsed = time.perf_counter() - started
    solver_ledger.audit(checked.stdout, 1 + len(erased_theorems), f"{name} behavior", ())
    return elapsed


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
        route_metrics: dict[str, dict[str, float | int]] = {}
        for path, name, key, ann_count in (
            (baseline, "AudioRouteBaseline", "fixed_mode", 0),
            (fixture, "AudioRouteGraded", "graded", annotations),
        ):
            started = time.perf_counter()
            status, gallina, error = _parser_command(["elaborate", str(path)])
            elab_s = time.perf_counter() - started
            ensure(status == 0, error)
            if key == "graded":
                ensure("_erased_StereoRoute_correspondence" in gallina,
                       "missing CBV erasure correspondence for StereoRoute")
            replay_s = _check_audio_route_behavior(directory, name, gallina)
            route_metrics[key] = {
                "annotations": ann_count,
                "elaborate_s": elab_s,
                "replay_s": replay_s,
            }

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
        route_metrics["fixed_mode"]["repair_edits"] = 2
        route_metrics["graded"]["repair_edits"] = 2
        ensure(
            route_metrics["graded"]["annotations"] == 12
            and route_metrics["fixed_mode"]["annotations"] == 0
            and all(math.isfinite(float(v)) for m in route_metrics.values() for v in m.values()),
            f"invalid StereoRoute Q25by comparison metrics: {route_metrics}",
        )


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


def _locked_transitive_grade_import() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-closure-") as temporary:
        workspace = Path(temporary)
        leaf = _write(workspace, "leaf", "v1", {}, "GradeLeaf") / "module.hf"
        relay = _write(workspace, "relay", "v1", {"leaf": "v1"}, "GradeRelay") / "module.hf"
        client = _write(workspace, "main", "v1", {"relay": "v1"}, "GradeRoot") / "module.hf"
        provider = ("module GradeLeaf;\n"
                    "public definition Vec<Nat, (left + left)> Preserve(\n"
                    "    Nat left @ NatExact(0), Nat right @ NatExact(0),\n"
                    "    Vec<Nat, (left + left)> samples @ NatExact(1)) => samples;\n")
        leaf.write_text(provider, encoding="utf-8")
        relay.write_text("module GradeRelay;\nimport GradeLeaf { Preserve as Keep };\n"
                         "definition Vec<Nat, (n + n)> Local(Nat n @ NatExact(0),\n"
                         "    Vec<Nat, (n + n)> samples @ NatExact(1)) => Keep(n, n, samples);\n"
                         "public definition Vec<Nat, (n + n)> Pass(Nat n @ NatExact(0),\n"
                         "    Vec<Nat, (n + n)> samples @ NatExact(1)) => Local(n, samples);\n",
                         encoding="utf-8")
        client.write_text("module GradeRoot;\nimport GradeRelay as Relay;\n"
                          "public definition Vec<Nat, (n + n)> Route(Nat n @ NatExact(0),\n"
                          "    Vec<Nat, (n + n)> samples @ NatExact(1)) => Relay.Pass(n, samples);\n",
                          encoding="utf-8")
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]

        def relock() -> None:
            status, _, error = _parser_command(lock_command)
            ensure(status == 0, error)

        def checked_route() -> str:
            relock()
            status, _, error = _parser_command(build_command)
            ensure(status == 0, error)
            emitted = str(json.loads(bundle.read_bytes())["modules"]["GradeRoot"])
            return next(line for line in emitted.splitlines() if "Graded replay Route NatExact" in line)

        first = checked_route()
        leaf.write_text(provider.replace("left + left", "right + right"), encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        ensure(checked_route() != first, "changed transitive type demand reused the root grade receipt")
        checked = bundle.read_bytes()

        leaf.write_text(provider.replace("samples @ NatExact(1)", "samples @ NatExact(0)"), encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked, "invalid transitive grade changed the retained bundle")


def _locked_graded_callback_import() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-callback-") as temporary:
        workspace = Path(temporary)
        lib = _write(workspace, "library", "v1", {}, "CallbackProvider") / "module.hf"
        client = _write(workspace, "main", "v1", {"library": "v1"}, "CallbackClient") / "module.hf"
        provider = ("module CallbackProvider;\n"
                    "public definition Nat Twice(Nat n @ NatExact(2)) => n + n;\n"
                    "public definition Nat Apply(Fn(Nat x @ NatExact(2)) -> Nat f @ NatExact(1),\n"
                    "    Nat n @ NatExact(2)) => f(n);\n")
        consumer = ("module CallbackClient;\nimport CallbackProvider as Provider;\n"
                    "public definition Nat UseNamed(Nat n @ NatExact(2)) => Provider.Apply(Provider.Twice, n);\n"
                    "public definition Nat UseLambda(Nat n @ NatExact(2)) =>\n"
                    "    Provider.Apply((Nat x @ NatExact(2)) => x + x, n);\n")
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]

        def relock() -> None:
            status, _, error = _parser_command(lock_command)
            ensure(status == 0, error)

        lib.write_text(provider, encoding="utf-8")
        client.write_text(consumer, encoding="utf-8")
        relock()
        status, _, error = _parser_command(build_command)
        ensure(status == 0, error)
        checked = bundle.read_bytes()
        emitted = str(json.loads(checked)["modules"]["CallbackClient"])
        ensure("Graded replay UseNamed NatExact: SHA256" in emitted
               and "Graded replay UseLambda NatExact: SHA256" in emitted,
               "locked higher-order graded build lost its grade receipt")

        client.write_text("module CallbackClient;\nimport CallbackProvider as Provider;\n"
                          "public definition Nat Unchecked(Nat n) => Provider.Apply((Nat x) => x, n);\n",
                          encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "accepts a graded callback and requires a checked caller" in error, error)

        client.write_text(consumer.replace("(Nat x @ NatExact(2)) => x + x", "(Nat x @ NatExact(1)) => x"),
                          encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked, "invalid higher-order graded import changed the retained bundle")

        client.write_text(consumer, encoding="utf-8")
        lib.write_text(
            provider.replace("Nat x @ NatExact(2)", "Nat x @ NatExact(1)").replace("Nat n @ NatExact(2)", "Nat n @ NatExact(1)"),
            encoding="utf-8",
        )
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked, "provider callback change corrupted the retained bundle")


def _locked_graded_type_import() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-type-import-") as temporary:
        workspace = Path(temporary)
        lib = _write(workspace, "library", "v1", {}, "TypeProvider") / "module.hf"
        client = _write(workspace, "main", "v1", {"library": "v1"}, "TypeClient") / "module.hf"
        provider = ("module TypeProvider;\n"
                    "public definition a Identity(Type a @ NatExact(0), a x @ NatExact(1)) => x;\n")
        consumer = ("module TypeClient;\nimport TypeProvider as Provider;\n"
                    "public definition Vec<Nat, (n + n)> Route(Nat n @ NatExact(0),\n"
                    "    Vec<Nat, (n + n)> samples @ NatExact(1)) => Provider.Identity(type Vec<Nat, (n + n)>, samples);\n")
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]

        def relock() -> None:
            status, _, error = _parser_command(lock_command)
            ensure(status == 0, error)

        def checked_route() -> str:
            relock()
            status, _, error = _parser_command(build_command)
            ensure(status == 0, error)
            emitted = str(json.loads(bundle.read_bytes())["modules"]["TypeClient"])
            return next(line for line in emitted.splitlines() if "Graded replay Route NatExact" in line)

        lib.write_text(provider, encoding="utf-8")
        client.write_text(consumer, encoding="utf-8")
        first = checked_route()
        client.write_text(consumer.replace("as Provider;", "{ Identity as KeepId };")
                          .replace("Provider.Identity", "KeepId"), encoding="utf-8")
        checked_route()
        client.write_text(consumer, encoding="utf-8")
        ensure(checked_route() == first, "identical type-polymorphic closure produced different grade receipts")
        checked = bundle.read_bytes()

        lib.write_text(provider + "\n", encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        ensure(checked_route() != first, "provider edit did not invalidate the type-polymorphic client receipt")
        checked = bundle.read_bytes()

        lib.write_text(provider.replace("NatExact", "NatBound"), encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "requires the NatBound grade domain" in error, error)

        lib.write_text(provider, encoding="utf-8")
        client.write_text(consumer.replace("type Vec<Nat, (n + n)>", "type Type"), encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "computation demand or natural-index checking" in error, error)
        ensure(bundle.read_bytes() == checked, "invalid type-polymorphic import changed the retained bundle")


def _locked_graded_box_import() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-graded-box-import-") as temporary:
        workspace = Path(temporary)
        lib = _write(workspace, "library", "v1", {}, "BoxProvider") / "module.hf"
        client = _write(workspace, "main", "v1", {"library": "v1"}, "BoxClient") / "module.hf"
        provider = ("module BoxProvider;\n"
                    "public record Box<T, grade q : NatExact>(T Value @ q);\n"
                    "public definition Box<Nat, 2> Pack(Nat n @ NatExact(2)) => Box<Nat, 2>(n);\n"
                    "public definition Nat Unpack(Box<Nat, 2> packed @ NatExact(1)) =>\n"
                    "    match (packed) as whole : Nat { Box(x) => x + x, };\n")
        consumer = ("module BoxClient;\nimport BoxProvider { Box, Pack, Unpack };\n"
                    "public definition Nat RoundTrip(Nat n @ NatExact(2)) => Unpack(Pack(n));\n"
                    "public definition Nat Forward(Box<Nat, 2> b @ NatExact(1)) => Unpack(b);\n")
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]

        def relock() -> None:
            status, _, error = _parser_command(lock_command)
            ensure(status == 0, error)

        lib.write_text(provider, encoding="utf-8")
        client.write_text(consumer, encoding="utf-8")
        relock()
        status, _, error = _parser_command(build_command)
        ensure(status == 0, error)
        checked = bundle.read_bytes()
        emitted = json.loads(checked)["modules"]
        client_v = str(emitted["BoxClient"])
        ensure("Graded replay RoundTrip NatExact: SHA256" in client_v
               and "Graded replay Forward NatExact: SHA256" in client_v,
               "locked graded box build lost its grade receipt")

        proof_dir = Path(temporary) / "rocq"
        proof_dir.mkdir()
        [module_name] = re.findall(r"^Module (HoldFastPackage_\S+)\.", client_v, re.MULTILINE)
        [round_trip] = re.findall(r"^Definition (\S+_RoundTrip) :", client_v, re.MULTILINE)
        box_verify, _ = rocq_cache.use_cached_prelude(
            client_v + f"""
Import {module_name}.
Theorem round_trip_doubles : forall n, {round_trip} n = n + n.
Proof. reflexivity. Qed.
Print Assumptions round_trip_doubles.
""",
            proof_dir,
        )
        (proof_dir / "BoxVerify.v").write_text(box_verify, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", "BoxVerify.v"], cwd=proof_dir,
                                capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
        solver_ledger.audit(replay.stdout, 1, "BoxClient", ())

        client.write_text("module BoxClient;\nimport BoxProvider { Box, Pack, Unpack };\n"
                          "public definition Nat Unchecked(Nat n) => Unpack(Pack(n));\n",
                          encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "uses a graded Box interface and requires a checked caller" in error, error)

        client.write_text("module BoxClient;\nimport BoxProvider { Box, Pack, Unpack };\n"
                          "public definition Nat WrongGrade(Box<Nat, 3> b @ NatExact(1)) => Unpack(b);\n",
                          encoding="utf-8")
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked, "invalid box import changed the retained bundle")

        client.write_text(consumer, encoding="utf-8")
        lib.write_text(provider.replace("NatExact", "NatBound"), encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "requires the NatBound grade domain" in error, error)
        ensure(bundle.read_bytes() == checked, "box domain mismatch changed the retained bundle")


def _check_protocol_client_behavior(directory: Path, name: str, gallina: str) -> float:
    [route_fn] = re.findall(r"^Definition (\S+_RouteTelemetry) :", gallina, re.MULTILINE)
    [header_fn] = re.findall(r"^Definition (\S+_FrameHeader) :", gallina, re.MULTILINE)
    erased_theorems = [
        line.split()[1] for line in gallina.splitlines()
        if line.startswith("Theorem ") and "_erased_" in line and "_correspondence" in line
    ]
    proof = directory / f"{name}.v"
    unit_text, _ = rocq_cache.use_cached_prelude(
        gallina + f"""
Import HoldFast_TelemetryFrameRouter.
Theorem telemetry_route_returns_payload :
  forall (slots audit_len : nat)
    (payload : @holdfast_Vec nat (slots + slots))
    (audit_trail : @holdfast_Vec nat audit_len),
    {route_fn} slots audit_len payload audit_trail = payload.
Proof. reflexivity. Qed.
Theorem telemetry_route_independent_of_audit_len :
  forall (slots audit_len_a audit_len_b : nat)
    (payload : @holdfast_Vec nat (slots + slots))
    (trail_a : @holdfast_Vec nat audit_len_a)
    (trail_b : @holdfast_Vec nat audit_len_b),
    {route_fn} slots audit_len_a payload trail_a =
      {route_fn} slots audit_len_b payload trail_b /\\
    {route_fn} slots audit_len_a payload trail_a = payload.
Proof. split; reflexivity. Qed.
Theorem frame_header_doubles_tag :
  forall tag : nat, {header_fn} tag = tag + tag.
Proof. reflexivity. Qed.
Print Assumptions telemetry_route_returns_payload.
Print Assumptions telemetry_route_independent_of_audit_len.
Print Assumptions frame_header_doubles_tag.
""" + "".join(f"Print Assumptions {thm}.\n" for thm in erased_theorems),
        directory,
    )
    )
    proof.write_text(unit_text, encoding="utf-8")
    started = time.perf_counter()
    checked = subprocess.run([*proofenv.rocq_command(), "-q", proof.name], cwd=directory,
                             capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
    elapsed = time.perf_counter() - started
    solver_ledger.audit(checked.stdout, 3 + len(erased_theorems), f"{name} behavior", ())
    return elapsed


def _graded_protocol_client_comparison() -> None:
    fixture = TOOLS / "tests" / "fixtures" / "graded-protocol-client.hf"
    source = fixture.read_text(encoding="utf-8")
    grade_annotations = re.compile(r" @ NatExact\([0-9]+\)")
    baseline_text, graded_annotations = grade_annotations.subn("", source)
    baseline_annotations = len(grade_annotations.findall(baseline_text))
    ensure(graded_annotations == 17 and baseline_annotations == 0,
           f"unexpected annotation counts: graded={graded_annotations}, baseline={baseline_annotations}")

    started = time.perf_counter()
    status, output, error = _parser_command(["check-grades", str(fixture), "RouteTelemetry"])
    check_grades_elapsed = time.perf_counter() - started
    ensure(status == 0, error)
    report = json.loads(output)
    binders = report["binders"]
    demands = [(binder["name"], binder["computation"], binder["type"]) for binder in binders]
    ensure(demands == [("slots", 0, 4), ("auditLen", 0, 1), ("payload", 1, 0), ("auditTrail", 0, 0)],
           f"wrong protocol router demands: {demands}")
    slots_use = {"name": "slots", "span": binders[0]["span"], "uses": 2}
    audit_use = {"name": "auditLen", "span": binders[1]["span"], "uses": 1}
    ensure(binders[2]["annotation_type_uses"] == report["result_type_uses"] == [slots_use],
           "payload and result type lost their shared slots index")
    ensure(all(entry["name"] != "auditLen" for entry in report["result_type_uses"]),
           "result type unexpectedly depends on auditLen")
    ensure(binders[3]["annotation_type_uses"] == [audit_use],
           "auditTrail lost its independent auditLen index")
    ensure(report["dependencies"] == ["RouteSpec", "ForwardPayload"],
           f"unexpected protocol router dependencies: {report['dependencies']}")

    status, header_output, error = _parser_command(["check-grades", str(fixture), "FrameHeader"])
    ensure(status == 0, error)
    header_report = json.loads(header_output)
    header_demands = [(b["name"], b["computation"], b["type"]) for b in header_report["binders"]]
    ensure(header_demands == [("headerTag", 2, 0)] and header_report["result_type_uses"] == [],
           f"wrong FrameHeader demands: {header_report}")

    with tempfile.TemporaryDirectory(prefix="holdfast-protocol-client-") as temporary:
        directory = Path(temporary)
        baseline = directory / "TelemetryBaseline.hf"
        baseline.write_text(baseline_text, encoding="utf-8")

        timings: dict[str, float] = {"check_grades": check_grades_elapsed}
        for path, label, prefix in ((baseline, "ProtocolBaseline", "baseline"),
                                    (fixture, "ProtocolGraded", "graded")):
            started = time.perf_counter()
            status, gallina, error = _parser_command(["elaborate", str(path)])
            timings[f"{prefix}_elaborate"] = time.perf_counter() - started
            ensure(status == 0, error)
            timings[f"{prefix}_replay"] = _check_protocol_client_behavior(directory, label, gallina)
        ensure(all(math.isfinite(value) and value >= 0.0 for value in timings.values()),
               f"invalid timing measurements: {timings}")
        comparison_metrics = {
            "fixed_mode": {
                "annotations": baseline_annotations,
                "explicit_proof_theorems": 3,
                "repair_edits_computation": 3,
                "repair_edits_dependency": 2,
                "replay_time": timings["baseline_replay"],
            },
            "graded": {
                "annotations": graded_annotations,
                "explicit_proof_theorems": 0,
                "repair_edits_computation": 3,
                "repair_edits_dependency": 2,
                "replay_time": timings["graded_replay"],
                "check_grades_time": timings["check_grades"],
            },
        }
        ensure(comparison_metrics["graded"]["annotations"] == 17
               and comparison_metrics["fixed_mode"]["annotations"] == 0,
               f"frozen Q25by comparison metrics drifted: {comparison_metrics}")

        candidate = directory / "ProtocolEdit.hf"
        # Computation edits: wrong allowance on payload, wrong usage in FrameHeader, and returning auditTrail.
        bad_allowance = source.replace("payload @ NatExact(1)", "payload @ NatExact(0)")
        ensure(grade_annotations.subn("", bad_allowance)[0] == baseline_text,
               "allowance edit changed the ungraded baseline")
        candidate.write_text(bad_allowance, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(candidate)])
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)

        bad_header = source.replace("headerTag + headerTag", "headerTag")
        candidate.write_text(bad_header, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(candidate)])
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)

        bad_return = source.replace("ForwardPayload(slots, auditLen, payload, auditTrail)", "auditTrail")
        candidate.write_text(bad_return, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(candidate)])
        ensure(status == 1 and not output, "returning auditTrail unexpectedly succeeded")

        # Dependency edits: result type depending on auditLen or swapping index arguments.
        bad_dep = source.replace("public definition Vec<Nat, (slots + slots)> RouteTelemetry(",
                                 "public definition Vec<Nat, (slots + auditLen)> RouteTelemetry(")
        candidate.write_text(bad_dep, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(candidate)])
        ensure(status == 1 and not output and "declared dependent type" in error, error)
        baseline.write_text(grade_annotations.sub("", bad_dep), encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(baseline)])
        ensure(status == 1 and not output and "dependent indices are not definitionally equal" in error, error)

        swapped_dep = source.replace("ForwardPayload(slots, auditLen, payload, auditTrail)",
                                     "ForwardPayload(auditLen, slots, payload, auditTrail)")
        candidate.write_text(swapped_dep, encoding="utf-8")
        status, output, error = _parser_command(["elaborate", str(candidate)])
        ensure(status == 1 and not output, "swapped dependent index unexpectedly succeeded")

        # Locked-package rebuild & stale-lock refusal on both provider and importing client.
        workspace = directory / "workspace"
        workspace.mkdir()
        provider_path = _write(workspace, "library", "v1", {}, "TelemetryProvider") / "module.hf"
        client_path = _write(workspace, "main", "v1", {"library": "v1"}, "TelemetryClient") / "module.hf"
        provider_src = source.replace("module TelemetryFrameRouter;", "module TelemetryProvider;")
        client_src = (
            "module TelemetryClient;\n"
            "import TelemetryProvider as Router;\n"
            "public definition Vec<Nat, (slots + slots)> ClientRoute(\n"
            "    Nat slots @ NatExact(0),\n"
            "    Nat auditLen @ NatExact(0),\n"
            "    Vec<Nat, (slots + slots)> payload @ NatExact(1),\n"
            "    Vec<Nat, auditLen> auditTrail @ NatExact(0)\n"
            ") => Router.RouteTelemetry(slots, auditLen, payload, auditTrail);\n"
        )
        lock = workspace / "holdfast.lock.json"
        bundle = workspace / "checked.json"
        lock_command = ["lock-package", str(workspace), "main", "v1", "--output", str(lock)]
        build_command = ["build-package", str(workspace), str(lock), "--output", str(bundle)]

        def relock() -> None:
            st, _, err = _parser_command(lock_command)
            ensure(st == 0, err)

        provider_path.write_text(provider_src, encoding="utf-8")
        client_path.write_text(client_src, encoding="utf-8")
        relock()
        status, _, error = _parser_command(build_command)
        ensure(status == 0, error)
        checked_bundle = bundle.read_bytes()
        emitted_modules = json.loads(checked_bundle)["modules"]
        ensure("Graded replay RouteTelemetry NatExact: SHA256" in str(emitted_modules["TelemetryProvider"]),
               "provider build lost RouteTelemetry grade receipt")
        client_v = str(emitted_modules["TelemetryClient"])
        ensure("Graded replay ClientRoute NatExact: SHA256" in client_v,
               "client build lost ClientRoute grade receipt")

        pkg_rocq = directory / "pkg-rocq"
        pkg_rocq.mkdir()
        [pkg_mod] = re.findall(r"^Module (HoldFastPackage_\S+)\.", client_v, re.MULTILINE)
        [client_fn] = re.findall(r"^Definition (\S+_ClientRoute) :", client_v, re.MULTILINE)
        client_verify, _ = rocq_cache.use_cached_prelude(
            client_v + f"""
Import {pkg_mod}.
Theorem client_route_independent_of_audit_len :
  forall (slots audit_len_a audit_len_b : nat)
    (payload : @holdfast_Vec nat (slots + slots))
    (trail_a : @holdfast_Vec nat audit_len_a)
    (trail_b : @holdfast_Vec nat audit_len_b),
    {client_fn} slots audit_len_a payload trail_a =
      {client_fn} slots audit_len_b payload trail_b /\\
    {client_fn} slots audit_len_a payload trail_a = payload.
Proof. split; reflexivity. Qed.
Print Assumptions client_route_independent_of_audit_len.
""",
            pkg_rocq,
        )
        (pkg_rocq / "ClientVerify.v").write_text(client_verify, encoding="utf-8")
        replay = subprocess.run([*proofenv.rocq_command(), "-q", "ClientVerify.v"], cwd=pkg_rocq,
                                capture_output=True, text=True, encoding="utf-8", check=True, timeout=30)
        solver_ledger.audit(replay.stdout, 1, "TelemetryClient", ())

        # 1. Provider computation edit: stale lock refusal, then computation demand failure.
        provider_path.write_text(provider_src.replace("payload @ NatExact(1)", "payload @ NatExact(0)"),
                                 encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked_bundle, "provider computation edit changed the retained bundle")

        # 2. Provider dependency edit: stale lock refusal, then declared dependent type failure.
        provider_path.write_text(provider_src, encoding="utf-8")
        relock()
        provider_path.write_text(
            provider_src.replace("public definition Vec<Nat, (slots + slots)> RouteTelemetry(",
                                 "public definition Vec<Nat, (slots + auditLen)> RouteTelemetry("),
            encoding="utf-8",
        )
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "declared dependent type" in error, error)
        ensure(bundle.read_bytes() == checked_bundle, "provider dependency edit changed the retained bundle")

        # 3. Client computation edit: stale lock refusal, then computation demand failure.
        provider_path.write_text(provider_src, encoding="utf-8")
        relock()
        client_path.write_text(client_src.replace("payload @ NatExact(1)", "payload @ NatExact(0)"),
                               encoding="utf-8")
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "fails exact computation demand" in error, error)
        ensure(bundle.read_bytes() == checked_bundle, "client computation edit changed the retained bundle")

        # 4. Client dependency edit: stale lock refusal, then declared dependent type failure.
        client_path.write_text(client_src, encoding="utf-8")
        relock()
        client_path.write_text(
            client_src.replace("public definition Vec<Nat, (slots + slots)> ClientRoute(",
                               "public definition Vec<Nat, (slots + auditLen)> ClientRoute("),
            encoding="utf-8",
        )
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "stale" in error, error)
        relock()
        status, output, error = _parser_command(build_command)
        ensure(status == 1 and not output and "declared dependent type" in error, error)
        ensure(bundle.read_bytes() == checked_bundle, "client dependency edit changed the retained bundle")


def cases() -> list[Case]:
    return [Case("exact-natural zero type-use substitution law", _type_irrelevance, lane="toolchain"),
            Case("paired graded and ordinary audio routing replay", _audio_route, lane="toolchain"),
            Case("independent Q25by telemetry protocol client comparison",
                 _graded_protocol_client_comparison, lane="toolchain"),
            Case("default graded replay in a locked package", _locked_grading, lane="toolchain"),
            Case("graded dependent calls through a locked import", _locked_graded_import, lane="toolchain"),
            Case("graded dependent calls through a transitive locked import", _locked_transitive_grade_import,
                 lane="toolchain"),
            Case("graded higher-order calls and callbacks through a locked import", _locked_graded_callback_import,
                 lane="toolchain"),
            Case("graded type-polymorphic calls through a locked import", _locked_graded_type_import,
                 lane="toolchain"),
            Case("graded box callable and locked module interfaces", _locked_graded_box_import,
                 lane="toolchain")]
