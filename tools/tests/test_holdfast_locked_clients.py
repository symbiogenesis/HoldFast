# SPDX-License-Identifier: Apache-2.0
"""Independent consumers of locked mathematical package builds."""

import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
from pathlib import Path

from tests.harness import TOOLS, Case, ensure
from toolchain import parser, proofenv, solver_ledger
from toolchain.cli import holdfast_parser


def _command(*args: str | Path, refusal: str | None = None) -> None:
    output = StringIO()
    errors = StringIO()
    with redirect_stdout(output), redirect_stderr(errors):
        status = holdfast_parser.main([str(arg) for arg in args])
    if refusal is None:
        ensure(status == 0, f"{args[0]} failed: {errors.getvalue()}")
    else:
        ensure(status != 0 and refusal in errors.getvalue(),
               f"{args[0]} returned {status}, expected {refusal!r}: {errors.getvalue()}")


def _workspace(directory: Path) -> Path:
    workspace = directory / "package sources"
    shutil.copytree(TOOLS.parent / "examples" / "packages", workspace)
    return workspace


def _lock(workspace: Path) -> Path:
    lock = workspace.parent / "lock.json"
    _command("lock-package", workspace, "scale", "v1", "--output", lock)
    return lock


def _replay(directory: Path, modules: dict[str, str]) -> None:
    # The expected values come from the client's scale contract.
    gallina = modules["Scale.Calibration"]
    [subject] = re.findall(r"^Module (HoldFastPackage_[a-z0-9_]+)\.$", gallina, re.MULTILINE)
    readings = re.compile(r"^Definition (\w+_ReadScale)\b", re.MULTILINE)
    [operation] = set(readings.findall(gallina)) - set(readings.findall(modules["Weights.Measure"]))
    checks = "".join(
        f"Example reading_{units} : {subject}.{operation} {units} = {value} := eq_refl.\n"
        for units, value in ((0, 2), (7, 9))
    )
    libraries = {"Consumer": gallina + checks, "Provider": modules["Weights.Measure"]}
    for name, unit in libraries.items():
        path = directory / f"{name}.v"
        path.write_text(unit, encoding="utf-8", newline="\n")
        _kernel(directory, ["rocq", "c", "-q", path.name])
    _kernel(directory, ["rocqchk", "-silent", *libraries])


def _kernel(directory: Path, arguments: list[str]) -> str:
    process = subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *arguments],
                             cwd=directory, check=False, capture_output=True, timeout=180)
    ensure(process.returncode == 0, f"{arguments}: {(process.stdout + process.stderr)[-3000:]!r}")
    return process.stdout.decode()


def _upgrade(workspace: Path, old: str, new: str, source: str) -> None:
    previous = workspace / "weights" / old
    current = workspace / "weights" / new
    shutil.copytree(previous, current)
    manifest = current / "holdfast-package.toml"
    manifest.write_text(manifest.read_text().replace(f'revision = "{old}"', f'revision = "{new}"'))
    (current / "Measure.hf").write_text(source)
    root = workspace / "scale" / "v1" / "holdfast-package.toml"
    root.write_text(root.read_text().replace(f'weights = "{old}"', f'weights = "{new}"'))


def _client_upgrade() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        workspace = _workspace(directory)
        bundle = directory / "bundle.json"
        lock = _lock(workspace)
        with parser.cached_build(TOOLS.parent) as compiled, compiled.executable.open("rb") as binary:
            first_line = binary.readline(4096)
            ensure(first_line.startswith(b"#!/") and first_line.endswith(b"\n"), "unsupported native parser executable")
            actual = hashlib.sha256(Path(first_line[2:-1].decode()).read_bytes()).hexdigest()
        ensure(json.loads(lock.read_bytes())["producer"]["ocamlrun_sha256"] == actual,
               "package lock differs from the interpreter selected by the parser's shebang")
        _command("build-package", workspace, lock, "--output", bundle)
        before = bundle.read_bytes()
        modules = json.loads(before)["modules"]
        ensure(set(modules) == {"Scale.Calibration", "Weights.Measure"}, "wrong package closure")
        _replay(directory, modules)
        library_lock = directory / "weights.lock"
        library_bundle = directory / "weights.json"
        _command("lock-package", workspace, "weights", "v1", "--output", library_lock)
        _command("build-package", workspace, library_lock, "--output", library_bundle)
        ensure(json.loads(library_bundle.read_bytes())["modules"] == {"Weights.Measure": modules["Weights.Measure"]},
               "standalone library and importing client built different provider outputs")
        _command("build-package", workspace, lock, "--output", bundle)
        ensure(bundle.read_bytes() == before, "rebuilding the same lock changed the bundle")

        source = (workspace / "weights" / "v1" / "Measure.hf").read_text()
        renamed = source.replace("local", "amount")
        _upgrade(workspace, "v1", "v2", renamed)
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        accepted = bundle.read_bytes()
        upgraded = json.loads(accepted)["modules"]
        def weight_type(outputs: dict[str, str]) -> str:
            provider = outputs["Weights.Measure"]
            [definition] = re.finditer(r"^Definition (\w+_Weight) :", provider, re.MULTILINE)
            return provider[definition.start(1):definition.end(1)]

        ensure(weight_type(upgraded) != weight_type(modules), "revisions shared a record identity")
        _replay(directory, upgraded)

        _upgrade(workspace, "v2", "v3", renamed.replace("as units", "as quantity"))
        _command("build-package", workspace, _lock(workspace), "--output", bundle,
                 refusal="expected argument label 'quantity', got 'units'")
        ensure(bundle.read_bytes() == accepted, "broken external label replaced accepted output")


def _closure_coherence() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        workspace = _workspace(Path(temporary))
        provider = workspace / "weights" / "v1"
        manifest = provider / "holdfast-package.toml"
        manifest.write_text(manifest.read_text().replace("[dependencies]", """
"Weights.First" = "First.hf"
"Weights.Second" = "Second.hf"

[dependencies]"""))
        for name, target, result in (("First", "bool", 5), ("Second", "Nat", 11)):
            (provider / f"{name}.hf").write_text(f"""module Weights.{name};
import Weights.Measure;
public impl IMeasured<{target}> {{ public definition Nat Measure({target} value) => {result}; }}
""")
        client = workspace / "scale" / "v1" / "Calibration.hf"
        original = client.read_text()
        bundle = workspace.parent / "bundle.json"
        imports = ["import Weights.First;", "import Weights.Second;"]
        for order in (imports, imports[::-1]):
            client.write_text(original.replace("import Weights.Measure;",
                                               "import Weights.Measure;\n" + "\n".join(order)) + """
public lemma ImportedReadings()
    ensures bool.Measure(true) == 5
    ensures Nat.Measure(7) == 11
    proof { assert bool.Measure(true) == 5; assert Nat.Measure(7) == 11; }
""")
            _command("build-package", workspace, _lock(workspace), "--output", bundle)
            _replay(workspace.parent, json.loads(bundle.read_bytes())["modules"])
        client.write_text(original)
        sibling = provider / "Second.hf"
        sibling.write_text(sibling.read_text().replace("IMeasured<Nat>", "IMeasured<bool>")
                           .replace("Measure(Nat value)", "Measure(bool value)"))
        _command("build-package", workspace, _lock(workspace), refusal="overlapping")
        sibling.write_text("module Weights.Second;")
        client.write_text(original + """
public record LocalWeight(Nat Units);
public impl IMeasured<LocalWeight> { public definition Nat Measure(LocalWeight x) => x.Units; }
""")
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        client.write_text(original + """
public impl IMeasured<Nat> { public definition Nat Measure(Nat value) => value; }
""")
        _command("build-package", workspace, _lock(workspace), refusal="must own")


def _namespace_edition() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        workspace = _workspace(directory)
        app = workspace / "scale" / "v1"
        lock = _lock(workspace)
        manifest = app / "holdfast-package.toml"
        manifest.write_text(manifest.read_text().replace('"math-1"', '"math-2"'))
        _command("build-package", workspace, lock, refusal="stale package lock")
        _command("build-package", workspace, _lock(workspace), refusal="Weight")
        client = app / "Calibration.hf"
        client.write_text(client.read_text().replace("Weight.Measure(Make(", "Measure.Weight.Measure(Measure.Make("))
        provider = workspace / "weights" / "v1" / "Measure.hf"
        provider.write_text(provider.read_text() + "\npublic definition Nat ReadScale(Nat x) => 9;\n")
        _command("fmt", client, "--syntax-only")
        bundle = directory / "qualified.json"
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        _replay(directory, json.loads(bundle.read_bytes())["modules"])


def _opaque_provider_upgrade() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        workspace = _workspace(directory)
        provider = workspace / "weights" / "v1" / "Measure.hf"
        source = provider.read_text() + """
private definition Nat Chosen() => 3;
public Nat Capacity() ensures result >= 1 => Chosen();
"""
        provider.write_text(source)
        client = workspace / "scale" / "v1" / "Calibration.hf"
        client.write_text(client.read_text() + """
public lemma PublishedLowerBound()
    ensures (Capacity() >= 1) == true
    proof { assert (Capacity() >= 1) == true; }
""")
        bundle = directory / "bundle.json"
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        _replay(directory, json.loads(bundle.read_bytes())["modules"])

        changed = source.replace("private definition Nat Chosen() => 3;", """
private record Limit(Nat Available);
private definition Nat Chosen() => Limit(4).Available;""")
        _upgrade(workspace, "v1", "v2", changed)
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        accepted = bundle.read_bytes()
        _replay(directory, json.loads(accepted)["modules"])

        _upgrade(workspace, "v2", "v3", changed.replace(" ensures result >= 1", ""))
        _command("build-package", workspace, _lock(workspace), "--output", bundle,
                 refusal="module 'Scale.Calibration': assertion could not be established")
        ensure(bundle.read_bytes() == accepted, "missing public bound replaced the accepted client")


def _composed_preconditions() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        workspace = _workspace(directory)
        provider = workspace / "weights" / "v1" / "Measure.hf"
        source = provider.read_text() + """
public Nat Seed() ensures result >= 1 => 3;
public Nat Keep(Nat n) requires n >= 1 ensures result >= 1 => n;
public Fn(Nat) -> Nat MakeReader(Nat seed)
    requires seed >= 1 ensures result(7) >= 1 => arg => 6;
"""
        provider.write_text(source)
        client = workspace / "scale" / "v1" / "Calibration.hf"
        client.write_text(client.read_text() + """
public lemma KeptBound()
    ensures (Keep(Keep(Seed())) >= 1) == true
    proof { assert (Keep(Keep(Seed())) >= 1) == true; }
public lemma ReturnedReaderBound()
    ensures (MakeReader(Seed())(7) >= 1) == true
    proof { assert (MakeReader(Seed())(7) >= 1) == true; }
""")
        bundle = directory / "bundle.json"
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        accepted = bundle.read_bytes()
        gallina = json.loads(accepted)["modules"]["Scale.Calibration"]
        [subject] = re.findall(r"^Module (HoldFastPackage_[a-z0-9_]+)\.$", gallina, re.MULTILINE)
        seed, keep, lemma, reader, reader_bound = (
            re.findall(rf"^Definition (\w+_{name}) :", gallina, re.MULTILINE)[0]
            for name in ("Seed", "Keep", "KeptBound", "MakeReader", "ReturnedReaderBound"))
        check = (f"\nImport {subject}.\nExample observed : Nat.leb 1 ({keep} ({keep} ({seed} tt))) = true "
                 f":= {lemma} tt.\nExample read_seven : Nat.leb 1 ({reader} ({seed} tt) 7) = true "
                 f":= {reader_bound} tt.\nPrint Assumptions observed.\nPrint Assumptions read_seven.\n")
        (directory / "Composed.v").write_text(gallina + check, encoding="utf-8")
        report = _kernel(directory, ["rocq", "c", "-q", "Composed.v"])
        solver_ledger.audit(report, 2, subject, ())
        _kernel(directory, ["rocqchk", "-silent", "Composed"])
        _upgrade(workspace, "v1", "v2", source.replace("Seed() ensures result >= 1", "Seed()"))
        _command("build-package", workspace, _lock(workspace), "--output", bundle, refusal="precondition")
        ensure(bundle.read_bytes() == accepted, "an unproved inner precondition replaced the checked bundle")


def cases() -> list[Case]:
    return [
        Case("independent locked client, kernel readings and label evolution", _client_upgrade, lane="toolchain"),
        Case("qualified imports compose with legacy packages across an added export", _namespace_edition, lane="toolchain"),
        Case("sibling instance coherence, declaration ownership and import order", _closure_coherence, lane="toolchain"),
        Case("locked client proof across opaque implementation and public law changes",
             _opaque_provider_upgrade, lane="toolchain"),
        Case("closed proof composes nested opaque calls across a locked boundary",
             _composed_preconditions, lane="toolchain"),
    ]
