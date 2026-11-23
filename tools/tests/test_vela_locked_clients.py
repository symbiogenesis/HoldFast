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
from toolchain import parser, proofenv
from toolchain.cli import vela_parser


def _command(*args: str | Path, refusal: str | None = None) -> None:
    output = StringIO()
    errors = StringIO()
    with redirect_stdout(output), redirect_stderr(errors):
        status = vela_parser.main([str(arg) for arg in args])
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
    [subject] = re.findall(r"^Module (VelaPackage_[a-z0-9_]+)\.$", gallina, re.MULTILINE)
    [operation] = re.findall(r"^Definition (\w+_ReadScale)\b", gallina, re.MULTILINE)
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


def _kernel(directory: Path, arguments: list[str]) -> None:
    process = subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *arguments],
                             cwd=directory, check=False, capture_output=True, timeout=180)
    ensure(process.returncode == 0, f"{arguments}: {(process.stdout + process.stderr)[-3000:]!r}")


def _upgrade(workspace: Path, old: str, new: str, source: str) -> None:
    previous = workspace / "weights" / old
    current = workspace / "weights" / new
    shutil.copytree(previous, current)
    manifest = current / "vela-package.toml"
    manifest.write_text(manifest.read_text().replace(f'revision = "{old}"', f'revision = "{new}"'))
    (current / "Measure.vela").write_text(source)
    root = workspace / "scale" / "v1" / "vela-package.toml"
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

        source = (workspace / "weights" / "v1" / "Measure.vela").read_text()
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
        manifest = provider / "vela-package.toml"
        manifest.write_text(manifest.read_text().replace("[dependencies]", """
"Weights.First" = "First.vela"
"Weights.Second" = "Second.vela"

[dependencies]"""))
        for name, target, result in (("First", "bool", 5), ("Second", "Nat", 11)):
            (provider / f"{name}.vela").write_text(f"""module Weights.{name};
import Weights.Measure;
public impl Measured<{target}> {{ public definition Nat Measure({target} value) => {result}; }}
""")
        client = workspace / "scale" / "v1" / "Calibration.vela"
        original = client.read_text()
        bundle = workspace.parent / "bundle.json"
        imports = ["import Weights.First;", "import Weights.Second;"]
        for order in (imports, imports[::-1]):
            client.write_text(original.replace("import Weights.Measure;",
                                               "import Weights.Measure;\n" + "\n".join(order)) + """
public lemma ImportedReadings()
    ensures Measured.Measure(true) == 5
    ensures Measured.Measure(7) == 11
    proof { assert Measured.Measure(true) == 5; assert Measured.Measure(7) == 11; }
""")
            _command("build-package", workspace, _lock(workspace), "--output", bundle)
            _replay(workspace.parent, json.loads(bundle.read_bytes())["modules"])
        client.write_text(original)
        sibling = provider / "Second.vela"
        sibling.write_text(sibling.read_text().replace("Measured<Nat>", "Measured<bool>")
                           .replace("Measure(Nat value)", "Measure(bool value)"))
        _command("build-package", workspace, _lock(workspace), refusal="overlapping")
        sibling.write_text("module Weights.Second;")
        client.write_text(original + """
public record LocalWeight(Nat Units);
public impl Measured<LocalWeight> { public definition Nat Measure(LocalWeight x) => x.Units; }
""")
        _command("build-package", workspace, _lock(workspace), "--output", bundle)
        client.write_text(original + """
public impl Measured<Nat> { public definition Nat Measure(Nat value) => value; }
""")
        _command("build-package", workspace, _lock(workspace), refusal="must own")


def _opaque_provider_upgrade() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        workspace = _workspace(directory)
        provider = workspace / "weights" / "v1" / "Measure.vela"
        source = provider.read_text() + """
private definition Nat Chosen() => 3;
public Nat Capacity() ensures result >= 1 => Chosen();
"""
        provider.write_text(source)
        client = workspace / "scale" / "v1" / "Calibration.vela"
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


def cases() -> list[Case]:
    return [
        Case("independent locked client, kernel readings and label evolution", _client_upgrade, lane="toolchain"),
        Case("sibling instance coherence, declaration ownership and import order", _closure_coherence, lane="toolchain"),
        Case("locked client proof across opaque implementation and public law changes",
             _opaque_provider_upgrade, lane="toolchain"),
    ]
