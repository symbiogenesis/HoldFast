# SPDX-License-Identifier: Apache-2.0
"""Locked closure controls independent of the native parser and its cache."""

import json
import shutil
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import packages, parser


def _write(workspace: Path, name: str, revision: str, deps: dict[str, str], module: str) -> Path:
    directory = workspace / name / revision
    directory.mkdir(parents=True)
    (directory / "module.vela").write_text(f"module {module};\n", encoding="utf-8")
    (directory / "target.cfg").write_bytes(b"stable-build-input")
    (directory / packages.MANIFEST).write_text(
        f'name = "{name}"\nrevision = "{revision}"\nedition = "math-1"\ntarget = "rocq-gallina"\n'
        f'inputs = ["target.cfg"]\n[modules]\n"{module}" = "module.vela"\n[dependencies]\n'
        + "".join(f'{key} = "{value}"\n' for key, value in deps.items()), encoding="utf-8")
    return directory


def _refuses(workspace: Path, message: str, *, lock: packages.Object | None = None) -> str:
    try:
        packages.resolve(workspace, "main", "v1", {"frontend": "fixed"}, locked=lock)
    except ValueError as error:
        ensure(message in str(error), f"wrong package refusal: {error}")
        return str(error)
    raise AssertionError(f"locked build accepted {message}")


def _locked_inputs() -> None:
    with TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        leaf = _write(workspace, "lib", "v1", {}, "Lib")
        top = _write(workspace, "main", "v1", {"lib": "v1"}, "Main")
        producer: packages.Object = {"frontend": "fixed"}
        first = packages.resolve(workspace, "main", "v1", producer)
        ensure(list(first.sources) == ["Lib", "Main"], "unexpected source dependency order")
        ensure(first.scopes["Lib"].modules == {"Lib"} and first.scopes["Main"].modules == {"Lib", "Main"},
               "package scopes did not respect the directed graph")
        (top / "ambient.vela").write_bytes(b"unused")
        lock = json.loads(json.dumps(first.lock))
        packages.resolve(workspace, "main", "v1", producer, locked=lock)
        copy = workspace / "elsewhere"
        for name in ("main", "lib"):
            shutil.copytree(workspace / name, copy / name)
        ensure(packages.resolve(copy, "main", "v1", producer, locked=lock).lock == lock,
               "relocation changed the exact package closure")
        for path in (leaf / "module.vela", leaf / "target.cfg", top / packages.MANIFEST):
            original = path.read_bytes()
            path.write_bytes(original + b"\n")
            _refuses(workspace, "stale package lock", lock=lock)
            path.write_bytes(original)
        lock["unexpected"] = True
        _refuses(workspace, "lock inventory", lock=lock)
        del lock["unexpected"]
        lock["producer"] = {"frontend": "changed"}
        _refuses(workspace, "compiler or parser changed", lock=lock)
        lock["producer"] = producer
        (leaf / "target.cfg").unlink()
        _refuses(workspace, "incomplete build: missing file", lock=lock)


def _diamond_and_cycle() -> None:
    with TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        _write(workspace, "main", "v1", {"left": "v1", "right": "v1"}, "Main")
        _write(workspace, "left", "v1", {"base": "v1"}, "Left")
        right = _write(workspace, "right", "v1", {"base": "v2"}, "Right")
        _write(workspace, "base", "v1", {}, "Base")
        reason = _refuses(workspace, "incompatible revisions for base")
        ensure("left@v1 requires v1" in reason and "right@v1 requires v2" in reason,
               "diamond diagnostic lost one of the two requirements")
        manifest = right / packages.MANIFEST
        contents = manifest.read_text(encoding="utf-8")
        manifest.write_text(contents.replace('base = "v2"', 'base = "v1"'), encoding="utf-8")
        valid = packages.resolve(workspace, "main", "v1", {})
        ensure(list(valid.sources) == ["Base", "Left", "Right", "Main"], "diamond rebuilt a dependency twice")
        ensure("Base" not in valid.scopes["Main"].modules, "diamond exposed a transitive import")
        manifest.write_text(contents.replace('base = "v2"', 'main = "v1"'), encoding="utf-8")
        _refuses(workspace, "main -> right -> main")
        manifest.write_text(contents.replace('base = "v2"', 'absent = "v1"'), encoding="utf-8")
        _refuses(workspace, "missing file")


def _declared_files_and_module_owners() -> None:
    with TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        _write(workspace, "lib", "v1", {}, "Lib")
        top = _write(workspace, "main", "v1", {"lib": "v1"}, "Lib")
        _refuses(workspace, "duplicate or built-in module path Lib")
        manifest = top / packages.MANIFEST
        text = manifest.read_text(encoding="utf-8").replace('"Lib"', '"Main"')
        for src, expected in (("../sibling.vela", "package-relative path"), ("C:/lib.vela", "package-relative path"),
                              ("unlisted.vela", "missing file")):
            manifest.write_text(text.replace("module.vela", src), encoding="utf-8")
            _refuses(workspace, expected)
        manifest.write_text(text.replace("rocq-gallina", "another-target"), encoding="utf-8")
        _refuses(workspace, "edition or target")


def _bound_producer() -> None:
    with TemporaryDirectory() as temporary:
        root = Path(temporary)
        tools = root / "tools"
        for name in packages.PRODUCER_INPUTS:
            path = tools / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(name.encode())
        binary = root / "parser"
        binary.write_bytes(b"fixture")
        compiled = parser.Build(root, binary, {"inputs": {}, "toolchain": {}})
        original = packages._producer(root, compiled)
        (tools / "toolchain" / "scratch.py").write_bytes(b"undeclared editor scratch file")
        ensure(packages._producer(root, compiled) == original, "unrelated helper invalidated the package lock")
        (tools / "toolchain" / "elaborate_solver.py").write_bytes(b"new arithmetic")
        ensure(packages._producer(root, compiled) != original, "changed semantic implementation retained the lock")
        compiled.receipt["generated_sha256"] = {"vela-parser": original["parser_sha256"]}
        with patch.object(parser, "_inputs", return_value={}) as inputs, patch.object(parser, "_toolchain", return_value={}):
            packages._recheck_parser(root, compiled)
            inputs.return_value = {"parser.mly": "updated grammar"}
            try:
                packages._recheck_parser(root, compiled)
            except ValueError as error:
                ensure("parser sources" in str(error), "late parser change reached an unrelated refusal")
            else:
                raise AssertionError("published a lock for a grammar which changed during the build")


def cases() -> list[Case]:
    return [Case("bound-relocatable-closure-and-file-invalidation", _locked_inputs),
            Case("package-diamonds-and-cycle-paths", _diamond_and_cycle),
            Case("distinct-module-owners-and-explicit-build-files", _declared_files_and_module_owners),
            Case("explicit-producer-file-closure", _bound_producer)]
