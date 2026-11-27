# SPDX-License-Identifier: Apache-2.0
"""Locked closure controls independent of the native parser and its cache."""

import hashlib
import json
import shutil
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from tests.harness import Case, ensure, raises
from toolchain import packages, parser


def _write(workspace: Path, name: str, revision: str, deps: dict[str, str], module: str) -> Path:
    directory = workspace / name / revision
    directory.mkdir(parents=True)
    (directory / "module.hf").write_text(f"module {module};\n", encoding="utf-8")
    (directory / "target.cfg").write_bytes(b"stable-build-input")
    (directory / packages.MANIFEST).write_text(
        f'name = "{name}"\nrevision = "{revision}"\nedition = "math-2"\ntarget = "rocq-gallina"\n'
        f'inputs = ["target.cfg"]\n[modules]\n"{module}" = "module.hf"\n[dependencies]\n'
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
        (top / "ambient.hf").write_bytes(b"unused")
        lock = json.loads(json.dumps(first.lock))
        packages.resolve(workspace, "main", "v1", producer, locked=lock)
        copy = workspace / "elsewhere"
        for name in ("main", "lib"):
            shutil.copytree(workspace / name, copy / name)
        ensure(packages.resolve(copy, "main", "v1", producer, locked=lock).lock == lock,
               "relocation changed the exact package closure")
        for path in (leaf / "module.hf", leaf / "target.cfg", top / packages.MANIFEST):
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
        for src, expected in (("../sibling.hf", "package-relative path"), ("C:/lib.hf", "package-relative path"),
                              ("unlisted.hf", "missing file")):
            manifest.write_text(text.replace("module.hf", src), encoding="utf-8")
            _refuses(workspace, expected)
        manifest.write_text(text.replace("rocq-gallina", "another-target"), encoding="utf-8")
        _refuses(workspace, "edition or target")


def _bound_producer() -> None:
    with TemporaryDirectory() as temporary, patch.object(parser, "bytecode_interpreter") as interpreter:
        root = Path(temporary)
        tools = root / "tools"
        for name in packages.PRODUCER_INPUTS:
            path = tools / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(name.encode())
        binary = root / "parser"
        binary.write_bytes(b"fixture")
        runtime = root / "runtime"
        runtime.write_bytes(b"selected OCaml runtime")
        interpreter.return_value = runtime
        digest = hashlib.sha256(runtime.read_bytes()).hexdigest()
        toolchain = {"binary_sha256": {"ocamlrun": digest}}
        compiled = parser.Build(root, binary, {"inputs": {}, "toolchain": toolchain})
        original = packages._producer(root, compiled)
        (tools / "toolchain" / "scratch.py").write_bytes(b"undeclared editor scratch file")
        ensure(packages._producer(root, compiled) == original, "unrelated helper invalidated the package lock")
        (tools / "toolchain" / "elaborate_solver.py").write_bytes(b"new arithmetic")
        ensure(packages._producer(root, compiled) != original, "changed semantic implementation retained the lock")
        compiled.receipt["generated_sha256"] = {"holdfast-parser": original["parser_sha256"]}
        with patch.object(parser, "_inputs", return_value={}) as inputs, patch.object(parser, "_toolchain", return_value=toolchain):
            packages._recheck_parser(root, compiled)
            inputs.return_value = {"parser.mly": "updated grammar"}
            with raises(ValueError,
                        msg="published a lock for a grammar which changed during the build") as raised:
                packages._recheck_parser(root, compiled)
            ensure("parser sources" in str(raised.exception), "late parser change reached an unrelated refusal")
        runtime.write_bytes(b"changed bytecode interpreter")
        with raises(ValueError,
                    msg="package lock accepted different runtime bytes with the original parser bytecode") as raised:
            packages._producer(root, compiled)
        ensure("interpreter differs" in str(raised.exception), "wrong runtime-mismatch refusal")


def _package_editions() -> None:
    with TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        _write(workspace, "lib", "v1", {}, "Lib")
        manifest = _write(workspace, "main", "v1", {"lib": "v1"}, "Main") / packages.MANIFEST
        current = manifest.read_text()
        producer: packages.Object = {"frontend": "fixed"}
        resolved = packages.resolve(workspace, "main", "v1", producer)
        ensure(resolved.scopes["Main"].edition == "math-2" and resolved.scopes["Lib"].edition == "math-2",
               "resolved package closure lost math-2 edition")
        packages.resolve(workspace, "main", "v1", producer, locked=resolved.lock)
        for bad_edition in ("math-1", "unknown"):
            manifest.write_text(current.replace("math-2", bad_edition))
            _refuses(workspace, "stale package lock", lock=resolved.lock)
            _refuses(workspace, "unsupported manifest")


def cases() -> list[Case]:
    return [Case("bound-relocatable-closure-and-file-invalidation", _locked_inputs),
            Case("edition-selected-per-package-and-bound-in-lock", _package_editions),
            Case("package-diamonds-and-cycle-paths", _diamond_and_cycle),
            Case("distinct-module-owners-and-explicit-build-files", _declared_files_and_module_owners),
            Case("explicit-producer-file-closure", _bound_producer)]
