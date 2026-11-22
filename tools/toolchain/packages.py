# SPDX-License-Identifier: Apache-2.0
"""Resolve and build the declared, offline mathematical package closure."""

import hashlib
import json
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from toolchain import parser
from toolchain.ast import MAX_SOURCE_BYTES
from toolchain.atomic import atomic_path
from toolchain.elaborate import FRONTEND_SOURCES, elaborate_package
from toolchain.elaborate_types import PackageScope
from toolchain.jsonutil import unique_object

type Object = dict[str, object]

MANIFEST = "vela-package.toml"
NAME = re.compile(r"[a-z][a-z0-9-]{0,63}")
REVISION = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
FILE_PART = re.compile(r"[A-Za-z0-9_-][A-Za-z0-9_.-]*")
MAX_PACKAGES = 64
MAX_FILES = 256
MAX_INPUT_BYTES = 1024 * 1024
MAX_CLOSURE_BYTES = 16 * MAX_INPUT_BYTES
MAX_GENERATED_BYTES = 32 * MAX_INPUT_BYTES

PRODUCER_INPUTS = (
    *(f"toolchain/{name}" for name in FRONTEND_SOURCES),
    "run.py", "pyproject.toml", "uv.lock", "opam/rocq.lock", "opam/sail.lock", "toolchain/atomic.py",
    "toolchain/cli/vela_parser.py", "toolchain/packages.py", "toolchain/commands.py", "toolchain/pyversion.py",
    "toolchain/toolenv.py", "toolchain/corpus.py", "toolchain/env.py", "toolchain/proofenv.py",
)


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _encode(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("ascii")


def _token(raw: object, pattern: re.Pattern[str], what: str) -> str:
    if not isinstance(raw, str) or not pattern.fullmatch(raw):
        raise ValueError(f"invalid package {what}: {raw!r}")
    return raw


def _object(raw: object, what: str) -> Object:
    if not isinstance(raw, dict):
        raise TypeError(f"expected {what} table")
    return cast("Object", raw)


def _read(path: Path, limit: int) -> bytes:
    if not path.is_file():
        raise ValueError(f"incomplete build: missing file {path}")
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise ValueError(f"package file exceeds {limit} bytes: {path}")
    return data


def _path(base: Path, name: object) -> Path:
    if not isinstance(name, str) or not all(FILE_PART.fullmatch(part) for part in name.split("/")):
        raise ValueError(f"invalid package-relative path: {name!r}")
    location = base / name
    if location.resolve() != location:
        raise ValueError(f"package path follows a filesystem alias: {name}")
    return location


def _producer(root: Path, compiled: parser.Build) -> Object:
    tools = root / "tools"
    sources = {name: _sha((tools / name).read_bytes()) for name in PRODUCER_INPUTS}
    return {"python": sys.version, "python_sha256": _sha(Path(sys.executable).read_bytes()),
            "frontend_sha256": _sha(_encode(sources)), "parser_inputs": compiled.receipt["inputs"],
            "parser_toolchain": compiled.receipt["toolchain"], "parser_sha256": _sha(compiled.executable.read_bytes())}


def _recheck_parser(root: Path, compiled: parser.Build) -> None:
    outputs = _object(compiled.receipt["generated_sha256"], "parser outputs")
    if (parser._inputs(root) != compiled.receipt["inputs"] or parser._toolchain(root) != compiled.receipt["toolchain"]
            or _sha(compiled.executable.read_bytes()) != outputs["vela-parser"]):
        raise ValueError("stale package inputs: parser sources, tools or generated executable changed")


@dataclass
class Closure:
    lock: Object
    sources: dict[str, bytes]
    scopes: dict[str, PackageScope]
    files: set[Path]


def resolve(workspace: Path, root_name: str, root_revision: str, producer: Object, *, locked: Object | None = None) -> Closure:
    workspace = workspace.resolve(strict=True)
    packages: dict[str, Object] = {}
    selected: dict[str, tuple[str, str]] = {}
    active: list[str] = []
    sources: dict[str, bytes] = {}
    scopes: dict[str, PackageScope] = {}
    files: set[Path] = set()
    total_bytes = 0
    pinned = _object(locked.get("packages"), "locked packages") if locked is not None else {}
    if locked is not None and _encode(locked.get("producer")) != _encode(producer):
        raise ValueError("stale package lock: compiler or parser changed")

    def visit(name: str, revision: str, required_by: str) -> None:
        nonlocal total_bytes
        _token(name, NAME, "name")
        _token(revision, REVISION, "revision")
        previous = selected.get(name)
        if previous is not None and revision != previous[0]:
            raise ValueError(f"incompatible revisions for {name}: {previous[1]} requires {previous[0]}, {required_by} requires {revision}")
        if name in active:
            raise ValueError("package cycle: " + " -> ".join([*active[active.index(name):], name]))
        if name in packages:
            return
        selected[name] = (revision, required_by)
        if len(selected) > MAX_PACKAGES:
            raise ValueError("package closure exceeds the package limit")
        base = _path(workspace, f"{name}/{revision}")
        path = _path(base, MANIFEST)
        row = _object(pinned.get(name), f"locked package {name}") if locked is not None else {}
        raw = _read(path, MAX_SOURCE_BYTES)
        manifest_digest = _sha(raw)
        if locked is not None and row.get("manifest_sha256") != manifest_digest:
            raise ValueError(f"stale package lock: manifest for {name}@{revision} changed")
        files.add(path)
        manifest = tomllib.loads(raw.decode("utf-8"))
        if (set(manifest) != {"name", "revision", "edition", "target", "modules", "dependencies", "inputs"}
                or (manifest["name"], manifest["revision"]) != (name, revision)
                or (manifest["edition"], manifest["target"]) != ("math-1", "rocq-gallina")):
            raise ValueError(f"unsupported manifest identity, fields, edition or target in {path}")
        dependencies = {key: _token(val, REVISION, "dependency revision")
                        for key, val in _object(manifest["dependencies"], "dependencies").items()}
        active.append(name)
        for dep, dep_revision in sorted(dependencies.items()):
            visit(dep, dep_revision, f"{name}@{revision}")
        active.pop()
        declared = _object(manifest["modules"], "modules")
        if not declared or not isinstance(manifest["inputs"], list):
            raise ValueError(f"package {name} needs declared modules and an input list")
        paths: dict[str, str | None] = {}
        for module, rel in sorted(declared.items()):
            _token(module, MODULE, "module name")
            if module == "Vela.Numerics" or module in sources:
                raise ValueError(f"duplicate or built-in module path {module}")
            if not isinstance(rel, str) or not rel.endswith(".vela") or rel in paths:
                raise ValueError(f"invalid or duplicate module path in {name}: {rel!r}")
            paths[rel] = module
        for item in manifest["inputs"]:
            if not isinstance(item, str) or item in paths or item == MANIFEST:
                raise ValueError(f"invalid or duplicate build input in {name}")
            paths[item] = None
        digests = {}
        for rel, declared_module in sorted(paths.items()):
            input_path = _path(base, rel)
            if len(files) >= MAX_FILES:
                raise ValueError("package closure exceeds the file limit")
            files.add(input_path)
            body = _read(input_path, MAX_SOURCE_BYTES if declared_module is not None else MAX_INPUT_BYTES)
            total_bytes += len(body)
            if total_bytes > MAX_CLOSURE_BYTES:
                raise ValueError("package closure exceeds the input byte budget")
            digests[rel] = _sha(body)
            if declared_module is not None:
                sources[declared_module] = body
        entry: Object = {"revision": revision, "manifest_sha256": manifest_digest, "files": digests,
                         "dependencies": dependencies, "modules": declared, "edition": "math-1", "target": "rocq-gallina"}
        instance = _sha(_encode([name, entry, {dep: packages[dep]["instance"] for dep in dependencies}]))
        entry["instance"] = instance
        if locked is not None and _encode(row) != _encode(entry):
            raise ValueError(f"stale package lock: inputs for {name}@{revision} changed")
        packages[name] = entry
        visible = set(declared)
        for dep in dependencies:
            visible.update(_object(packages[dep]["modules"], "dependency modules"))
        for module in declared:
            scopes[module] = PackageScope(instance, frozenset(visible))

    visit(root_name, root_revision, "workspace root")
    lock: Object = {"schema": 1, "root": [root_name, root_revision], "packages": packages, "producer": producer}
    if locked is not None and _encode(locked) != _encode(lock):
        raise ValueError("stale or malformed package lock inventory")
    return Closure(lock, sources, scopes, files)


def _publish(destination: Path, value: Object, protected: set[Path]) -> None:
    if destination.resolve() in protected or (destination.exists() and any(destination.samefile(path) for path in protected)):
        raise ValueError("package output aliases a build input")
    with atomic_path(destination) as pending:
        pending.write_bytes(_encode(value) + b"\n")


def lock_package(root: Path, workspace: Path, name: str, revision: str, destination: Path) -> Object:
    with parser.cached_build(root) as compiled:
        closure = resolve(workspace, name, revision, _producer(root, compiled))
        _recheck_parser(root, compiled)
        resolve(workspace, name, revision, _producer(root, compiled), locked=closure.lock)
    _publish(destination, closure.lock, closure.files)
    return {"status": "locked", "lock_sha256": _sha(_encode(closure.lock) + b"\n"),
            "packages": list(_object(closure.lock["packages"], "packages"))}


def build_package(root: Path, workspace: Path, lock_path: Path, destination: Path | None) -> Object:
    raw = _read(lock_path, MAX_INPUT_BYTES)
    lock = _object(json.loads(raw, object_pairs_hook=unique_object), "lock")
    selection = lock.get("root")
    if not isinstance(selection, list) or len(selection) != 2:
        raise ValueError("invalid locked package root")
    name, revision = _token(selection[0], NAME, "name"), _token(selection[1], REVISION, "revision")
    with parser.cached_build(root) as compiled:
        closure = resolve(workspace, name, revision, _producer(root, compiled), locked=lock)
        modules = []
        for module, source in closure.sources.items():
            parsed = parser.parse_source(compiled, source, surface=True)
            ast = _object(parsed["ast"], "parsed source")
            if _object(ast["name"], "module name").get("text") != module:
                raise ValueError(f"manifest module {module} differs from the source declaration")
            modules.append((source, parsed))
        outputs = elaborate_package(modules, scopes=closure.scopes, require_word_proofs=True,
                                    output_limit=MAX_GENERATED_BYTES)
        _recheck_parser(root, compiled)
        resolve(workspace, name, revision, _producer(root, compiled), locked=lock)
        if raw != _read(lock_path, MAX_INPUT_BYTES):
            raise ValueError("package lock changed during the build")
    binding = _sha(raw)
    if destination is not None:
        _publish(destination, {"schema": 1, "lock_sha256": binding,
                               "modules": {module: result.gallina for module, result in outputs.items()}},
                 closure.files | {lock_path.resolve()})
    return {"status": "elaborated", "lock_sha256": binding, "build_order": list(outputs),
            "modules": {module: {"instance": closure.scopes[module].instance, "source_sha256": output.source_sha256,
                                 "gallina_sha256": _sha(output.gallina.encode())} for module, output in outputs.items()}}
