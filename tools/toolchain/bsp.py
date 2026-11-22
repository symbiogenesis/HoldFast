# SPDX-License-Identifier: Apache-2.0
"""Build Server Protocol projection of the offline mathematical package graph."""

import contextlib
import hashlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, cast

from toolchain import packages, parser
from toolchain.jsonutil import unique_object
from toolchain.protocol_json import MAX_BODY_BYTES, decode_message, encode_message, read_frame

type Object = dict[str, object]
type Send = Callable[[Object], None]
VERSION = "2.1.1"
MAX_CONFIGS = 8
BUILD_SECONDS = 180
# A JSON string can encode each input byte using a six-byte Unicode escape.
MAX_BUNDLE = 6 * packages.MAX_GENERATED_BYTES + MAX_BODY_BYTES


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _object(value: object) -> Object:
    if not isinstance(value, dict):
        raise TypeError("expected an object")
    return cast("Object", value)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Config:
    path: Path
    digest: str
    name: str
    revision: str
    lock: Object

    def target(self, name: str) -> str:
        return f"vela-build:{self.digest}/{name}"

    def check(self, workspace: Path, producer: Object) -> None:
        if _sha(packages._read(self.path, packages.MAX_INPUT_BYTES)) != self.digest:
            raise ValueError("package lock changed; reopen the workspace")
        packages.resolve(workspace, self.name, self.revision, producer, locked=self.lock)


class Workspace:
    def __init__(self, root: Path, workspace: Path, locks: list[Path], store: Path) -> None:
        self.root = root
        self.workspace = workspace.resolve(strict=True)
        self.store = store
        self.configs: list[Config] = []
        self.outputs: dict[str, dict[str, str]] = {}
        if not 1 <= len(locks) <= MAX_CONFIGS:
            raise ValueError("supply one to eight package locks")
        for path in locks:
            raw, lock, name, revision = packages.read_lock(path)
            config = Config(path.resolve(strict=True), _sha(raw), name, revision, lock)
            if any(config.digest == prior.digest for prior in self.configs):
                raise ValueError("duplicate package configuration")
            self.configs.append(config)

    def check(self, configs: list[Config]) -> None:
        with parser.cached_build(self.root) as compiled:
            producer = packages._producer(self.root, compiled)
            for config in configs:
                config.check(self.workspace, producer)

    def targets(self) -> Object:
        self.check(self.configs)
        targets: list[Object] = []
        for config in self.configs:
            for name, value in _object(config.lock["packages"]).items():
                row = _object(value)
                directory = self.workspace / name / str(row["revision"])
                targets.append({
                    "id": {"uri": config.target(name)}, "displayName": f"{name}@{row['revision']}",
                    "baseDirectory": directory.as_uri(), "tags": ["library"], "languageIds": ["vela"],
                    "dependencies": [{"uri": config.target(dep)} for dep in sorted(_object(row["dependencies"]))],
                    "capabilities": {"canCompile": name == config.name},
                    "dataKind": "vela-locked-package",
                    "data": {"lockUri": config.path.as_uri(), "lockSha256": config.digest,
                             "edition": row["edition"], "target": row["target"], "instance": row["instance"],
                             "inputs": row["files"], "producer": config.lock["producer"]},
                })
        return {"targets": targets}

    def select(self, params: Object) -> list[tuple[Config, str]]:
        identifiers = params.get("targets")
        if not isinstance(identifiers, list) or not 1 <= len(identifiers) <= MAX_CONFIGS * packages.MAX_PACKAGES:
            raise ValueError("expected a bounded, nonempty target selection")
        available = {config.target(name): (config, name) for config in self.configs
                     for name in _object(config.lock["packages"])}
        selected = []
        seen: set[str] = set()
        for target in identifiers:
            uri = _object(target).get("uri")
            if not isinstance(uri, str) or uri not in available or uri in seen:
                raise ValueError("unknown, stale or duplicate build target")
            seen.add(uri)
            selected.append(available[uri])
        return selected

    def sources(self, params: Object) -> Object:
        selected = self.select(params)
        self.check(list({config.digest: config for config, _ in selected}.values()))
        items: list[Object] = []
        for config, name in selected:
            row = _object(_object(config.lock["packages"])[name])
            base = self.workspace / name / str(row["revision"])
            files: list[Object] = []
            generated = self.outputs.get(config.digest, {})
            for module, relative in _object(row["modules"]).items():
                files.append({"uri": (base / str(relative)).as_uri(), "kind": 1, "generated": False})
                if module in generated:
                    path = self.store / config.digest / f"{module}.v"
                    if _sha(packages._read(path, packages.MAX_GENERATED_BYTES)) != generated[module]:
                        raise ValueError("generated source changed after compilation")
                    files.append({"uri": path.as_uri(), "kind": 1, "generated": True})
            items.append({"target": {"uri": config.target(name)}, "sources": files, "roots": [base.as_uri()]})
        return {"items": items}

    def prepare_outputs(self, config: Config, directory: Path, batch: Object) -> tuple[Object, dict[str, str]]:
        raw = packages._read(directory / "bundle.json", MAX_BUNDLE)
        bundle = _object(json.loads(raw, object_pairs_hook=unique_object))
        if (batch.get("status") != "elaborated" or batch.get("lock_sha256") != config.digest
                or bundle.get("schema") != 1 or bundle.get("lock_sha256") != config.digest):
            raise ValueError("batch verdict does not match the selected lock")
        outputs = _object(bundle.get("modules"))
        receipts = _object(batch.get("modules"))
        modules = {}
        for value in _object(config.lock["packages"]).values():
            row = _object(value)
            for module, rel in _object(row["modules"]).items():
                modules[module] = (row["instance"], _object(row["files"])[str(rel)])
        if receipts.keys() != modules.keys() or outputs.keys() != modules.keys():
            raise ValueError("incomplete batch module inventory")
        digests = {}
        for module, (instance, source_hash) in modules.items():
            gallina = outputs[module]
            if not isinstance(gallina, str):
                raise TypeError("invalid Gallina output")
            data = gallina.encode("utf-8")
            digest = _sha(data)
            if receipts[module] != {"instance": instance, "source_sha256": source_hash, "gallina_sha256": digest}:
                raise ValueError("batch output does not match the locked module and artifact identities")
            (directory / f"{module}.v").write_bytes(data)
            digests[module] = digest
        destination = self.store / config.digest
        if destination.exists():
            for path in directory.iterdir():
                if path.read_bytes() != packages._read(destination / path.name, MAX_BUNDLE):
                    raise ValueError("previously published build output changed")
        return {"batch": batch, "bundleUri": (destination / "bundle.json").as_uri(),
                "bundleSha256": _sha(raw)}, digests


def _run_batch(graph: Workspace, config: Config, directory: Path, cancel: threading.Event) -> tuple[int, Object]:
    command = [sys.executable, str(graph.root / "tools/run.py"), "vela-parser", "build-package",
               str(graph.workspace), str(config.path), "--output", str(directory / "bundle.json")]
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr, subprocess.Popen(
        command, cwd=graph.root, stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
        start_new_session=True,
    ) as process:
        deadline = time.monotonic() + BUILD_SECONDS
        try:
            while process.poll() is None:
                if cancel.wait(0.05):
                    return 3, {"message": "build cancelled"}
                if time.monotonic() >= deadline:
                    raise ValueError("batch build exceeded its time budget")
        finally:
            if process.poll() is None:
                if sys.platform == "win32":
                    process.kill()
                else:
                    with contextlib.suppress(ProcessLookupError):
                        os.killpg(process.pid, signal.SIGKILL)
                process.wait(timeout=10)
        if process.returncode:
            stderr.seek(0)
            return 2, {"exitCode": process.returncode, "message": stderr.read(4096).decode("utf-8", "replace").strip()}
        stdout.seek(0)
        return 1, decode_message(stdout.read(MAX_BODY_BYTES + 1))


class Server:
    def __init__(self, graph: Workspace, send: Send) -> None:
        self.graph, self.send = graph, send
        self.phase = "new"
        self.lock = threading.Lock()
        self.active: tuple[object, threading.Event] | None = None
        self.worker: threading.Thread | None = None

    def stop(self) -> None:
        with self.lock:
            if self.active:
                self.active[1].set()
        if self.worker is not None:
            self.worker.join()

    def compile(self, request: object, params: Object) -> None:
        selected = self.graph.select(params)
        if len(selected) != 1 or selected[0][0].name != selected[0][1] or params.get("arguments"):
            raise ValueError("compile one configured root with its exact locked arguments")
        origin = params.get("originId")
        if origin is not None and (not isinstance(origin, str) or len(origin) > 1024):
            raise ValueError("invalid build origin")
        config = selected[0][0]
        cancelled = threading.Event()

        def work() -> None:
            result: Object = {"dataKind": "vela-batch-build"}
            if origin is not None:
                result["originId"] = origin
            try:
                with tempfile.TemporaryDirectory(dir=self.graph.store) as temporary:
                    staging = Path(temporary)
                    status, data = _run_batch(self.graph, config, staging, cancelled)
                    digests: dict[str, str] = {}
                    if status == 1 and not cancelled.is_set():
                        data, digests = self.graph.prepare_outputs(config, staging, data)
                        self.graph.check([config])
                    with self.lock:
                        if cancelled.is_set():
                            status, data = 3, {"message": "build cancelled"}
                        elif status == 1:
                            destination = self.graph.store / config.digest
                            if not destination.exists():
                                staging.rename(destination)
                            self.graph.outputs[config.digest] = digests
                        result.update(statusCode=status, data=data)
                        self.send({"jsonrpc": "2.0", "id": request, "result": result})
                        self.active = None
            except (OSError, RuntimeError, TypeError, ValueError, subprocess.SubprocessError) as error:
                with self.lock:
                    result.update(statusCode=3 if cancelled.is_set() else 2, data={"message": str(error)[:4096]})
                    self.send({"jsonrpc": "2.0", "id": request, "result": result})
                    self.active = None

        with self.lock:
            if self.active:
                raise ValueError("another build is active")
            self.active = (request, cancelled)
            self.worker = threading.Thread(target=work)
            self.worker.start()

    def handle(self, message: Object) -> int | None:
        method, request = message.get("method"), message.get("id")
        call = "id" in message
        if message.get("jsonrpc") != "2.0" or not isinstance(method, str) or (call and type(request) not in (int, str)):
            self.error(None, -32600, "invalid request")
            return None
        try:
            params = _object(message.get("params", {}))
            if method == "build/exit" and not call:
                return 0 if self.phase == "shutdown" else 1
            if method == "$/cancelRequest" and not call:
                with self.lock:
                    if self.active and type(params.get("id")) is type(self.active[0]) and params.get("id") == self.active[0]:
                        self.active[1].set()
                return None
            result = None
            if method == "build/initialize" and call and self.phase == "new":
                _require(params.get("bspVersion") == VERSION and params.get("rootUri") == self.graph.workspace.as_uri(),
                         "unsupported BSP version or mismatched workspace root")
                result = {"displayName": "Vela locked packages", "version": "1", "bspVersion": VERSION,
                          "capabilities": {"compileProvider": {"languageIds": ["vela"]}}}
                self.phase = "initializing"
            elif method == "build/initialized" and not call and self.phase == "initializing":
                self.phase = "ready"
            elif self.phase != "ready":
                if call:
                    self.error(request, -32002, "build server is not ready")
                return None
            elif method == "build/shutdown" and call:
                self.stop()
                self.phase = "shutdown"
            elif method == "buildTarget/compile" and call:
                self.compile(request, params)
                return None
            elif method in {"workspace/buildTargets", "buildTarget/sources"} and call:
                with self.lock:
                    _require(self.active is None, "build in progress; retry the graph query after completion")
                result = self.graph.targets() if method == "workspace/buildTargets" else self.graph.sources(params)
            else:
                if call:
                    self.error(request, -32601, "method not supported")
                return None
            if call:
                self.send({"jsonrpc": "2.0", "id": request, "result": result})
        except (OSError, RuntimeError, ValueError, TypeError, subprocess.SubprocessError) as error:
            if call:
                self.error(request, -32602, str(error)[:4096])
        return None

    def error(self, request: object, code: int, message: str) -> None:
        self.send({"jsonrpc": "2.0", "id": request, "error": {"code": code, "message": message}})


def serve(root: Path, workspace: Path, locks: list[Path], source: BinaryIO, output: BinaryIO) -> int:
    write_lock = threading.Lock()

    def send(message: Object) -> None:
        frame = encode_message(message)
        with write_lock:
            output.write(frame)
            output.flush()

    with tempfile.TemporaryDirectory(prefix="vela-bsp-") as tmp:
        server = Server(Workspace(root, workspace, locks, Path(tmp)), send)
        try:
            while (frame := read_frame(source)) is not None:
                code = server.handle(decode_message(frame))
                if code is not None:
                    return code
        finally:
            server.stop()
    return 1
