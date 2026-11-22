# SPDX-License-Identifier: Apache-2.0
"""Independent graph, publication and cancellation controls for the BSP projection."""

import hashlib
import json
import shutil
import threading
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import bsp, packages


def _graph(directory: Path) -> bsp.Workspace:
    root = Path(__file__).resolve().parents[2]
    workspace = directory / "project with spaces"
    shutil.copytree(root / "examples/packages", workspace)
    locks = []
    for name in ("scale", "weights"):
        closure = packages.resolve(workspace, name, "v1", {})
        lock = directory / f"{name}.lock"
        lock.write_text(json.dumps(closure.lock), encoding="utf-8")
        locks.append(lock)
    return bsp.Workspace(root, workspace, locks, directory)


def _targets_and_changes() -> None:
    with TemporaryDirectory() as temporary, patch.object(bsp.parser, "cached_build"), patch.object(
        packages, "_producer", return_value={},
    ):
        graph = _graph(Path(temporary))
        # Compare against the independently authored scale/weights manifests.
        targets = graph.targets()["targets"]
        if not isinstance(targets, list) or len(targets) != 3:
            raise AssertionError("lost locked configuration")
        root, provider, standalone = (next(item for item in targets if item["id"]["uri"] == uri) for uri in
                                      (graph.configs[0].target("scale"), graph.configs[0].target("weights"),
                                       graph.configs[1].target("weights")))
        ensure(root["dependencies"] == [provider["id"]] and standalone["id"] != provider["id"],
               "dependencies or configuration identities crossed locks")
        ensure(not provider["capabilities"]["canCompile"] and standalone["capabilities"]["canCompile"],
               "advertised a build for a target with no batch entry point")
        source = graph.workspace / "weights/v1/Measure.vela"
        source.write_bytes(source.read_bytes() + b"\n")
        for query in (graph.targets, lambda: graph.sources({"targets": [root["id"]]})):
            try:
                query()
            except ValueError as error:
                ensure("stale package lock" in str(error), "wrong stale-graph refusal")
            else:
                raise AssertionError("stale package graph remained available")


def _publication() -> None:
    with TemporaryDirectory() as temporary:
        graph = _graph(Path(temporary))
        config = graph.configs[1]
        closure = packages.resolve(graph.workspace, "weights", "v1", {})
        source = closure.sources["Weights.Measure"]
        gold = "Module Compiled. End Compiled.\n"
        digest = hashlib.sha256(gold.encode()).hexdigest()
        receipt = {"instance": closure.scopes["Weights.Measure"].instance,
                   "source_sha256": hashlib.sha256(source).hexdigest(), "gallina_sha256": digest}
        batch: bsp.Object = {"status": "elaborated", "lock_sha256": config.digest,
                             "build_order": ["Weights.Measure"], "modules": {"Weights.Measure": receipt}}
        staging = Path(temporary) / "staging"
        staging.mkdir()
        path = staging / "bundle.json"
        bundle = {"schema": 1, "lock_sha256": config.digest, "modules": {"Weights.Measure": gold}}
        path.write_text(json.dumps(bundle), encoding="utf-8")
        data, outputs = graph.prepare_outputs(config, staging, batch)
        ensure(data["batch"] == batch and outputs == {"Weights.Measure": digest}, "lost batch verdict")
        ensure((staging / "Weights.Measure.v").read_bytes() == gold.encode(), "altered generated source bytes")
        for order in ([], ["Weights.Measure", "Weights.Measure"], ["Other"]):
            try:
                graph.prepare_outputs(config, staging, {**batch, "build_order": order})
            except ValueError as error:
                ensure("order" in str(error), "invalid order failed at the wrong check")
            else:
                raise AssertionError("incomplete or duplicate batch order passed")
        for damaged in ({"Weights.Measure": gold + " "}, {}, {"Extra": gold, "Weights.Measure": gold}):
            path.write_text(json.dumps({**bundle, "modules": damaged}), encoding="utf-8")
            try:
                graph.prepare_outputs(config, staging, batch)
            except ValueError:
                pass
            else:
                raise AssertionError("corrupted or incomplete bundle was eligible for publication")


def _cancel_and_join() -> None:
    with TemporaryDirectory() as temporary:
        graph = _graph(Path(temporary))
        target = {"uri": graph.configs[0].target("scale")}
        replies: list[bsp.Object] = []
        server = bsp.Server(graph, replies.append)
        server.phase = "ready"
        started, release = threading.Event(), threading.Event()

        def running(_graph: bsp.Workspace, _config: bsp.Config, _directory: Path,
                    cancel: threading.Event) -> tuple[int, bsp.Object]:
            started.set()
            ensure(release.wait(3), "starved build worker")
            ensure(cancel.is_set(), "cancel did not reach running worker")
            return 1, {"status": "elaborated"}

        with patch.object(bsp, "_run_batch", running):
            server.compile(4, {"targets": [target], "originId": "client"})
            ensure(started.wait(3), "batch worker did not start")
            server.handle({"jsonrpc": "2.0", "method": "$/cancelRequest", "params": {"id": "4"}})
            ensure(server.active is not None and not server.active[1].is_set(), "cancelled the wrong request ID")
            server.handle({"jsonrpc": "2.0", "method": "$/cancelRequest", "params": {"id": 4}})
            release.set()
            server.stop()
        ensure(len(replies) == 1 and bsp._object(replies[0]["result"]).get("statusCode") == 3
               and not graph.outputs, "cancelled worker published artifacts or succeeded")


def _malformed_lock() -> None:
    with TemporaryDirectory() as temporary:
        graph = _graph(Path(temporary))
        del graph.configs[0].lock["packages"]
        replies: list[bsp.Object] = []
        server = bsp.Server(graph, replies.append)
        server.phase = "ready"
        for method in ("buildTarget/sources", "buildTarget/compile"):
            server.handle({"jsonrpc": "2.0", "id": 1, "method": method,
                           "params": {"targets": [{"uri": graph.configs[0].target("scale")}]}})
            ensure("error" in replies[-1] and server.active is None, "invalid lock escaped request handling")
        server.handle({"jsonrpc": "2.0", "id": 2, "method": "build/shutdown"})
        ensure(replies[-1] == {"jsonrpc": "2.0", "id": 2, "result": None}, "malformed lock stopped BSP")


def cases() -> list[Case]:
    return [Case("BSP graphs and sources bind exact package configurations", _targets_and_changes),
            Case("BSP refuses a malformed graph on the first target request", _malformed_lock),
            Case("BSP artifact handoff checks the exact batch module inventory", _publication),
            Case("BSP cancellation wins before artifact publication", _cancel_and_join)]
