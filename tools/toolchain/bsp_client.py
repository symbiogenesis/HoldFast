# SPDX-License-Identifier: Apache-2.0
"""Exercise the locked mathematical build through the pinned Neovim BSP client."""

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from toolchain import lsp_clients, packages
from toolchain.hashing import file_sha256

REVISION = "42f77554d1242b71174da0216e1d29705da7b9d0"
PLUGIN = lsp_clients.ArchivePin(
    url=f"https://codeload.github.com/616b2f/bsp.nvim/zip/{REVISION}",
    filename=f"bsp.nvim-{REVISION}.zip",
    archive_sha256="00b786de9cb17cce036d54a391b61969f416dc39b2e5ddafb565de58165ff11d",
    prefix=f"bsp.nvim-{REVISION}",
    executable="lua/bsp.lua",
    required_sha256={
        "lua/bsp.lua": "b08832ac3b3c0d0ea524c59debd04d721243c6db343de8e56074f71a7a97c84b",
        "LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    },
)

SESSION = r"""
local cfg = vim.json.decode(table.concat(vim.fn.readfile(vim.env.VELA_BSP_CASE), "\n"))
vim.opt.runtimepath:prepend(cfg.plugin)
local bsp = require("bsp")
local exited, version
local id = assert(bsp.start_client({
    name = "vela", root_dir = cfg.workspace, cmd = cfg.command, cmd_cwd = cfg.root,
    capabilities = {languageIds = {"vela"}},
    on_init = function(_, result) version = result.bspVersion end,
    on_exit = function(code) exited = code end,
}))
local client = assert(bsp.get_client_by_id(id))
local function wait(check, reason)
    assert(vim.wait(90000, check, 20), reason)
end
local function call(method, params)
    local reply = assert(client.request_sync(method, params, 90000))
    assert(not reply.err, vim.inspect(reply.err))
    return assert(reply.result)
end
local function contents(uri)
    local file = assert(io.open(vim.uri_to_fname(uri), "rb"))
    local data = file:read("*a")
    file:close()
    return data
end
wait(function() return #client.sources > 0 end, "bsp.nvim never loaded project sources")
assert(version == "2.1.1")
local observed = { targets = client.build_targets, sources = client.sources, version = version }
local target = { uri = cfg.target }
local params = {targets = {target}, originId = "qualification"}
local built = call("buildTarget/compile", params)
assert(built.statusCode == 1 and built.originId == params.originId, vim.inspect(built))
observed.batch = built.data.batch
observed.bundle = vim.fn.sha256(contents(built.data.bundleUri))
assert(observed.bundle == built.data.bundleSha256)
local items = call("buildTarget/sources", {targets = {target, {uri = cfg.dependency}}}).items
observed.generated = {}
for _, item in ipairs(items) do
    for _, source in ipairs(item.sources) do
        if source.generated then
            assert(source.kind == 1)
            table.insert(observed.generated, vim.fn.sha256(contents(source.uri)))
        end
    end
end
local cancelled
local sent, request_id = client.request("buildTarget/compile", params, function(err, result)
    assert(not err, vim.inspect(err))
    cancelled = result
end)
assert(sent and client.cancel_request(request_id))
wait(function() return cancelled ~= nil end, "missing cancelled build verdict")
observed.cancelled = cancelled.statusCode
local failed = call("buildTarget/compile", {targets = {{uri = cfg.broken}}})
observed.failed = failed.statusCode
observed.diagnostic = failed.data.message
local changed = assert(io.open(cfg.input, "ab"))
changed:write("\n// dependency changed\n")
changed:close()
local stale = assert(client.request_sync("workspace/buildTargets", nil, 90000))
assert(stale.err and not stale.result, vim.inspect(stale))
observed.stale = stale.err.message
client.stop()
wait(function() return exited ~= nil end, "server did not shut down")
assert(exited == 0)
assert(vim.fn.writefile({vim.json.encode(observed)}, cfg.observations) == 0)
"""


def qualify(root: Path) -> dict[str, object]:
    """Build the package fixture in independent batch and editor sessions."""
    cache = lsp_clients._default_cache_root() / "downloads"
    archive = lsp_clients._download_bytes(PLUGIN.url, PLUGIN.archive_sha256, cache, PLUGIN.filename)
    with tempfile.TemporaryDirectory(prefix="vela-bsp-client-") as temporary:
        stage = Path(temporary)
        neovim, editor = lsp_clients._stage_neovim(cache, stage)
        plugin = stage / "client"
        lsp_clients.extract_verified_archive(archive, PLUGIN, plugin, allow_predicate=("lua/",))
        workspace = stage / "package sources"
        shutil.copytree(root / "examples" / "packages", workspace)
        broken = workspace / "scale" / "broken"
        shutil.copytree(workspace / "scale" / "v1", broken)
        manifest = broken / packages.MANIFEST
        manifest.write_text(manifest.read_text().replace('revision = "v1"', 'revision = "broken"'))
        source = broken / "Calibration.vela"
        source.write_text(source.read_text().replace("Make(units:", "UnknownScale(units:"))

        locks = [stage / f"{label}.lock" for label in ("scale", "weights", "broken")]
        targets = []
        for lock, (name, revision) in zip(locks, (("scale", "v1"), ("weights", "v1"), ("scale", "broken")), strict=True):
            packages.lock_package(root, workspace, name, revision, lock)
            targets.append(f"vela-build:{file_sha256(lock)}/{name}")
        batch_file = stage / "batch.json"
        batch = packages.build_package(root, workspace, locks[0], batch_file)
        observations = stage / "observations.json"
        config = stage / "case.json"
        config.write_text(json.dumps({
            "plugin": str(plugin), "root": str(root), "workspace": str(workspace),
            "command": [sys.executable, str(root / "tools/run.py"), "vela-parser", "bsp", str(workspace), *map(str, locks)],
            "target": targets[0], "dependency": targets[0].rsplit("/", 1)[0] + "/weights", "broken": targets[2],
            "input": str(workspace / "weights/v1/Measure.vela"), "observations": str(observations),
        }))
        script = stage / "qualify.lua"
        script.write_text(SESSION, encoding="utf-8")
        process = subprocess.run(
            [str(neovim), "--headless", "-u", "NONE", "-i", "NONE", "-n", "-l", str(script)],
            cwd=workspace, env={**os.environ, "VELA_BSP_CASE": str(config), "XDG_STATE_HOME": str(stage / "state")},
            capture_output=True, timeout=360, check=False,
        )
        if process.returncode or not observations.is_file():
            raise ValueError(f"BSP editor session failed: {(process.stdout + process.stderr)[-3500:]!r}")
        actual = json.loads(observations.read_bytes())
        delivered = json.loads(batch_file.read_bytes())
        generated = sorted(hashlib.sha256(unit.encode()).hexdigest() for unit in delivered["modules"].values())
        if (actual["batch"] != batch or actual["bundle"] != file_sha256(batch_file)
                or sorted(actual["generated"]) != generated or actual["failed"] != 2 or actual["cancelled"] != 3
                or "UnknownScale" not in actual["diagnostic"] or "stale" not in actual["stale"].lower()):
            raise ValueError(f"editor verdict, generated files or bundle differ from batch: {actual}")
        target_rows = actual["targets"]
        expected_sources: dict[str, str] = {}
        for lock, target_uri in zip(locks, targets, strict=True):
            locked = json.loads(lock.read_bytes())
            prefix = target_uri.rsplit("/", 1)[0]
            for name, package in locked["packages"].items():
                uri = f"{prefix}/{name}"
                row = target_rows[uri]
                if (row["id"] != {"uri": uri} or row["displayName"] != f"{name}@{package['revision']}"
                        or row["dataKind"] != "vela-locked-package"
                        or row["data"]["lockUri"] != lock.as_uri() or row["data"]["lockSha256"] != prefix.split(":")[1]
                        or row["data"]["inputs"] != package["files"] or row["data"]["producer"] != locked["producer"]
                        or row["data"]["edition"] != "math-1" or row["data"]["target"] != "rocq-gallina"
                        or row["data"]["instance"] != package["instance"]
                        or row["capabilities"]["canCompile"] != (uri == target_uri)
                        or row["dependencies"] != [{"uri": f"{prefix}/{dep}"} for dep in package["dependencies"]]):
                    raise ValueError(f"bsp.nvim loaded different target information: {row}")
                filename, = package["modules"].values()
                expected_sources[uri] = (workspace / name / package["revision"] / filename).as_uri()
        if set(target_rows) != set(expected_sources) or len(actual["sources"]) != len(expected_sources):
            raise ValueError("bsp.nvim loaded a different target inventory")
        for item in actual["sources"]:
            uri = item["target"]["uri"]
            if item["sources"] != [{"kind": 1, "uri": expected_sources.pop(uri), "generated": False}]:
                raise ValueError(f"unexpected client source inventory: {item}")
        return {"status": "passed", "protocol": actual["version"], "editor": editor,
                "plugin_revision": REVISION, "plugin_sha256": PLUGIN.archive_sha256,
                "targets": sorted(target_rows), "batch": batch, "bundle_sha256": actual["bundle"],
                "generated_sha256": generated, "cancelled_status": 3, "failed_status": 2,
                "failed_diagnostic": actual["diagnostic"], "stale_dependency": actual["stale"]}
