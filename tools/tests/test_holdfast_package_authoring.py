# SPDX-License-Identifier: Apache-2.0
"""Drive the default build checks and explicit buffer formatting of a locked package."""

import json
import shlex
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.harness import TOOLS, Case, ensure
from tests.test_holdfast_elaboration_cli import _invoke
from toolchain import corpus

ROOT = TOOLS.parent
LAYOUT = b"""module Trail.Route;

import TrailUnits;

public record StepCount(Nat Value);

public union Option<T>
{
    None();
    Some(T Value);
}

public definition Option<Nat> Distance(Option<Option<StepCount>> steps) => Some(steps? ? .Value * TrailUnits.Step);
"""
ROUGH = LAYOUT.replace(b"steps? ? .Value", b"steps?\t?\t.Value").replace(b"\n", b"\r\n")
DOCUMENT = "docs/tooling/authoring-tools.md"


def _documented_units() -> bytes:
    document = corpus.from_text((ROOT / DOCUMENT).read_text(encoding="utf-8"), DOCUMENT)
    [example] = [fence for fence in document.holdfast_examples
                 if fence.info == "holdfast-check" and fence.source.startswith("module TrailUnits;\n")]
    return example.source.encode()


def _editor(source: bytes) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run([sys.executable, str(TOOLS / "run.py"), "holdfast-parser", "fmt", "-", "--syntax-only"],
                          input=source, cwd=ROOT, capture_output=True, check=False, timeout=60)


def _authoring_defaults() -> None:
    with TemporaryDirectory(prefix="holdfast trail '") as temporary:
        workspace = Path(temporary)
        base = workspace / "trail" / "v1"
        base.mkdir(parents=True)
        manifest = base / "holdfast-package.toml"
        manifest.write_bytes(b"""name = "trail"
revision = "v1"
edition = "math-2"
target = "rocq-gallina"
inputs = []
[modules]
"Trail.Route" = "Route.hf"
"TrailUnits" = "Units.hf"
[dependencies]
""")
        route, units = base / "Route.hf", base / "Units.hf"
        route.write_bytes(ROUGH)
        documented_units = _documented_units()
        units.write_bytes(documented_units)
        lock, output = workspace / "lock.json", workspace / "bundle.json"
        output.write_bytes(b"previous bundle")
        lock_args = ["lock-package", str(workspace), "trail", "v1", "--output", str(lock)]
        build_args = ["build-package", str(workspace), str(lock), "--output", str(output)]
        code, _, err = _invoke(lock_args)
        ensure(code == 0, f"locking the authored package failed: {err}")
        files = (manifest, route, units, lock)
        snapshots = [(path.read_bytes(), path.stat().st_mtime_ns) for path in files]
        code, out, err = _invoke(build_args)
        repair = shlex.join(["python3", "tools/run.py", "holdfast-parser", "fmt", str(route), "--syntax-only"])
        ensure(code == 1 and not out and "canonical mathematical layout" in err and repair in err,
               f"default build skipped the layout check or lost the repair command: {err}")
        ensure(output.read_bytes() == b"previous bundle" and
               [(path.read_bytes(), path.stat().st_mtime_ns) for path in files] == snapshots,
               "failed check modified its inputs or previous bundle")

        edited = _editor(ROUGH)
        ensure(edited.returncode == 0 and edited.stdout == LAYOUT and not edited.stderr
               and route.read_bytes() == ROUGH, f"editor did not return the expected layout: {edited.stderr}")
        malformed = _editor(b"module Trail.Route; public Nat")
        ensure(malformed.returncode == 1 and not malformed.stdout and b"syntax" in malformed.stderr,
               "invalid editor buffer produced a replacement")
        for separated, compact in ((b"? ?", b"??"), (b"? .Value", b"?.Value")):
            refused = _editor(LAYOUT.replace(separated, compact))
            ensure(refused.returncode == 1 and not refused.stdout and b"syntax" in refused.stderr,
                   f"reserved contiguous spelling {compact!r} produced an editor replacement")
        code, _, err = _invoke(shlex.split(repair)[3:])
        ensure(code == 0 and route.read_bytes() == edited.stdout, f"repair diverged from editor layout: {err}")
        code, _, err = _invoke(build_args)
        ensure(code == 1 and "stale package lock" in err, "repair silently updated the source-bound lock")
        code, _, err = _invoke(lock_args)
        ensure(code == 0, f"relocking the formatted source failed: {err}")
        snapshots = [(path.read_bytes(), path.stat().st_mtime_ns) for path in files]
        code, out, err = _invoke(build_args)
        ensure(code == 0 and json.loads(out)["build_order"] == ["TrailUnits", "Trail.Route"]
               and f"{route}:13:31: warning HOLDFAST102:" in err and str(units) not in err,
               f"canonical package lost its qualified import, attached docs or advisory lint: {err}")
        ensure([(path.read_bytes(), path.stat().st_mtime_ns) for path in files] == snapshots,
               "successful package build modified its inputs")

        upgraded = base.with_name("v2")
        upgraded.mkdir()
        (upgraded / manifest.name).write_bytes(manifest.read_bytes().replace(b'revision = "v1"', b'revision = "v2"'))
        client, provider = upgraded / route.name, upgraded / units.name
        client.write_bytes(LAYOUT)
        provider.write_bytes(documented_units.replace(b"Step = 2", b"Step = 3"))
        code, out, err = _invoke(["diff-contract", str(units), str(provider)])
        ensure(code == 0 and not err and set(json.loads(out)["changed"]["Step"]) == {"value"},
               f"public constant upgrade lost its authored contract change: {err}")
        lock_args[3] = "v2"
        code, _, err = _invoke(lock_args)
        ensure(code == 0, f"relocking the upgraded package failed: {err}")
        code, out, err = _invoke(build_args)
        ensure(code == 0 and json.loads(out)["build_order"] == ["TrailUnits", "Trail.Route"]
               and client.read_bytes() == LAYOUT, f"upgraded package or unchanged client failed authoring checks: {err}")


def cases() -> list[Case]:
    return [Case("locked package default layout, editor repair, lint and public upgrade", _authoring_defaults, lane="guest")]
