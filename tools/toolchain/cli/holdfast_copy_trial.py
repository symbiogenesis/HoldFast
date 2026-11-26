# SPDX-License-Identifier: Apache-2.0
"""Replay frozen Q25bb public observations on the native C baseline."""

import argparse
import json
import shutil
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path
from tempfile import TemporaryDirectory

from toolchain.hashing import file_sha256, sha256_bytes

BASELINE = "498127d6be3d1a70581ba4a9cc025c2d923e66f7"
CONFIG_SHA256 = "6ac893cc25b83485f2efb22e83c0f65d863cb4de7a5a37c50ff134ed48b64d77"
SOURCE = "copy-service/src/copy_service.c"
HEADERS = ("copy-service/include/vos_copy_service.h", "copy-service/include/vos_copy_atomic.h")
FIXTURES = Path(__file__).resolve().parents[2] / "tests" / "fixtures"
CFLAGS = ("-std=c17", "-O1", "-Wall", "-Wextra", "-Wstrict-prototypes", "-Werror", "-pedantic")
CONTROLS = (
    ("tightened_payload_limit", b"length > vos_copy_payload_limit(operation)",
     b"(length != 0 && length >= vos_copy_payload_limit(operation))", 14),
    ("changed_staged_prefix", b"slot->length = length;",
     b"if (length != 0) slot->bytes[0] = 0;\n    slot->length = length;", 7),
    ("changed_suffix", b"*length = slot->length;",
     b"if (slot->length < capacity) destination[slot->length] = 0;\n    *length = slot->length;", 8),
    ("changed_refusal_output",
     b"if (!vos_copy_take_snapshot(ring, destination, capacity, length, request, &view)) return 0;",
     b"if (!vos_copy_take_snapshot(ring, destination, capacity, length, request, &view)) { *length = 0; return 0; }",
     2),
)


def _run(argv: Sequence[str | Path], work: Path, context: str, expected: int = 0) -> bytes:
    command = subprocess.run(argv, cwd=work, stdin=subprocess.DEVNULL, capture_output=True,
                             check=False, timeout=30)
    if command.returncode != expected:
        detail = (command.stderr or command.stdout).decode("utf-8", errors="replace").strip()
        raise ValueError(f"{context}: exit {command.returncode}, expected {expected}\n{detail}".strip())
    return command.stdout


def _replay(git_dir: Path, prepared_header: Path, cc: Path) -> dict[str, object]:
    configuration = prepared_header.read_bytes()
    if sha256_bytes(configuration) != CONFIG_SHA256:
        raise ValueError("prepared header does not match the frozen copy-service source record")

    compiler_sha256 = file_sha256(cc)
    with TemporaryDirectory(prefix="holdfast-q25bb-replay-") as temporary:
        work = Path(temporary)
        version = _run([cc, "--version"], work, "C compiler version").decode("utf-8", errors="replace").strip()
        baseline_inputs = {
            Path(path).name: _run(["git", "--no-lazy-fetch", "--no-replace-objects",
                                  "--git-dir", git_dir, "show", f"{BASELINE}:{path}"], work, path)
            for path in (SOURCE, *HEADERS)
        }
        fixture_inputs = {
            name: (FIXTURES / name).read_bytes()
            for name in ("q25bb-copy-client.h", "q25bb-copy-client.c")
        }
        inputs = {**baseline_inputs, **fixture_inputs, "copy_service_config.h": configuration}
        for name, raw in inputs.items():
            (work / name).write_bytes(raw)

        fixture = work / "q25bb-copy-client.c"
        _run([cc, *CFLAGS, "-DVOS_COPY_TARGET", "-ffreestanding", "-fsyntax-only", "-I", work, fixture],
             work, "syntax against the target ABI declarations")

        source = baseline_inputs["copy_service.c"]
        variants = [("baseline", source, 0)]
        for name, old, new, expected in CONTROLS:
            if source.count(old) != 1:
                raise ValueError(f"{name}: expected exactly one source anchor")
            variants.append((name, source.replace(old, new, 1), expected))

        results: dict[str, dict[str, str | int]] = {}
        for name, code, expected in variants:
            unit = work / f"{name}.c"
            image = work / f"{name}.exe"
            unit.write_bytes(code)
            _run([cc, *CFLAGS, "-DHOLDFAST_COPY_TRIAL_HOST", "-I", work, fixture, unit, "-o", image],
                 work, f"{name} native compile")
            image_sha256 = file_sha256(image)
            _run([image], work, f"{name} native execution", expected)
            results[name] = {"exit": expected, "source_sha256": sha256_bytes(code), "image_sha256": image_sha256}

    if file_sha256(cc) != compiler_sha256:
        raise ValueError("C compiler changed during replay")
    return {
        "schema": "holdfast-copy-trial-native/1",
        "verifiedos_revision": BASELINE,
        "compiler": {"version": version, "sha256": compiler_sha256},
        "cflags": CFLAGS,
        "inputs_sha256": {name: sha256_bytes(raw) for name, raw in inputs.items()},
        "target_declarations_syntax_exit": 0,
        "native_cases": results,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verifiedos-git-dir", required=True, type=Path, help="local VerifiedOS Git directory")
    parser.add_argument("--prepared-header", required=True, type=Path, help="copy_service_config.h from the frozen recipe")
    parser.add_argument("--cc", default="cc", help="native C compiler executable (default: cc)")
    args = parser.parse_args(argv)
    compiler = shutil.which(args.cc)
    if compiler is None:
        print(f"holdfast-copy-trial: C compiler unavailable: {args.cc}", file=sys.stderr)
        return 1
    try:
        report = _replay(args.verifiedos_git_dir.resolve(), args.prepared_header.resolve(), Path(compiler).resolve())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"holdfast-copy-trial: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0
