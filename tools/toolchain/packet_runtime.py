# SPDX-License-Identifier: Apache-2.0
"""Reconstruct the selected Linux compiler and prover's user-space runtime."""

import os
import re
import shutil
import struct
import subprocess
import sys
from pathlib import Path

from toolchain import packet_trace, proofenv, trace_runtime

MAX_ROOTS = 512
MAX_OUTPUT = 256 * 1024


def _run(command: list[str], *, environment: dict[str, str] | None = None,
         directory: Path | None = None) -> bytes:
    result = subprocess.run(command, env=environment, cwd=directory, stdin=subprocess.DEVNULL, capture_output=True,
                            timeout=30, check=False)
    if result.returncode or len(result.stdout) > MAX_OUTPUT or len(result.stderr) > MAX_OUTPUT:
        raise ValueError(f"packet runtime lookup failed for {Path(command[0]).name}")
    return result.stdout


def _elf(path: Path) -> tuple[bool, Path | None]:
    """Read the dynamic and interpreter program headers of a supported ELF64 image."""
    with path.open("rb") as stream:
        header = stream.read(64)
        if len(header) != 64 or header[:7] != b"\x7fELF\x02\x01\x01":
            raise ValueError(f"unexpected packet runtime executable format: {path}")
        offset, = struct.unpack_from("<Q", header, 32)
        size, count = struct.unpack_from("<HH", header, 54)
        if size != 56 or not 1 <= count <= 1024:
            raise ValueError("unsupported ELF program header table")
        dynamic = False
        loader = None
        for index in range(count):
            stream.seek(offset + index * size)
            row = stream.read(size)
            if len(row) != size:
                raise ValueError("truncated ELF program headers")
            kind, = struct.unpack_from("<I", row)
            if kind == 2:  # PT_DYNAMIC
                dynamic = True
            if kind == 3:  # PT_INTERP
                position, = struct.unpack_from("<Q", row, 8)
                length, = struct.unpack_from("<Q", row, 32)
                if not 2 <= length <= 4096 or loader is not None:
                    raise ValueError("invalid ELF interpreter size or count")
                stream.seek(position)
                name = stream.read(length)
                if len(name) != length or not name.startswith(b"/") or not name.endswith(b"\0"):
                    raise ValueError("unresolved ELF interpreter")
                loader = Path(os.fsdecode(name[:-1]))
    return dynamic, loader


def _linked(output: bytes) -> list[Path]:
    if output.strip() == b"statically linked":
        return []
    paths: list[Path] = []
    for line in output.decode().splitlines():
        match = re.fullmatch(r"\s*(?:(\S+) => )?(.+) \(0x[0-9a-fA-F]+\)", line)
        if not match:
            raise ValueError("unresolved packet runtime dependency")
        name = match[2]
        if name in {"linux-vdso.so.1", "linux-gate.so.1"} and match[1] is None:
            continue
        path = Path(name)
        if not path.is_absolute():
            raise ValueError("relative packet runtime dependency")
        paths.append(path)
    if not paths:
        raise ValueError("empty native library resolution")
    return paths


def _parser_interpreter(parser: Path) -> Path:
    with parser.open("rb") as stream:
        line = stream.readline(4096)
    if not line.startswith(b"#!/") or not line.endswith(b"\n"):
        raise ValueError("missing packet parser bytecode interpreter")
    return Path(os.fsdecode(line[2:-1]))


def _resolve_images(roots: set[Path], loader: Path, environment: dict[str, str],
                    files: dict[str, Path], *, directory: Path | None = None) -> dict[str, list[str]]:
    if environment.get("LD_PRELOAD", "") or environment.get("LD_AUDIT", ""):
        raise ValueError("packet runtime loader injection is outside the selected profile")
    resolutions: dict[str, list[str]] = {}
    for path in sorted(roots):
        files[str(path)] = path
        dynamic, interpreter = _elf(path)
        if dynamic:
            selected = interpreter or loader
            files[str(selected)] = selected
            lookup = _run([str(selected), "--list", str(path)], environment={**environment, "LC_ALL": "C"},
                          directory=directory)
            linked = _linked(lookup)
            files.update({str(item): item for item in linked})
            resolutions[str(path)] = [str(item) for item in linked]
    return resolutions


def identity(parser: Path, prover_files: dict[str, str], proof_directory: Path) -> str:
    """Bind Python, the actual switch lookup and every selected native dependency."""
    if sys.platform != "linux":
        raise ValueError("packet runtime identity requires Linux")
    opam = shutil.which("opam")
    if opam is None:
        raise ValueError("packet proof switch is unavailable")
    raw = _run([opam, "exec", "--switch", proofenv.ROCQ_SWITCH, "--", "/usr/bin/env", "-0"],
               directory=proof_directory)
    environment = dict(os.fsdecode(item).split("=", 1) for item in raw.split(b"\0") if item)
    prefix = Path(environment.get("OPAM_SWITCH_PREFIX", ""))
    if not prefix.is_absolute():
        raise ValueError("packet proof switch has no absolute prefix")
    preload = Path("/etc/ld.so.preload")
    if preload.exists() and preload.read_bytes().strip():
        raise ValueError("packet runtime loader injection is outside the selected profile")
    rocq = prefix / "bin" / "rocq"
    checker = prefix / "bin" / "rocqchk"
    for executable in (rocq, checker):
        actual = shutil.which(executable.name, path=environment.get("PATH"))
        if actual is None or not executable.samefile(actual):
            raise ValueError("packet prover dispatch escaped the proof switch")
    worker_dir = prefix / "lib/rocq-runtime"
    bytecode = {parser, worker_dir / "rocqworker_with_drop", worker_dir / "rocqworker.byte"}
    roots = {rocq, checker, worker_dir / "rocqworker"}
    roots.update(_parser_interpreter(path) for path in bytecode if path != parser)
    libraries = {prefix / "lib"}
    libraries.update(Path(entry) for entry in environment.get("CAML_LD_LIBRARY_PATH", "").split(":") if entry)
    for library_root in libraries:
        if not library_root.is_absolute() or not library_root.is_dir():
            raise ValueError("unavailable native plugin library directory")
        for candidate in library_root.rglob("*"):
            if candidate.is_symlink() and candidate.is_dir():
                raise ValueError("native plugin search contains a directory alias")
            if candidate.suffix == ".cmxs" or re.search(r"\.so(?:\.[0-9]+)*$", candidate.name):
                roots.add(candidate)
    roots.update(Path(name) for name in prover_files if name.endswith(".cmxs") or re.search(r"\.so(?:\.[0-9]+)*$", name))
    if len(roots) > MAX_ROOTS:
        raise ValueError("packet runtime native roots exceed the inventory limit")
    _, default_loader = _elf(rocq)
    if default_loader is None:
        raise ValueError("packet prover has no selected native loader")
    files = {str(path): path for path in bytecode}
    files["/etc/ld.so.cache"] = Path("/etc/ld.so.cache")
    host = _resolve_images({_parser_interpreter(parser)}, default_loader, dict(os.environ), files)
    dispatch = _resolve_images({Path(opam)}, default_loader, dict(os.environ), files, directory=proof_directory)
    switch = _resolve_images(roots, default_loader, environment, files, directory=proof_directory)
    lookup_inputs = {key: value for key, value in environment.items()
                     if key.startswith(("LD_", "OCAML", "CAML_", "COQ", "ROCQ"))}
    descriptor = {"python": trace_runtime.identity(), "flags": str(sys.flags), "sys_path": sys.path,
                  "kernel": os.uname().release, "native": trace_runtime.file_identity(files),
                  "host_images": host, "dispatch_images": dispatch, "switch_images": switch, "lookup": lookup_inputs}
    return packet_trace.digest(descriptor)
