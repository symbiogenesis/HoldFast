# SPDX-License-Identifier: Apache-2.0
"""Guard explicit compiler output and source rewrites against stale snapshots and aliases."""

import os
import stat
from dataclasses import dataclass
from pathlib import Path

from toolchain.ast import MAX_SOURCE_BYTES
from toolchain.atomic import atomic_path


@dataclass(frozen=True)
class SourceFile:
    path: Path
    data: bytes
    identity: tuple[int, int, int, int]
    mode: int


def _identity(value: os.stat_result) -> tuple[int, int, int, int]:
    # Compare identity, size, mtime and bytes. Windows path and descriptor
    # stats can report different ctime values for the same file.
    return value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns


def read_source(path: Path, *, max_bytes: int = MAX_SOURCE_BYTES) -> SourceFile:
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode):
        raise OSError("source must be a regular file, not a symbolic link or special file")
    with path.open("rb") as stream:
        if _identity(os.fstat(stream.fileno())) != _identity(before):
            raise OSError("source changed while it was opened")
        data = stream.read(max_bytes + 1)
    if _identity(path.lstat()) != _identity(before):
        raise OSError("source changed while it was read")
    return SourceFile(path, data, _identity(before), stat.S_IMODE(before.st_mode))


def ensure_unchanged(source: SourceFile) -> None:
    current = read_source(source.path, max_bytes=max(MAX_SOURCE_BYTES, len(source.data)))
    if current.identity != source.identity or current.data != source.data:
        raise OSError("source changed during compilation; no pending source rewrite was applied")


def check_destination(source: Path, destination: Path) -> None:
    if (source.resolve() == destination.resolve()
            or (destination.exists() and source.samefile(destination))):
        raise OSError("output aliases the input")
    if not destination.parent.is_dir():
        raise OSError("output parent directory does not exist")
    if destination.is_symlink() or (destination.exists() and not destination.is_file()):
        raise OSError("output must be a regular file, not a symbolic link or special file")


def rewrite_source(source: SourceFile, formatted: bytes) -> SourceFile:
    ensure_unchanged(source)
    if formatted == source.data:
        return source
    with atomic_path(source.path) as pending:
        pending.write_bytes(formatted)
        pending.chmod(source.mode)
        ensure_unchanged(source)
    current = read_source(source.path)
    if current.data != formatted:
        raise OSError("source changed after formatting; generated output was not published")
    return current
