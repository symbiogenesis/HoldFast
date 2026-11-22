# SPDX-License-Identifier: Apache-2.0
"""Independent native loader and packet runtime inventory controls."""

import struct
import tempfile
from collections.abc import Callable
from functools import partial
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import packet_runtime, trace_runtime

INDEPENDENT_CASES = True


def _refuses(action: Callable[[], object]) -> None:
    try:
        action()
    except (OSError, ValueError):
        return
    raise AssertionError("unresolved packet runtime was accepted")


def _elf_fixture(interpreter: bytes) -> bytes:
    header = bytearray(64)
    header[:7] = b"\x7fELF\x02\x01\x01"
    struct.pack_into("<Q", header, 32, 64)
    struct.pack_into("<HH", header, 54, 56, 2)
    segments = bytearray(112)
    struct.pack_into("<I", segments, 0, 2)
    struct.pack_into("<I", segments, 56, 3)
    struct.pack_into("<Q", segments, 64, 176)
    struct.pack_into("<Q", segments, 88, len(interpreter))
    return bytes(header + segments + interpreter)


def _elf_contract() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        target = Path(temporary) / "binary"
        target.write_bytes(_elf_fixture(b"/loader\0"))
        ensure(packet_runtime._elf(target) == (True, Path("/loader")), "wrong interpreter selection")
        for invalid in (_elf_fixture(b"relative\0"), _elf_fixture(b"/missing-nul"), b"\x7fELF"):
            target.write_bytes(invalid)
            _refuses(lambda: packet_runtime._elf(target))
        target.write_bytes(b"#!/switch/ocamlrun\ncompiled bytecode")
        ensure(packet_runtime._parser_interpreter(target) == Path("/switch/ocamlrun"), "bytecode interpreter omitted")
        target.write_bytes(b"#!ocamlrun\n")
        _refuses(lambda: packet_runtime._parser_interpreter(target))


def _transitive_bindings() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        worker, loader, library = (directory / name for name in ("worker", "loader", "dependency"))
        for path in (worker, loader, library):
            path.write_bytes(path.name.encode())
        files: dict[str, Path] = {}
        listing = f"linux-vdso.so.1 (0x10)\nlibgmp.so => {library} (0x20)\n{loader} (0x30)".encode()
        with patch.object(packet_runtime, "_elf", return_value=(True, loader)), \
                patch.object(packet_runtime, "_run", return_value=listing):
            selected = packet_runtime._resolve_images({worker}, loader, {}, files)
            ensure(selected == {str(worker): [str(library), str(loader)]}
                   and set(files.values()) == {worker, loader, library}, "native closure omitted dependencies")
            prior = trace_runtime.file_identity(files)
            library.write_bytes(b"same version, changed contents")
            ensure(trace_runtime.file_identity(files) != prior, "changed native dependency retained its binding")
            _refuses(lambda: packet_runtime._resolve_images({worker}, loader, {"LD_PRELOAD": "injected"}, {}))
            library.unlink()
            _refuses(lambda: trace_runtime.file_identity(files))
        for raw in (b"", b"libgmp.so => not found", b"libgmp.so => relative (0x12)"):
            _refuses(partial(packet_runtime._linked, raw))
        ensure(packet_runtime._linked(b"statically linked\n") == [], "valid static runtime omitted")


def cases() -> list[Case]:
    return [Case("actual interpreter selection from ELF and bytecode", _elf_contract),
            Case("transitive runtime replacement and missing dependency refusals", _transitive_bindings)]
