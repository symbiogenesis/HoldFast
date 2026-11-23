# SPDX-License-Identifier: Apache-2.0
"""Linkage regressions for the purecap differential harness."""

import tempfile
from pathlib import Path

from tests.harness import Case, ensure
from toolchain import asm, compiler_diff


def _symbol_collisions() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        target = Path(temporary) / "program.elf"
        valid = ".text\nmain: entry_alias: j done\ndone: ret\n"
        refusals, size = compiler_diff.assemble(valid, "linked", target)
        ensure(not refusals and size > 0, "distinct labels sharing an address should assemble")
        original = target.read_bytes()
        for symbol, stream in (
            ("main", valid + ".data\nmain: .dword 0\n"),
            ("done", valid + "done: ret\n"),
            ("entry_alias", valid + ".equ entry_alias, 17\n"),
            ("entry_alias", ".set entry_alias, 17\n" + valid),
            ("__holdfast_handler", valid + "__holdfast_handler: ret\n"),
            ("tohost", valid + ".data\ntohost: .dword 0\n"),
        ):
            refusals, size = compiler_diff.assemble(stream, "linked", target)
            ensure(len(refusals) == 1 and size == 0 and f"duplicate symbol {symbol} (" in refusals[0].detail,
                   f"missing collision at {symbol}: {refusals}")
            ensure(target.read_bytes() == original, "symbol collision replaced a previously valid image")


def _main_target() -> None:
    with tempfile.TemporaryDirectory() as temporary:
        target = Path(temporary) / "program.elf"
        for stream in (".data\nmain: .dword 0", ".text\nmain:", ".text\nmain: .byte 0",
                       ".text\n.half 0\nmain: ret"):
            refused, size = compiler_diff.assemble(stream, "entry", target)
            ensure(len(refused) == 1 and size == 0 and refused[0].kind == "symbol"
                   and refused[0].name == "main" and "complete aligned word" in refused[0].detail
                   and stream.splitlines()[refused[0].line - 1].startswith("main:"),
                   f"wrong main entry accepted or misdiagnosed: {refused}")
            ensure(not target.exists(), "invalid entry produced a new image")
        stream = ".text\nmain: .word 0x00000013\n"
        refused, size = compiler_diff.assemble(stream, "entry", target)
        ensure(not refused and size > 0, "complete aligned last instruction was refused")
        sections, symbols, _ = asm.Assembler(compiler_diff.compose(stream)).assemble()
        text = next(section for section in sections if section.name == ".text")
        ensure(symbols["main"] == (".text", text.addr + len(text.data) - 4),
               "positive boundary did not identify the last executable word")


def _constant_bindings() -> None:
    stream = (
        ".text\nmain: ret\n.data\n"
        ".word forward, version\n"
        ".equ forward, target + 1\n.equ target, 40\n"
        ".set version, 3\n.word version\n.set version, version + 4\n.word version\n"
        ".equ location, .\n.dword location, later_label - location\nlater_label:\n"
    )
    sections, _, _ = asm.Assembler(stream).assemble()
    data = next(section for section in sections if section.name == ".data")
    expected = b"".join(n.to_bytes(4, "little") for n in (41, 3, 3, 7))
    expected += (asm.DATA_BASE + 16).to_bytes(8, "little") + (16).to_bytes(8, "little")
    ensure(data.data == expected, "forward constants, assignment versions or definition-site addresses changed")
    with tempfile.TemporaryDirectory() as temporary:
        target = Path(temporary) / "program.elf"
        refusals, size = compiler_diff.assemble(stream, "constants", target)
        ensure(not refusals and size > 0, "valid constant expressions did not link")
        original = target.read_bytes()
        for definitions, reason in (
            (".equ answer, 1, 2", "takes a name and a value"),
            (".equ answer, missing_label", "no symbol missing_label"),
            (".equ answer, later\n.equ later, missing_label", "no symbol missing_label"),
            (".equ answer, answer", "cyclic constant definition"),
            (".equ answer, later\n.equ later, answer", "cyclic constant definition"),
            (".equ answer, 1 / 0", "invalid constant expression"),
        ):
            source = f".text\nmain: li a0, answer\nret\n{definitions}\n"
            refused, size = compiler_diff.assemble(source, "constants", target)
            ensure(len(refused) == 1 and size == 0 and reason in refused[0].detail,
                   f"invalid constant did not reach its resolution diagnostic: {refused}")
            ensure(target.read_bytes() == original, "failed constant resolution replaced a valid image")


def cases() -> list[Case]:
    return [Case("unique-labels-across-composed-sections", _symbol_collisions),
            Case("main-resolves-to-complete-executable-word", _main_target),
            Case("resolved-and-versioned-constant-definitions", _constant_bindings)]
