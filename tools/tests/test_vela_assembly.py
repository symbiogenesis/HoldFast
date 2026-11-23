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
            ("__vela_handler", valid + "__vela_handler: ret\n"),
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


def cases() -> list[Case]:
    return [Case("unique-labels-across-composed-sections", _symbol_collisions),
            Case("main-resolves-to-complete-executable-word", _main_target)]
