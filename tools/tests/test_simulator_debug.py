# SPDX-License-Identifier: Apache-2.0
"""Host controls for exact Sail stop records, input identity and divergent replay."""

import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import asm
from toolchain import simulator_debug as debug


def _records() -> None:
    pc = 0x8000_0000
    sites = {pc: debug.Site(1, 0x13, asm.Item("insn", 1, ".text", "nop"))}
    first = b"I 0 0000000080000000 00000013\n"
    effect = b"X 5 0 0000000000000004\n"
    ensure(debug._retirements(first + effect, sites, 1) == [debug.Retirement(pc, (effect.decode().strip(),))],
           "first instruction lost its actual tagged register effect")
    for data, limit, reason in (
        (first.replace(b"00000013", b"00000017"), 1, "exact image"),
        (first.replace(b"80000000", b"80000004"), 1, "exact image"),
        (first + first, 2, "retirement order"),
        (first + first.replace(b"I 0", b"I 1"), 1, "retirement order"),
        (effect, 1, "without a retired instruction"),
        (first + effect.replace(b"X 5", b"X 32"), 1, "register write"),
        (first + b"R 8000 8 1 FF\n", 1, "memory effect"),
        (first + b"malformed row\n", 1, "malformed Sail"),
    ):
        try:
            debug._retirements(data, sites, limit)
        except ValueError as error:
            ensure(reason in str(error), f"wrong malformed record refusal: {error}")
        else:
            raise AssertionError("malformed architectural observation was accepted")


def _divergence() -> None:
    pc = 0x8000_0000
    prefix = [debug.Retirement(pc, ("X 4 1 C800000000000000",)), debug.Retirement(pc + 4, ())]
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        simulator, profile = directory / "simulator", directory / "profile"
        simulator.write_bytes(b"test executable identity")
        profile.write_bytes(b"test configuration")
        with patch.object(debug.Session, "_execute", return_value=(prefix, 0)):
            session = debug.Session("pass", simulator, profile, directory)
        initial = session.handle
        wrong_tag = [debug.Retirement(pc, ("X 4 0 C800000000000000",))]
        with patch.object(debug.Session, "_execute", return_value=(wrong_tag, None)) as rerun:
            try:
                session.advance(initial)
            except ValueError as error:
                ensure("diverged" in str(error), "missed the changed capability tag")
            else:
                raise AssertionError("accepted a state from another execution")
            rerun.assert_called_once_with(2, stop_pc=pc + 4)
        ensure(session.handle is None, "divergent execution retained an inspectable stop")
        session.disconnect()
        profile.write_bytes(b"changed configuration")
        try:
            session.reconnect()
        except ValueError as error:
            ensure("stale Sail" in str(error), "changed profile reached the wrong refusal")
        else:
            raise AssertionError("reconnected a different target configuration")
        ensure(not session.connected, "failed reconnect retained a connection")


def cases() -> list[Case]:
    return [Case("exact-retired-instructions-and-effects", _records),
            Case("divergent-replay-and-changed-target", _divergence)]
