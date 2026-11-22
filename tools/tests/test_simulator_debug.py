# SPDX-License-Identifier: Apache-2.0
"""Host controls for exact Sail stop records, input identity and divergent replay."""

import tempfile
from pathlib import Path
from unittest.mock import patch

from tests.harness import Case, ensure, raises
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
        with raises(ValueError, msg="malformed architectural observation was accepted") as raised:
            debug._retirements(data, sites, limit)
        error = raised.exception
        ensure(reason in str(error), f"wrong malformed record refusal: {error}")


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
            with raises(ValueError, msg="accepted a state from another execution") as raised:
                session.advance(initial)
            ensure("diverged" in str(raised.exception), "missed the changed capability tag")
            rerun.assert_called_once_with(2, stop_pc=pc + 4)
        ensure(session.handle is None, "divergent execution retained an inspectable stop")
        session.disconnect()
        session.reconnect()
        restored_stop = session.handle
        profile.write_bytes(b"changed configuration")
        with raises(ValueError, msg="inspected a different target configuration") as raised:
            session.where(restored_stop)
        ensure("stale Sail" in str(raised.exception), "changed profile reached the wrong refusal")
        profile.write_bytes(b"test configuration")
        with raises(ValueError, msg="expired target handle was resurrected") as raised:
            session.where(restored_stop)
        ensure("stale or disconnected" in str(raised.exception), "restored bytes did not expire the stop")
        ensure(session.reconnect()["pc"] == pc and session.handle != restored_stop,
               "restored identical target failed to reconnect with a fresh stop")


def cases() -> list[Case]:
    return [Case("exact-retired-instructions-and-effects", _records),
            Case("divergent-replay-and-changed-target", _divergence)]
