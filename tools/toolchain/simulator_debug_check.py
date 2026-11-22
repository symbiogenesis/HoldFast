# SPDX-License-Identifier: Apache-2.0
"""Independent packet-control expectations for live simulator inspection."""

from collections.abc import Callable
from pathlib import Path

from toolchain.simulator_debug import Session, command


def _line(session: Session, instruction: str) -> int:
    matches = [n for n, line in enumerate(session.source.splitlines(), 1) if line.strip() == instruction]
    if len(matches) != 1:
        raise ValueError(f"expected one control instruction {instruction!r}")
    return matches[0]


def _expect(actual: object, expected: object) -> None:
    if actual != expected:
        raise ValueError(f"debugger observed {actual!r}, expected {expected!r}")


def _refusal(action: Callable[[], object], reason: str) -> None:
    try:
        action()
    except ValueError as error:
        if reason not in str(error):
            raise
    else:
        raise ValueError(f"expected debugger refusal containing {reason!r}")


def qualify_controls(simulator: Path, profile: Path, directory: Path) -> dict[str, object]:
    passing = Session("pass", simulator, profile, directory)
    initial = passing.handle
    _expect(passing.where(initial)["pc"], 0x80000000)
    _expect(passing.evaluate(initial, "c13.tag"), {"status": "unavailable"})
    _refusal(lambda: passing.advance(initial, 1), "no executable instruction")
    stop = passing.advance(initial, _line(passing, "call    main"))
    _expect((stop["pc"], stop["retired"]), (0x8000004C, 19))
    _refusal(lambda: passing.where(initial), "stale")
    stop = passing.advance(passing.handle)
    _expect((stop["pc"], stop["retired"]), (0x80000098, 20))
    stack = passing.stack(passing.handle)
    _expect([(row["name"], row["pc"]) for row in stack], [("main", 0x80000098), ("_start", 0x8000004C)])
    _expect(passing.evaluate(passing.handle, "cra.tag"), {"status": "available", "value": 1})
    stop = passing.advance(passing.handle, _line(passing, "cgetlen t0, c13"))
    _expect((stop["pc"], stop["retired"]), (0x80000168, 72))
    _expect(passing.evaluate(passing.handle, "c13.tag"), {"status": "available", "value": 1})
    _expect(passing.evaluate(passing.handle, "c13.length"), {"status": "unavailable"})
    _expect(passing.evaluate(passing.handle, "t0.bits"), {"status": "available", "value": 0x40})
    stop = passing.advance(passing.handle)
    _expect(stop["pc"], 0x8000016C)
    _expect(passing.evaluate(passing.handle, "t0.bits"), {"status": "available", "value": 4})
    _expect(passing.evaluate(passing.handle, "c13.length"), {"status": "available", "value": 4})
    _expect(passing.evaluate(passing.handle, "c13.permissions"), {"status": "unavailable"})
    previous = passing.handle
    passing.disconnect()
    _refusal(lambda: passing.evaluate(previous, "t0"), "disconnected")
    _expect(passing.reconnect()["pc"], stop["pc"])
    _refusal(lambda: passing.evaluate(previous, "t0"), "stale")
    _expect(passing.evaluate(passing.handle, "c13.length"), {"status": "available", "value": 4})
    for expression in ("t0 = 3", "mem[0]", "call(main)", "c32.tag", "cap(1)"):
        _refusal(lambda expression=expression: command(passing, "eval " + expression), "read-only")
    _refusal(lambda: command(passing, "eval " + "x" * 64), "32 characters")
    stop = passing.advance(passing.handle, _line(passing, "beqz    a0, __vela_pass"))
    _expect(stop["pc"], 0x80000050)
    _expect([row["name"] for row in passing.stack(passing.handle)], ["_start"])
    exit_state = passing.advance(passing.handle, finish=True)
    _expect(exit_state, {"status": "exited", "retired": 93, "htif": 0})
    _refusal(lambda: passing.where(previous), "stale")

    controls = {"pass": passing.identities}
    for control in ("tag-trap", "bounds-trap", "perm-trap"):
        session = Session(control, simulator, profile, directory)
        controls[control] = session.identities
        _refusal(lambda session=session: session.where(initial), "stale")
        if control == "tag-trap":
            session.advance(session.handle, _line(session, "cmove   c13, cnull"))
            _expect(session.evaluate(session.handle, "c13.tag"), {"status": "available", "value": 1})
            session.advance(session.handle)
            _expect(session.evaluate(session.handle, "c13.tag"), {"status": "available", "value": 0})
        stop = session.advance(session.handle, _line(session, "csrr    t0, mcause"))
        _expect(stop["pc"], 0x80000088)
        _expect([frame["name"] for frame in session.stack(session.handle)], ["__vela_handler", "main", "_start"])
        session.advance(session.handle)
        _expect(session.evaluate(session.handle, "t0.bits"), {"status": "available", "value": 28})
        _expect(session.advance(session.handle, finish=True)["htif"], 284)
        session.disconnect()
        with session.elf.open("ab") as image_stream:
            image_stream.write(b"changed")
        _refusal(session.reconnect, "stale Sail")
    return {"status": "qualified", "sha256": controls, "pass_retirements": 93,
            "packet_view_length": 4, "trap_mcause": 28, "trap_htif": 284}
