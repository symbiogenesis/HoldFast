# SPDX-License-Identifier: Apache-2.0
"""Exercise independent packet-call observations on normalized commit records."""

from tests.harness import Case, ensure, raises
from toolchain import packet_entry

START = 0x8000_0000
ENTRY = START + 8
RETURN = START + 12
STACK = 0x8000_9000
ARENA = STACK + 0x100
OUT = STACK + 0x200
DST = STACK + 0x300
PKT = STACK + 0x400
SYMBOLS = {packet_entry.ENTRY: (".text", ENTRY), "__holdfast_stack": (".data", STACK),
           "__holdfast_stack_top": (".data", STACK + 16384)}


def _stores(address: int, fields: list[tuple[int, bytes]]) -> list[str]:
    return [f"W {address + offset:X} {len(data)} 0 {data[::-1].hex().upper()}" for offset, data in fields]


def _words(*fields: tuple[int, int]) -> list[tuple[int, bytes]]:
    result: list[tuple[int, bytes]] = []
    offset = 0
    for width, value in fields:
        result.append((offset, value.to_bytes(width, "little")))
        offset += width
    return result


def _trace(*, view_cursor: int = 132, store_result: bool = True, tag: int = 0,
           forbidden_read: bool = False, wrong_output: bool = False) -> list[str]:
    records = [
        f"I {START:016X} 00000000",
        *(f"X {reg} 1 {0xC800_0000_0000_0000 | address:016X}"
          for reg, address in ((1, RETURN), (10, ARENA), (11, OUT), (12, DST), (13, PKT))),
        *_stores(DST, _words((8, 64), (8, 64), (8, 10), (4, 1), (4, 1), (4, 1))),
        *_stores(PKT, _words((8, 128), (8, 128), (8, 8), (4, 1), (4, 1), (4, 1))),
        *_stores(ARENA + 64, [(0, bytes(8)), (8, b"\xc3\0")]),
        *_stores(ARENA + 128, [(0, bytes.fromhex("56005a0100000000"))]),
    ]
    result = _stores(OUT, _words((4, 1), (4, 0), (8, 0), (8, view_cursor), (8, 68),
                                 (8, 0), (4, 1), (4, 1), (4, 0)))
    records.extend(result)  # Prior values cannot cover fields omitted by this call.
    records.append(f"I {ENTRY:016X} 00000000")
    records.extend(_stores(ARENA + 64, [(0, bytes.fromhex("55005a0100000000" if wrong_output else "56005a0100000000"))]))
    if forbidden_read:
        records.append(f"R {ARENA + 132:X} 1 0 00")
    if store_result:
        records.extend(result)
    if tag:
        records.append(f"W {OUT + 16:X} 8 1 {view_cursor:016X}")
    records.append(f"I {RETURN:016X} 00000000")
    return records


def _boundary() -> None:
    report = packet_entry.observe(_trace(), SYMBOLS, range(START, START + 16), 4)
    ensure(report["calls"] == [
        {"case": "empty", "resume_pc": RETURN, "input": "56005a0100000000",
         "before": "0000000000000000c300", "after": "56005a0100000000c300", "error": 0, "copied": 0,
         "view": {"cursor": 132, "base": 68, "length": 0, "tag": 1, "perm_read": 1, "perm_write": 0},
         "backing_reads": [], "backing_writes": list(range(64, 72)), "mismatches": ["view.cursor"]},
    ], "expected altered cursor must be observable before the first caller instruction")

    for records, detail in (
        (_trace(view_cursor=68), "changed view mismatches"),
        (_trace(view_cursor=131), "did not redirect"),
        (_trace(store_result=False), "incomplete or had a tagged store"),
        (_trace(tag=1), "incomplete or had a tagged store"),
        (_trace(forbidden_read=True), "backing access"),
        (_trace(wrong_output=True), "post-state bytes"),
        (_trace()[:-1], "incomplete validator calls"),
    ):
        with raises(ValueError, msg=f"accepted a trace with {detail}") as failure:
            packet_entry.observe(records, SYMBOLS, range(START, START + 16), 4)
        ensure(detail in str(failure.exception), f"refused for unrelated reason, expected {detail}")


def cases() -> list[Case]:
    return [Case("validator-return-proves-neither-htif-success-nor-a-caller-assertion", _boundary)]
