# SPDX-License-Identifier: Apache-2.0
"""Read finite packet-call observations from the compiled Sail commit trace."""

import struct
from dataclasses import asdict, dataclass, field
from itertools import pairwise

from toolchain.compiler_diff import STACK_BYTES

ENTRY = "PrepareAndValidatePacket"
ARENA_BYTES = 136
CURSOR_MASK = (1 << 36) - 1
SPAN = struct.Struct("<QQQIII")
OUTCOME = struct.Struct("<IIQ")
RESULT_BYTES = OUTCOME.size + SPAN.size


@dataclass(frozen=True)
class Scenario:
    name: str
    packet: str
    before: str
    after: str
    error: int
    copied: int = 0
    packet_offset: int = 128
    read_bytes: int = 4


SCENARIOS = (
    Scenario("empty", "56005a0100000000", "0000000000000000c300", "56005a0100000000c300", 0),
    Scenario("full", "56041e0110203040", "0000000000000000", "56041e0110203040", 0, 4, read_bytes=8),
    Scenario("partial", "56026b011122dead", "aaaaaaaaaaaaaaaaaaaa", "56026b0111220000aaaa", 0, 2, read_bytes=6),
    Scenario("short", "000000", "0000000000000000", "0000000000000000", 1, read_bytes=0),
    Scenario("bad-magic", "00023a01aacc0000", "0000000000000000", "0000000000000000", 2),
    Scenario("oversized", "56055f0110203040", "0000000000000000", "0000000000000000", 3),
    Scenario("checksum", "5604ff0110203040", "77777777777777777777", "00000000000000007777", 4, read_bytes=8),
    Scenario("overlap", "56041e0110203040", "a300000056041e01", "a300000056041e01", 1, packet_offset=68, read_bytes=0),
    Scenario("bad-flags-and-oversized", "5605000011223344", "a5a5a5a5a5a5a5a5a5a5", "0000000000000000a5a5", 2),
)

# The other four controls alter caller expectations only. Their callee observations still agree.
CONTROL_PREFIXES = {0: (9, ()), 4: (1, ("view.cursor",)), 6: (2, ("view.cursor",)), 7: (2, ()),
                    10: (3, ("view.perm_write",)), 12: (3, ()), 16: (7, ()), 17: (7, ())}


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise ValueError(f"packet entry observation: {detail}")


def _bytes(memory: dict[int, int], start: int, size: int) -> bytes:
    try:
        return bytes(memory[at] for at in range(start, start + size))
    except KeyError as error:
        raise ValueError(f"packet entry observation: byte at {error.args[0]:#x} lacks a recorded write") from error


@dataclass(frozen=True)
class Span:
    cursor: int
    base: int
    length: int
    tag: int
    perm_read: int
    perm_write: int

    @classmethod
    def read(cls, memory: dict[int, int], address: int) -> Span:
        return cls(*SPAN.unpack(_bytes(memory, address, SPAN.size)))


@dataclass
class Call:
    scenario: Scenario
    resume: int
    arena: int
    out: int
    dst_address: int
    pkt_address: int
    dst: Span
    pkt: Span
    reads: set[int] = field(default_factory=set)
    writes: set[int] = field(default_factory=set)
    result_stores: set[int] = field(default_factory=set)
    tagged_result_store: bool = False

    @classmethod
    def begin(cls, scenario: Scenario, registers: dict[int, tuple[int, int]], memory: dict[int, int],
              stack: range, text: range) -> Call:
        def cursor(reg: int) -> int:
            tag, bits = registers.get(reg, (0, 0))
            _require(tag == 1, f"missing tagged argument or return register c{reg}")
            return bits & CURSOR_MASK

        resume = cursor(1)
        _require(resume in text and resume % 4 == 0, "return register leaves executable text")
        arena, out, dst_address, pkt_address = map(cursor, (10, 11, 12, 13))
        extents = sorted(((arena, ARENA_BYTES), (out, RESULT_BYTES), (dst_address, SPAN.size), (pkt_address, SPAN.size)))
        for start, size in extents:
            _require(start in stack and start + size - 1 in stack, "argument leaves development stack")
        for (start, size), (following, _) in pairwise(extents):
            _require(start + size <= following, "arena, descriptor or result storage aliases another argument")

        dst, pkt = Span.read(memory, dst_address), Span.read(memory, pkt_address)
        before, packet = bytes.fromhex(scenario.before), bytes.fromhex(scenario.packet)
        _require(dst == Span(64, 64, len(before), 1, 1, 1), f"{scenario.name}: changed destination descriptor")
        packet_offset = scenario.packet_offset
        _require(pkt == Span(packet_offset, packet_offset, len(packet), 1, 1, 1),
                 f"{scenario.name}: changed input descriptor")
        _require(_bytes(memory, arena + dst.cursor, dst.length) == before
                 and _bytes(memory, arena + pkt.cursor, pkt.length) == packet,
                 f"{scenario.name}: changed entry bytes")
        return cls(scenario, resume, arena, out, dst_address, pkt_address, dst, pkt)

    def access(self, kind: str, start: int, size: int, tag: str) -> None:
        arena = range(max(start, self.arena) - self.arena, min(start + size, self.arena + ARENA_BYTES) - self.arena)
        (self.reads if kind == "R" else self.writes).update(arena)
        if kind == "W":
            result = range(max(start, self.out) - self.out, min(start + size, self.out + RESULT_BYTES) - self.out)
            self.result_stores.update(result)
            self.tagged_result_store |= bool(result) and tag == "1"

    def finish(self, memory: dict[int, int], expected_mismatches: tuple[str, ...]) -> dict[str, object]:
        case = self.scenario
        _require(len(self.result_stores) == RESULT_BYTES and not self.tagged_result_store,
                 f"{case.name}: result fields were incomplete or had a tagged store")
        ok, error, copied = OUTCOME.unpack(_bytes(memory, self.out, OUTCOME.size))
        view = Span.read(memory, self.out + OUTCOME.size)
        _require((ok, error, copied) == (int(case.error == 0), case.error, case.copied),
                 f"{case.name}: changed validator outcome")
        _require(Span.read(memory, self.dst_address) == self.dst and Span.read(memory, self.pkt_address) == self.pkt,
                 f"{case.name}: descriptor restoration failed")
        after = _bytes(memory, self.arena + self.dst.cursor, self.dst.length).hex()
        _require(after == case.after and _bytes(memory, self.arena + self.pkt.cursor, self.pkt.length).hex() == case.packet,
                 f"{case.name}: changed post-state bytes")
        permitted_reads = range(self.pkt.cursor, self.pkt.cursor + case.read_bytes)
        permitted_writes = range(self.dst.cursor, self.dst.cursor + (0 if case.error == 1 else 8))
        _require(self.reads.issubset(permitted_reads) and self.writes.issubset(permitted_writes),
                 f"{case.name}: backing access exceeds the scenario's read or write extent")
        if case.error:
            wanted = Span(self.dst.cursor, self.dst.base, self.dst.length, 0, 0, 0)
        else:
            start = self.dst.cursor + 4
            wanted = Span(start, start, case.copied, 1, 1, 0)
        mismatches = tuple(f"view.{name}" for name, value in asdict(wanted).items() if getattr(view, name) != value)
        _require(mismatches == expected_mismatches, f"{case.name}: changed view mismatches {mismatches}")
        if "view.cursor" in mismatches:
            _require(view.cursor == self.pkt.cursor + 4, f"{case.name}: control did not redirect to input payload")
        if "view.perm_write" in mismatches:
            _require(view.perm_write == 1, f"{case.name}: control did not enable write permission")
        return {"case": case.name, "resume_pc": self.resume, "input": case.packet,
                "before": case.before, "after": after, "error": error, "copied": copied,
                "view": asdict(view), "backing_reads": sorted(self.reads), "backing_writes": sorted(self.writes),
                "mismatches": list(mismatches)}


def observe(records: list[str], symbols: dict[str, tuple[str, int]], text: range, control: int) -> dict[str, object]:
    """Read validated trace records using symbols from the byte-identical regenerated image."""
    section, entry = symbols.get(ENTRY, ("", 0))
    stack_section, stack_start = symbols.get("__holdfast_stack", ("", 0))
    top_section, stack_end = symbols.get("__holdfast_stack_top", ("", 0))
    _require(section == ".text" and entry in text and entry % 4 == 0, "missing executable validator symbol")
    _require(stack_section == top_section == ".data" and stack_end - stack_start == STACK_BYTES,
             "missing bounded development stack")
    stack = range(stack_start, stack_end)
    count, final_mismatches = CONTROL_PREFIXES[control]
    registers: dict[int, tuple[int, int]] = {}
    memory: dict[int, int] = {}
    calls: list[dict[str, object]] = []
    active: Call | None = None
    for record in records:
        parts = record.split()
        kind = parts[0]
        if kind == "I":
            pc = int(parts[1], 16)
            if active is not None and pc == active.resume:
                expected = final_mismatches if len(calls) + 1 == count else ()
                calls.append(active.finish(memory, expected))
                active = None
            if pc == entry:
                _require(active is None and len(calls) < count, "unexpected validator entry")
                active = Call.begin(SCENARIOS[len(calls)], registers, memory, stack, text)
        elif kind == "X":
            registers[int(parts[1])] = (int(parts[2]), int(parts[3], 16))
        elif kind in {"R", "W"}:
            start, size = int(parts[1], 16), int(parts[2])
            _require(0 < size <= 8 and start + size <= (1 << 64), "invalid memory event extent")
            if active is not None:
                active.access(kind, start, size, parts[3])
            if kind == "W" and start < stack.stop and stack.start < start + size:
                data = bytes.fromhex(parts[4])[::-1]
                for at in range(max(start, stack.start), min(start + size, stack.stop)):
                    memory[at] = data[at - start]
        elif kind == "T":
            raise ValueError("packet entry observation: unexpected trap")
    _require(active is None and len(calls) == count, "incomplete validator calls")
    return {"scope": "compiled-development-scalar-descriptor", "entry_pc": entry, "calls": calls}
