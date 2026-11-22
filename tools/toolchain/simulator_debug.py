# SPDX-License-Identifier: Apache-2.0
"""Read-only Sail execution and inspection of the packet assembly controls."""

import hashlib
import re
import subprocess
import uuid
from dataclasses import dataclass
from pathlib import Path

from toolchain import asm, compiler_diff, dialect, first_slice, image, trace
from toolchain.hashing import file_sha256

CONTROLS = ("pass", "bounds-trap", "tag-trap", "perm-trap")
INSTRUCTION_LIMIT = 256
TRACE_LIMIT = 128 * 1024


@dataclass(frozen=True)
class Site:
    line: int
    word: int
    item: asm.Item


@dataclass(frozen=True)
class Retirement:
    pc: int
    effects: tuple[str, ...]


def _retirements(data: bytes, sites: dict[int, Site], limit: int) -> list[Retirement]:
    result: list[Retirement] = []
    pc: int | None = None
    effects: list[str] = []
    for row in data.decode("ascii").splitlines():
        if trace.COMMIT_RE.fullmatch(row) is None:
            raise ValueError("malformed Sail commit record")
        fields = row.split()
        if fields[0] == "I":
            if pc is not None:
                result.append(Retirement(pc, tuple(effects)))
            pc = int(fields[2], 16)
            if (int(fields[1]) != len(result) or len(result) >= limit
                    or pc not in sites or sites[pc].word != int(fields[3], 16)):
                raise ValueError("Sail instruction differs from the exact image or retirement order")
            effects = []
        elif pc is None:
            raise ValueError("architectural effect without a retired instruction")
        else:
            if fields[0] == "X" and not 0 < int(fields[1]) < 32:
                raise ValueError("unexpected architectural register write")
            if fields[0] in {"R", "W"} and (int(fields[2]) not in {1, 2, 4, 8}
                                             or len(fields[4]) != 2 * int(fields[2])):
                raise ValueError("malformed memory effect")
            effects.append(row)
    if pc is not None:
        result.append(Retirement(pc, tuple(effects)))
    return result


class Session:
    """A replayable single-hart session on one private, assembled packet control."""

    def __init__(self, control: str, simulator: Path, profile: Path, directory: Path) -> None:
        if control not in CONTROLS:
            raise ValueError("unsupported assembly control")
        self.source = compiler_diff.compose(first_slice._purecap_cheri_asm_stream(control))
        assembly = asm.Assembler(self.source)
        sections, self.symbols, entry = assembly.assemble()
        self.elf = directory / f"packet-{control}.elf"
        image.write_elf(self.elf, sections, self.symbols, entry)
        first_slice._check_purecap_control_image(self.elf.read_bytes())
        self.simulator, self.profile = simulator.resolve(strict=True), profile.resolve(strict=True)
        self.files = {"image": self.elf, "simulator": self.simulator, "profile": self.profile}
        self.identities = {key: file_sha256(path) for key, path in self.files.items()}
        self.identities["source"] = hashlib.sha256(self.source.encode()).hexdigest()
        code = sections[0]
        self.sites: dict[int, Site] = {}
        for item in assembly.items:
            if item.kind == "insn" and item.section == ".text":
                for pc in range(item.address, item.address + item.size, 4):
                    offset = pc - code.addr
                    word = int.from_bytes(code.data[offset:offset + 4], "little")
                    self.sites[pc] = Site(item.line, word, item)
        self.execution, terminal = self._execute(INSTRUCTION_LIMIT)
        if not self.execution or self.execution[0].pc != entry or terminal is None:
            raise ValueError("assembly control has no complete execution within the instruction budget")
        self.terminal = terminal
        self.position = 0
        self.handle: str | None = uuid.uuid4().hex
        self.connected = True

    def _check_files(self) -> None:
        try:
            changed = any(file_sha256(path) != self.identities[key] for key, path in self.files.items())
        except OSError:
            self.disconnect()
            raise
        if changed:
            self.disconnect()
            raise ValueError("stale Sail executable, profile or control image")

    def _execute(self, limit: int, *, stop_pc: int | None = None) -> tuple[list[Retirement], int | None]:
        self._check_files()
        trace_file = self.elf.with_suffix(".trace")
        trace_file.unlink(missing_ok=True)
        args = [str(self.simulator), "--config", str(self.profile), "--trace-commit",
                "--trace-output", str(trace_file), "--inst-limit", str(limit)]
        if stop_pc is not None:
            args.extend(("--stop-at-pc", hex(stop_pc)))
        args.append(str(self.elf))
        process = subprocess.run(args, stdin=subprocess.DEVNULL, capture_output=True, timeout=10,
                                 cwd=self.elf.parent, check=False)
        if trace_file.stat().st_size > TRACE_LIMIT or len(process.stdout) + len(process.stderr) > TRACE_LIMIT:
            raise ValueError("Sail debugger output budget exceeded")
        self._check_files()
        data = trace_file.read_bytes()
        records = _retirements(data, self.sites, limit)
        said = (process.stdout + process.stderr).decode("utf-8")
        terminal = None
        if any(row.lstrip().startswith(("SUCCESS", "FAILURE")) for row in said.splitlines()):
            _, terminal, _ = first_slice._simulator_transcript(data.decode("ascii") + said, process.returncode)
        elif process.returncode != 0 or (stop_pc is None and len(records) != limit):
            raise ValueError("Sail execution ended before the requested stop")
        return records, terminal

    def _current(self, handle: str | None) -> None:
        if handle is None or self.handle != handle or not self.connected:
            raise ValueError("stale or disconnected stop handle")
        self._check_files()

    def _stop(self, position: int) -> dict[str, object]:
        self.handle = None
        if position:
            if position == len(self.execution):
                records, terminal = self._execute(position)
            else:
                pc = self.execution[position].pc
                if any(record.pc == pc for record in self.execution[:position]):
                    raise ValueError("repeated PC is outside the packet control stop map")
                # One instruction of headroom distinguishes a PC stop from a missed breakpoint.
                records, terminal = self._execute(position + 1, stop_pc=pc)
            expected = self.terminal if position == len(self.execution) else None
            if records != self.execution[:position] or terminal != expected:
                raise ValueError("Sail replay diverged from the selected control execution")
        else:
            self._check_files()
        self.position = position
        if position == len(self.execution):
            return {"status": "exited", "retired": position, "htif": self.terminal}
        self.handle = uuid.uuid4().hex
        return self.where(self.handle)

    def where(self, handle: str | None) -> dict[str, object]:
        self._current(handle)
        pc = self.execution[self.position].pc
        site = self.sites[pc]
        return {"status": "stopped", "handle": handle, "retired": self.position,
                "pc": pc, "line": site.line, "instruction": self.source.splitlines()[site.line - 1].strip()}

    def advance(self, handle: str | None, line: int | None = None, *, finish: bool = False) -> dict[str, object]:
        self._current(handle)
        if line is not None:
            if not any(site.line == line for site in self.sites.values()):
                raise ValueError("no executable instruction at that assembly line")
            target = next((i for i in range(self.position + 1, len(self.execution))
                           if self.sites[self.execution[i].pc].line == line), len(self.execution))
        else:
            target = len(self.execution) if finish else self.position + 1
        return self._stop(target)

    def disconnect(self) -> None:
        self.handle = None
        self.connected = False

    def reconnect(self) -> dict[str, object]:
        if self.connected:
            raise ValueError("session is already connected")
        self.connected = True
        try:
            return self._stop(self.position)
        except (OSError, RuntimeError, ValueError, subprocess.SubprocessError):
            self.disconnect()
            raise

    def stack(self, handle: str | None) -> list[dict[str, object]]:
        self._current(handle)
        frames: list[tuple[str, int]] = [("_start", self.execution[0].pc)]
        for index, retired in enumerate(self.execution[:self.position]):
            item = self.sites[retired.pc].item
            next_pc = self.execution[index + 1].pc
            if any(effect.startswith("T ") for effect in retired.effects):
                if next_pc != self.symbols["__vela_handler"][1]:
                    raise ValueError("unmapped trap handler")
                frames.append(("__vela_handler", retired.pc))
            elif item.text == "call":
                if next_pc != self.symbols[item.args[0]][1]:
                    raise ValueError("call target disagrees with execution")
                frames.append((item.args[0], retired.pc))
            elif item.text == "cjalr" and item.args == ["cnull", "cra", "0"]:
                if len(frames) < 2 or frames[-1][1] + 4 != next_pc:
                    raise ValueError("return target disagrees with the call stack")
                frames.pop()
        frame_pc = self.execution[self.position].pc
        result: list[dict[str, object]] = []
        for name, caller in reversed(frames):
            result.append({"name": name, "pc": frame_pc, "line": self.sites[frame_pc].line})
            frame_pc = caller
        return result

    def evaluate(self, handle: str | None, expression: str) -> dict[str, object]:
        """Inspect one merged register or one observed field."""
        self._current(handle)
        if len(expression) > 32:
            raise ValueError("inspection expression exceeds 32 characters")
        name, _, field = expression.partition(".")
        if name not in dialect.REGISTERS or (field and field not in {
                "tag", "bits", "length", "base", "address", "permissions", "sealed", "provenance"}):
            raise ValueError("only read-only architectural register fields are supported")
        if "." in expression and not field:
            raise ValueError("empty register field")
        number = dialect.REGISTERS[name]
        fields: dict[str, int] = {}
        for retired in self.execution[:self.position]:
            item = self.sites[retired.pc].item
            for effect in retired.effects:
                if not effect.startswith("X "):
                    continue
                _, destination, tag, bits = effect.split()
                if int(destination) == number:
                    fields = {"tag": int(tag), "bits": int(bits, 16)}
                elif (item.text == "cgetlen" and dialect.REGISTERS[item.args[1]] == number
                      and dialect.REGISTERS[item.args[0]] == int(destination)):
                    fields["length"] = int(bits, 16)
        if field:
            return {"status": "available", "value": fields[field]} if field in fields else {"status": "unavailable"}
        return {"status": "available", **fields} if fields else {"status": "unavailable"}


def command(session: Session, text: str) -> object:
    """Apply a bounded local inspection command to the current stop."""
    if len(text) > 80:
        raise ValueError("inspection command exceeds 80 characters")
    if text == "step":
        return session.advance(session.handle)
    if text == "continue":
        return session.advance(session.handle, finish=True)
    if text == "where":
        return session.where(session.handle)
    if text == "source":
        return [{"line": i, "text": line} for i, line in enumerate(session.source.splitlines(), 1)]
    if text == "stack":
        return session.stack(session.handle)
    if text == "disconnect":
        session.disconnect()
        return {"status": "disconnected"}
    if text == "reconnect":
        return session.reconnect()
    if match := re.fullmatch(r"until ([1-9][0-9]{0,5})", text):
        return session.advance(session.handle, int(match[1]))
    if text.startswith("eval "):
        return session.evaluate(session.handle, text[5:])
    raise ValueError("unsupported simulator inspection command")
