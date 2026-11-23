# SPDX-License-Identifier: Apache-2.0
"""Report open goals from a diagnostic-only mathematical elaboration."""

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from toolchain.ast import VelaError, position
from toolchain.elaborate_types import _SORT, Node, _Binding, _Meta, _Term

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator

MAX_HOLES = 128
MAX_GOAL_BYTES = 65_536
_UNREACHED = "Checking did not reach this site"
_EMPTY = "Empty local context"


@dataclass(frozen=True)
class HoleGoal:
    name: str
    line: int
    column: int
    status: str
    expected: str | None
    context: str

    def describe(self) -> str:
        goal = f"expected {self.expected}" if self.expected is not None else "expected type unavailable"
        return f"{self.name} {self.status} at {self.line}:{self.column}, {goal}. {self.context}"


class OpenGoalsError(VelaError):
    def __init__(self, goals: tuple[HoleGoal, ...], stopped: VelaError | None) -> None:
        first = goals[0]
        message = "\n".join(goal.describe() for goal in goals)
        if stopped is None:
            super().__init__("inference", first.line, first.column, message)
        else:
            super().__init__(stopped.kind, stopped.line, stopped.column,
                             f"{stopped.message} at {stopped.line}:{stopped.column}\n{message}")
        self.goals = goals
        self.stopped = stopped


class HoleInspection:
    def __init__(self, elaborator: _Elaborator) -> None:
        self.elaborator = elaborator
        self.observations: dict[int, tuple[str | None, str]] = {}
        self.pending_types: dict[int, tuple[int, _Meta, dict[int, str]]] = {}
        self.placeholders: dict[int, str] = {}
        self.remaining = MAX_GOAL_BYTES - len(elaborator.protocol.holes) * max(len(_EMPTY), len(_UNREACHED))

    def _write(self, chunks: list[str], text: str) -> None:
        self.remaining -= len(text.encode("utf-8"))
        if self.remaining < 0:
            raise self.elaborator.fail("limit", "named-hole context exceeds the diagnostic budget")
        chunks.append(text)

    def _term(self, chunks: list[str], term: _Term, names: dict[int, str]) -> None:
        checker = self.elaborator
        term = checker.resolve(term)
        if term.kind == "var":
            index = cast("int", term.value)
            self._write(chunks, names.get(index, self.placeholders.get(index, f"#{index}")))
        elif term.kind in {"const", "nat"}:
            self._write(chunks, str(term.value))
        elif term.kind == "bool":
            self._write(chunks, "true" if term.value else "false")
        elif term.kind == "app":
            head, args = checker.spine(term)
            self._term(chunks, head, names)
            self._args(chunks, args, names)
        else:
            self._write(chunks, term.kind)
            if term.value != "":
                self._write(chunks, f"[{term.value}]")
            if term.args:
                self._args(chunks, term.args, names)

    def _args(self, chunks: list[str], args: list[_Term] | tuple[_Term, ...], names: dict[int, str]) -> None:
        self._write(chunks, "(")
        for index, argument in enumerate(args):
            if index:
                self._write(chunks, ", ")
            self._term(chunks, argument, names)
        self._write(chunks, ")")

    def observe(self, node: Node, expected: _Term | None, environment: dict[str, _Binding],
                *, facts: tuple[_Binding, ...] = ()) -> _Binding:
        checker = self.elaborator
        start, end = cast("list[int]", node["span"])
        names = {cast("int", binding.term.value): name for name, binding in environment.items()
                 if binding.term.kind == "var"}
        chunks: list[str] = []
        domain = checker.resolve(expected) if expected is not None else checker.meta(_SORT, environment)
        if domain.kind != "meta":
            self._term(chunks, domain, names)
        goal = "".join(chunks) or None
        chunks.clear()

        def entry(label: str, value: _Term | None = None) -> None:
            self._write(chunks, ", " if chunks else "Context: ")
            self._write(chunks, label)
            if value is not None:
                self._term(chunks, value, names)

        for name, binding in environment.items():
            entry(f"{name}: ", binding.type)
            if binding.term.kind != "var":
                self._write(chunks, " = ")
                self._term(chunks, binding.term, names)
        for fact in checker.active_facts:
            entry("branch fact ", fact)
        for proof in facts:
            entry("hypothesis ", proof.type)
        for name, (mode, owner, fields) in checker.local_borrows.items():
            entry(f"{name}: {mode} loan of {'.'.join((owner, *fields))}")
        for name, owner in checker.slice_views.items():
            entry(f"{name}: view of {owner}")
        for name in sorted(checker.uninitialized_out_params):
            entry(f"{name}: awaiting initialization")
        if checker.current_return_type is not None:
            entry("return ", checker.current_return_type)
        context = "".join(chunks) or _EMPTY
        self.observations[start] = (goal, context)
        if domain.kind == "meta":
            index = cast("int", domain.value)
            self.pending_types[start] = (index, checker.metas[index], names)
        else:
            self.pending_types.pop(start, None)
        variable = checker.fresh(domain)
        self.placeholders[cast("int", variable.value)] = checker.protocol.source[start:end].decode("ascii")
        return _Binding(variable, domain)

    def _resolved_types(self) -> None:
        checker = self.elaborator
        for start, (index, record, names) in self.pending_types.items():
            # Backtracking can discard a meta and reuse its index for another judgment.
            if index < len(checker.metas) and checker.metas[index] is record and record.solution is not None:
                chunks: list[str] = []
                self._term(chunks, record.solution, names)
                self.observations[start] = ("".join(chunks), self.observations[start][1])
        self.pending_types.clear()

    def refusal(self, declarations: list[Node]) -> OpenGoalsError:
        checker = self.elaborator
        stopped: VelaError | None = None
        try:
            for declaration in declarations:
                checker.declaration(declaration)
                self._resolved_types()
        except VelaError as error:
            stopped = error
        source = checker.protocol.source
        goals: list[HoleGoal] = []
        for start, node in sorted(checker.protocol.holes.items()):
            end = cast("list[int]", node["span"])[1]
            site = position(source[:start].decode("utf-8"))
            status = "unresolved"
            if start in self.observations:
                expected, context = self.observations[start]
            else:
                expected, context = None, _UNREACHED
                if stopped is not None and stopped.kind in {"unsupported", "limit", "timeout"}:
                    status = stopped.kind
            goals.append(HoleGoal(source[start:end].decode("ascii"), site.line, site.column, status, expected, context))
        return OpenGoalsError(tuple(goals), stopped)
