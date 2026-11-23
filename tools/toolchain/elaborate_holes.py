# SPDX-License-Identifier: Apache-2.0
"""Report open goals from a diagnostic-only mathematical elaboration."""

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from toolchain.ast import VelaError, position
from toolchain.elaborate_types import _SORT, Node, _Binding, _Term

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


@dataclass(frozen=True)
class HoleGoal:
    name: str
    line: int
    column: int
    expected: str | None
    context: str

    def describe(self) -> str:
        goal = f"expected {self.expected}" if self.expected else "expected type unavailable"
        return f"{self.name} unresolved at {self.line}:{self.column}, {goal}. {self.context}"


class OpenGoals(VelaError):
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
        self.placeholders: dict[int, str] = {}
        self.remaining = 65_536

    def _text(self, term: _Term, names: dict[int, str]) -> str:
        checker = self.elaborator
        term = checker.resolve(term)
        if term.kind == "var":
            index = cast("int", term.value)
            return names.get(index, self.placeholders.get(index, f"#{index}"))
        if term.kind in {"const", "nat"}:
            return str(term.value)
        if term.kind == "bool":
            return "true" if term.value else "false"
        if term.kind == "app":
            head, args = checker.spine(term)
            return f"{self._text(head, names)}({', '.join(self._text(arg, names) for arg in args)})"
        value = f"[{term.value}]" if term.value != "" else ""
        args = ", ".join(self._text(arg, names) for arg in term.args)
        return term.kind + value + (f"({args})" if args else "")

    def observe(self, node: Node, expected: _Term | None, environment: dict[str, _Binding]) -> _Binding:
        checker = self.elaborator
        start, end = cast("list[int]", node["span"])
        names = {cast("int", binding.term.value): name for name, binding in environment.items()
                 if binding.term.kind == "var"}
        goal = self._text(expected, names) if expected is not None else None
        details = [f"{name}: {self._text(binding.type, names)}" for name, binding in environment.items()]
        details.extend(f"branch fact {self._text(fact, names)}" for fact in checker.active_facts)
        details.extend(f"{name}: {mode} loan of {'.'.join((owner, *fields))}"
                       for name, (mode, owner, fields) in checker.local_borrows.items())
        details.extend(f"{name}: view of {owner}" for name, owner in checker.slice_views.items())
        details.extend(f"{name}: awaiting initialization" for name in sorted(checker.uninitialized_out_params))
        if checker.current_return_type is not None:
            details.append(f"return {self._text(checker.current_return_type, names)}")
        context = "Context: " + ", ".join(details) if details else "Empty local context"
        self.remaining -= len(context.encode()) + len((goal or "").encode())
        if self.remaining < 0:
            raise checker.fail("limit", "named-hole context exceeds the diagnostic budget", node)
        self.observations[start] = (goal, context)
        domain = expected if expected is not None else checker.meta(_SORT, environment)
        variable = checker.fresh(domain)
        self.placeholders[cast("int", variable.value)] = checker.protocol.source[start:end].decode("ascii")
        return _Binding(variable, domain)

    def refusal(self, declarations: list[Node]) -> OpenGoals:
        checker = self.elaborator
        stopped: VelaError | None = None
        try:
            for declaration in declarations:
                checker.declaration(declaration)
        except VelaError as error:
            stopped = error
        source = checker.protocol.source
        goals: list[HoleGoal] = []
        for start, node in sorted(checker.protocol.holes.items()):
            end = cast("list[int]", node["span"])[1]
            site = position(source[:start].decode("utf-8"))
            expected, context = self.observations.get(start, (None, "Checking did not reach this site"))
            goals.append(HoleGoal(source[start:end].decode("ascii"), site.line, site.column, expected, context))
        return OpenGoals(tuple(goals), stopped)
