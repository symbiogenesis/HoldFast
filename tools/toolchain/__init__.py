# SPDX-License-Identifier: Apache-2.0
"""Check pure HoldFast declarations and translate them to Gallina.

The Rocq-extracted parser supplies syntax to the name and type checker.
See the [pure prototype](../../docs/tooling/pure-prototype.md) for its scope.
"""

import hashlib
from dataclasses import dataclass, replace
from importlib import import_module
from typing import TYPE_CHECKING, cast

from toolchain import ast as syntax
from toolchain.ast import (
    MAX_BLOCK_DEPTH,
    MAX_EXPRESSION_DEPTH,
    MAX_LITERAL_DIGITS,
    MAX_SOURCE_BYTES,
    HoldFastError,
    ValueType,
)
from toolchain.compiler_trace import Recorder
from toolchain.facts import Facts, PureType, SymbolKind

if TYPE_CHECKING:
    from toolchain.remarks import Decisions

__all__ = [
    "MAX_BLOCK_DEPTH",
    "MAX_EXPRESSION_DEPTH",
    "MAX_LITERAL_DIGITS",
    "MAX_SOURCE_BYTES",
    "HoldFastError",
    "StaticEvaluation",
    "Translation",
    "ValueType",
    "evaluate",
    "inspect_source",
    "parse_module",
    "translate",
    "translate_ast",
]

_TYPES: dict[ValueType, str] = {
    "Nat": "Corelib.Init.Datatypes.nat",
    "bool": "Corelib.Init.Datatypes.bool",
}
_TRUE = "Corelib.Init.Datatypes.true"
_FALSE = "Corelib.Init.Datatypes.false"
_SATURATING_SUB = "Nat.SaturatingSub"
_NAT_ARITHMETIC = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "modulo",
                   _SATURATING_SUB: "sub"}
_NAT_PREMISES = {"-": "Nat subtraction requires proof that the left operand is at least the right operand. "
                       "Use Nat.SaturatingSub to clamp at zero",
                 "/": "Nat division requires proof of a nonzero divisor",
                 "%": "Nat remainder requires proof of a nonzero divisor"}
MAX_STATIC_WORK = 20_000
MAX_STATIC_DEPTH = 128
MAX_STATIC_NAT = 10 ** MAX_LITERAL_DIGITS - 1
MAX_OUTPUT_BYTES = 1_048_576
type _Premises = frozenset[tuple[str, str, str]]


def _nat_term(value: int) -> str:
    return f"({value} : {_TYPES['Nat']})"


@dataclass(frozen=True)
class Translation:
    module: str
    gallina: str


@dataclass(frozen=True)
class StaticEvaluation:
    value_type: ValueType
    value: int | bool


@dataclass(frozen=True)
class _Token:
    kind: str
    text: str
    line: int
    column: int

    @property
    def site(self) -> syntax.Site:
        return syntax.Site(self.line, self.column)


@dataclass(frozen=True)
class _Expression:
    value_type: ValueType
    gallina: str
    depth: int = 1
    natural: int | None = None
    minimum: int = 0
    when_true: _Premises = frozenset()
    when_false: _Premises = frozenset()

    @property
    def proof_term(self) -> str:
        return self.gallina if self.natural is None else _nat_term(self.natural)


@dataclass(frozen=True)
class _Signature:
    parameters: tuple[tuple[syntax.Name, ValueType, int | None], ...]
    result: ValueType
    symbol: int | None
    source: syntax.Function
    constants: dict[str, _Local]


@dataclass(frozen=True)
class _Static:
    value_type: ValueType
    value: int | bool


@dataclass(frozen=True)
class _Local:
    value_type: ValueType
    symbol: int | None
    static: _Static | None = None
    required_static: bool = False
    gallina: str | None = None
    initializer: _Expression | None = None


def _tokens(source: bytes) -> list[_Token]:
    text = syntax.source_text(source).replace("\r\n", "\n").replace("\r", "\n")
    result: list[_Token] = []
    offset, line, column = 0, 1, 1
    while offset < len(text):
        character = text[offset]
        if character in " \t\n":
            if character == "\n":
                line, column = line + 1, 1
            else:
                column += 1
            offset += 1
            continue
        if text.startswith("//", offset):
            end = text.find("\n", offset)
            end = len(text) if end == -1 else end
            column += end - offset
            offset = end
            continue
        if match := syntax.IDENTIFIER.match(text, offset):
            spelling = match.group()
            if spelling in syntax.UNSUPPORTED:
                raise HoldFastError("unsupported", line, column, syntax.unsupported_message(spelling))
            kind = "keyword" if spelling in syntax.KEYWORDS else "name"
        elif match := syntax.DECIMAL.match(text, offset):
            spelling = match.group()
            if len(spelling.replace("_", "")) > MAX_LITERAL_DIGITS:
                raise HoldFastError("limit", line, column,
                                f"literal exceeds {MAX_LITERAL_DIGITS} decimal digits")
            kind = "decimal"
        elif text[offset:offset + 2] in {"->", "=>", "==", "!=", "<=", ">=", "&&", "||"}:
            spelling, kind = text[offset:offset + 2], "symbol"
        elif character in "();,:.{}=+*/%-!<>":
            spelling, kind = character, "symbol"
        else:
            raise HoldFastError("syntax", line, column, f"unexpected character {character!r}")
        result.append(_Token(kind, spelling, line, column))
        offset += len(spelling)
        column += len(spelling)
    result.append(_Token("eof", "end of file", line, column))
    return result


def _error(kind: str, message: str, site: syntax.Site) -> HoldFastError:
    return HoldFastError(kind, site.line, site.column, message)


def _comparison_premises(op: str, left: str, right: str) -> tuple[_Premises, _Premises]:
    if op in {">", ">="}:
        op, left, right = ("<" if op == ">" else "<="), right, left
    if op in {"==", "!="}:
        left, right = sorted((left, right))
        return frozenset({(op, left, right)}), frozenset({("!=" if op == "==" else "==", left, right)})
    return frozenset({(op, left, right)}), frozenset({("<=" if op == "<" else "<", right, left)})


def _natural_result(op: str, left: int, right: int) -> int | None:
    if op == "+":
        return left + right
    if op == "*":
        return left * right
    if op == _SATURATING_SUB:
        return max(0, left - right)
    if op == "-":
        return left - right if left >= right else None
    if not right:
        return None
    return left // right if op == "/" else left % right


class _Elaborator:
    """Resolve and type located syntax, emitting only the established pure terms."""

    def __init__(self, facts: Facts | None = None, *, decisions: Decisions | None = None) -> None:
        self.functions: dict[str, _Signature] = {}
        self.constants: dict[str, _Local] = {}
        self.static_work = MAX_STATIC_WORK
        self.specialization_depth = 0
        self.fresh_argument = 0
        self.facts = facts
        self.decisions = decisions

    def copy(self) -> _Elaborator:
        cloned = _Elaborator()
        cloned.functions = dict(self.functions)
        cloned.constants = dict(self.constants)
        cloned.static_work = self.static_work
        cloned.specialization_depth = self.specialization_depth
        cloned.fresh_argument = self.fresh_argument
        return cloned

    def _declare(self, name: syntax.Name, kind: SymbolKind, detail: str, value_type: PureType, *,
                 inferred: bool | None = None) -> int | None:
        return None if self.facts is None else self.facts.declare(name, kind, detail, value_type, inferred=inferred)

    def _reference(self, identity: int | None, site: syntax.Site) -> None:
        if self.facts is not None:
            if identity is None:
                raise RuntimeError("pure inspection is missing a resolved declaration identity")
            self.facts.reference(identity, site)

    def _bounded(self, value_type: ValueType, gallina: str,
                 children: tuple[_Expression, ...], site: syntax.Site) -> _Expression:
        if len(gallina) > MAX_OUTPUT_BYTES:
            raise _error("limit", "pure translation exceeds its output byte budget", site)
        depth = max((child.depth for child in children), default=0) + 1
        if depth > MAX_EXPRESSION_DEPTH:
            raise _error("limit", f"expression exceeds depth {MAX_EXPRESSION_DEPTH}", site)
        return _Expression(value_type, gallina, depth)

    def function(self, function: syntax.Function) -> str:
        name = function.name
        if name.text in self.functions or name.text in self.constants:
            raise _error("name", f"duplicate function '{name.text}'", name.site)
        parameters = ", ".join(f"{'const ' if parameter.text in function.const_parameters else ''}{value_type} {parameter.text}"
                               for parameter, value_type in function.parameters)
        identity = self._declare(name, "function",
                                 f"public {'const ' if function.is_const else ''}{function.result} {name.text}({parameters})",
                                 PureType(function.result, tuple(
                                     (value_type, parameter.text in function.const_parameters)
                                     for parameter, value_type in function.parameters), function.is_const))
        if self.facts is not None:
            self.facts.enter_scope("function", name.site)
        environment: dict[str, _Local] = {}
        parameter_facts: list[tuple[syntax.Name, ValueType, int | None]] = []
        for parameter, value_type in function.parameters:
            if parameter.text in environment:
                raise _error("name", f"duplicate parameter '{parameter.text}'", parameter.site)
            required_static = parameter.text in function.const_parameters
            symbol = self._declare(parameter, "parameter",
                                   f"{'const ' if required_static else ''}{parameter.text}: {value_type}",
                                   PureType(value_type))
            environment[parameter.text] = _Local(value_type, symbol, required_static=required_static)
            parameter_facts.append((parameter, value_type, symbol))
        body = self._block(function.body, environment, 1)
        if self.facts is not None:
            self.facts.leave_scope()
        if body.value_type != function.result:
            raise _error("type", f"function '{name.text}' returns {body.value_type}, "
                         f"expected {function.result}", function.body.site)
        self.functions[name.text] = _Signature(tuple(parameter_facts),
                                               function.result, identity, function, dict(self.constants))
        binders = "".join(f" (v_{parameter.text} : {_TYPES[value_type]})"
                          for parameter, value_type in function.parameters)
        return f"Definition f_{name.text}{binders} : {_TYPES[function.result]} :=\n  {body.gallina}."

    def _static_tick(self, site: syntax.Site, depth: int = 0) -> None:
        self.static_work -= 1
        if self.static_work < 0 or depth > MAX_STATIC_DEPTH:
            raise _error("limit", "constant evaluation work or nesting budget exhausted", site)

    def _literal(self, value: _Static) -> str:
        if value.value_type == "bool":
            return _TRUE if value.value else _FALSE
        return _nat_term(int(value.value))

    def _require_static(self, expression: syntax.Expression, environment: dict[str, _Local]) -> None:
        pending = [expression]
        while pending:
            current = pending.pop()
            self._static_tick(current.site)
            if self.facts is not None:
                self.facts.require_static_literal(current.site)
            if current.kind == "name":
                name = cast("str", current.value)
                local = environment.get(name, self.constants.get(name))
                if local is not None and local.static is None and not local.required_static:
                    raise _error("unsupported", f"constant initializer depends on runtime binding '{name}'; "
                                 "only earlier constants and static pure-call arguments are permitted", current.site)
            pending.extend(reversed(current.children))

    def _static_value(self, expression: syntax.Expression, environment: dict[str, _Local]) -> _Static | None:
        """Evaluate closed static inputs; retain symbolic static binders until specialization."""
        pending = [expression]
        while pending:
            current = pending.pop()
            self._static_tick(current.site)
            if current.kind == "name":
                local = environment.get(cast("str", current.value), self.constants.get(cast("str", current.value)))
                if local is not None and local.static is None:
                    return None
            pending.extend(current.children)
        available = {name: local.static for name, local in {**self.constants, **environment}.items()
                     if local.static is not None}
        return self._evaluate(expression, available)

    def _constant(self, declaration: syntax.Constant, environment: dict[str, _Local],
                  premises: _Premises = frozenset()) -> _Local:
        checked = self._expression(declaration.value, environment, premises)
        if checked.value_type != declaration.value_type:
            raise _error("type", f"constant '{declaration.name.text}' must be {declaration.value_type}, "
                         f"got {checked.value_type}", declaration.name.site)
        self._require_static(declaration.value, environment)
        value = self._static_value(declaration.value, environment)
        detail = f"const {declaration.value_type} {declaration.name.text}"
        if value is not None:
            spelling = ("true" if value.value else "false") if value.value_type == "bool" else str(value.value)
            detail += f" = {spelling}"
        symbol = self._declare(declaration.name, "constant", detail, PureType(declaration.value_type))
        return _Local(declaration.value_type, symbol, value, True,
                      initializer=checked if value is None else replace(checked, gallina=self._literal(value)))

    def constant(self, declaration: syntax.Constant) -> str:
        name = declaration.name
        if name.text in self.constants or name.text in self.functions:
            raise _error("name", f"duplicate declaration '{name.text}'", name.site)
        local = self._constant(declaration, {})
        self.constants[name.text] = local
        if local.static is None:
            raise RuntimeError("constant declaration lost its static value")
        return f"Definition c_{name.text} : {_TYPES[local.value_type]} :=\n  {self._literal(local.static)}."

    def _evaluate(self, expression: syntax.Expression, environment: dict[str, _Static], depth: int = 0) -> _Static:
        self._static_tick(expression.site, depth)
        kind, name = expression.kind, cast("str", expression.value)
        if kind == "nat":
            return _Static("Nat", int(name.replace("_", "")))
        if kind == "bool":
            return _Static("bool", cast("bool", expression.value))
        if kind == "name":
            value = environment.get(name)
            if value is None:
                raise _error("unsupported", f"constant initializer has no static value for '{name}'", expression.site)
            return value
        if kind == "group":
            return self._evaluate(expression.children[0], environment, depth + 1)
        if kind == "unary":
            operand = self._evaluate(expression.children[0], environment, depth + 1)
            return _Static("bool", not operand.value)
        if kind == "binary" and name in {"&&", "||"}:
            left = self._evaluate(expression.children[0], environment, depth + 1)
            if name == "&&" and not left.value:
                return _Static("bool", False)
            if name == "||" and left.value:
                return _Static("bool", True)
            return self._evaluate(expression.children[1], environment, depth + 1)
        arguments = tuple(self._evaluate(child, environment, depth + 1) for child in expression.children)
        if kind == "call" and name != _SATURATING_SUB:
            signature = self.functions[name]
            inputs = {parameter.text: value for (parameter, _, _), value in zip(signature.parameters, arguments, strict=True)}
            captured = {label: local.static for label, local in signature.constants.items() if local.static is not None}
            return self._evaluate_block(signature.source.body, {**captured, **inputs}, depth + 1)
        left, right = arguments
        if name == "==":
            return _Static("bool", left.value == right.value)
        if name == "!=":
            return _Static("bool", left.value != right.value)
        first, second = left.value, right.value
        if name == "<=":
            return _Static("bool", first <= second)
        if name == "<":
            return _Static("bool", first < second)
        if name == ">=":
            return _Static("bool", first >= second)
        if name == ">":
            return _Static("bool", first > second)
        if ((name == "+" and first > MAX_STATIC_NAT - second)
                or (name == "*" and first != 0 and second > MAX_STATIC_NAT // first)):
            raise _error("limit", f"constant result exceeds {MAX_LITERAL_DIGITS} decimal digits", expression.site)
        result = _natural_result(name, first, second)
        if result is None:
            raise _error("type", _NAT_PREMISES[name], expression.site)
        return _Static("Nat", result)

    def _evaluate_block(self, block: syntax.Block, environment: dict[str, _Static], depth: int) -> _Static:
        self._static_tick(block.site, depth)
        extended = dict(environment)
        for binding in block.bindings:
            if isinstance(binding, syntax.Reassignment):
                raise _error("unsupported", "constant evaluation does not admit reassignment", binding.site)
            value = self._evaluate(binding.value, extended, depth + 1)
            extended[binding.name.text] = value
        terminal = block.terminal
        if isinstance(terminal, syntax.Return):
            return self._evaluate(terminal.value, extended, depth + 1)
        condition = self._evaluate(terminal.condition, extended, depth + 1)
        return self._evaluate_block(terminal.yes if condition.value else terminal.no, extended, depth + 1)

    def _block(self, block: syntax.Block, environment: dict[str, _Local], nesting: int,
               premises: _Premises = frozenset()) -> _Expression:
        if self.facts is not None:
            self.facts.enter_scope("block", block.site)
        try:
            return self._scoped_block(block, environment, nesting, premises)
        finally:
            if self.facts is not None:
                self.facts.leave_scope()

    def _scoped_block(self, block: syntax.Block, environment: dict[str, _Local], nesting: int,
                      premises: _Premises) -> _Expression:
        if nesting + len(block.bindings) > MAX_BLOCK_DEPTH:
            raise _error("limit", f"block or binding nesting exceeds {MAX_BLOCK_DEPTH}", block.site)
        extended = dict(environment)
        values: list[tuple[syntax.Binding | syntax.Constant, _Expression]] = []
        for binding in block.bindings:
            if isinstance(binding, syntax.Reassignment):
                selected = extended.get(binding.name.text, self.constants.get(binding.name.text))
                if selected is None:
                    raise _error("name", f"unbound assignment target '{binding.name.text}'", binding.name.site)
                mode = "const" if selected.static is not None or selected.required_static else "immutable binding"
                raise _error("unsupported", f"cannot reassign {mode} '{binding.name.text}'; "
                             "let and unmarked type-first bindings are immutable. Declare var for local "
                             "reassignment in the wider HoldFast surface; the pure prototype does not support mutation",
                             binding.name.site)
            if binding.name.text in extended:
                raise _error("name", f"duplicate local binding '{binding.name.text}'", binding.name.site)
            if isinstance(binding, syntax.Constant):
                local = self._constant(binding, extended, premises)
                extended[binding.name.text] = local
                if local.initializer is None:
                    raise RuntimeError("local constant lost its checked expression")
                values.append((binding, local.initializer))
                continue
            value = self._expression(binding.value, extended, premises)
            if binding.annotation is not None and binding.annotation != value.value_type:
                raise _error("type", f"local '{binding.name.text}' requires {binding.annotation}, "
                             f"but its initializer has type {value.value_type}", binding.site)
            symbol = self._declare(binding.name, "variable", f"{binding.name.text}: {value.value_type}",
                                   PureType(value.value_type),
                                   inferred=False if binding.annotation is not None else None)
            extended[binding.name.text] = _Local(value.value_type, symbol, initializer=value)
            values.append((binding, value))
        terminal = block.terminal
        if isinstance(terminal, syntax.Return):
            body = self._expression(terminal.value, extended, premises)
        else:
            condition = self._expression(terminal.condition, extended, premises)
            if condition.value_type != "bool":
                raise _error("type", "if condition must be bool", terminal.site)
            yes = self._block(terminal.yes, extended, nesting + len(values) + 1, premises | condition.when_true)
            no = self._block(terminal.no, extended, nesting + len(values) + 1, premises | condition.when_false)
            if yes.value_type != no.value_type:
                raise _error("type", "if branches must have the same type", terminal.site)
            body = self._bounded(yes.value_type,
                                 f"(if {condition.gallina} then {yes.gallina} else {no.gallina})",
                                 (condition, yes, no), terminal.site)
        for binding, value in reversed(values):
            body = self._bounded(body.value_type,
                                 f"(let v_{binding.name.text} := {value.gallina} in {body.gallina})",
                                 (value, body), binding.site)
        return body

    def _expression(self, expression: syntax.Expression,
                    environment: dict[str, _Local], premises: _Premises = frozenset()) -> _Expression:
        checked = self._checked_expression(expression, environment, premises)
        if self.facts is not None:
            self.facts.expression(expression.kind, expression.site, checked.value_type)
            if self.facts.collect_completion_options and expression.kind in {"nat", "bool"}:
                available = {**self.constants, **environment}
                candidates = tuple(local for local in available.values()
                                   if local.symbol is not None and local.value_type == checked.value_type)
                choices = tuple(local.symbol for local in candidates if local.symbol is not None)
                static = tuple(local.symbol for local in candidates if local.symbol is not None
                               and (local.required_static or local.static is not None))
                spelling = (cast("str", expression.value) if expression.kind == "nat"
                            else "true" if expression.value else "false")
                self.facts.literal_values(expression.site, spelling, checked.value_type, choices, static)
        return checked

    def _checked_expression(self, expression: syntax.Expression,
                            environment: dict[str, _Local], premises: _Premises) -> _Expression:
        kind, value, site = expression.kind, expression.value, expression.site
        if kind == "nat":
            literal = int(cast("str", value).replace("_", ""))
            return _Expression("Nat", _nat_term(literal), natural=literal, minimum=literal)
        if kind == "bool":
            return _Expression("bool", _TRUE if value else _FALSE)
        if kind == "group":
            return self._expression(expression.children[0], environment, premises)
        name = cast("str", value)
        if kind == "name":
            local = environment.get(name, self.constants.get(name))
            if local is None:
                raise _error("name", f"unbound value '{name}'", site)
            self._reference(local.symbol, site)
            if self.facts is not None and self.facts.collect_completion_options:
                available = {**self.constants, **environment}
                choices = tuple(candidate.symbol for candidate in available.values()
                                if candidate.symbol is not None and candidate.value_type == local.value_type
                                and (not (local.required_static or local.static is not None)
                                     or candidate.required_static or candidate.static is not None))
                self.facts.visible_values(site, choices)
            term = local.gallina if local.gallina is not None else f"v_{name}" if name in environment else f"c_{name}"
            defined = local.initializer or _Expression(local.value_type, term)
            if local.static is not None and local.value_type == "Nat":
                literal = int(local.static.value)
                return replace(defined, gallina=term, depth=1, natural=literal, minimum=literal)
            return replace(defined, gallina=term, depth=1)
        # Specialization may expand a short source argument into a large term.
        # Bound retained siblings before building the application's joined text.
        collected: list[_Expression] = []
        argument_bytes = 0
        for child in expression.children:
            child_premises = premises
            if collected and kind == "binary":
                if name == "&&":
                    child_premises |= collected[0].when_true
                elif name == "||":
                    child_premises |= collected[0].when_false
            argument = self._expression(child, environment, child_premises)
            argument_bytes += len(argument.gallina)
            if argument_bytes > MAX_OUTPUT_BYTES:
                raise _error("limit", "pure translation exceeds its output byte budget", site)
            collected.append(argument)
        arguments = tuple(collected)
        if kind == "call" and name == _SATURATING_SUB:
            if len(arguments) != 2:
                raise _error("type", f"'{name}' expects 2 arguments, got {len(arguments)}", site)
            if any(label is not None for label in expression.labels):
                raise _error("type", f"'{name}' takes positional arguments", site)
        elif kind == "call":
            signature = self.functions.get(name)
            if signature is None:
                local = environment.get(name, self.constants.get(name))
                if local is not None and (local.static is not None or local.required_static):
                    raise _error("type", f"constant '{name}' is a value and cannot be called", site)
                raise _error("name", f"unknown or forward function '{name}'; "
                             "only earlier declarations are callable", site)
            if len(arguments) != len(signature.parameters):
                raise _error("type", f"function '{name}' expects {len(signature.parameters)} arguments, "
                             f"got {len(arguments)}", site)
            labeled = False
            for index, (argument, (parameter, expected, symbol), label) in enumerate(
                    zip(arguments, signature.parameters, expression.labels, strict=True), start=1):
                if label is None:
                    if labeled:
                        raise _error("name", "positional arguments cannot follow a named argument", expression.children[index - 1].site)
                else:
                    labeled = True
                    if label.text != parameter.text:
                        raise _error("name", f"argument {index} to '{name}' must name parameter '{parameter.text}', "
                                     f"got '{label.text}'", label.site)
                    self._reference(symbol, label.site)
                if argument.value_type != expected:
                    raise _error("type", f"argument {index} to '{name}' must be {expected}, "
                                 f"got {argument.value_type}", site)
                if parameter.text in signature.source.const_parameters:
                    try:
                        self._require_static(expression.children[index - 1], environment)
                    except HoldFastError as error:
                        if self.decisions is not None:
                            self.decisions.refused(site, signature.source.name, error)
                        raise
            self._reference(signature.symbol, site)
            if signature.source.const_parameters:
                try:
                    static_arguments = {parameter.text: self._static_value(source, environment)
                                        for (parameter, _, _), source in zip(signature.parameters, expression.children, strict=True)
                                        if parameter.text in signature.source.const_parameters}
                    closed_arguments = {key: value for key, value in static_arguments.items() if value is not None}
                    if len(closed_arguments) == len(static_arguments):
                        specialized = self._specialize(signature, arguments, closed_arguments, site)
                        if self.decisions is not None:
                            self.decisions.record("Specialized", site, signature.source.name, "closed static inputs substituted; call eliminated")
                        return specialized
                except HoldFastError as error:
                    if self.decisions is not None:
                        self.decisions.refused(site, signature.source.name, error)
                    raise
                if self.decisions is not None:
                    pending = ", ".join(key for key, value in static_arguments.items() if value is None)
                    self.decisions.record("SymbolicStaticArgument", site, signature.source.name,
                                          f"call retained pending static parameter(s): {pending}")
            term = f"f_{name}"
            if arguments:
                term = "(" + term + " " + " ".join(argument.gallina for argument in arguments) + ")"
            return self._bounded(signature.result, term, arguments, site)
        if kind == "unary":
            operand, = arguments
            if operand.value_type != "bool":
                raise _error("type", "'!' operand must be bool", site)
            checked = self._bounded("bool", f"(if {operand.gallina} then {_FALSE} else {_TRUE})", arguments, site)
            return replace(checked, when_true=operand.when_false, when_false=operand.when_true)
        left, right = arguments
        if name in {"&&", "||"}:
            if left.value_type != "bool" or right.value_type != "bool":
                raise _error("type", f"'{name}' operands must be bool", site)
            term = (f"(if {left.gallina} then {right.gallina} else {_FALSE})" if name == "&&"
                    else f"(if {left.gallina} then {_TRUE} else {right.gallina})")
            checked = self._bounded("bool", term, arguments, site)
            if name == "&&":
                return replace(checked, when_true=left.when_true | right.when_true)
            return replace(checked, when_false=left.when_false | right.when_false)
        if name in _NAT_ARITHMETIC:
            if left.value_type != "Nat" or right.value_type != "Nat":
                raise _error("type", f"'{name}' operands must be Nat", site)
            return self._natural_expression(name, expression, environment, premises, left, right)
        if left.value_type != right.value_type:
            raise _error("type", f"'{name}' operands must have the same type", site)
        if name in {"<", "<=", ">", ">="}:
            if left.value_type != "Nat":
                raise _error("type", f"'{name}' operands must be Nat", site)
            operation = "ltb" if name in {"<", ">"} else "leb"
            if name in {">", ">="}:
                term = (f"(let holdfast_cmp_left := {left.gallina} in "
                        f"let holdfast_cmp_right := {right.gallina} in "
                        f"Corelib.Init.Nat.{operation} holdfast_cmp_right holdfast_cmp_left)")
            else:
                term = f"(Corelib.Init.Nat.{operation} {left.gallina} {right.gallina})"
        elif left.value_type == "Nat":
            term = f"(Corelib.Init.Nat.eqb {left.gallina} {right.gallina})"
        else:
            # User locals start with v_; these fresh binders evaluate operands once.
            term = (f"(let holdfast_eq_left := {left.gallina} in "
                    f"let holdfast_eq_right := {right.gallina} in "
                    "if holdfast_eq_left then holdfast_eq_right else "
                    f"(if holdfast_eq_right then {_FALSE} else {_TRUE}))")
        if name == "!=":
            term = f"(if {term} then {_FALSE} else {_TRUE})"
        checked = self._bounded("bool", term, arguments, site)
        if left.value_type == "Nat":
            when_true, when_false = _comparison_premises(name, left.proof_term, right.proof_term)
            return replace(checked, when_true=when_true, when_false=when_false)
        return checked

    def _natural_expression(self, op: str, expression: syntax.Expression, environment: dict[str, _Local],
                            premises: _Premises, left: _Expression, right: _Expression) -> _Expression:
        if op == "-":
            a, b = left.proof_term, right.proof_term
            proven = (a == b or (right.natural is not None and left.minimum >= right.natural)
                      or ("<=", b, a) in premises or ("<", b, a) in premises
                      or ("==", min(a, b), max(a, b)) in premises)
            if not proven:
                bound = self._static_value(expression.children[1], environment)
                if bound is not None:
                    proven = left.minimum >= bound.value
                    if not proven:
                        actual = self._static_value(expression.children[0], environment)
                        proven = actual is not None and actual.value >= bound.value
            if not proven:
                raise _error("type", _NAT_PREMISES[op], expression.site)
        elif op in {"/", "%"}:
            zero, one, divisor = _nat_term(0), _nat_term(1), right.proof_term
            proven = (right.minimum > 0 or ("<", zero, divisor) in premises
                      or ("<=", one, divisor) in premises
                      or ("==", min(one, divisor), max(one, divisor)) in premises
                      or ("!=", min(zero, divisor), max(zero, divisor)) in premises)
            if not proven:
                bound = self._static_value(expression.children[1], environment)
                if bound is None or bound.value == 0:
                    raise _error("type", _NAT_PREMISES[op], expression.site)
        natural = (_natural_result(op, left.natural, right.natural)
                   if left.natural is not None and right.natural is not None else None)
        if natural is not None and natural > MAX_STATIC_NAT:
            natural = None
        minimum = natural or 0
        if op == "+":
            minimum = min(MAX_STATIC_NAT, left.minimum + right.minimum)
        elif op == "*":
            minimum = min(MAX_STATIC_NAT, left.minimum * right.minimum)
        operation = _NAT_ARITHMETIC[op]
        term = f"(Corelib.Init.Nat.{operation} {left.gallina} {right.gallina})"
        checked = self._bounded("Nat", term, (left, right), expression.site)
        return replace(checked, natural=natural, minimum=minimum)

    def _specialize(self, signature: _Signature, arguments: tuple[_Expression, ...],
                    static_arguments: dict[str, _Static], site: syntax.Site) -> _Expression:
        """Instantiate static binders while evaluating each runtime argument exactly once."""
        self.specialization_depth += 1
        if self.decisions is not None:
            self.decisions.expansions.append(syntax.Name(signature.source.name.text, site))
        previous_facts = self.facts
        previous_constants = self.constants
        self.facts = None
        self.constants = signature.constants
        try:
            self._static_tick(site, self.specialization_depth)
            # Captured module values remain the global fallback, as they were
            # when checking the original definition. They are not local binders:
            # parameters and locals may shadow them without becoming duplicates.
            environment: dict[str, _Local] = {}
            bindings: list[tuple[str, _Expression]] = []
            for (parameter, value_type, _), argument in zip(signature.parameters, arguments, strict=True):
                value = static_arguments.get(parameter.text)
                if value is not None:
                    environment[parameter.text] = _Local(value_type, None, value, True, self._literal(value))
                else:
                    fresh = f"holdfast_arg_{self.fresh_argument}"
                    self.fresh_argument += 1
                    bindings.append((fresh, argument))
                    environment[parameter.text] = _Local(value_type, None, gallina=fresh)
            body = self._block(signature.source.body, environment, 1)
            for fresh, argument in reversed(bindings):
                body = self._bounded(body.value_type, f"(let {fresh} := {argument.gallina} in {body.gallina})",
                                     (argument, body), site)
            return body
        finally:
            if self.decisions is not None:
                self.decisions.expansions.pop()
            self.facts = previous_facts
            self.constants = previous_constants
            self.specialization_depth -= 1


def gallina_module_name(name: str) -> str:
    """Encode an ASCII HoldFast module path injectively as a standalone Gallina identifier."""
    if "_" in name:
        return "HoldFastEncoded_" + name.encode("ascii").hex()
    return "HoldFast_" + name.replace(".", "_")


def _translate(source: bytes, module: syntax.Module, facts: Facts | None = None, *,
               elaborator: _Elaborator | None = None, trace: Recorder | None = None) -> Translation:
    elaborator = _Elaborator(facts) if elaborator is None else elaborator
    name = module.name.text
    emitted_module = gallina_module_name(name)
    # REUSE-IgnoreStart
    header = ("(* SPDX-License-Identifier: Apache-2.0 *)\n"
              # REUSE-IgnoreEnd
              f"(* HoldFast pure prototype: unqualified. Source SHA256: {hashlib.sha256(source).hexdigest()} *)\n"
              "From Corelib Require Import Init.Datatypes Init.Nat.\n\n"
              f"Module {emitted_module}.\n\n")
    footer = f"\n\nEnd {emitted_module}.\n"
    output_bytes = len(header) + len(footer)
    if output_bytes > MAX_OUTPUT_BYTES:
        raise _error("limit", "pure translation exceeds its output byte budget", module.name.site)
    definitions: list[str] = []
    for declaration in module.declarations:
        is_constant = isinstance(declaration, syntax.Constant)
        if elaborator.decisions is not None:
            elaborator.decisions.function = ("c_" if is_constant else "f_") + declaration.name.text
        if trace is None:
            definition = (elaborator.constant(declaration) if isinstance(declaration, syntax.Constant)
                          else elaborator.function(declaration))
        else:
            with trace.declaration(declaration.name.text, "constant" if is_constant else "function",
                                   declaration.name.site.line, declaration.name.site.column):
                definition = (elaborator.constant(declaration) if isinstance(declaration, syntax.Constant)
                              else elaborator.function(declaration))
        # Emission is ASCII: identifiers are ASCII and comments are not emitted.
        # Account for separators and the footer before retaining another definition.
        output_bytes += len(definition) + (2 if definitions else 0)
        if output_bytes > MAX_OUTPUT_BYTES:
            raise _error("limit", "pure translation exceeds its output byte budget", declaration.name.site)
        definitions.append(definition)
    gallina = header + "\n\n".join(definitions) + footer
    return Translation(name, gallina)


_LAST_ELABORATED: tuple[tuple[bytes, int, int, int, int], _Elaborator] | None = None


def _budget_key(source: bytes) -> tuple[bytes, int, int, int, int]:
    return (source, MAX_OUTPUT_BYTES, MAX_STATIC_WORK, MAX_STATIC_DEPTH, MAX_EXPRESSION_DEPTH)


def parse_module(source: bytes, *, trace: Recorder | None = None) -> syntax.Module:
    """Parse and decode pure HoldFast source through the Rocq-extracted checked parser."""
    checked = import_module("toolchain.parser_checked")
    if trace is None:
        return syntax.decode(source, checked.parse_checked(source))
    with trace.span("checked-parse"):
        parsed = checked.parse_checked(source)
    with trace.span("syntax-decode"):
        return syntax.decode(source, parsed)


def translate(source: bytes, *, trace: Recorder | None = None) -> Translation:
    """Validate the complete bounded source through the Rocq-extracted checked parser."""
    global _LAST_ELABORATED  # noqa: PLW0603
    elaborator = _Elaborator()
    if trace is None:
        translated = _translate(source, parse_module(source), elaborator=elaborator)
    else:
        with trace.span("compile"):
            trace.counter("source_bytes", len(source))
            with trace.span("parse"):
                module = parse_module(source, trace=trace)
            with trace.span("elaborate-and-emit"):
                translated = _translate(source, module, elaborator=elaborator, trace=trace)
            trace.counter("gallina_bytes", len(translated.gallina.encode("utf-8")))
    _LAST_ELABORATED = (_budget_key(source), elaborator.copy())
    return translated


def evaluate(source: bytes, expression: str, value_type: ValueType) -> StaticEvaluation:
    """Check the original source and one closed compiler constant initializer.

    The [playground contract](../../docs/tooling/playground.md#browser-behavior)
    restricts this development service to the existing bounded static evaluator.
    """
    global _LAST_ELABORATED  # noqa: PLW0603
    key = _budget_key(source)
    if _LAST_ELABORATED is not None and _LAST_ELABORATED[0] == key:
        elaborator = _LAST_ELABORATED[1].copy()
    else:
        elaborator = _Elaborator()
        _translate(source, parse_module(source), elaborator=elaborator)
        _LAST_ELABORATED = (key, elaborator.copy())
    if value_type not in {"Nat", "bool"}:
        raise HoldFastError("type", 1, 1, "expression: expected Nat or bool result type")
    if len(expression.encode("utf-8")) > 4096:
        raise HoldFastError("limit", 1, 1, "expression: exceeds 4096 UTF-8 bytes")
    probe = (f"module Playground;\npublic const {value_type} __holdfast_console_result =\n"
             f"{expression}\n;").encode()
    try:
        parsed = parse_module(probe)
    except HoldFastError as error:
        lines = expression.replace("\r\n", "\n").replace("\r", "\n").split("\n")
        line = max(1, error.line - 2)
        column = error.column if line <= len(lines) else len(lines[-1]) + 1
        line = min(line, len(lines))
        column = min(column, len(lines[line - 1]) + 1)
        raise HoldFastError(error.kind, line, column,
                        f"expression: {error.message}") from error
    if (len(parsed.declarations) != 1
            or not isinstance(parsed.declarations[0], syntax.Constant)
            or parsed.declarations[0].name.text != "__holdfast_console_result"):
        raise HoldFastError("syntax", 1, 1, "expression: expected exactly one constant initializer")
    try:
        result = elaborator._constant(parsed.declarations[0], {}).static
    except HoldFastError as error:
        # Evaluation may visit an earlier function's source site. Anchor the
        # refusal to this console invocation instead of relabeling that site.
        raise HoldFastError(error.kind, 1, 1,
                        f"expression: {error.message}") from error
    if result is None:
        raise HoldFastError("unsupported", 1, 1, "expression: expression must be closed and static")
    return StaticEvaluation(result.value_type, result.value)


def inspect_source(source: bytes, *, syntax_tree: bool = False,
                   completion_options: bool = False) -> dict[str, object]:
    """Return diagnostic resolution facts only after a complete successful pure check."""
    response = None
    if syntax_tree:
        response = import_module("toolchain.parser_checked").parse_checked(source)
        module = syntax.decode(source, response)
    else:
        module = parse_module(source)
    declaration_sites = {declaration.name.site: declaration.site
                         for declaration in module.declarations}
    facts = Facts(source, declaration_sites, expression_types=syntax_tree,
                  completion_options=completion_options)
    facts.enter_scope("module", module.name.site)
    _translate(source, module, facts)
    result = facts.result(expression_types=syntax_tree)
    if response is not None:
        result["syntax"] = response
    return result


def translate_ast(source: bytes, response: object) -> Translation:
    """Decode native located syntax and use the common checker/emitter, with no fallback."""
    return _translate(source, syntax.decode(source, response))
