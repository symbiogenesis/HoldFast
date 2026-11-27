# SPDX-License-Identifier: Apache-2.0
"""Solver-trust ledger for elaborated HoldFast Gallina and its kernel assumption audit.

The mathematical elaborator emits an obligation it cannot kernel-prove as a named
`holdfast_solver_*` axiom carrying the real statement, preceded by a marker naming its
export, source location and reason. This module reads that ledger from emitted
text and checks that `Print Assumptions` reports exactly those axioms and nothing
else. A non-empty ledger is never acceptance evidence.
"""

import re
from dataclasses import dataclass

_MARKER = re.compile(
    r"^\(\* holdfast-solver-trust: (?P<export>\S+) at (?P<line>\d+):(?P<column>\d+); (?P<reason>.*?) \*\)\n"
    r"Axiom (?P<axiom>holdfast_solver_[A-Za-z0-9_]+) :",
    flags=re.MULTILINE,
)
_AXIOM = re.compile(r"^Axiom (\S+)", flags=re.MULTILINE)
_UNLEDGERED_ASSUMPTION = re.compile(
    r"^\s*(?:Parameter|Parameters|Variable|Variables|Hypothesis|Hypotheses|Conjecture|Axioms)\b",
    flags=re.MULTILINE,
)
_PROOF_BYPASS = re.compile(r"\b(?:Admitted|admit)\s*\.")
_KERNEL_BYPASS = re.compile(
    r"\b(?:Unset\s+(?:Guard|Positivity|Universe)\s+Checking"
    r"|Set\s+Type\s+in\s+Type"
    r"|Set\s+Universe\s+Checking\s+Off"
    r"|Bypass_check"
    r"|bypass_check"
    r"|Declare\s+ML\s+Module"
    r"|Unsafe)\b"
)
_ASSUMPTION_NAME = re.compile(r"^(?P<name>[A-Za-z_][A-Za-z0-9_'.]*) :")
_VERSION_RE = re.compile(r"\bversion\s+(?P<major>\d+)\.(?P<minor>\d+)(?:\.(?P<patch>\d+))?\b")


def _strip_rocq_comments(text: str) -> str:
    """Remove nested Rocq ``(* ... *)`` comments while preserving newlines and string literals."""
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        if depth == 0:
            if in_string:
                out.append(ch)
                if ch == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        out.append('"')
                        i += 2
                        continue
                    in_string = False
                i += 1
            elif ch == '"':
                in_string = True
                out.append(ch)
                i += 1
            elif ch == "(" and i + 1 < n and text[i + 1] == "*":
                depth = 1
                i += 2
            else:
                out.append(ch)
                i += 1
        elif ch == "(" and i + 1 < n and text[i + 1] == "*":
            depth += 1
            i += 2
        elif ch == "*" and i + 1 < n and text[i + 1] == ")":
            depth -= 1
            i += 2
        else:
            if ch == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def check_prover_version(
    version_output: str, minimum: tuple[int, int, int] = (9, 3, 0),
) -> tuple[int, int, int]:
    """Verify the Rocq prover meets the minimum patched kernel version (9.3.0+ fixes #22382)."""
    match = _VERSION_RE.search(version_output)
    if match is None:
        raise ValueError(f"could not parse Rocq prover version from {version_output!r}")
    parsed = (
        int(match["major"]),
        int(match["minor"]),
        int(match["patch"]) if match["patch"] is not None else 0,
    )
    if parsed < minimum:
        raise ValueError(
            f"Rocq prover {parsed[0]}.{parsed[1]}.{parsed[2]} is below minimum sound version "
            f"{minimum[0]}.{minimum[1]}.{minimum[2]}"
        )
    return parsed


def math_exports(gallina: str) -> list[str]:
    """List mathematical declarations and erased assertion witnesses for the kernel audit."""
    pattern = (r"^Definition (holdfast(?:_m[0-9a-f]+(?:_[0-9a-f]+)?)?_"
               r"(?:d[0-9]+_[A-Za-z_][A-Za-z0-9_]*|assert_\d+_\d+_\d+))\s*(?:\(|:)")
    return [match[1] for match in re.finditer(pattern, gallina, flags=re.MULTILINE)]


@dataclass(frozen=True)
class TrustedObligation:
    """One obligation the kernel sees only as an assumption."""

    export: str
    axiom: str
    line: int
    column: int
    reason: str

    def as_json(self) -> dict[str, object]:
        return {"export": self.export, "axiom": self.axiom, "line": self.line,
                "column": self.column, "reason": self.reason}


def ledger(gallina: str) -> tuple[TrustedObligation, ...]:
    """Return every solver-trusted obligation declared in emitted Gallina.

    Every `Axiom` in the text must be a marked solver-trust axiom; unledgered
    assumptions (`Parameter`, `Conjecture`, ...), `Admitted`/`admit`, and
    kernel-soundness-bypassing directives (`Unset Guard Checking`, etc.) refuse.
    """
    stripped = _strip_rocq_comments(gallina)
    if (assumption := _UNLEDGERED_ASSUMPTION.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina declares prohibited assumption keyword: {assumption.group(0).strip()}")
    if (bypass := _PROOF_BYPASS.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina contains prohibited proof bypass: {bypass.group(0).strip()}")
    if (directive := _KERNEL_BYPASS.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina contains prohibited kernel-bypass directive: {directive.group(0).strip()}")
    entries = tuple(
        TrustedObligation(match["export"], match["axiom"], int(match["line"]),
                          int(match["column"]), match["reason"])
        for match in _MARKER.finditer(gallina)
    )
    declared = _AXIOM.findall(stripped)
    marked = [entry.axiom for entry in entries]
    if sorted(declared) != sorted(marked) or len(set(marked)) != len(marked):
        unmarked = sorted(set(declared) - set(marked))
        raise ValueError(f"emitted Gallina declares unledgered or duplicate axioms: {unmarked or marked}")
    for entry in entries:
        if entry.axiom != f"holdfast_solver_{entry.export}":
            raise ValueError(f"solver-trust axiom {entry.axiom} does not name its export {entry.export}")
    return entries


def audit(output: str, audited: int, module: str,
          entries: tuple[TrustedObligation, ...]) -> list[str]:
    """Check `Print Assumptions` output for `audited` exports against the ledger.

    Returns the sorted ledger axioms the kernel reported. Any other assumption,
    a missing report or a ledger axiom no export depends on refuses.
    """
    lines = [line.rstrip() for line in output.splitlines() if line.strip()]
    reports = sum(1 for line in lines if line in {"Closed under the global context", "Axioms:"})
    if reports != audited:
        raise ValueError(f"expected {audited} assumption reports, found {reports}")
    allowed = {f"{module}.{entry.axiom}" for entry in entries}
    reported: set[str] = set()
    in_axioms = False
    has_axiom = False
    for line in lines:
        if line in {"Closed under the global context", "Axioms:"}:
            if in_axioms and not has_axiom:
                raise ValueError("empty or malformed kernel assumption report")
            in_axioms = line == "Axioms:"
            has_axiom = False
            continue
        if line[0].isspace():
            if not in_axioms or not has_axiom:
                raise ValueError("unexpected kernel assumption continuation")
            continue
        match = _ASSUMPTION_NAME.match(line)
        if match is None or not in_axioms:
            raise ValueError("unsupported kernel assumption report")
        name = match["name"]
        if name not in allowed:
            raise ValueError(f"exports depend on an unledgered assumption: {name}")
        reported.add(name)
        has_axiom = True
    if in_axioms and not has_axiom:
        raise ValueError("empty or malformed kernel assumption report")
    if reported != allowed:
        raise ValueError(f"ledger axioms not reported by any export: {sorted(allowed - reported)}")
    return sorted(reported)
