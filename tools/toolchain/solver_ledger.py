# SPDX-License-Identifier: Apache-2.0
"""Solver-trust ledger for elaborated HoldFast Gallina and its kernel assumption audit.

The mathematical elaborator emits an obligation it cannot kernel-prove as a named
`holdfast_solver_*` axiom carrying the real statement, preceded by a marker naming its
export, source location and reason. This module reads that ledger from emitted
text and checks that `Print Assumptions` reports exactly those axioms and nothing
else. A non-empty ledger is never acceptance evidence.
"""

import hashlib
import re
from collections.abc import Sequence
from dataclasses import dataclass

from toolchain import proofenv

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
_REWRITE_SYMBOL = re.compile(r"^\s*Symbol(?:s)?\b", flags=re.MULTILINE)
_PROOF_BYPASS = re.compile(r"\b(?:Admitted|admit)\s*\.")
_KERNEL_BYPASS = re.compile(
    r"\b(?:Unset\s+(?:Guard|Positivity|Universe)\s+Checking"
    r"|Unset\s+Strict\s+Universe\s+Declaration"
    r"|Set\s+Type\s+in\s+Type"
    r"|Set\s+Universe\s+Checking\s+Off"
    r"|Set\s+Allow\s+Rewrite\s+Rules"
    r"|Rewrite\s+Rule"
    r"|enable_rewrite_rules"
    r"|Admit\s+Obligations"
    r"|Bypass_check"
    r"|bypass_check"
    r"|Declare\s+ML\s+Module"
    r"|Unsafe)\b"
)
_ASSUMPTION_NAME = re.compile(r"^(?P<name>[A-Za-z_][A-Za-z0-9_'.]*) :")
_VERSION_RE = re.compile(r"\bversion\s+(?P<major>\d+)\.(?P<minor>\d+)(?:\.(?P<patch>\d+))?\b")
_PROHIBITED_PROVER_FLAGS: frozenset[str] = frozenset({
    "-allow-rewrite-rules",
    "--allow-rewrite-rules",
    "-type-in-type",
    "--type-in-type",
    "-impredicative-set",
    "--impredicative-set",
    "-bypass-qed",
    "--bypass-qed",
    "-admit",
    "--admit",
    "-norec",
    "--norec",
})
_COMPILER_MODE_FLAGS: frozenset[str] = frozenset({
    "-bytecode-compiler",
    "--bytecode-compiler",
    "-native-compiler",
    "--native-compiler",
})

STATEMENT_AUDIT_MARKER = "holdfast_audit_statements_begin"
STATEMENT_AUDIT_TYPE = "holdfast_audit_statements_marker"

_KERNEL_PROFILE_RULES: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "bytecode/native kernel cast or native_compute",
        re.compile(r"\b(?:vm_cast_no_check|native_cast_no_check|native_compute)\b"),
    ),
    (
        "universe or sort polymorphism",
        re.compile(
            r"(?m)^(?:[ \t]*(?:\#\[[^\]]*\]|(?:Local|Global|Export)\b))*"
            r"[ \t]*(?:Polymorphic|Cumulative|NonCumulative)\b"
            r"|\#\[[^\]]*\buniverses\s*\(\s*polymorphic\b"
        ),
    ),
    (
        "SProp or Universe Polymorphism",
        re.compile(r"\bSProp\b|\bUniverse\s+Polymorphism\b"),
    ),
    (
        "primitive type or Register directive",
        re.compile(
            r"(?m)^(?:[ \t]*(?:\#\[[^\]]*\]|(?:Local|Global|Export|Polymorphic)\b))*"
            r"[ \t]*(?:Primitive|Register)\b"
        ),
    ),
    (
        "module type functor/subtyping",
        re.compile(
            r"(?m)^(?:[ \t]*(?:\#\[[^\]]*\]|(?:Local|Global|Export)\b))*"
            r"[ \t]*Module\s+Type\b"
        ),
    ),
)
_COFIX_RULE = (
    "coinductive/cofixpoint guard-checker surface",
    re.compile(r"\b(?:CoFixpoint|CoInductive|cofix)\b"),
)
_STATEMENT_MARKER_RE = re.compile(
    rf"(?m)^(?:[A-Za-z0-9_.']+\.)?{STATEMENT_AUDIT_MARKER}\s*\r?\n"
    rf"\s+:\s+(?:[A-Za-z0-9_.']+\.)?{STATEMENT_AUDIT_TYPE}\s*$"
)
_CHECK_BLOCK_RE = re.compile(r"(?m)^@?[A-Za-z_][A-Za-z0-9_.']*\r?\n\s+:\s")

_REQUIRED_TCB_PACKAGES: tuple[str, ...] = (
    "rocq-core",
    "rocq-runtime",
    "ocaml-base-compiler",
    "zarith",
    "conf-gmp",
)


def check_prover_flags(argv: Sequence[str]) -> None:
    """Refuse soundness-weakening CLI flags passed to ``rocq`` or ``rocqchk``."""
    args = list(argv)
    for idx, arg in enumerate(args):
        normalized, sep, value = arg.partition("=")
        if normalized in _PROHIBITED_PROVER_FLAGS:
            raise ValueError(f"prohibited Rocq kernel-weakening flag: {arg}")
        if normalized in _COMPILER_MODE_FLAGS:
            mode = value if sep else (args[idx + 1] if idx + 1 < len(args) else "")
            if mode != "no":
                raise ValueError(f"prohibited Rocq compiler-mode flag: {arg} {mode}".strip())


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


def _strip_rocq_comments_and_strings(text: str) -> str:
    """Remove nested Rocq comments and string-literal contents while preserving newlines."""
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        if depth == 0:
            if in_string:
                if ch == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        out.append("  ")
                        i += 2
                        continue
                    in_string = False
                    out.append(" ")
                else:
                    out.append("\n" if ch == "\n" else " ")
                i += 1
            elif ch == '"':
                in_string = True
                out.append(" ")
                i += 1
            elif ch == "(" and i + 1 < n and text[i + 1] == "*":
                depth = 1
                out.append(" ")
                i += 2
            else:
                out.append(ch)
                i += 1
        elif ch == "(" and i + 1 < n and text[i + 1] == "*":
            depth += 1
            i += 2
        elif ch == "*" and i + 1 < n and text[i + 1] == ")":
            depth -= 1
            if depth == 0:
                out.append(" ")
            i += 2
        else:
            if ch == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def check_kernel_profile(gallina: str, *, allow_cofixpoint: bool = False) -> None:
    """Enforce HoldFast's minimal CIC kernel-feature profile on Gallina sources."""
    stripped = _strip_rocq_comments_and_strings(gallina)
    rules = _KERNEL_PROFILE_RULES if allow_cofixpoint else (*_KERNEL_PROFILE_RULES, _COFIX_RULE)
    for label, pattern in rules:
        if (found := pattern.search(stripped)) is not None:
            raise ValueError(
                f"Gallina uses {label} ({found.group(0).strip()!r}), which is excluded from the minimal CIC profile"
            )


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
    assumptions (`Parameter`, `Conjecture`, ...), `Admitted`/`admit`,
    kernel-soundness-bypassing directives (`Unset Guard Checking`, etc.), and
    excluded CIC kernel features refuse.
    """
    check_kernel_profile(gallina)
    stripped = _strip_rocq_comments(gallina)
    if (assumption := _UNLEDGERED_ASSUMPTION.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina declares prohibited assumption keyword: {assumption.group(0).strip()}")
    if (bypass := _PROOF_BYPASS.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina contains prohibited proof bypass: {bypass.group(0).strip()}")
    if (directive := _KERNEL_BYPASS.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina contains prohibited kernel-bypass directive: {directive.group(0).strip()}")
    if (sym := _REWRITE_SYMBOL.search(stripped)) is not None:
        raise ValueError(f"emitted Gallina contains prohibited rewrite-rule symbol declaration: {sym.group(0).strip()}")
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


def audit_rocqchk_context(output: str, allowed_axioms: Sequence[str] = ()) -> list[str]:
    """Verify ``rocqchk -silent -o`` CONTEXT SUMMARY reports sound theory and exact axioms."""
    lines = [line.rstrip() for line in output.splitlines()]
    try:
        start = next(i for i, line in enumerate(lines) if line.strip() == "CONTEXT SUMMARY")
    except StopIteration as err:
        raise ValueError("rocqchk output omitted CONTEXT SUMMARY") from err
    idx = start + 1
    while idx < len(lines) and not lines[idx].strip():
        idx += 1
    if idx >= len(lines) or lines[idx].strip() != "===============":
        raise ValueError("malformed rocqchk CONTEXT SUMMARY header")
    idx += 1
    if any(line.strip() == "CONTEXT SUMMARY" for line in lines[idx:]):
        raise ValueError("rocqchk output contains multiple CONTEXT SUMMARY blocks")

    bullets: list[tuple[str, str, list[str]]] = []
    current: tuple[str, str, list[str]] | None = None
    for line in lines[idx:]:
        if not line.strip():
            continue
        if line.startswith("* "):
            header, sep, inline_val = line[2:].partition(":")
            if not sep:
                raise ValueError(f"malformed rocqchk context bullet: {line!r}")
            current = (header.strip(), inline_val.strip(), [])
            bullets.append(current)
            continue
        if line[0].isspace() and current is not None:
            current[2].append(line.strip())
            continue
        raise ValueError(f"unexpected line in rocqchk CONTEXT SUMMARY: {line!r}")

    theories = [inline for head, inline, items in bullets if head == "Theory" and not items]
    if set(theories) != {"Set is predicative", "Rewrite rules are not allowed"} or len(theories) != 2:
        raise ValueError(f"unexpected rocqchk theory summary: {theories!r}")

    by_header: dict[str, tuple[str, list[str]]] = {}
    for head, inline, items in bullets:
        if head == "Theory":
            continue
        if head in by_header:
            raise ValueError(f"duplicate rocqchk context bullet: {head}")
        by_header[head] = (inline, items)

    for required_none in (
        "Constants/Inductives relying on type-in-type",
        "Constants/Inductives relying on unsafe (co)fixpoints",
        "Inductives whose positivity is assumed",
    ):
        entry = by_header.get(required_none)
        if entry is None or entry != ("<none>", []):
            raise ValueError(f"rocqchk reported unsafe kernel dependency in {required_none!r}: {entry!r}")

    axioms_entry = by_header.get("Axioms")
    if axioms_entry is None:
        raise ValueError("rocqchk CONTEXT SUMMARY omitted Axioms bullet")
    inline_ax, item_ax = axioms_entry
    if inline_ax == "<none>" and not item_ax:
        reported: list[str] = []
    elif not inline_ax and item_ax:
        reported = item_ax
    else:
        raise ValueError(f"malformed rocqchk Axioms bullet: {axioms_entry!r}")

    expected_set = set(allowed_axioms)
    if set(reported) != expected_set:
        raise ValueError(
            f"rocqchk axioms {sorted(reported)!r} differ from allowed {sorted(expected_set)!r}"
        )
    return sorted(reported)


def build_audit_script(import_line: str, targets: Sequence[str]) -> str:
    """Emit a ``Set Printing All.`` assumption + canonical statement check script."""
    lines = [import_line.strip(), "Set Printing All."]
    lines.extend(f"Print Assumptions {target}." for target in targets)
    lines.append(f"Inductive {STATEMENT_AUDIT_TYPE} := {STATEMENT_AUDIT_MARKER}.")
    lines.append(f"Check {STATEMENT_AUDIT_MARKER}.")
    lines.extend(f"Check @{target}." for target in targets)
    return "\n".join(lines) + "\n"


def parse_full_audit(
    output: str,
    audited: int,
    module: str,
    entries: tuple[TrustedObligation, ...],
) -> tuple[list[str], str]:
    """Audit ``Print Assumptions`` and canonical ``Set Printing All`` ``Check`` output."""
    matches = list(_STATEMENT_MARKER_RE.finditer(output))
    if len(matches) != 1:
        raise ValueError(f"expected one {STATEMENT_AUDIT_MARKER} separator, found {len(matches)}")
    marker = matches[0]
    assumptions_part = output[:marker.start()]
    statements_part = output[marker.end():].lstrip("\r\n")
    reported_axioms = audit(assumptions_part, audited, module, entries)
    check_blocks = _CHECK_BLOCK_RE.findall(statements_part)
    if len(check_blocks) != audited:
        raise ValueError(
            f"expected {audited} canonical Set Printing All statement checks, found {len(check_blocks)}"
        )
    canonical_digest = hashlib.sha256(statements_part.encode("utf-8")).hexdigest()
    return reported_axioms, canonical_digest


def locked_runtime_tcb(lock_text: str) -> dict[str, str]:
    """Extract and validate pinned Rocq, OCaml, Zarith, and GMP versions from ``rocq.lock``."""
    tcb: dict[str, str] = {}
    for package in _REQUIRED_TCB_PACKAGES:
        versions = set(re.findall(r'"' + re.escape(package) + r'\.([^"\s]+)"', lock_text))
        if len(versions) != 1:
            raise ValueError(f"rocq.lock must pin one {package} version, found {sorted(versions)!r}")
        tcb[package] = versions.pop()
    if tcb["rocq-core"] != proofenv.ROCQ_VERSION:
        raise ValueError(f"rocq.lock pins rocq-core {tcb['rocq-core']}, expected {proofenv.ROCQ_VERSION}")
    if tcb["ocaml-base-compiler"] != proofenv.OCAML_VERSION:
        raise ValueError(
            f"rocq.lock pins ocaml-base-compiler {tcb['ocaml-base-compiler']}, expected {proofenv.OCAML_VERSION}"
        )
    return tcb


@dataclass(frozen=True)
class ProverAdvisory:
    """One tracked upstream prover soundness advisory and its enforced HoldFast control."""

    advisory_id: str
    source: str
    summary: str
    affected_feature: str
    mitigation: str
    lock_rocq_version: str


ROCQ_CRITICAL_BUG_REGISTER: tuple[ProverAdvisory, ...] = (
    ProverAdvisory(
        advisory_id="rocq-22382",
        source="https://github.com/rocq-prover/rocq/issues/22382",
        summary="CVE-2026-72705 guard-checker bug accepting False in Rocq 9.2.0",
        affected_feature="Fixpoint guard checker",
        mitigation="check_prover_version",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-vm-native",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="VM conversion and OCaml identifier injection bugs (20260819, 20261027)",
        affected_feature="vm_cast_no_check / native_compute / bytecode-native compiler",
        mitigation="check_kernel_profile",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-sort-sprop-relevance",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="SProp, sort polymorphism, and irrelevant-to-relevant match bugs (20260302-4/7/8, 20260820-4)",
        affected_feature="SProp / sort polymorphism",
        mitigation="check_kernel_profile",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-univ-variance-subtyping",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="Universe polymorphism, variance inference, and let-in subtyping bugs (20260302-2, 20260820-2/5/6, 20261030)",
        affected_feature="Polymorphic / Cumulative / Universe Polymorphism",
        mitigation="check_kernel_profile",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-functor-strengthening",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="Aliased functor strengthening and delta-resolver bugs (20260228, 20260827)",
        affected_feature="Module Type functors",
        mitigation="check_kernel_profile",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-primitive-register",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="Primitive ints/arrays and Register Inline universe bugs (20260310, 20260910, 20261104)",
        affected_feature="Primitive / Register",
        mitigation="check_kernel_profile",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-cofix-guard",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="Nested mutual cofixpoint guard-checker bugs (20260820-7/8)",
        affected_feature="CoFixpoint / CoInductive / cofix",
        mitigation="check_kernel_profile",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
    ProverAdvisory(
        advisory_id="rocq-2026-checker-bypass",
        source="https://cr.yp.to/proofs/falseccp.html",
        summary="Checker flags or unsafe kernel theory bypassing independent verification",
        affected_feature="rocqchk -admit / -norec / type-in-type / rewrite rules",
        mitigation="audit_rocqchk_context",
        lock_rocq_version=proofenv.ROCQ_VERSION,
    ),
)


def verify_critical_bug_register(lock_text: str) -> list[str]:
    """Verify the locked runtime TCB and critical-bug register against ``rocq.lock``."""
    findings: list[str] = []
    try:
        tcb = locked_runtime_tcb(lock_text)
    except ValueError as err:
        return [f"tools/opam/rocq.lock: {err}"]
    if not ROCQ_CRITICAL_BUG_REGISTER:
        findings.append("ROCQ_CRITICAL_BUG_REGISTER is empty")
    for advisory in ROCQ_CRITICAL_BUG_REGISTER:
        if advisory.lock_rocq_version != tcb["rocq-core"]:
            findings.append(
                f"{advisory.advisory_id}: targets Rocq {advisory.lock_rocq_version}, "
                f"but rocq.lock pins {tcb['rocq-core']}"
            )
        fn = globals().get(advisory.mitigation)
        if not callable(fn):
            findings.append(f"{advisory.advisory_id}: unknown mitigation {advisory.mitigation!r}")
    return findings
