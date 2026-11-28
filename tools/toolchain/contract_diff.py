# SPDX-License-Identifier: Apache-2.0
"""Compare authored public declarations for review of a module upgrade."""

from collections.abc import Sequence
from typing import cast

from toolchain.hashing import sha256_bytes
from toolchain.parser import Json
from toolchain.syntax_campaigns import strip_spans

type Node = dict[str, Json]
type Changes = dict[str, dict[str, Json]]


def _name(node: Node) -> str:
    name = node.get("name")
    if not isinstance(name, dict) or not isinstance(text := name.get("text"), str):
        raise TypeError("authored contract requires named public declarations")
    return text


def _interface(ast: Node) -> tuple[dict[str, Node], list[Node]]:
    declarations: dict[str, Node] = {}
    resolution = []
    for declaration in cast("Sequence[Node]", ast["declarations"]):
        kind = declaration["kind"]
        if kind in ("import", "impl"):
            # These declarations can change the meaning of an unchanged spelling.
            resolution.append(declaration)
        if "public" not in cast("list[Json]", declaration["modifiers"]):
            continue
        name = _name(declaration)
        if name in declarations:
            raise ValueError(f"ambiguous public declaration '{name}'")
        signature = dict(declaration)
        if kind in ("function", "lemma", "theorem"):
            del signature["body"]
        declarations[name] = signature
    return declarations, resolution


def _changes(before: Node, after: Node) -> Changes:
    return {key: {"before": before.get(key), "after": after.get(key)}
            for key in sorted(before.keys() | after.keys()) if before.get(key) != after.get(key)}


def _contains_negation(node: object) -> bool:
    if isinstance(node, dict):
        if node.get("kind") == "unary":
            op = node.get("operator")
            if isinstance(op, dict) and op.get("text") == "!":
                return True
        return any(_contains_negation(value) for value in node.values())
    if isinstance(node, list):
        return any(_contains_negation(item) for item in node)
    return False


def _contract_roles(contracts: object) -> dict[str, list[Node]]:
    grouped: dict[str, list[Node]] = {}
    if not isinstance(contracts, list):
        return grouped
    for item in contracts:
        if not isinstance(item, dict):
            continue
        role = item.get("role") if item.get("kind") == "contract" else item.get("kind")
        if isinstance(role, str):
            grouped.setdefault(role, []).append(cast("Node", item))
    return grouped


def _review_entry(name: str, delta: Changes) -> tuple[dict[str, object], list[str]]:
    notes: list[str] = []
    flags: list[str] = []
    if "contracts" in delta:
        before_roles = _contract_roles(delta["contracts"].get("before"))
        after_roles = _contract_roles(delta["contracts"].get("after"))
        if before_roles.get("requires", []) != after_roles.get("requires", []):
            flags.append("precondition-changed")
            notes.append("requires clause changed; verify old caller domains remain admitted")
        if before_roles.get("ensures", []) != after_roles.get("ensures", []):
            flags.append("postcondition-changed")
            notes.append("ensures clause changed; verify downstream proofs remain discharged")
        if before_roles.get("restores", []) != after_roles.get("restores", []):
            flags.append("restores-changed")
            notes.append("restores clause changed; verify borrow-end invariants")
        before_eff = before_roles.get("effects", [])
        after_eff = after_roles.get("effects", [])
        if before_eff != after_eff:
            flags.append("effects-changed")
            notes.append("effects clause changed; inspect footprint and policy bounds")
            if _contains_negation(before_eff) and not _contains_negation(after_eff):
                flags.append("prohibition-removed")
                notes.append("effect prohibition ('!') removed")
        other_roles = (set(before_roles) | set(after_roles)) - {"requires", "ensures", "restores", "effects"}
        if any(before_roles.get(role, []) != after_roles.get(role, []) for role in other_roles):
            flags.append("signature-changed")
            notes.append("other contract or constraint clauses changed")
    for field in ("value", "canceled_by"):
        if field in delta:
            flags.append("effect-set-changed")
            notes.append(f"effect set '{field}' changed")
            break
    remaining = set(delta) - {"contracts", "value", "canceled_by"}
    if remaining:
        flags.append("signature-changed")
        notes.append("declaration fields changed: " + ", ".join(sorted(remaining)))
    return {"declaration": name, "changed_fields": sorted(delta), "notes": notes}, flags


def _build_review_summary(
    added: dict[str, Node],
    removed: dict[str, Node],
    changed: dict[str, Changes],
    resolution_changed: bool,
) -> dict[str, object]:
    risk_flags: set[str] = set()
    entries: list[dict[str, object]] = []
    for name in sorted(removed):
        risk_flags.add("public-declaration-removed")
        entries.append({
            "declaration": name,
            "changed_fields": ["removed"],
            "notes": [f"public {removed[name].get('kind', 'declaration')} removed"],
        })
    entries.extend({
        "declaration": name,
        "changed_fields": ["added"],
        "notes": [f"public {added[name].get('kind', 'declaration')} added"],
    } for name in sorted(added))
    for name in sorted(changed):
        entry, flags = _review_entry(name, changed[name])
        entries.append(entry)
        risk_flags.update(flags)
    if resolution_changed:
        risk_flags.add("resolution-changed")
        entries.append({
            "declaration": "<module-resolution>",
            "changed_fields": ["imports/impls"],
            "notes": ["imports or interface impl declarations changed; unchanged spellings may resolve differently"],
        })
    return {
        "compatibility_verdict": "unverified-syntax-diff",
        "risk_flags": sorted(risk_flags),
        "entries": entries,
    }


def format_human(report: dict[str, object]) -> str:
    """Render a plain-text PR audit summary for human review of authored contract changes."""
    summary = cast("dict[str, object]", report.get("review_summary", {}))
    flags = cast("list[str]", summary.get("risk_flags", []))
    entries = cast("list[dict[str, object]]", summary.get("entries", []))
    lines = [
        f"Contract audit for module {report.get('module', '<unknown>')}",
        f"  baseline : {report.get('baseline_sha256', '')}",
        f"  candidate: {report.get('candidate_sha256', '')}",
        f"  verdict  : {summary.get('compatibility_verdict', 'unverified-syntax-diff')} "
        "(syntax diff only; replay check-upgrade and Rocq proofs for compatibility)",
        "  risks    : " + (", ".join(flags) if flags else "none detected"),
    ]
    if entries:
        lines.append("Changes:")
        for entry in entries:
            fields = ", ".join(cast("list[str]", entry.get("changed_fields", [])))
            notes = "; ".join(cast("list[str]", entry.get("notes", [])))
            lines.append(f"  - {entry.get('declaration')} [{fields}]: {notes}")
    else:
        lines.append("Changes: none (trivia/implementation bodies only)")
    return "\n".join(lines)


def compare(baseline: bytes, baseline_tree: Node, candidate: bytes, candidate_tree: Node) -> dict[str, object]:
    old_ast = cast("Node", strip_spans(baseline_tree["ast"]))
    new_ast = cast("Node", strip_spans(candidate_tree["ast"]))
    module = _name(old_ast)
    if _name(new_ast) != module:
        raise ValueError("contract revisions must declare the same module")
    before, old_resolution = _interface(old_ast)
    after, new_resolution = _interface(new_ast)
    changed: dict[str, Changes] = {}
    for name in sorted(before.keys() & after.keys()):
        changes = _changes(before[name], after[name])
        if changes:
            changed[name] = changes
    added = {name: after[name] for name in sorted(after.keys() - before.keys())}
    removed = {name: before[name] for name in sorted(before.keys() - after.keys())}
    resolution = {"before": old_resolution, "after": new_resolution} if old_resolution != new_resolution else {}
    return {
        "schema": 1,
        "status": "authored-contract-diff",
        "module": module,
        "baseline_sha256": sha256_bytes(baseline),
        "candidate_sha256": sha256_bytes(candidate),
        "added": added,
        "removed": removed,
        "changed": changed,
        "resolution": resolution,
        "review_summary": _build_review_summary(added, removed, changed, bool(resolution)),
    }
