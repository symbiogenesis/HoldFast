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


def compare(baseline: bytes, baseline_tree: Node, candidate: bytes, candidate_tree: Node) -> dict[str, object]:
    old_ast = cast("Node", strip_spans(baseline_tree["ast"]))
    new_ast = cast("Node", strip_spans(candidate_tree["ast"]))
    module = _name(old_ast)
    if _name(new_ast) != module:
        raise ValueError("contract revisions must declare the same module")
    before, old_resolution = _interface(old_ast)
    after, new_resolution = _interface(new_ast)
    changed = {}
    for name in sorted(before.keys() & after.keys()):
        changes = _changes(before[name], after[name])
        if changes:
            changed[name] = changes
    return {
        "schema": 1,
        "status": "authored-contract-diff",
        "module": module,
        "baseline_sha256": sha256_bytes(baseline),
        "candidate_sha256": sha256_bytes(candidate),
        "added": {name: after[name] for name in sorted(after.keys() - before.keys())},
        "removed": {name: before[name] for name in sorted(before.keys() - after.keys())},
        "changed": changed,
        "resolution": {"before": old_resolution, "after": new_resolution} if old_resolution != new_resolution else {},
    }
