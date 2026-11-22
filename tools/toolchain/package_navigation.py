# SPDX-License-Identifier: Apache-2.0
"""Source-bound navigation decisions recorded by the locked mathematical elaborator."""

from dataclasses import dataclass, field
from typing import cast

from toolchain.elaborate_types import Node


@dataclass(frozen=True, order=True)
class Site:
    module: str
    start: int
    end: int

    @classmethod
    def at(cls, module: str, node: Node) -> Site:
        start, end = cast("list[int]", node["span"])
        return cls(module, start, end)


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    emitted: str | None = None
    implements: Site | None = None


@dataclass
class Navigation:
    declarations: dict[Site, Declaration] = field(default_factory=dict)
    references: set[tuple[Site, Site]] = field(default_factory=set)
    instances: dict[Site, tuple[Site, tuple[str, ...]]] = field(default_factory=dict)
    bindings: dict[str | int, Site] = field(default_factory=dict)
    methods: dict[tuple[str, str], Site] = field(default_factory=dict)

    def declare(self, module: str, name: object, kind: str, *, binding: str | int | None = None,
                emitted: str | None = None, implements: Site | None = None) -> Site:
        ident = cast("Node", name)
        site = Site.at(module, ident)
        decl = Declaration(cast("str", ident["text"]), kind, emitted, implements)
        if site in self.declarations and self.declarations[site] != decl:
            raise ValueError("ambiguous elaboration origin for a navigation declaration")
        self.declarations[site] = decl
        if binding is not None:
            self.bindings[binding] = site
        return site

    def reference(self, module: str, name: object, binding: str | int) -> None:
        if binding in self.bindings:
            self.references.add((Site.at(module, cast("Node", name)), self.bindings[binding]))
