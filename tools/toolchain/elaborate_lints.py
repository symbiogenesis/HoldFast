# SPDX-License-Identifier: Apache-2.0
"""Shared lint reporting, source-offset extraction, and sandboxed elaboration probes."""

from collections.abc import Generator
from contextlib import contextmanager
from typing import TYPE_CHECKING, cast

from toolchain.ast import HoldFastError
from toolchain.elaborate_types import Node

if TYPE_CHECKING:
    from toolchain.elaborate import _Elaborator


def node_offset(node: Node) -> int:
    """Return the UTF-8 byte start offset for AST ``node``."""
    return cast("list[int]", node["span"])[0]


def report_lint(
    compiler: _Elaborator,
    code: str,
    node: Node,
    message: str,
    *,
    suppressed_by: tuple[str, ...] = (),
) -> None:
    """Record semantic lint ``code`` at ``node`` unless suppressed by an earlier code."""
    offset = node_offset(node)
    if suppressed_by and any((earlier, offset) in compiler.semantic_lints for earlier in suppressed_by):
        return
    compiler.semantic_lints[code, offset] = message


@contextmanager
def lint_probe(
    compiler: _Elaborator,
    *,
    work_limit: int,
    reduction_limit: int,
    cap_to_remaining: bool = False,
) -> Generator[None]:
    """Isolate elaboration budgets, caches, and metas for advisory lint checks."""
    work, reductions, site = compiler.work, compiler.reductions, compiler.site
    serial = compiler.serial
    saved_metas = compiler.snapshot_metas()
    cache = compiler.whnf_cache
    freezes, freeze_bytes = compiler.freeze_checks, compiler.freeze_check_bytes
    compiler.whnf_cache = {}
    compiler.freeze_checks = {}
    compiler.work = min(work, work_limit) if cap_to_remaining else work_limit
    compiler.reductions = min(reductions, reduction_limit) if cap_to_remaining else reduction_limit
    try:
        yield
    except (HoldFastError, RecursionError):
        pass
    finally:
        for binder in range(serial, compiler.serial, compiler.binder_stride):
            compiler.types.pop(binder, None)
        compiler.serial = serial
        compiler.work, compiler.reductions, compiler.site = work, reductions, site
        compiler.restore_metas(saved_metas)
        compiler.whnf_cache = cache
        compiler.freeze_checks, compiler.freeze_check_bytes = freezes, freeze_bytes
