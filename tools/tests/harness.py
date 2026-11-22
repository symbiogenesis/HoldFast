# SPDX-License-Identifier: Apache-2.0
"""Shared test cases and assertions.

Each module under `tools/tests/` exports `cases()` returning `Case` objects that
signal failure by raising. `ensure` raises `AssertionError` explicitly so checks
remain active under `python -O`. `raises` provides the standard unittest exception assertion
for these function-based cases.
"""

from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Literal
from unittest import TestCase

TOOLS = Path(__file__).resolve().parents[1]
raises = TestCase().assertRaises

type Lane = Literal["any", "host", "guest", "toolchain"]


@dataclass(frozen=True)
class Case:
    """A single test case (`fn` returns `None` on pass and raises on failure).

    `slow` cases run only under `--slow`. `lane` is `"any"`, `"host"`, `"guest"`, or
    `"toolchain"` (guest with the Sail opam switch provisioned).
    """

    name: str
    fn: Callable[[], None]
    slow: bool = False
    lane: Lane = "any"


def ensure(cond: bool, msg: str) -> None:
    """Raise `AssertionError(msg)` if `cond` is false, even under `python -O`."""
    if not cond:
        raise AssertionError(msg)
