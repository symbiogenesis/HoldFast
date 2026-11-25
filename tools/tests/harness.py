# SPDX-License-Identifier: Apache-2.0
"""Shared test cases and assertions.

Each `test_*.py` module exports `cases()` to register its cases with the
[behavioral runner](../README.md#validation-profiles).
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

    `slow` cases require `--slow`. `any` runs on either platform, `host` runs on
    Windows, and `guest` runs on Linux, including WSL. `toolchain` also requires
    the Sail opam switch on Linux.
    """

    name: str
    fn: Callable[[], None]
    slow: bool = False
    lane: Lane = "any"


def ensure(cond: bool, msg: str) -> None:
    """Raise `AssertionError(msg)` if `cond` is false, even under `python -O`."""
    if not cond:
        raise AssertionError(msg)
