# SPDX-License-Identifier: Apache-2.0
"""Kernel-replay audit for mechanized Funnel Hashing in Rocq 9.3.0."""

from tests.harness import Case, ensure
from tests.test_holdfast_graded import _replay

_FUNNEL_PROOFS = (
    "probe_indices_in_bounds",
    "level_ranges_disjoint",
    "insert_preserves_length",
    "insert_no_reordering",
    "lookup_after_insert_hit",
    "insert_preserves_other_keys",
    "insert_full_fails_closed",
    "probe_steps_bounded",
    "demo_funnel_behavior",
)


def _replay_funnel_table() -> None:
    _replay("funnel_table", "FunnelTable", _FUNNEL_PROOFS, ())
    ensure(len(_FUNNEL_PROOFS) == 9, "funnel theorem audit list mismatch")


def cases() -> list[Case]:
    return [Case("funnel-table-rocq-replay", _replay_funnel_table, lane="toolchain")]
