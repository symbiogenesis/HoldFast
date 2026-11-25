# SPDX-License-Identifier: Apache-2.0
"""Replay exact natural use against sequenced call-by-value observations."""

from functools import partial

from tests.harness import Case
from tests.test_holdfast_graded import _replay

_AUDITED = (
    "index_reads_match_demand",
    "checked_lambda_reads",
    "checked_application_preserves_argument",
    "application_preserves_argument_failure",
    "zero_grade_keeps_the_argument_observations",
    "two_reads_reuse_the_returned_value",
    "failure_stops_at_the_argument_effects",
)


def cases() -> list[Case]:
    return [Case("graded natural call-by-value replay",
                 partial(_replay, "graded_cbv", "GradedCbv", _AUDITED, ("graded_pure",)),
                 lane="toolchain")]
