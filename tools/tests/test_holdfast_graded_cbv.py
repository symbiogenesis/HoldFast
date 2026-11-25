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
    "natural_telescope_reads",
    "singleton_sequence_matches_application",
    "sequence_preserves_returned_prefix",
    "sequence_preserves_failure",
    "checked_sequence_preserves_arguments",
    "zero_grade_keeps_the_argument_observations",
    "two_reads_reuse_the_returned_value",
    "failure_stops_at_the_argument_effects",
    "sequenced_zero_and_repeated_uses",
    "sequenced_failure_keeps_prior_effects_and_skips_later_arguments",
    "sequenced_telescope_rejects_wrong_exact_grade",
)


def cases() -> list[Case]:
    return [Case("graded natural call-by-value replay",
                 partial(_replay, "graded_cbv", "GradedCbv", _AUDITED, ("graded_pure",)),
                 lane="toolchain")]
