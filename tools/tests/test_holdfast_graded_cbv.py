# SPDX-License-Identifier: Apache-2.0
"""Replay exact and bounded natural use against call-by-value observations."""

from functools import partial

from tests.harness import Case
from tests.test_holdfast_graded import _replay
from toolchain import rocq_cache
from toolchain.elaborate_types import _PRELUDE

_AUDITED = (
    "index_reads_match_demand",
    "checked_lambda_reads",
    "checked_application_preserves_argument",
    "application_preserves_argument_failure",
    "natural_telescope_reads_with",
    "natural_telescope_reads",
    "singleton_sequence_matches_application",
    "sequence_preserves_returned_prefix",
    "sequence_preserves_failure",
    "checked_sequence_preserves_arguments_with",
    "checked_sequence_preserves_arguments",
    "checked_bounded_sequence_preserves_arguments",
    "zero_grade_keeps_the_argument_observations",
    "two_reads_reuse_the_returned_value",
    "failure_stops_at_the_argument_effects",
    "sequenced_zero_and_repeated_uses",
    "sequenced_failure_keeps_prior_effects_and_skips_later_arguments",
    "sequenced_telescope_rejects_wrong_exact_grade",
    "sequenced_bounds_admit_unused_and_repeated_values",
    "sequenced_bounds_reject_overuse",
)
_SPAN_AUDITED = (
    "restore_written_slice",
    "scoped_argument_preserves_owner",
    "span_sequence_preserves_owner",
    "checked_bounded_span_sequence",
    "zero_and_repeated_uses_restore_the_scoped_owner",
    "failure_restores_after_write_and_skips_suffix",
    "out_of_bounds_slice_fails_without_taking_the_loan",
    "shared_owner_fails_without_taking_the_exclusive_loan",
)
_MODAL_AUDITED = (
    "dependent_pair_counts_reads",
    "checked_box_open_preserves_argument_with",
    "unused_box_payload_keeps_effect_and_type",
    "repeated_box_payload_reuses_one_effect",
    "checked_slice_box_preserves_owner_with",
    "unused_slice_box_keeps_extent_and_restores_owner",
    "bounded_slice_box_reuses_the_original_payload",
    "failed_slice_box_keeps_writeback_without_an_extent",
)
_ERASURE_AUDITED = (
    "evaluate_index_reads",
    "evaluate_index_extensional",
    "erased_sequence_agrees_derives",
    "sentinel_sequence_agrees_derives",
    "cbv_zero_grade_erasure_sound_with",
    "cbv_zero_grade_erasure_sound",
    "cbv_exact_zero_grade_erasure_sound",
    "cbv_bounded_zero_grade_erasure_sound",
    "cbv_sentinel_erasure_sound",
    "cbv_zero_grade_erasure_preserves_failure",
    "slice_writeback_exact",
    "span_sequence_prefix_writeback",
    "cbv_span_erasure_preserves_owner_and_frame",
    "cbv_span_erasure_preserves_returned_reads",
    "exact_zero_grade_erasure_example",
    "bound_zero_grade_erasure_example",
    "erasure_preserves_failure_prefix_example",
    "span_zero_grade_erasure_preserves_owner_and_writeback",
    "span_erasure_failure_preserves_prefix_and_writeback",
)


def cases() -> list[Case]:
    batch = rocq_cache.BatchChecker()
    return [
        Case("graded natural call-by-value replay",
             partial(_replay, "graded_cbv", "GradedCbv", _AUDITED, ("graded_pure", "graded_domains"),
                     batch=batch),
             lane="toolchain"),
        Case("graded call-by-value scoped Span exits",
             partial(_replay, "graded_cbv_span", "GradedCbvSpan", _SPAN_AUDITED,
                     ("graded_pure", "graded_domains", "graded_cbv"), (("graded_cbv_span_carrier", _PRELUDE),),
                     batch=batch),
             lane="toolchain"),
        Case("graded dependent box call-by-value replay",
             partial(_replay, "graded_modal_cbv", "GradedModalCbv", _MODAL_AUDITED,
                     ("graded_pure", "graded_domains", "graded_modal", "graded_cbv", "graded_cbv_span"),
                     (("graded_cbv_span_carrier", _PRELUDE),),
                     batch=batch),
             lane="toolchain"),
        Case("graded call-by-value zero-grade erasure replay",
             partial(_replay, "graded_cbv_erasure", "GradedCbvErasure", _ERASURE_AUDITED,
                     ("graded_pure", "graded_domains", "graded_cbv", "graded_cbv_span"),
                     (("graded_cbv_span_carrier", _PRELUDE),),
                     batch=batch),
             lane="toolchain"),
        Case("kernel check call-by-value graded proofs with rocqchk", batch.verify_all, lane="toolchain"),
    ]
