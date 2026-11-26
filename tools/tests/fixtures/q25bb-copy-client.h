/* SPDX-License-Identifier: Apache-2.0 */
#ifndef HOLDFAST_Q25BB_COPY_CLIENT_H
#define HOLDFAST_Q25BB_COPY_CLIENT_H

#include "vos_copy_service.h"

#define HOLDFAST_COPY_TRIAL_VIEW_BYTES (VOS_COPY_MAX_PAYLOAD + 1u)
#define HOLDFAST_COPY_TRIAL_SOURCE_OFFSET 1u
#define HOLDFAST_COPY_TRIAL_DESTINATION_OFFSET (HOLDFAST_COPY_TRIAL_VIEW_BYTES + 2u)
#define HOLDFAST_COPY_TRIAL_OVERLAPPING_OFFSET (HOLDFAST_COPY_TRIAL_VIEW_BYTES)
#define HOLDFAST_COPY_TRIAL_ARENA_BYTES (2u * HOLDFAST_COPY_TRIAL_VIEW_BYTES + 3u)

enum holdfast_copy_trial_result {
    HOLDFAST_COPY_TRIAL_PASS = 0,
    HOLDFAST_COPY_TRIAL_INITIALIZE = 1,
    HOLDFAST_COPY_TRIAL_EMPTY = 2,
    HOLDFAST_COPY_TRIAL_STALE = 3,
    HOLDFAST_COPY_TRIAL_SUBMIT = 4,
    HOLDFAST_COPY_TRIAL_DUPLICATE = 5,
    HOLDFAST_COPY_TRIAL_TOO_SMALL = 6,
    HOLDFAST_COPY_TRIAL_SNAPSHOT = 7,
    HOLDFAST_COPY_TRIAL_SUFFIX = 8,
    HOLDFAST_COPY_TRIAL_FRAME = 9,
    HOLDFAST_COPY_TRIAL_FILL = 10,
    HOLDFAST_COPY_TRIAL_FULL = 11,
    HOLDFAST_COPY_TRIAL_FIFO = 12,
    HOLDFAST_COPY_TRIAL_DRAIN = 13,
    HOLDFAST_COPY_TRIAL_PAYLOAD_LIMIT = 14,
    HOLDFAST_COPY_TRIAL_PAYLOAD_OVER_LIMIT = 15,
    HOLDFAST_COPY_TRIAL_SHORT_SOURCE = 16,
    HOLDFAST_COPY_TRIAL_ZERO_GENERATION = 17,
    HOLDFAST_COPY_TRIAL_RENEW_GENERATION = 18
};

/* The caller owns an aligned ring and a disjoint arena of the stated extent.
 * Both views have the stated length and remain live across submit and take.
 * The overlapping caller uses the same source and the alternate destination
 * offset above. It must fail the caller check before this C API is invoked. */
int holdfast_copy_trial(vos_copy_ring *ring, uint8_t *arena);

#endif
