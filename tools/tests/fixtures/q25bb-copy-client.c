// SPDX-License-Identifier: Apache-2.0
#include "q25bb-copy-client.h"

enum {
    guard = 0xe7,
    untouched = 0xa5,
    signal_sentinel = 92,
    length_sentinel = 93,
    request_sentinel = 91
};

static void fill(uint8_t *bytes, size_t count, uint8_t value)
{
    for (size_t i = 0; i < count; ++i)
        bytes[i] = value;
}

static int all_bytes(const uint8_t *bytes, size_t count, uint8_t value)
{
    for (size_t i = 0; i < count; ++i)
        if (bytes[i] != value)
            return 0;
    return 1;
}

static int take_refused(vos_copy_ring *ring, uint8_t *destination, size_t capacity)
{
    size_t length = length_sentinel;
    uint32_t request = request_sentinel;
    return vos_copy_take(ring, destination, capacity, &length, &request) == 0
        && length == length_sentinel && request == request_sentinel
        && all_bytes(destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, untouched);
}

static int snapshot_case(vos_copy_ring *ring, uint8_t *source, uint8_t *destination)
{
    uint32_t signal = signal_sentinel;
    uint32_t request = request_sentinel;
    size_t length = length_sentinel;
    const uint32_t generation = VOS_COPY_GENERATION;

    if (!vos_copy_init_generation(ring, generation))
        return HOLDFAST_COPY_TRIAL_INITIALIZE;
    fill(destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, untouched);
    if (!take_refused(ring, destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES))
        return HOLDFAST_COPY_TRIAL_EMPTY;

    source[0] = 0x12;
    source[1] = 0x34;
    source[2] = 0x56;
    if (vos_copy_submit(ring, generation + 1u, 41, 0, source, 3, 3, &signal) != 0
        || signal != signal_sentinel)
        return HOLDFAST_COPY_TRIAL_STALE;
    if (vos_copy_submit(ring, generation, 41, 0, source, 2, 3, &signal) != 0
        || signal != signal_sentinel)
        return HOLDFAST_COPY_TRIAL_SHORT_SOURCE;
    if (vos_copy_submit(ring, generation, 41, 0, source, 3, 3, &signal) != 1 || signal != 0)
        return HOLDFAST_COPY_TRIAL_SUBMIT;

    signal = signal_sentinel;
    if (vos_copy_submit(ring, generation, 41, 0, source, 1, 1, &signal) != 0
        || signal != signal_sentinel)
        return HOLDFAST_COPY_TRIAL_DUPLICATE;
    if (!take_refused(ring, destination, 2))
        return HOLDFAST_COPY_TRIAL_TOO_SMALL;

    fill(source, 3, 0xf2);
    if (vos_copy_take(ring, destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, &length, &request) != 1
        || length != 3 || request != 41
        || destination[0] != 0x12 || destination[1] != 0x34 || destination[2] != 0x56)
        return HOLDFAST_COPY_TRIAL_SNAPSHOT;
    if (!all_bytes(destination + 3, HOLDFAST_COPY_TRIAL_VIEW_BYTES - 3u, untouched))
        return HOLDFAST_COPY_TRIAL_SUFFIX;
    if (!all_bytes(source, 3, 0xf2) || !all_bytes(source + 3, HOLDFAST_COPY_TRIAL_VIEW_BYTES - 3u, guard))
        return HOLDFAST_COPY_TRIAL_FRAME;
    fill(destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, untouched);
    if (!take_refused(ring, destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES))
        return HOLDFAST_COPY_TRIAL_DRAIN;

    if (vos_copy_init_generation(ring, 0) != 0
        || vos_copy_submit(ring, generation, 41, 0, source, 1, 1, &signal) != 1
        || vos_copy_take(ring, destination, 1, &length, &request) != 1
        || length != 1 || request != 41 || destination[0] != 0xf2)
        return HOLDFAST_COPY_TRIAL_ZERO_GENERATION;
    if (vos_copy_init_generation(ring, generation + 1u) != 1)
        return HOLDFAST_COPY_TRIAL_RENEW_GENERATION;

    signal = signal_sentinel;
    if (vos_copy_submit(ring, generation, 41, 0, source, 1, 1, &signal) != 0
        || signal != signal_sentinel
        || vos_copy_submit(ring, generation + 1u, 41, 0, source, 1, 1, &signal) != 1
        || vos_copy_take(ring, destination, 1, &length, &request) != 1
        || length != 1 || request != 41 || destination[0] != 0xf2)
        return HOLDFAST_COPY_TRIAL_RENEW_GENERATION;
    return HOLDFAST_COPY_TRIAL_PASS;
}

static int capacity_case(vos_copy_ring *ring, uint8_t *source, uint8_t *destination)
{
    if (vos_copy_init_generation(ring, VOS_COPY_GENERATION) != 1)
        return HOLDFAST_COPY_TRIAL_INITIALIZE;

    /* Two complete wire-index periods followed by a fresh full window. */
    const uint32_t windows = 2u * VOS_COPY_INDEX_SPAN / VOS_COPY_CAPACITY + 1u;
    for (uint32_t window = 0; window < windows; ++window) {
        uint32_t signal = signal_sentinel;
        for (uint32_t i = 0; i < VOS_COPY_CAPACITY; ++i) {
            source[0] = (uint8_t)(window * 11u + i * 3u);
            if (vos_copy_submit(ring, VOS_COPY_GENERATION, 100u + i, 0, source, 1, 1, &signal) != 1
                || signal != 0)
                return HOLDFAST_COPY_TRIAL_FILL;
        }
        signal = signal_sentinel;
        if (vos_copy_submit(ring, VOS_COPY_GENERATION, 100u + VOS_COPY_CAPACITY, 0, source, 1, 1, &signal) != 0
            || signal != signal_sentinel)
            return HOLDFAST_COPY_TRIAL_FULL;
        source[0] = 0xff;
        fill(destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, untouched);
        for (uint32_t i = 0; i < VOS_COPY_CAPACITY; ++i) {
            size_t length = length_sentinel;
            uint32_t request = request_sentinel;
            if (vos_copy_take(ring, destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, &length, &request) != 1
                || length != 1 || request != 100u + i
                || destination[0] != (uint8_t)(window * 11u + i * 3u))
                return HOLDFAST_COPY_TRIAL_FIFO;
        }
        if (!all_bytes(destination + 1, HOLDFAST_COPY_TRIAL_VIEW_BYTES - 1u, untouched))
            return HOLDFAST_COPY_TRIAL_SUFFIX;
    }
    fill(destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, untouched);
    if (!take_refused(ring, destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES))
        return HOLDFAST_COPY_TRIAL_DRAIN;
    return HOLDFAST_COPY_TRIAL_PASS;
}

static int payload_limit_case(vos_copy_ring *ring, uint8_t *source, uint8_t *destination)
{
    if (vos_copy_init_generation(ring, VOS_COPY_GENERATION) != 1)
        return HOLDFAST_COPY_TRIAL_INITIALIZE;

    for (uint32_t op = 0; op < VOS_COPY_OPERATION_COUNT; ++op) {
        const size_t limit = vos_copy_payload_limit(op);
        const uint8_t pattern = (uint8_t)(21u + op);
        size_t length = length_sentinel;
        uint32_t request = request_sentinel;
        uint32_t signal = signal_sentinel;
        fill(source, HOLDFAST_COPY_TRIAL_VIEW_BYTES, pattern);
        fill(destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES, untouched);

        if (vos_copy_submit(ring, VOS_COPY_GENERATION, op, op, source, limit + 1u, limit + 1u, &signal) != 0
            || signal != signal_sentinel || !take_refused(ring, destination, HOLDFAST_COPY_TRIAL_VIEW_BYTES))
            return HOLDFAST_COPY_TRIAL_PAYLOAD_OVER_LIMIT;

        /* Tightening any nonzero limit by one excludes this old legal caller. */
        if (vos_copy_submit(ring, VOS_COPY_GENERATION, op, op, source, limit, limit, &signal) != 1
            || signal != 0 || vos_copy_take(ring, destination, limit, &length, &request) != 1
            || length != limit || request != op
            || !all_bytes(destination, limit, pattern))
            return HOLDFAST_COPY_TRIAL_PAYLOAD_LIMIT;
        if (!all_bytes(destination + limit, HOLDFAST_COPY_TRIAL_VIEW_BYTES - limit, untouched))
            return HOLDFAST_COPY_TRIAL_SUFFIX;
        if (!all_bytes(source, HOLDFAST_COPY_TRIAL_VIEW_BYTES, pattern))
            return HOLDFAST_COPY_TRIAL_FRAME;
    }
    return HOLDFAST_COPY_TRIAL_PASS;
}

int holdfast_copy_trial(vos_copy_ring *ring, uint8_t *arena)
{
    fill(arena, HOLDFAST_COPY_TRIAL_ARENA_BYTES, guard);
    uint8_t *source = arena + HOLDFAST_COPY_TRIAL_SOURCE_OFFSET;
    uint8_t *destination = arena + HOLDFAST_COPY_TRIAL_DESTINATION_OFFSET;

    int result = snapshot_case(ring, source, destination);
    if (result == HOLDFAST_COPY_TRIAL_PASS)
        result = capacity_case(ring, source, destination);
    if (result == HOLDFAST_COPY_TRIAL_PASS)
        result = payload_limit_case(ring, source, destination);
    if (result != HOLDFAST_COPY_TRIAL_PASS)
        return result;

    if (arena[0] != guard || arena[HOLDFAST_COPY_TRIAL_DESTINATION_OFFSET - 1u] != guard
        || arena[HOLDFAST_COPY_TRIAL_ARENA_BYTES - 1u] != guard)
        return HOLDFAST_COPY_TRIAL_FRAME;
    return HOLDFAST_COPY_TRIAL_PASS;
}

#ifdef HOLDFAST_COPY_TRIAL_HOST
int main(void)
{
    static vos_copy_ring ring;
    static uint8_t arena[HOLDFAST_COPY_TRIAL_ARENA_BYTES];
    return holdfast_copy_trial(&ring, arena);
}
#endif
