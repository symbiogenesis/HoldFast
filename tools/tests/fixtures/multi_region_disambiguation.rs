// SPDX-License-Identifier: Apache-2.0

#[cfg(not(unified_region))]
fn select_left_mutate_right<'a, 'b>(
    left: &'a [u8; 4],
    right: &'b mut [u8; 4],
    i: usize,
) -> Option<&'a u8> {
    if i >= 4 {
        return None;
    }
    right[i] = 9;
    Some(&left[i])
}

#[cfg(unified_region)]
fn select_left_mutate_right<'a>(
    left: &'a [u8; 4],
    right: &'a mut [u8; 4],
    i: usize,
) -> Option<&'a u8> {
    if i >= 4 {
        return None;
    }
    right[i] = 9;
    Some(&left[i])
}

pub fn observe_disjoint(left: &[u8; 4], right: &mut [u8; 4], i: usize) -> Option<u8> {
    let view = select_left_mutate_right(left, right, i)?;
    right[0] = 7; // unified-region-conflict
    Some(*view)
}

#[test]
fn expected_observations() {
    let left = [1, 2, 3, 4];
    for i in 0..=4 {
        let mut right = [10, 11, 12, 13];
        let observed = observe_disjoint(&left, &mut right, i);
        let mut expected = [10, 11, 12, 13];
        if i < 4 {
            expected[i] = 9;
            expected[0] = 7;
        }
        assert_eq!((observed, right), (left.get(i).copied(), expected), "i={i}");
    }
}
