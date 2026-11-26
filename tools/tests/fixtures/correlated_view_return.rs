// SPDX-License-Identifier: Apache-2.0

pub fn patch_other(values: &mut [u8; 4], first: bool) -> &[u8] {
    #[cfg(any(direct, overlapping_write))]
    {
        let view = if first { &values[..1] } else { &values[1..2] };
        if first {
            #[cfg(direct)]
            {
                values[1] = 8; // first-disjoint-write
            }
            #[cfg(overlapping_write)]
            {
                values[0] = 8; // first-overlapping-write
            }
        } else {
            values[0] = 9; // second-disjoint-write
        }
        view
    }
    #[cfg(not(any(direct, overlapping_write)))]
    if first {
        values[1] = 8;
        &values[..1]
    } else {
        values[0] = 9;
        &values[1..2]
    }
}

#[test]
fn expected_observations() {
    for initial in [[3, 4, 5, 6], [0, 255, 1, 0]] {
        for first in [false, true] {
            let (selected_index, written_index, written_byte) = if first { (0, 1, 8) } else { (1, 0, 9) };
            let mut expected = initial;
            expected[written_index] = written_byte;
            let mut actual = initial;
            let view = patch_other(&mut actual, first);
            assert_eq!(view, &[initial[selected_index]]);
            assert_eq!(actual, expected);
        }
    }
}
