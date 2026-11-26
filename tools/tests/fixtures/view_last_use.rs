// SPDX-License-Identifier: Apache-2.0

fn observe_and_write(values: &mut [u8; 4], i: usize, read_first: bool) -> u8 {
    let selected = &values[i];
    if read_first {
        #[cfg(live_conflict)]
        {
            values[i] = 9; // write-before-last-use
            *selected
        }
        #[cfg(not(live_conflict))]
        {
            let observed = *selected;
            values[i] = 9;
            observed
        }
    } else if i != 0 {
        #[cfg(direct)]
        {
            values[0] = 8; // disjoint-write-before-read
            *selected
        }
        #[cfg(coincident)]
        {
            values[i] = 8; // overlapping-write-before-read
            *selected
        }
        #[cfg(not(any(direct, coincident)))]
        {
            let (prefix, suffix) = values.split_at_mut(i);
            let selected = &suffix[0];
            prefix[0] = 8;
            *selected
        }
    } else {
        *selected
    }
}

#[test]
fn expected_observations() {
    for initial in [[3, 4, 5, 6], [0, 255, 1, 0]] {
        for i in 0..4 {
            for read_first in [false, true] {
                let mut expected = initial;
                if read_first {
                    expected[i] = 9;
                } else if i != 0 {
                    expected[0] = 8;
                }
                let mut actual = initial;
                assert_eq!(observe_and_write(&mut actual, i, read_first), initial[i]);
                assert_eq!(actual, expected);
            }
        }
    }
}
