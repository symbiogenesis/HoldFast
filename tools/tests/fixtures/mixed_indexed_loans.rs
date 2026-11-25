// SPDX-License-Identifier: Apache-2.0

fn copy_peer(source: &u8, target: &mut u8) -> u8 {
    *target = *source;
    *source
}

pub fn client(values: &mut [u8; 4], i: usize, j: usize) -> u8 {
    if i < j && j < 4 {
        #[cfg(direct)]
        return copy_peer(&values[i], &mut values[j]); // direct-mixed-conflict
        #[cfg(coincident)]
        return copy_peer(&values[i], &mut values[i]); // coincident-mixed-conflict
        #[cfg(not(any(direct, coincident)))]
        {
            let (prefix, suffix) = values.split_at_mut(j);
            return copy_peer(&prefix[i], &mut suffix[0]);
        }
    }
    0
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4];
    for i in 0..=5 {
        for j in 0..=5 {
            let mut actual = initial;
            let observed = client(&mut actual, i, j);
            let mut expected = initial;
            let read = if i < j && j < 4 {
                expected[j] = initial[i];
                initial[i]
            } else {
                0
            };
            assert_eq!((observed, actual), (read, expected), "i={i}, j={j}");
        }
    }
}
