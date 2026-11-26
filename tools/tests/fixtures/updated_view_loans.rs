// SPDX-License-Identifier: Apache-2.0

fn copy_peer(source: &u8, target: &mut u8) -> u8 {
    *target = *source;
    *source
}

pub fn client(values: &mut [u8; 4], i: usize, j: usize) -> u8 {
    if i < 2 && j < 4 && j != 2 + i {
        #[cfg(any(direct, overlapping_write))]
        {
            let outer = &values[1..];
            let inner = &outer[1..];
            #[cfg(direct)]
            {
                values[0] = 9; // disjoint-write
            }
            #[cfg(overlapping_write)]
            {
                values[2 + i] = 9; // overlapping-write
            }
            return copy_peer(&inner[i], &mut values[j]);
        }
        #[cfg(not(any(direct, overlapping_write)))]
        {
            values[0] = 9;
            let [source, target] = values.get_disjoint_mut([2 + i, j]).unwrap();
            return copy_peer(source, target);
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
            let read = if i < 2 && j < 4 && j != 2 + i {
                expected[0] = 9;
                expected[j] = initial[2 + i];
                initial[2 + i]
            } else {
                0
            };
            assert_eq!((observed, actual), (read, expected), "i={i}, j={j}");
        }
    }
}
