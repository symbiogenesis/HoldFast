// SPDX-License-Identifier: Apache-2.0

fn copy_peer(source: &u8, target: &mut u8) -> u8 {
    *target = *source;
    *source
}

pub fn client(values: &mut [u8; 4], i: usize, j: usize) -> u8 {
    if i < 3 && j < 4 && j != 1 + i {
        #[cfg(any(direct, coincident))]
        let shifted = &values[1..];
        #[cfg(direct)]
        return copy_peer(&shifted[i], &mut values[j]); // owner-coordinate-conflict
        #[cfg(coincident)]
        return copy_peer(&shifted[i], &mut values[1 + i]); // owner-coordinate-coincident
        #[cfg(not(any(direct, coincident)))]
        {
            let [source, target] = values.get_disjoint_mut([1 + i, j]).unwrap();
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
            let read = if i < 3 && j < 4 && j != 1 + i {
                expected[j] = initial[1 + i];
                initial[1 + i]
            } else {
                0
            };
            assert_eq!((observed, actual), (read, expected), "i={i}, j={j}");
        }
    }
}
