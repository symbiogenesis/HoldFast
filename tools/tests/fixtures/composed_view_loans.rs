// SPDX-License-Identifier: Apache-2.0

fn copy_peer(source: &u8, target: &mut u8) -> u8 {
    *target = *source;
    *source
}

pub fn client(values: &mut [u8; 4], i: usize, j: usize) -> u8 {
    if i < 2 && j < 4 && j != 2 + i {
        #[cfg(any(direct, coincident))]
        let outer = &values[1..];
        #[cfg(any(direct, coincident))]
        let inner = &outer[1..];
        #[cfg(direct)]
        return copy_peer(&inner[i], &mut values[j]); // composed-view-conflict
        #[cfg(coincident)]
        return copy_peer(&inner[i], &mut values[2 + i]); // composed-view-coincident
        #[cfg(not(any(direct, coincident)))]
        {
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
                expected[j] = initial[2 + i];
                initial[2 + i]
            } else {
                0
            };
            assert_eq!((observed, actual), (read, expected), "i={i}, j={j}");
        }
    }
}
