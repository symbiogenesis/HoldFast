// SPDX-License-Identifier: Apache-2.0

fn set_two(a: &mut u8, b: &mut u8) {
    *a = 9;
    *b = 8;
}

#[cfg(any(direct, coincident))]
pub fn client(values: &mut [u8; 4], i: usize, j: usize) -> bool {
    if i < 4 && j < 4 && i != j {
        #[cfg(direct)]
        set_two(&mut values[i], &mut values[j]); // direct-conflict
        #[cfg(coincident)]
        set_two(&mut values[i], &mut values[i]); // coincident-conflict
        return true;
    }
    false
}

#[cfg(not(any(direct, coincident)))]
pub fn client(values: &mut [u8; 4], i: usize, j: usize) -> bool {
    let Ok([a, b]) = values.get_disjoint_mut([i, j]) else {
        return false;
    };
    set_two(a, b);
    true
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4];
    for i in 0..=5 {
        for j in 0..=5 {
            let mut actual = initial;
            let accepted = client(&mut actual, i, j);
            let mut expected = initial;
            let should_accept = i < 4 && j < 4 && i != j;
            if should_accept {
                expected[i] = 9;
                expected[j] = 8;
            }
            assert_eq!((accepted, actual), (should_accept, expected), "i={i}, j={j}");
        }
    }
}
