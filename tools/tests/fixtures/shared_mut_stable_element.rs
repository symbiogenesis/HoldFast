// SPDX-License-Identifier: Apache-2.0

pub fn read_and_overwrite(values: &mut [u8; 4], i: usize, j: usize) -> Option<u8> {
    if i >= 4 || j >= 4 {
        return None;
    }
    #[cfg(direct)]
    {
        let selected = &values[i];
        values[j] = 9; // unguarded-element-write
        Some(*selected)
    }
    #[cfg(not(direct))]
    {
        let selected = values[i];
        values[j] = 9;
        Some(selected)
    }
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4];
    for i in 0..=4 {
        for j in 0..=4 {
            let mut actual = initial;
            let observed = read_and_overwrite(&mut actual, i, j);
            let mut expected = initial;
            let expected_byte = if i < 4 && j < 4 {
                expected[j] = 9;
                Some(initial[i])
            } else {
                None
            };
            assert_eq!((observed, actual), (expected_byte, expected), "i={i}, j={j}");
        }
    }
}
