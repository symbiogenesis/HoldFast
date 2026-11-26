// SPDX-License-Identifier: Apache-2.0

#[cfg(any(direct, coincident))]
pub fn client(values: &mut [u8; 4], n: usize) -> Option<&u8> {
    let limit = if cfg!(coincident) { 4 } else { 3 };
    if n > limit {
        return None;
    }
    let view = &values[3];
    for j in 0..n {
        values[j] = 9; // loop-prefix-write
    }
    Some(view)
}

#[cfg(not(any(direct, coincident)))]
pub fn client(values: &mut [u8; 4], n: usize) -> Option<&u8> {
    if n > 3 {
        return None;
    }
    let (prefix, suffix) = values.split_at_mut(3);
    let view = &suffix[0];
    for j in 0..n {
        prefix[j] = 9;
    }
    Some(view)
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4];
    for n in 0..=5 {
        let mut actual = initial;
        let result = client(&mut actual, n).copied();
        let mut expected = initial;
        if n <= 3 {
            expected[..n].fill(9);
        }
        assert_eq!((result, actual), ((n <= 3).then_some(initial[3]), expected), "n={n}");
    }
}
