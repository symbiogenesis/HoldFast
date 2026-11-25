// SPDX-License-Identifier: Apache-2.0

#[cfg(any(direct, coincident))]
pub fn client(values: &mut [u8; 4], i: usize) -> Option<&u8> {
    if i >= values.len() {
        return None;
    }
    let view = &values[i];
    if i == 0 {
        #[cfg(direct)]
        {
            values[1] = 8; // disjoint-zero-write
        }
        #[cfg(coincident)]
        {
            values[0] = 8; // coincident-zero-write
        }
    } else {
        values[0] = 9; // nonzero-write
    }
    Some(view)
}

#[cfg(not(any(direct, coincident)))]
pub fn client(values: &mut [u8; 4], i: usize) -> Option<&u8> {
    let (target, replacement) = if i == 0 { (1, 8) } else { (0, 9) };
    let [view, slot] = values.get_disjoint_mut([i, target]).ok()?;
    *slot = replacement;
    Some(view)
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4];
    for i in 0..=5 {
        let mut actual = initial;
        let result = client(&mut actual, i).copied();
        let mut expected = initial;
        if i == 0 {
            expected[1] = 8;
        } else if i < initial.len() {
            expected[0] = 9;
        }
        assert_eq!((result, actual), (initial.get(i).copied(), expected), "i={i}");
    }
}
