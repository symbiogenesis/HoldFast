// SPDX-License-Identifier: Apache-2.0

pub fn client(values: &mut [u8; 4], i: usize) -> Option<&u8> {
    if let Some(view) = values.get(i) {
        #[cfg(live_conflict)]
        {
            values[0] = 9; // live-conflict
        }
        return Some(view);
    }
    values[0] = 8; // sibling-write
    None
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4];
    for i in 0..=5 {
        let mut actual = initial;
        let result = client(&mut actual, i).copied();
        let mut expected = initial;
        if i >= initial.len() {
            expected[0] = 8;
        }
        assert_eq!((result, actual), (initial.get(i).copied(), expected), "i={i}");
    }
}
