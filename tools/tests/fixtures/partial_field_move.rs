// SPDX-License-Identifier: Apache-2.0

#[derive(Debug, PartialEq, Eq)]
pub struct PairBuffer {
    pub left: Vec<u8>,
    pub right: Vec<u8>,
}

pub fn rotate_left_field(mut pair: PairBuffer) -> (Vec<u8>, PairBuffer) {
    let moved_left = pair.left;
    pair.right.push(9);
    #[cfg(use_moved)]
    let _bad = pair.left.len(); // moved-field-use
    pair.left = vec![1, 2];
    (moved_left, pair)
}

#[test]
fn expected_observations() {
    let pair = PairBuffer { left: vec![3, 4], right: vec![5] };
    let (old_left, restored) = rotate_left_field(pair);
    assert_eq!(old_left, vec![3, 4]);
    assert_eq!(restored, PairBuffer { left: vec![1, 2], right: vec![5, 9] });
}
