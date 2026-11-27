// SPDX-License-Identifier: Apache-2.0

pub fn get_or_insert<'a>(entries: &'a mut Vec<(u8, u8)>, key: u8, default: u8) -> &'a mut u8 {
    if let Some(found) = entries.iter_mut().find(|(k, _)| *k == key).map(|(_, v)| v) {
        return found;
    }
    entries.push((key, default)); // fallback-push
    &mut entries.last_mut().unwrap().1 // fallback-tail
}

#[cfg(live_conflict)]
pub fn conflicting_insert(entries: &mut Vec<(u8, u8)>, key: u8, default: u8) -> u8 {
    let first = get_or_insert(entries, key, default);
    entries.push((key.wrapping_add(1), default)); // live-conflict
    *first
}

#[test]
fn expected_observations() {
    let mut entries = vec![(1, 10), (2, 20)];
    *get_or_insert(&mut entries, 1, 99) = 15;
    *get_or_insert(&mut entries, 3, 30) += 5;
    assert_eq!(entries, vec![(1, 15), (2, 20), (3, 35)]);
}
