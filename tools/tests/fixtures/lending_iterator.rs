// SPDX-License-Identifier: Apache-2.0

trait LendingIterator {
    type Item<'next>
    where
        Self: 'next;

    fn next(&mut self) -> Option<Self::Item<'_>>;
}

struct Cursor<'owner> {
    values: &'owner mut [u8],
    index: usize,
}

impl LendingIterator for Cursor<'_> {
    type Item<'next> = &'next mut u8 where Self: 'next;

    fn next(&mut self) -> Option<Self::Item<'_>> {
        let element = self.values.get_mut(self.index)?;
        self.index += 1;
        Some(element)
    }
}

fn rewrite_elements(values: &mut [u8]) -> usize {
    let mut cursor = Cursor { values, index: 0 };
    let mut visits = 0;
    while let Some(element) = cursor.next() {
        *element = if *element == 0 { 9 } else { 1 };
        visits += 1;
    }
    visits
}

fn rewrite_prefix(values: &mut [u8; 4], count: usize) -> Option<usize> {
    Some(rewrite_elements(values.get_mut(..count)?))
}

#[cfg(filter_return)]
fn first_nonzero<'loan>(cursor: &'loan mut Cursor<'_>) -> Option<&'loan mut u8> {
    loop {
        let element = cursor.next()?; // filtered-reborrow
        if *element != 0 {
            return Some(element);
        }
    }
}

#[cfg(live_conflict)]
fn conflicting_next(cursor: &mut Cursor<'_>) -> Option<u8> {
    let first = cursor.next()?;
    let second = cursor.next()?; // live-conflict
    Some(*first + *second)
}

#[cfg(owner_conflict)]
fn conflicting_owner(cursor: &mut Cursor<'_>) -> Option<u8> {
    let position = cursor.index;
    let element = cursor.next()?;
    cursor.values[position] = 9; // owner-conflict
    Some(*element)
}

#[test]
fn expected_observations() {
    for (initial, rewritten) in [([0, 2, 0, 4], [9, 1, 9, 1]), ([1, 0, 3, 0], [1, 9, 1, 9])] {
        for count in 0..=5 {
            let mut actual = initial;
            let mut expected = initial;
            if count <= 4 {
                expected[..count].copy_from_slice(&rewritten[..count]);
            }
            assert_eq!(rewrite_prefix(&mut actual, count), (count <= 4).then_some(count));
            assert_eq!(actual, expected, "count={count}");
        }
    }

    #[cfg(filter_return)]
    {
        let mut values = [0, 0, 3, 0];
        let mut cursor = Cursor { values: &mut values, index: 0 };
        let found = first_nonzero(&mut cursor).unwrap();
        assert_eq!(*found, 3);
        *found = 9;
        assert!(first_nonzero(&mut cursor).is_none());
        assert_eq!(values, [0, 0, 9, 0]);
    }
}
