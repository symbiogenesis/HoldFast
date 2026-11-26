// SPDX-License-Identifier: Apache-2.0

fn with_view<F>(values: &[u8; 4], mut select: F) -> &u8
where
    F: for<'fresh> FnMut(&'fresh u8) -> &'fresh u8,
{
    select(&values[1])
}

fn identity(value: &u8) -> &u8 {
    value
}

#[cfg(escaping_view)]
fn retain_view(values: &[u8; 4]) {
    let mut retained = None;
    with_view(values, |view| {
        retained = Some(view); // escaping-view
        view
    });
    assert!(retained.is_some());
}

#[test]
fn expected_observations() {
    let values = [1, 2, 3, 4];
    let other = [5, 6, 7, 8];
    let first = with_view(&values, identity);
    let second = with_view(&other, identity);
    assert_eq!((*first, *second), (2, 6));
    assert!(std::ptr::eq(first, &values[1]));
    assert!(std::ptr::eq(second, &other[1]));
}
