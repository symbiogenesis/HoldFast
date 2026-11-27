// SPDX-License-Identifier: Apache-2.0

pub fn push_while_borrowed(buf: &mut Vec<u8>, item: u8) -> Option<u8> {
    if buf.is_empty() || buf.len() >= buf.capacity() {
        return None;
    }
    #[cfg(direct)]
    {
        let first = &buf[0];
        buf.push(item); // direct-push-conflict
        Some(*first)
    }
    #[cfg(coincident)]
    {
        let first = &buf[0];
        buf.clear(); // coincident-clear-conflict
        let _ = item;
        Some(*first)
    }
    #[cfg(not(any(direct, coincident)))]
    {
        let first = buf[0];
        buf.push(item);
        Some(first)
    }
}

#[test]
fn expected_observations() {
    let mut buf = Vec::with_capacity(4);
    assert_eq!(push_while_borrowed(&mut buf, 10), None);
    buf.push(5);
    assert_eq!(push_while_borrowed(&mut buf, 10), Some(5));
    assert_eq!(push_while_borrowed(&mut buf, 20), Some(5));
    assert_eq!(push_while_borrowed(&mut buf, 30), Some(5));
    assert_eq!(push_while_borrowed(&mut buf, 40), None);
    assert_eq!(buf, vec![5, 10, 20, 30]);
    assert_eq!(buf.capacity(), 4);
}
