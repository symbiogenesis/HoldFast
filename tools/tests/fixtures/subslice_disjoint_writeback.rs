// SPDX-License-Identifier: Apache-2.0

fn write_slices(left: &mut [u8], right: &mut [u8]) {
    left.fill(9);
    right.fill(8);
}

pub fn write_disjoint(buf: &mut [u8], a: usize, m: usize, b: usize, n: usize) -> bool {
    if a + m > buf.len() || b + n > buf.len() || !(a + m <= b || b + n <= a) {
        return false;
    }
    #[cfg(direct)]
    {
        write_slices(&mut buf[a..a + m], &mut buf[b..b + n]); // direct-subslice-conflict
        true
    }
    #[cfg(coincident)]
    {
        write_slices(&mut buf[a..a + m], &mut buf[a..a + m]); // coincident-subslice-conflict
        true
    }
    #[cfg(not(any(direct, coincident)))]
    {
        let (left, right) = if a + m <= b {
            let (head, tail) = buf.split_at_mut(b);
            (&mut head[a..a + m], &mut tail[..n])
        } else {
            let (head, tail) = buf.split_at_mut(a);
            (&mut tail[..m], &mut head[b..b + n])
        };
        write_slices(left, right);
        true
    }
}

#[test]
fn expected_observations() {
    let initial = [1, 2, 3, 4, 5, 6];
    for a in 0..=6 {
        for m in 0..=4 {
            for b in 0..=6 {
                for n in 0..=4 {
                    let mut actual = initial;
                    let accepted = write_disjoint(&mut actual, a, m, b, n);
                    let mut expected = initial;
                    let should_accept =
                        a + m <= initial.len() && b + n <= initial.len() && (a + m <= b || b + n <= a);
                    if should_accept {
                        expected[a..a + m].fill(9);
                        expected[b..b + n].fill(8);
                    }
                    assert_eq!((accepted, actual), (should_accept, expected), "a={a}, m={m}, b={b}, n={n}");
                }
            }
        }
    }
}
