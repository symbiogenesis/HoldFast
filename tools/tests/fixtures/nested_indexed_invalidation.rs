// SPDX-License-Identifier: Apache-2.0

pub fn observe(rows: &mut [Vec<u8>], i: usize, j: usize) -> Option<u8> {
    if i >= 2 || j >= 2 || i == j {
        return None;
    }
    #[cfg(any(direct, coincident))]
    {
        let selected = &rows[i][0];
        #[cfg(direct)]
        rows[j].clear(); // distinct-index-invalidation
        #[cfg(coincident)]
        rows[i].clear(); // coincident-index-invalidation
        Some(*selected)
    }
    #[cfg(not(any(direct, coincident)))]
    {
        let (selected_row, changed_row) = if i < j {
            let (left, right) = rows.split_at_mut(j);
            (&left[i], &mut right[0])
        } else {
            let (left, right) = rows.split_at_mut(i);
            (&right[0], &mut left[j])
        };
        let selected = &selected_row[0];
        changed_row.clear();
        Some(*selected)
    }
}

#[test]
fn expected_observations() {
    for i in 0..4 {
        for j in 0..4 {
            let mut rows = [vec![3, 4], vec![6, 7], vec![9, 10]];
            let mut expected = rows.clone();
            let expected_byte = if i < 2 && j < 2 && i != j {
                expected[j].clear();
                Some(expected[i][0])
            } else {
                None
            };
            assert_eq!(observe(&mut rows, i, j), expected_byte);
            assert_eq!(rows, expected);
        }
    }
}
