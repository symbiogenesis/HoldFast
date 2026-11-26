// SPDX-License-Identifier: Apache-2.0

pub fn observe_and_update(
    grid: &mut [Vec<u8>],
    r1: usize,
    c1: usize,
    r2: usize,
    c2: usize,
) -> Option<u8> {
    if r1 >= grid.len()
        || r2 >= grid.len()
        || c1 >= grid[r1].len()
        || c2 >= grid[r2].len()
        || (r1 == r2 && c1 == c2)
    {
        return None;
    }
    #[cfg(any(direct, coincident))]
    {
        let selected = &grid[r1][c1];
        #[cfg(direct)]
        {
            grid[r2][c2] = 7; // multidim-direct-conflict
        }
        #[cfg(coincident)]
        {
            grid[r1][c1] = 7; // multidim-coincident-conflict
        }
        Some(*selected)
    }
    #[cfg(not(any(direct, coincident)))]
    {
        if r1 != r2 {
            let (selected_row, changed_row) = if r1 < r2 {
                let (left, right) = grid.split_at_mut(r2);
                (&left[r1], &mut right[0])
            } else {
                let (left, right) = grid.split_at_mut(r1);
                (&right[0], &mut left[r2])
            };
            let selected = &selected_row[c1];
            changed_row[c2] = 7;
            Some(*selected)
        } else {
            let row = &mut grid[r1];
            let (selected, changed) = if c1 < c2 {
                let (left, right) = row.split_at_mut(c2);
                (&left[c1], &mut right[0])
            } else {
                let (left, right) = row.split_at_mut(c1);
                (&right[0], &mut left[c2])
            };
            *changed = 7;
            Some(*selected)
        }
    }
}

#[test]
fn expected_observations() {
    for r1 in 0..3 {
        for c1 in 0..3 {
            for r2 in 0..3 {
                for c2 in 0..3 {
                    let mut grid = [vec![1, 2], vec![3, 4]];
                    let mut expected = grid.clone();
                    let expected_byte =
                        if r1 < 2 && r2 < 2 && c1 < 2 && c2 < 2 && (r1 != r2 || c1 != c2) {
                            let value = expected[r1][c1];
                            expected[r2][c2] = 7;
                            Some(value)
                        } else {
                            None
                        };
                    assert_eq!(observe_and_update(&mut grid, r1, c1, r2, c2), expected_byte);
                    assert_eq!(grid, expected);
                }
            }
        }
    }
}
