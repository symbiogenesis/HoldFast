// SPDX-License-Identifier: Apache-2.0

struct Link {
    visits: u8,
    next: Option<Box<Link>>,
}

fn visit(mut cursor: &mut Option<Box<Link>>, steps: &[bool]) {
    for advance in steps {
        if let Some(node) = cursor { // loop-reborrow
            #[cfg(live_conflict)]
            {
                *cursor = None; // live-conflict
            }
            node.visits = node.visits.saturating_add(1);
            if *advance {
                cursor = &mut node.next;
            }
        }
    }
}

#[test]
fn expected_observations() {
    let mut head = Some(Box::new(Link {
        visits: 0,
        next: Some(Box::new(Link { visits: 0, next: None })),
    }));
    visit(&mut head, &[false, true, false, false, true, true]);
    let first = head.as_ref().unwrap();
    let second = first.next.as_ref().unwrap();
    assert_eq!((first.visits, second.visits), (2, 3));
    assert!(second.next.is_none());
}
