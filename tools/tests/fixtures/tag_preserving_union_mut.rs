// SPDX-License-Identifier: Apache-2.0

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Slot {
    Active { header: u8, payload: [u8; 4] },
    Vacant,
}

#[cfg(direct)]
fn overwrite_payload(slot: &mut Slot, byte: u8) {
    if let Slot::Active { payload, .. } = slot {
        payload.fill(byte);
    }
}

pub fn update_active_payload(slot: &mut Slot, byte: u8) -> Option<u8> {
    #[cfg(any(direct, coincident))]
    {
        let header_ref = match &*slot {
            Slot::Active { header, .. } => header,
            Slot::Vacant => return None,
        };
        #[cfg(direct)]
        overwrite_payload(slot, byte); // tag-preserving-write
        #[cfg(coincident)]
        {
            let _ = byte;
            *slot = Slot::Vacant; // tag-changing-write
        }
        Some(*header_ref)
    }
    #[cfg(not(any(direct, coincident)))]
    {
        match slot {
            Slot::Active { header, payload } => {
                let observed = *header;
                payload.fill(byte);
                Some(observed)
            }
            Slot::Vacant => None,
        }
    }
}

#[test]
fn expected_observations() {
    let mut active = Slot::Active { header: 7, payload: [1, 2, 3, 4] };
    assert_eq!(update_active_payload(&mut active, 9), Some(7));
    assert_eq!(active, Slot::Active { header: 7, payload: [9, 9, 9, 9] });
    let mut vacant = Slot::Vacant;
    assert_eq!(update_active_payload(&mut vacant, 9), None);
    assert_eq!(vacant, Slot::Vacant);
}
