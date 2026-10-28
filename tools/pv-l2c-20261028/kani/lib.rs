// Control-only native association: the selected native call graph contains
// row endpoints, counters, indexing and masks, with no field arithmetic.
#[path="control_cut.rs"]
mod native;

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1026)]
fn native_active_rows_match_masks() {
    let (rows, len) = native::pool_v1_pair_forest_copy_active_rows_v1().unwrap();
    let masks = native::pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
    assert_eq!(len, 214);
    let mut active = [false; 1024];
    let mut i = 0;
    while i < len {
        let row = rows[i] as usize;
        assert!(row < 1024);
        assert!(!active[row]);
        active[row] = true;
        i += 1;
    }
    let mut row = 0;
    while row < 1024 {
        assert_eq!(active[row], masks[row >> 4] & (1u16 << (row & 15)) != 0);
        row += 1;
    }
    assert!(!active[0]);
}

// Split the timed-out 1024-row construction from the packed-mask source cut.
// This exact public-row quantifier matches both native audit loops.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(138)]
fn packed_masks_match_schedule() {
    let masks = native::pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
    let schedule = native::build_pool_v1_pair_forest_copy_row_schedule_v1().unwrap();
    let row: usize = kani::any();
    kani::assume(row < 1024);
    let mut expected = false;
    let mut i = 0;
    while i < schedule.len {
        let link = schedule.data[i];
        expected |= link.producer_row as usize == row || link.consumer_row as usize == row;
        i += 1;
    }
    assert_eq!(masks[row >> 4] & (1u16 << (row & 15)) != 0, expected);
}

// Actual shipped native codec; only byte conversions, slices and guards.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn native_qm31_parser_roundtrip() {
    use aspis_core::field::{CM31, M31, QM31, P};
    let limbs: [u32; 4] = kani::any();
    let mut i = 0;
    while i < 4 { kani::assume(limbs[i] < P); i += 1; }
    let q = QM31 { c0: CM31::new(M31(limbs[0]), M31(limbs[1])),
                   c1: CM31::new(M31(limbs[2]), M31(limbs[3])) };
    let mut bytes = [0u8; 16];
    q.write_le_bytes(&mut bytes);
    assert!(QM31::from_le_bytes(&bytes) == Some(q));
}

// Scalar lane identity for the native packed-mask insertion statement.
// No array/slice/value aggregate is created or copied by this harness.
#[cfg(kani)]
#[kani::proof]
fn packed_lane_insert() {
    let old: u16 = kani::any();
    let p: usize = kani::any();
    let q: usize = kani::any();
    kani::assume(p < 16 && q < 16);
    let mut lane = old;
    lane |= 1u16 << (p as u32);
    assert_eq!(lane & (1u16 << q) != 0,
               old & (1u16 << q) != 0 || p == q);
}
