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
