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
