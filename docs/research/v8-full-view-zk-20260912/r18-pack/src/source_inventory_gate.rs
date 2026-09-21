//! Rust integration TEST DRAFT: insert in the existing test-only basis module.
//! This calls the actual source inventory, rather than accepting the C++ projection.
//! The bit-affine candidate is REJECTED for full-view use; its legal raw lift alone
//! does not repair the H1 compatible image.
#[test]
fn r18_source_inventory_for_rejected_bit_affine_candidate() {
    use aspis_statement::pool_v1::{
        pool_v1_pair_forest_copy_active_rows_v1,
        pool_v1_pair_forest_relation_free_mask_cells_v1,
    };
    let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let pi0 = |j: usize| 16 * (j & 63) + (15 - (j >> 6));
    let mut order: [usize; 1024] = core::array::from_fn(pi0);
    order.swap(128, 1023);
    assert_eq!(order[1023], 13);
    for row in order[..89].iter().copied().chain(core::iter::once(13)) {
        assert!(!active.contains(&(row as u16)));
        assert_ne!(row, 1014);
        for column in 0..16 {
            assert!(cells.iter().any(|c| usize::from(c.row) == row && usize::from(c.column) == column));
        }
    }
    // Do NOT install this transport after a passing inventory test.
    // The source-shaped full H1 diagnostic loses 23 dimensions (540 -> 517).
}
