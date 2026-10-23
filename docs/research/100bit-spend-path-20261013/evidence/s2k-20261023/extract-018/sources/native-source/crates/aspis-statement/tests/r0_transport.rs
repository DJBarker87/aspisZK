use aspis_core::r0::{opening, transport};
use aspis_statement::pool_v1::{
    pool_v1_pair_forest_copy_active_rows_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
};

#[test]
fn transport_pads_match_authoritative_inventory_and_historical_order() {
    let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let legal = |r| (0..16).all(|c| cells.iter().any(|x| x.row == r && x.column == c));
    let pads: Vec<u16> = (0..1023)
        .filter(|r| !active.contains(r) && *r != 1014 && legal(*r))
        .take(89)
        .collect();
    assert_eq!(pads.len(), 89);
    assert_eq!(pads.as_slice(), transport::PAD_ROWS);
    for &r in pads.iter().chain(core::iter::once(&1023)) {
        assert!(!active.contains(&r));
        for column in 0..16 {
            assert!(cells.iter().any(|x| x.row == r && x.column == column));
        }
    }
    let mut order = pads.clone();
    order.extend((0..1023).filter(|r| !pads.contains(r)));
    order.push(1023);
    assert_eq!(order.as_slice(), transport::COEFFICIENT_TO_ROW);
    for r in 0..1024 {
        assert_eq!(opening::inactive(r).unwrap(), !active.contains(&(r as u16)));
    }
}
