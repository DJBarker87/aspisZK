pub mod reference132;
#[cfg(test)]
#[path="../owned133.rs"]
mod owned133;
#[cfg(test)]
mod owned132;
#[test]
fn native132_finite() {
    let native=aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let owned=owned132::pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let reference=reference132::cells();
    assert_eq!(native,owned);
    let host=aspis_prover::host_forest::pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    assert_eq!(host.1,3803);
    assert_eq!(host.0.iter().map(|x|(x.row,x.column)).collect::<Vec<_>>(),
      reference.0.iter().map(|x|(x.row,x.column)).collect::<Vec<_>>());
    let pairs=|v: Vec<aspis_statement::trace_v4::TraceCell>| v.into_iter().map(|x|(x.row,x.column)).collect::<Vec<_>>();
    assert_eq!(pairs(native),reference.0.into_iter().map(|x|(x.row,x.column)).collect::<Vec<_>>());
    assert_eq!(reference132::cells().1,3803);
    println!("original/owned/reference same-unit complete output; 3803 ordered cells; finite validation");
}
