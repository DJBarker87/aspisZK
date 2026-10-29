use aspis_statement::pool_v1::pair_forest_hiding::*;
#[no_mangle]
#[inline(never)]
pub fn PV_OWNG_rows() -> Result<Vec<u16>, aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1> {pool_v1_pair_forest_copy_active_rows_v1()}
#[no_mangle]
#[inline(never)]
pub fn PV_OWNG_masks() -> Result<[u16;64], aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1> {pool_v1_pair_forest_copy_active_row_masks_v1()}
fn main() {
 let rows=std::hint::black_box(PV_OWNG_rows()).unwrap();
 let masks=std::hint::black_box(PV_OWNG_masks()).unwrap();
 println!("rows={:?}\nmasks={:?}",rows,masks);
 println!("rows_fingerprint={:016x}",pool_v1_pair_forest_copy_active_rows_fingerprint_v1().unwrap());
 // The crate has no dedicated active-mask fingerprint; inactive mask uses complemented values.
 println!("inactive_masks_fingerprint={:016x}",pool_v1_pair_forest_copy_inactive_row_masks_fingerprint_v1().unwrap());
}
