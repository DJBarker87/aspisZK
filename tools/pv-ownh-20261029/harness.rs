use aspis_statement::pool_v1::pair_forest_hiding::*;
use aspis_statement::pool_v1::pair_tree_hiding::PoolV1PairHidingLayoutErrorV1 as Error;
#[no_mangle]
#[inline(never)]
pub fn PV_OWNH_rows() -> Result<Vec<u16>, Error> {
    pool_v1_pair_forest_copy_active_rows_v1()
}
#[no_mangle]
#[inline(never)]
pub fn PV_OWNH_masks() -> Result<[u16;64], Error> {
    pool_v1_pair_forest_copy_active_row_masks_v1()
}
fn emit(words: &[u16]) {
    // Canonical semantic Result encoding: Ok=0, length as LE u64, then LE u16.
    // This never reads Vec/enum/array padding or addresses.
    print!("result=00");
    for b in (words.len() as u64).to_le_bytes() { print!("{b:02x}"); }
    for w in words { for b in w.to_le_bytes() { print!("{b:02x}"); } }
    println!();
}
fn main() {
    let mode=std::env::args().nth(1).unwrap(); // Harness driver, outside either root.
    if mode=="rows" {
        let words=std::hint::black_box(PV_OWNH_rows()).unwrap();
        emit(&words);
        println!("capacity={}",words.capacity());
    } else {
        assert_eq!(mode,"masks");
        let words=std::hint::black_box(PV_OWNH_masks()).unwrap();
        emit(&words);
    }
    // Independent crate APIs; these are outside the target root's observation.
    println!("rows_fingerprint={:016x}",pool_v1_pair_forest_copy_active_rows_fingerprint_v1().unwrap());
    println!("schedule_fingerprint={:016x}",pool_v1_pair_forest_copy_row_schedule_fingerprint_v1().unwrap());
}
