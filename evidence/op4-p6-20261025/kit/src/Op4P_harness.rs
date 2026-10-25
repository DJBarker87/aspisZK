use super::{Op4P_reference as r,Op4P_shipped as s};
#[kani::proof]
#[kani::unwind(57700)]
fn Op4P_whole_scan() {
    let bytes:[u8;57607]=kani::any();
    assert_eq!(s::canonical_scan(&bytes),r::canonical_scan(&bytes));
}
