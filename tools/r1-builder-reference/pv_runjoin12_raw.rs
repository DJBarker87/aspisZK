//! Unstubbed all-word primitive gate; no root computation or input assumptions.
use super::*;
#[kani::proof]
#[kani::unwind(25)]
fn raw_all_words() {
    let words=kani::any::<[u32;8]>();
    let digest=words.map(M31);
    let actual=raw(&digest);
    let expected=super::super::records_reference::pv_runjoin12_raw_owned_check(digest);
    for lane in 0..8 {kani::assert(actual[lane]==expected[lane],"shipped raw equals extracted owned raw");}
}
