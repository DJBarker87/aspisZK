// One arbitrary source window for TX1's frozen folded_root conversion.
// No field arithmetic, observer, contracts, writable statics, or digest model.
#[allow(dead_code,non_snake_case)]
mod copies { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
#[kani::stub(core::ptr::copy_nonoverlapping,copies::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,copies::KMX_copy_from_slice)]
#[kani::proof]
#[kani::unwind(34)]
fn folded_root_window() {
    let proof: [u8;64]=kani::any();
    let start: usize=kani::any();
    kani::assume(start<=32);
    let folded_root: [u8;32]=proof[start..start+32].try_into().unwrap();
    let j: usize=kani::any();
    kani::assume(j<32);
    let good=folded_root[j]==proof[start+j];
    assert!(good!=cfg!(NHW_invert));
}
