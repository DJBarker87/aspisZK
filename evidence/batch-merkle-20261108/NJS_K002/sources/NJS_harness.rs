use super::*;
#[allow(non_snake_case)]
mod kmx { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn key_at() {
 let keys:[u64;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);
 let actual=batch_key_at(&keys,i);
 #[cfg(not(NJS_invert))] assert_eq!(actual,keys[i]);
 #[cfg(NJS_invert)] assert_ne!(actual,keys[i]);
}
#[kani::proof]
#[kani::unwind(18)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn same_index() {
 let values:[u32;16]=kani::any();let i:usize=kani::any();let expected:u32=kani::any();kani::assume(i<16);
 let actual=same_batch_index(&values,i,expected);
 #[cfg(not(NJS_invert))] assert_eq!(actual,values[i]==expected);
 #[cfg(NJS_invert)] assert_ne!(actual,values[i]==expected);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn same_leaf() {
 let values:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<16);
 let actual=same_batch_leaf(&values,i,leaf);
 #[cfg(not(NJS_invert))] assert_eq!(actual,values[i]==leaf);
 #[cfg(NJS_invert)] assert_ne!(actual,values[i]==leaf);
}
