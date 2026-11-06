use super::*;
#[allow(non_snake_case)]
mod kmx { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NKL_fragments.rs"));
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn merkle_exit(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);
 let before_i=idx[j];let before_v=val[j][k];
 let out=merkle_exit_fragment(&mut idx,&mut val);
 #[cfg(not(NKL_invert))] assert!(matches!(out,Err(Error::Merkle)));
 #[cfg(NKL_invert)] assert!(!(matches!(out,Err(Error::Merkle))));
 assert_eq!(idx[j],before_i);assert_eq!(val[j][k],before_v);
}
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn ok_exit(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);
 let before_i=idx[j];let before_v=val[j][k];
 let out=ok_exit_fragment(&mut idx,&mut val);
 #[cfg(not(NKL_invert))] assert!(matches!(out,Ok(())));
 #[cfg(NKL_invert)] assert!(!(matches!(out,Ok(()))));
 assert_eq!(idx[j],before_i);assert_eq!(val[j][k],before_v);
}
