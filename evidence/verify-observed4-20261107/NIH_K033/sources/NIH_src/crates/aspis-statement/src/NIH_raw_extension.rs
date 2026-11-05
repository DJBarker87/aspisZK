use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_raw_extension(){
 let limbs:[u64;4]=kani::any();
 kani::assume(limbs[0]<(1u64<<62)&&limbs[1]<(1u64<<62)&&limbs[2]<(1u64<<62)&&limbs[3]<(1u64<<62));
 let out=extension_from_raw_limbs(limbs);let index:usize=kani::any();kani::assume(index<4);
 let word=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0][index];
 assert_eq!(word,M31::reduce_u62(limbs[index]).0 ^ if cfg!(NIH_invert){1}else{0});
}
