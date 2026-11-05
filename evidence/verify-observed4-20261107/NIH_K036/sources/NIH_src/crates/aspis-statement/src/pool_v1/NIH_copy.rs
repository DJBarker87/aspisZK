use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lift(){
 let raw:u32=kani::any();let out=lift_m31(M31(raw));
 let i:usize=kani::any();kani::assume(i<4);
 let got=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0][i];
 assert_eq!(got,(if i==0{raw}else{0}) ^ if cfg!(NIH_invert){1}else{0});
}
