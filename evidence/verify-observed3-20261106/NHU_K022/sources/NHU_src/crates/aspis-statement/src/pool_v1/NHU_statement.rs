use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn words(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_lift(){let raw:u32=kani::any();let out=lift_m31(M31(raw));let i:usize=kani::any();kani::assume(i<4);assert_eq!(words(out)[i],(if i==0{raw}else{0})^if cfg!(NHU_invert){1}else{0});}
