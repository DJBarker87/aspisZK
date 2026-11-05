use super::*;
use crate::field::P;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn canonical_cm()->CM31 { let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P);kani::assume(b<P);CM31::new(M31(a),M31(b)) }
fn add(a:u32,b:u32)->u32 { let s=a+b;if s>=P{s-P}else{s} }
fn sub(a:u32,b:u32)->u32 { if a>=b{a-b}else{P-(b-a)} }
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_cm_i(){let v=canonical_cm();let result=cm31_mul_i(v);let expected=if v.b.0==0{0}else{P-v.b.0};assert_eq!(result.a.0,expected^if cfg!(NHU_invert){1}else{0});assert_eq!(result.b.0,v.a.0);assert!(result.a.0<P&&result.b.0<P);}
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_cm_r(){let v=canonical_cm();let result=cm31_mul_r(v);assert_eq!(result.a.0,sub(add(v.a.0,v.a.0),v.b.0)^if cfg!(NHU_invert){1}else{0});assert_eq!(result.b.0,add(v.a.0,add(v.b.0,v.b.0)));assert!(result.a.0<P&&result.b.0<P);}
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_copy(){let source:[u8;4]=kani::any();let mut target:[u8;4]=kani::any();unsafe{core::ptr::copy_nonoverlapping(source.as_ptr(),target.as_mut_ptr(),4);}let i:usize=kani::any();kani::assume(i<4);assert_eq!(target[i],source[i]^if cfg!(NHU_invert){1}else{0});}
