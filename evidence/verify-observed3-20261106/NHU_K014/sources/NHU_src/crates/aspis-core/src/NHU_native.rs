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
fn wi(c:CM31)->CM31{CM31::new(M31(if c.b.0==0{0}else{P-c.b.0}),c.a)}
fn wr(c:CM31)->CM31{CM31::new(M31(sub(add(c.a.0,c.a.0),c.b.0)),M31(add(c.a.0,add(c.b.0,c.b.0))))}
fn canonical_q()->QM31{QM31{c0:canonical_cm(),c1:canonical_cm()}}
fn words(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_tower(){let v=canonical_q();let c:usize=kani::any();kani::assume(c<4);let result=mul_tower_basis(v,c);let expected=match c{0=>v,1=>QM31{c0:wi(v.c0),c1:wi(v.c1)},2=>QM31{c0:wr(v.c1),c1:v.c0},_=>QM31{c0:wi(wr(v.c1)),c1:wi(v.c0)}};let i:usize=kani::any();kani::assume(i<4);assert_eq!(words(result)[i],words(expected)[i]^if cfg!(NHU_invert){1}else{0});assert!(words(result)[i]<P);}

include!("NHU_power.rs");

include!("NHU_linear.rs");
