use super::*;
use crate::field::{CM31,M31,P};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn any_e()->WideExact{WideExact{c0:any_q(),c1:any_q()}}
fn new_q(r:QM31,v:QM31)->bool{r.c0.a.0==v.c0.a.0%P && r.c0.b.0==v.c0.b.0%P && r.c1.a.0==v.c1.a.0%P && r.c1.b.0==v.c1.b.0%P}
pub(super) fn new_matches(r:&WideExact,c0:QM31,c1:QM31)->bool{new_q(r.c0,c0) && new_q(r.c1,c1)}
fn cq(v:QM31)->bool{v.c0.a.0<P && v.c0.b.0<P && v.c1.a.0<P && v.c1.b.0<P}
pub(super) fn canonical(v:WideExact)->bool{cq(v.c0)&&cq(v.c1)}
fn nw(x:u32)->u32{if x==0{0}else{P-x}}
fn neg_q(r:QM31,v:QM31)->bool{r.c0.a.0==nw(v.c0.a.0)&&r.c0.b.0==nw(v.c0.b.0)&&r.c1.a.0==nw(v.c1.a.0)&&r.c1.b.0==nw(v.c1.b.0)}
pub(super) fn neg_matches(r:&WideExact,v:WideExact)->bool{neg_q(r.c0,v.c0)&&neg_q(r.c1,v.c1)}
#[kani::proof_for_contract(WideExact::new)]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn new_contract(){let _=WideExact::new(any_q(),any_q());}
#[kani::proof_for_contract(WideExact::neg)]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn neg_contract(){let v=any_e();kani::assume(canonical(v));let _=v.neg();}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let src=any_e();let mut dst=any_e();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.c0.c0.a.0==src.c0.c0.a.0&&dst.c1.c1.b.0==src.c1.c1.b.0);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let src=any_e();let mut dst=any_e();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.c1.c1.b.0!=src.c1.c1.b.0);}
