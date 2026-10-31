use super::*;
use crate::field::{NEB_additive as A,M31,CM31,QM31};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub fn canon(x:WideExact)->bool{A::canon_q(x.c0)&&A::canon_q(x.c1)}
fn any_e()->WideExact{WideExact{c0:A::any_q(),c1:A::any_q()}}
pub fn words(x:WideExact)->[u32;8]{[x.c0.c0.a.0,x.c0.c0.b.0,x.c0.c1.a.0,x.c0.c1.b.0,x.c1.c0.a.0,x.c1.c0.b.0,x.c1.c1.a.0,x.c1.c1.b.0]}
pub fn post_add(x:WideExact,y:WideExact,r:WideExact)->bool {let want=A::reference::add8(words(x),words(y));let good=r.c0.c0.a.0==want[0] && r.c0.c0.b.0==want[1] && r.c0.c1.a.0==want[2] && r.c0.c1.b.0==want[3] && r.c1.c0.a.0==want[4] && r.c1.c0.b.0==want[5] && r.c1.c1.a.0==want[6] && r.c1.c1.b.0==want[7] && canon(r);if cfg!(NEB_wrong_e_add){!good}else{good}}
#[kani::proof_for_contract(WideExact::add)] #[kani::unwind(66)]
#[kani::stub_verified(M31::add)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn e_add(){let x=any_e();let y=any_e();kani::assume(canon(x)&&canon(y));let _=x.add(y);}
pub fn post_sub(x:WideExact,y:WideExact,r:WideExact)->bool {let want=A::reference::sub8(words(x),words(y));let good=r.c0.c0.a.0==want[0] && r.c0.c0.b.0==want[1] && r.c0.c1.a.0==want[2] && r.c0.c1.b.0==want[3] && r.c1.c0.a.0==want[4] && r.c1.c0.b.0==want[5] && r.c1.c1.a.0==want[6] && r.c1.c1.b.0==want[7] && canon(r);if cfg!(NEB_wrong_e_sub){!good}else{good}}
#[kani::proof_for_contract(WideExact::sub)] #[kani::unwind(66)]
#[kani::stub_verified(M31::sub)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn e_sub(){let x=any_e();let y=any_e();kani::assume(canon(x)&&canon(y));let _=x.sub(y);}
pub fn limbs_post(x:WideExact,r:[u32;8])->bool{let good=r==words(x);if cfg!(NEB_wrong_limbs){!good}else{good}}
#[kani::proof_for_contract(WideExact::to_limbs)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn limbs(){let _=any_e().to_limbs();}
pub fn canonical_post(x:QM31,r:QM31)->bool {let good=r.c0.a.0==A::reference::normalize_word(x.c0.a.0)&&r.c0.b.0==A::reference::normalize_word(x.c0.b.0)&&r.c1.a.0==A::reference::normalize_word(x.c1.a.0)&&r.c1.b.0==A::reference::normalize_word(x.c1.b.0)&&A::canon_q(r);if cfg!(NEB_wrong_canonical){!good}else{good}}
#[kani::proof_for_contract(canonical_qm31)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn canonical(){let _=canonical_qm31(A::any_q());}
pub fn embed_post(x:QM31,r:WideExact)->bool{let good=canonical_post(x,r.c0)&&r.c1.c0.a.0==0&&r.c1.c0.b.0==0&&r.c1.c1.a.0==0&&r.c1.c1.b.0==0;if cfg!(NEB_wrong_embed){!good}else{good}}
#[kani::proof_for_contract(WideExact::from_qm31)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn embed(){let _=WideExact::from_qm31(A::any_q());}
