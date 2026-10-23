use super::*;
use aspis_core::field::{M31,CM31};
use alloc::boxed::Box;
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{[0;32]}}
fn qm(x:[u32;4])->K {K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn wide(x:[u32;8])->E {E::new(qm([x[0],x[1],x[2],x[3]]),qm([x[4],x[5],x[6],x[7]]))}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 use aspis_core::circle::SecureCirclePoint;
 r1_semantic::Verified {
 roots:[[0;32];2],challenges:Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:core::array::from_fn(|_|K::ZERO),mu:K::ZERO,eta:K::ZERO},
 alpha:[K::ZERO;10],claims:Box::new(claims.map(|row|row.map(qm))),extra:extra.map(qm),before_z1:before.map(qm),state_before_z0:[0;32],
 z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],transcript:SemanticTranscript::new(Hash,&[],&[0;32]).unwrap(),
 }
}
// Arbitrary full integer accumulator representation; no enum/reference/drop
// fields. Size equality is checked by Rust's transmute type checker. Every
// bit pattern is valid. No field order is assumed or compared to a model.
fn dot_state(x:[u64;9])->fast_pairing::EbyKDot {unsafe{core::mem::transmute(x)}}
fn dot_image(x:fast_pairing::EbyKDot)->[u64;9] {unsafe{core::mem::transmute(x)}}
#[kani::proof]
#[kani::unwind(128)]
fn scalar_push_step_actual() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();let l:usize=kani::any();kani::assume(point<5&&l<29);
 let coeffs:[[u32;8];29]=kani::any();let g=coeffs.map(wide);
 let state:[u64;9]=kani::any();let mut old=dot_state(state);let mut new=dot_state(state);
 let a=original_step(&sem,&[],&g,point,l,&mut old);
 let b=helper_step(&sem,&[],&g,point,l,&mut new);
 assert_eq!(a,b);assert_eq!(dot_image(old),dot_image(new));
 kani::cover!(a.is_ok(),"successful actual push");kani::cover!(a.is_err(),"rejected actual push");
}
