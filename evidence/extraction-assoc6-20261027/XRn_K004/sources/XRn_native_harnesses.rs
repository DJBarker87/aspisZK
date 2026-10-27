use super::*;
use aspis_core::field::CM31;
// This counter records the whole NATIVE leaf's selected scalar call order.
// Only Dot push/finish arithmetic is stubbed. No verifier body is replaced.
static mut XRn_COUNT:usize=0;
static mut XRn_STOP:usize=174;
static mut XRn_HASHES:usize=0;
fn k(n:u32)->K {K{c0:CM31{a:M31(n),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}}}
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{unsafe{XRn_HASHES+=1;} [0;32]}}
fn XRn_push(_: &mut crate::fast_pairing::EbyKDot,value:E,scalar:K)->Result<(),()> {
 let n=unsafe{XRn_COUNT}; assert!(n<174);assert_eq!(value,E::ZERO);
 assert_eq!(scalar,k((n/29+1) as u32));
 unsafe{XRn_COUNT=n+1;}
 if n==unsafe{XRn_STOP}{Err(())}else{Ok(())}
}
fn XRn_finish(_:crate::fast_pairing::EbyKDot)->E {E::ZERO}
fn sem()->crate::r1_semantic::Verified<Hash>{
 crate::r1_semantic::Verified{
 roots:[[0;32];2],challenges:crate::r1_wire::Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:[K::ZERO;10],mu:K::ZERO,eta:K::ZERO},
 alpha:[K::ZERO;10],claims:Box::new([[k(1);29],[k(2);29],[k(3);29]]),extra:[k(4);29],before_z1:[k(5);29],state_before_z0:[0;32],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],
 transcript:crate::r1_wire::SemanticTranscript::new(Hash,&[],&[0;32]).unwrap()}
}
fn y1()->[u8;928]{
 let mut out=[0;928];let cell=E::from_qm31(k(6)).to_le_bytes();
 for i in 0..29{out[32*i..32*(i+1)].copy_from_slice(&cell);}out
}
#[kani::proof] #[kani::unwind(176)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_selection_success(){
 unsafe{XRn_COUNT=0;XRn_STOP=174;XRn_HASHES=0;}
 let sem=sem();let y=y1();let out=prepared_claim(&sem,&y,E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Ok(E::ZERO));assert_eq!(unsafe{XRn_COUNT},174);assert_eq!(unsafe{XRn_HASHES},1);
}
#[kani::proof] #[kani::unwind(176)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,XRn_finish)]
fn XRn_claim_selection_error(){
 let stop:usize=kani::any();kani::assume(stop<174);
 unsafe{XRn_COUNT=0;XRn_STOP=stop;XRn_HASHES=0;}
 let sem=sem();let y=y1();let out=prepared_claim(&sem,&y,E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},stop+1);assert_eq!(unsafe{XRn_HASHES},1);
 kani::cover!(stop==0);kani::cover!(stop==173);
}
// After the whole-loop timeout, isolate the first actual rejected push.
fn XRn_powers<const N:usize>(_:E)->[E;N]{let mut out=[E::ZERO;N];if N>0{out[0]=E::ONE;}out}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,XRn_push)]
#[kani::stub(crate::weights::powers,XRn_powers)]
fn XRn_claim_first_rejection(){
 unsafe{XRn_COUNT=0;XRn_STOP=0;XRn_HASHES=0;}
 let sem=sem();let out=prepared_claim(&sem,&[],E::ZERO,&[E::ZERO;29],E::ZERO);
 assert_eq!(out,Err(Error::Parse));assert_eq!(unsafe{XRn_COUNT},1);assert_eq!(unsafe{XRn_HASHES},1);
}
