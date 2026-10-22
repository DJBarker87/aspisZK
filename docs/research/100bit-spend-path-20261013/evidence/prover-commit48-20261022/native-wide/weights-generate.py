from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
p=Path('crates/aspis-r1-cost-probe/src/weights.rs');s=p.read_text()
a=s.index('pub struct Weights {');b=s.index('    pub fn raw(&self',a)
body=s[a:b]+'}\n'
text='''use field::{QM31 as K,M31,CM31};
use std::boxed::Box;
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum Variant {S1,S2,D}
#[derive(Clone,Copy)] pub struct SecureCirclePoint {pub x:K,pub y:K}
#[derive(Debug)] pub enum Error {Allocation}
const TAU:[usize;5]=[3,4,2,0,1];
static mut POINTS:[[K;10];3]=[[K::ZERO;10];3];
mod aspis_core {
 pub mod r0 {pub mod heap {
  pub fn uninit<T>()->Result<Box<core::mem::MaybeUninit<T>>,crate::Error> {Ok(Box::<T>::new_uninit())}
 }}
 pub mod state_only_prefix {pub mod r0 {
  pub fn statement_points(_alpha:&[crate::K;10])->[[crate::K;10];3] {unsafe {crate::POINTS}}
 }}
}
fn double(x:K)->K {x.mul(x).add(x.mul(x)).sub(K::ONE)}
'''+body+'''
#[cfg(kani)] mod weight_proofs {
 use super::*;
 fn arbitrary_qm()->K {
  let words:[u32;4]=kani::any();
  for i in 0..4 {kani::assume(words[i]<field::P);}
  K{c0:CM31{a:M31(words[0]),b:M31(words[1])},c1:CM31{a:M31(words[2]),b:M31(words[3])}}
 }
 fn arbitrary_binary(_x:K,_y:K)->K {arbitrary_qm()}
 #[kani::proof] #[kani::unwind(34)]
 #[kani::stub(crate::field::QM31::mul,arbitrary_binary)]
 #[kani::stub(crate::field::QM31::add,arbitrary_binary)]
 #[kani::stub(crate::field::QM31::sub,arbitrary_binary)]
 fn weights_initialization() {
  let alpha=core::array::from_fn(|_|arbitrary_qm());
  let points=core::array::from_fn(|_|core::array::from_fn(|_|arbitrary_qm()));
  unsafe {POINTS=points;}
  let z=core::array::from_fn(|_|SecureCirclePoint{x:arbitrary_qm(),y:arbitrary_qm()});
  let variant=match kani::any::<u8>()%3 {0=>Variant::S1,1=>Variant::S2,_=>Variant::D};
  let out=Weights::new(variant,&alpha,&z).unwrap();
  assert_eq!(out.variant,variant);assert_eq!(out.points,points);assert_eq!(out.extra,[alpha[8],alpha[9]]);
  for k in 0..5 {for d in 0..5 {for lane in 0..4 {
   let q=out.factors[k][d][lane];
   for word in [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0] {assert!(word<field::P);}
  }}}
 }
}
'''
(H/'weights-init.rs').write_text(text)
(H/'weights-spans.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),literal_body_sha256=hashlib.sha256(body.encode()).hexdigest(),generated_sha256=hashlib.sha256(text.encode()).hexdigest(),scope='Successful allocator branch only, no allocation totality. Statement-points helper returns arbitrary complete canonical points; arithmetic stubs return arbitrary canonical QM31. No value/model or probability assertion.'),indent=2)+'\n')
