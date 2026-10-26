//! Proof references only; no shipped source changes.
use aspis_core::field::{M31,CM31,QM31};
pub fn compression_single(tag:M31, x:M31, lambda:QM31)->QM31 {
 QM31::from_cm31(CM31::from_m31(tag)).add(lambda.mul_m31(x))
}
#[cfg(kani)]
mod compression_split {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn one_b() {
  let raw:[u32;6]=kani::any();
  let t=M31(raw[0]);let x=M31(raw[1]);
  let l=QM31{c0:CM31{a:M31(raw[2]),b:M31(raw[3])},c1:CM31{a:M31(raw[4]),b:M31(raw[5])}};
  let a=aspis_statement::logup::compress_tagged_tuple(t,&[x],l);
  let b=compression_single(t,x,l);
  assert_eq!(a.c0.b.0,b.c0.b.0);
 }
}

pub fn trace_clone(x:&aspis_statement::state_only_trace::StateOnlyTraceFoundation)->aspis_statement::state_only_trace::StateOnlyTraceFoundation {x.clone()}
