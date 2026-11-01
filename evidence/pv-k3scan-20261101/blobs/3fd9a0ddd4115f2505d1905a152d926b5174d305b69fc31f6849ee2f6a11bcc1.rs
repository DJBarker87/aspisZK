// Proof-local gates only. The shipped crates are unchanged.
#[cfg(kani)]
#[path="../../pv-rw-step/proof/generated.rs"]
mod generated;
#[cfg(kani)]
#[path="../../pv-rw-step/proof/iterator_state_step.rs"]
mod combined;
#[cfg(kani)]
mod gates {
 use aspis_core::field::{M31,CM31,QM31,P};
 use super::{generated,combined};
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 fn zero()->QM31 {QM31::from_cm31(CM31::from_m31(M31(0)))}
 fn equal(a:QM31,b:QM31) {
  assert_eq!(a.c0.a.0,b.c0.a.0); assert_eq!(a.c0.b.0,b.c0.b.0);
  assert_eq!(a.c1.a.0,b.c1.a.0); assert_eq!(a.c1.b.0,b.c1.b.0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn empty_original() {
  let tag=M31(kani::any());let lambda=q();
  equal(generated::compress_tagged_tuple(tag,&[],lambda),QM31::from_cm31(CM31::from_m31(tag)));
 }
 #[kani::proof] #[kani::unwind(2)]
 fn empty_combined() {
  let out=q();let power=q();let lambda=q();let values:[M31;0]=[];
  let (live,next,out1,power1)=combined::iterator_state_step(values.iter(),out,power,lambda);
  assert!(!live);assert_eq!(next.as_slice().len(),0);equal(out1,out);equal(power1,power);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn exhausted_combined16() {
  let values:[u32;16]=kani::any();let data=values.map(M31);let mut iter=data.iter();let mut i=0;
  while i<16 {iter.next();i+=1;}
  let out=q();let power=q();let lambda=q();
  let (live,next,out1,power1)=combined::iterator_state_step(iter,out,power,lambda);
  assert!(!live);assert_eq!(next.as_slice().len(),0);equal(out1,out);equal(power1,power);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn exhaustion_stable16() {
  let values:[u32;16]=kani::any();let data=values.map(M31);let mut iter=data[16..].iter();
  assert_eq!(iter.next(),None);assert_eq!(iter.next(),None);assert_eq!(iter.as_slice().len(),0);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn next16_from_initial() {
  let raw:[u32;16]=kani::any();let values=raw.map(M31);let mut iter=values.iter();
  assert_eq!(iter.next(),Some(&M31(raw[0])));assert_eq!(iter.as_slice(),&values[1..]);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn next16_from_suffix() {
  let raw:[u32;16]=kani::any();let values=raw.map(M31);let i:usize=kani::any();kani::assume(i<16);
  let mut iter=values[i..].iter();assert_eq!(iter.next(),Some(&values[i]));assert_eq!(iter.as_slice(),&values[i+1..]);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn next16_last() {
  let raw:[u32;16]=kani::any();let values=raw.map(M31);let mut iter=values[15..].iter();
  assert_eq!(iter.next(),Some(&values[15]));assert_eq!(iter.next(),None);assert_eq!(iter.len(),0);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn next16_preserves_tail() {
  let raw:[u32;16]=kani::any();let values=raw.map(M31);let i:usize=kani::any();kani::assume(i<16);
  let mut iter=values[i..].iter();iter.next();let j:usize=kani::any();kani::assume(j<15-i);
  assert_eq!(iter.as_slice()[j].0,raw[i+1+j]);
 }
 #[kani::proof] #[kani::unwind(18)]
 fn next16_preserves_source() {
  let raw:[u32;16]=kani::any();let values=raw.map(M31);let before=values;
  let i:usize=kani::any();kani::assume(i<=16);let mut iter=values[i..].iter();iter.next();assert_eq!(values,before);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn zero_power_state() {
  let tag:u32=kani::any();kani::assume(tag<P);let out=QM31::from_cm31(CM31::from_m31(M31(tag)));
  let value=M31(kani::any());let lambda=q();let (out1,power1)=generated::shipped_step(out,zero(),&value,lambda);
  equal(out1,out);equal(power1,zero());
 }
 #[kani::proof] #[kani::unwind(3)]
 fn zero_lambda_single() {
  let tag:u32=kani::any();kani::assume(tag<P);let value=M31(kani::any());
  equal(generated::compress_tagged_tuple(M31(tag),&[value],zero()),QM31::from_cm31(CM31::from_m31(M31(tag))));
 }
 #[kani::proof] #[kani::unwind(18)]
 fn zero_lambda_16() {
  let tag:u32=kani::any();kani::assume(tag<P);let raw:[u32;16]=kani::any();let values=raw.map(M31);
  equal(generated::compress_tagged_tuple(M31(tag),&values,zero()),QM31::from_cm31(CM31::from_m31(M31(tag))));
 }
 #[kani::proof] #[kani::unwind(2)]
 fn unit_power_zero_value() {
  let tag:u32=kani::any();kani::assume(tag<P);let out=QM31::from_cm31(CM31::from_m31(M31(tag)));
  let one=QM31::from_cm31(CM31::from_m31(M31(1)));
  let (out1,power1)=generated::shipped_step(out,one,&M31(0),one);equal(out1,out);equal(power1,one);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn canonical_scalar_mul() {
  let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P);kani::assume(b<P);
  assert_eq!(M31(a).mul(M31(b)).0,aspis_core::field::ct::reduce64((a as u64)*(b as u64)));
 }
 #[kani::proof] #[kani::unwind(2)]
 fn canonical_scale_c0a() {
  let p=q();let v:u32=kani::any();kani::assume(p.c0.a.0<P);kani::assume(v<P);
  assert_eq!(p.mul_m31(M31(v)).c0.a.0,p.c0.a.mul(M31(v)).0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn canonical_power_c0a() {
  let out=zero();let p=q();let l=q();let v=M31(0);
  kani::assume(p.c0.a.0<P);kani::assume(p.c0.b.0<P);kani::assume(p.c1.a.0<P);kani::assume(p.c1.b.0<P);
  kani::assume(l.c0.a.0<P);kani::assume(l.c0.b.0<P);kani::assume(l.c1.a.0<P);kani::assume(l.c1.b.0<P);
  assert_eq!(generated::shipped_step(out,p,&v,l).1.c0.a.0,p.mul(l).c0.a.0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn reduce64_product_bound() {
  let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P);kani::assume(b<P);
  let x=(a as u64)*(b as u64);assert!(x<(1u64<<62));
 }
 #[kani::proof] #[kani::unwind(2)]
 fn canonical_add_bound() {
  let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P);kani::assume(b<P);
  assert!(M31(a).add(M31(b)).0<P);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn canonical_reduce64_bound() {let x:u64=kani::any();assert!(aspis_core::field::ct::reduce64(x)<P);}
 #[kani::proof] #[kani::unwind(2)]
 fn canonical_scalar_product_u16() {
  let a:u16=kani::any();let b:u16=kani::any();
  assert_eq!(M31(a as u32).mul(M31(b as u32)).0,aspis_core::field::ct::reduce64((a as u64)*(b as u64)));
 }
}
