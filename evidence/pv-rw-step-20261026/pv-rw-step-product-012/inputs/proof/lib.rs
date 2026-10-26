pub mod generated;
#[cfg(kani)]
mod checks {
 use super::generated::*;
 use aspis_core::field::{M31,CM31,QM31};
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 #[kani::proof]
 #[kani::unwind(2)]
 fn compression_state_step() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  let a=shipped_step(out,power,&value,lambda);let b=reference_step(out,power,value,lambda);
  assert_eq!(a.0.c0.a.0,b.0.c0.a.0);assert_eq!(a.0.c0.b.0,b.0.c0.b.0);
  assert_eq!(a.0.c1.a.0,b.0.c1.a.0);assert_eq!(a.0.c1.b.0,b.0.c1.b.0);
  assert_eq!(a.1.c0.a.0,b.1.c0.a.0);assert_eq!(a.1.c0.b.0,b.1.c0.b.0);
  assert_eq!(a.1.c1.a.0,b.1.c1.a.0);assert_eq!(a.1.c1.b.0,b.1.c1.b.0);
 }
}
#[cfg(kani)]
mod leaves {
 use super::generated::*;
 use aspis_core::field::{M31,CM31,QM31};
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 #[kani::proof] #[kani::unwind(2)]
 fn compression_accumulator_c0a() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  let a=shipped_step(out,power,&value,lambda).0.c0.a.0;
  let b=out.c0.a.add(power.c0.a.mul(value)).0;
  assert_eq!(a,b);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_accumulator_c0b() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).0.c0.b.0,out.c0.b.add(power.c0.b.mul(value)).0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_accumulator_c1a() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).0.c1.a.0,out.c1.a.add(power.c1.a.mul(value)).0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_accumulator_c1b() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).0.c1.b.0,out.c1.b.add(power.c1.b.mul(value)).0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_power_c0a() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).1.c0.a.0,power.mul(lambda).c0.a.0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_power_c0b() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).1.c0.b.0,power.mul(lambda).c0.b.0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_power_c1a() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).1.c1.a.0,power.mul(lambda).c1.a.0);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_power_c1b() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  assert_eq!(shipped_step(out,power,&value,lambda).1.c1.b.0,power.mul(lambda).c1.b.0);
 }
 // Iterator control is checked independently of the separately checked arithmetic.
 #[kani::proof] #[kani::unwind(18)]
 fn compression_iterator16_next() {
  let raw:[u32;16]=kani::any();let consumed:usize=kani::any();kani::assume(consumed<=16);
  let mut iterator=raw.iter();let mut i=0;
  while i<consumed {assert_eq!(iterator.next(),Some(&raw[i]));i+=1;}
  if consumed<16 {assert_eq!(iterator.next(),Some(&raw[consumed]));}
  else {assert_eq!(iterator.next(),None);}
 }
}
pub mod sampler_step;
#[cfg(kani)]
mod primitive_split {
 use aspis_core::field::{M31,CM31,QM31};
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 #[kani::proof] #[kani::unwind(2)]
 fn scale_c0a() {let p=q();let v=M31(kani::any());assert_eq!(p.mul_m31(v).c0.a.0,p.c0.a.mul(v).0);}
 #[kani::proof] #[kani::unwind(2)]
 fn add_c0a() {let p=q();let v=q();assert_eq!(p.add(v).c0.a.0,p.c0.a.add(v.c0.a).0);}
}
#[cfg(kani)]
mod scalar_split {
 use aspis_core::field::{M31,ct};
 #[kani::proof] #[kani::unwind(2)]
 fn scalar_mul_wrapper() {
  let a:u32=kani::any();let b:u32=kani::any();
  assert_eq!(M31(a).mul(M31(b)).0,ct::reduce64(u64::from(a)*u64::from(b)));
 }
 #[kani::proof] #[kani::unwind(2)]
 fn reduce64_wrapper() {
  let a:u64=kani::any();assert_eq!(M31::reduce_u64(a).0,ct::reduce64(a));
 }
}
#[cfg(kani)]
mod actual_shape {
 use aspis_core::field::{M31,CM31,QM31};
 #[kani::proof] #[kani::unwind(18)]
 fn compression_m31_suffix_next() {
  let raw:[u32;16]=kani::any();
  let values=[M31(raw[0]),M31(raw[1]),M31(raw[2]),M31(raw[3]),M31(raw[4]),M31(raw[5]),M31(raw[6]),M31(raw[7]),M31(raw[8]),M31(raw[9]),M31(raw[10]),M31(raw[11]),M31(raw[12]),M31(raw[13]),M31(raw[14]),M31(raw[15])];
  let i:usize=kani::any();kani::assume(i<=16);
  let mut iter=values[i..].iter();
  if i<16 {assert_eq!(iter.next().map(|m|m.0),Some(raw[i]));assert_eq!(iter.as_slice().len(),15-i);}
  else {assert_eq!(iter.next(),None);assert!(iter.as_slice().is_empty());}
 }
 #[kani::proof] #[kani::unwind(2)]
 fn compression_initial_state() {
  let tag:u32=kani::any();let compressed=QM31::from_cm31(CM31::from_m31(M31(tag)));
  assert_eq!(compressed.c0.a.0,tag);assert_eq!(compressed.c0.b.0,0);
  assert_eq!(compressed.c1.a.0,0);assert_eq!(compressed.c1.b.0,0);
 }
}
#[inline(always)]
pub fn scalar_product_owned(a:u32,b:u32)->u64 {a as u64 * b as u64}
#[inline(always)]
pub fn scalar_mul_owned(a:u32,b:u32)->u32 {aspis_core::field::ct::reduce64(scalar_product_owned(a,b))}
#[cfg(kani)]
mod scalar_product_split {
 #[kani::proof] #[kani::unwind(2)]
 fn scalar_product_casts() {
  let a:u32=kani::any();let b:u32=kani::any();
  assert_eq!(u64::from(a)*u64::from(b),super::scalar_product_owned(a,b));
 }
 #[kani::proof] #[kani::unwind(2)]
 fn scalar_mul_literal_body() {
  let a:u32=kani::any();let b:u32=kani::any();
  assert_eq!(aspis_core::field::M31(a).mul(aspis_core::field::M31(b)).0,super::scalar_mul_owned(a,b));
 }
}
