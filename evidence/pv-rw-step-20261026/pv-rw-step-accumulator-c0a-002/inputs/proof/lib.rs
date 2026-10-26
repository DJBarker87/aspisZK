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
