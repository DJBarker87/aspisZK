//! Safe reference and native comparison only; no production source edits.
use aspis_core::field::{M31,CM31,QM31};
#[path = "../../../../crates/aspis-r1-cost-probe/src/ct_pole.rs"]
mod shipped_pole;
pub fn all_slots_clear(values: &[[[QM31;2];2]], masks: &[u16;64], chi: QM31) -> bool {
    let mut clear = true;
    let mut row = 0usize;
    while row < values.len() {
        let active = masks[row >> 4] & (1u16 << (row & 15)) != 0;
        clear = clear & !(active & shipped_pole::equal(chi, values[row][0][0]));
        clear = clear & !(active & shipped_pole::equal(chi, values[row][0][1]));
        clear = clear & !(active & shipped_pole::equal(chi, values[row][1][0]));
        clear = clear & !(active & shipped_pole::equal(chi, values[row][1][1]));
        row += 1;
    }
    clear
}

#[cfg(kani)]
mod checks {
 use super::*;
 fn q(x:[u32;4])->QM31 {QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
 #[kani::proof]
 #[kani::unwind(1026)]
 fn pole_full_domain() {
  let raw:[[[[u32;4];2];2];1024]=kani::any();
  let mut values=[[[QM31::ZERO;2];2];1024];
  let mut i=0usize;
  while i<1024 {values[i]=[[q(raw[i][0][0]),q(raw[i][0][1])],[q(raw[i][1][0]),q(raw[i][1][1])]];i+=1;}
  let masks:[u16;64]=kani::any();let chi=q(kani::any());
  let len:usize=kani::any();kani::assume(len<=1024);
  let actual=shipped_pole::all_slots_clear(&values[..len],&masks,chi);
  let reference=all_slots_clear(&values[..len],&masks,chi);
  assert_eq!(actual,reference);
 }
}

pub fn compression_step(out:QM31,power:QM31,value:M31,lambda:QM31)->(QM31,QM31) {
 (out.add(power.mul_m31(value)), power.mul(lambda))
}
pub fn compression_single_state(tag:M31,value:M31,lambda:QM31)->QM31 {
 let out=QM31::from_cm31(CM31::from_m31(tag));
 compression_step(out,lambda,value,lambda).0
}
#[cfg(kani)]
mod compression_checks {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn compression_one_wordlevel() {
  let raw:[u32;6]=kani::any();let tag=M31(raw[0]);let value=M31(raw[1]);
  let lambda=QM31{c0:CM31{a:M31(raw[2]),b:M31(raw[3])},c1:CM31{a:M31(raw[4]),b:M31(raw[5])}};
  let a=aspis_statement::logup::compress_tagged_tuple(tag,&[value],lambda);
  let b=compression_single_state(tag,value,lambda);
  assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);
  assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
 }
}

#[cfg(kani)]
mod fixed_pole_checks {
 use super::*;
 fn any_q()->QM31 {let x:[u32;4]=kani::any();QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
 #[kani::proof]
 #[kani::unwind(1026)]
 fn pole_exact1024() {
  let mut values=[[[QM31::ZERO;2];2];1024];
  let mut i=0usize;
  while i<1024 {values[i]=[[any_q(),any_q()],[any_q(),any_q()]];i+=1;}
  let masks:[u16;64]=kani::any();let chi=any_q();
  assert_eq!(shipped_pole::all_slots_clear(&values,&masks,chi),all_slots_clear(&values,&masks,chi));
 }
}

// Owned array arguments avoid the native closure's captured array borrow.
pub fn polynomial_block(polynomial:[QM31;28],powers:[QM31;3],block:usize)->QM31 {
 let start=4*block;
 polynomial[start].add(aspis_core::field::qm31_sum_products3(powers,[polynomial[start+1],polynomial[start+2],polynomial[start+3]]))
}
pub fn polynomial_owned(polynomial:[QM31;28],challenge:QM31)->QM31 {
 let x2=challenge.square();let x3=challenge.mul(x2);let x4=x2.square();
 let powers=[challenge,x2,x3];let prepared=aspis_core::field::PreparedQm31Multiplier::new(x4);
 let mut accumulator=polynomial_block(polynomial,powers,6);let mut block=6usize;
 while block>0 {block-=1;accumulator=prepared.mul(accumulator).add(polynomial_block(polynomial,powers,block));}
 accumulator
}

#[cfg(kani)]
mod pole_small_checks {
 use super::*;
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 #[kani::proof]
 #[kani::unwind(1030)]
 fn pole_prefix16() {
  let mut values=[[[QM31::ZERO;2];2];16];let mut i=0usize;
  while i<16 {values[i]=[[q(),q()],[q(),q()]];i+=1;}
  let masks:[u16;64]=kani::any();let chi=q();
  let n:usize=kani::any();kani::assume(n<=16);
  assert_eq!(shipped_pole::all_slots_clear(&values[..n],&masks,chi),all_slots_clear(&values[..n],&masks,chi));
 }
}

#[cfg(kani)]
mod polynomial_checks {
 use super::*;
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 #[kani::proof]
 #[kani::unwind(512)]
 fn polynomial_full() {
  let mut p=[QM31::ZERO;28];let mut i=0usize;
  while i<28 {p[i]=q();i+=1;}
  let chi=q();
  let a=aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(&p,chi);
  let b=polynomial_owned(p,chi);
  assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);
  assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);
 }
}

#[path = "../../../../crates/aspis-r1-cost-probe/src/sampler.rs"]
mod shipped_sampler;
pub mod sampler_owned;
#[cfg(kani)]
mod ordinary_checks {
 #[kani::proof]
 #[kani::unwind(10)]
 fn ordinary_all_blocks() {
  let bytes:[u8;32]=kani::any();
  let a=super::shipped_sampler::ordinary_sample(&bytes);
  let b=super::sampler_owned::ordinary_sample(&bytes);
  assert_eq!(a.c0().c0.a.0,b.c0().c0.a.0);assert_eq!(a.c0().c0.b.0,b.c0().c0.b.0);
  assert_eq!(a.c0().c1.a.0,b.c0().c1.a.0);assert_eq!(a.c0().c1.b.0,b.c0().c1.b.0);
  assert_eq!(a.c1().c0.a.0,b.c1().c0.a.0);assert_eq!(a.c1().c0.b.0,b.c1().c0.b.0);
  assert_eq!(a.c1().c1.a.0,b.c1().c1.a.0);assert_eq!(a.c1().c1.b.0,b.c1().c1.b.0);
 }
}

#[cfg(kani)]
mod division_pass_checks {
 #[kani::proof]
 #[kani::unwind(40)]
 fn division_pass_all_ranks() {
  let rank:[u32;8]=kani::any();
  let a=super::sampler_owned::iterator_div_pass(rank);
  let b=super::sampler_owned::qm31_div_pass(rank);
  let mut i=0usize;
  while i<8 {assert_eq!(a.0[i],b.0[i]);i+=1;}
  assert_eq!(a.1,b.1);
 }
}
