//! Cached multiplier constructor and multiplication; independent answer tapes.
use aspis_core::field::{M31,CM31 as C,QM31 as Q,PreparedQm31Multiplier,P};
use super::{reference_tower_field as r,tower_inverse_contracts as t};
fn current(a:[u32;4])->Q {Q{c0:C::new(M31(a[0]),M31(a[1])),c1:C::new(M31(a[2]),M31(a[3]))}}
fn old(a:[u32;4])->r::QM31 {r::QM31{c0:r::CM31::new(r::M31(a[0]),r::M31(a[1])),c1:r::CM31::new(r::M31(a[2]),r::M31(a[3]))}}
fn raw(a:Q)->[u32;4] {[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0]}
fn old_raw(a:r::QM31)->[u32;4] {[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0]}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(aspis_core::field::M31::add,t::madd)]
#[kani::stub(aspis_core::field::M31::sub,t::msub)]
#[kani::stub(aspis_core::field::M31::mul,t::mmul)]
#[kani::stub(aspis_core::field::CM31::add,t::cadd)]
#[kani::stub(aspis_core::field::CM31::sub,t::csub)]
fn cached_multiplier_trace() {
 let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();for x in a {kani::assume(x<P);}for x in b {kani::assume(x<P);}
 let prepare:[[u32;8];32]=kani::any();let multiply:[[u32;8];32]=kani::any();
 for row in prepare {for x in row {kani::assume(x<P);}}
 for row in multiply {for x in row {kani::assume(x<P);}}
 t::begin(prepare);let left=r::PreparedQm31Multiplier::new(old(a));let count=t::replay();assert_eq!(count,4);
 let right=PreparedQm31Multiplier::new(current(a));assert_eq!(unsafe{t::COUNT},count);
 t::begin(multiply);let expected=old_raw(left.mul(old(b)));let count=t::replay();assert_eq!(count,29);
 let actual=raw(right.mul(current(b)));assert_eq!(actual,expected);assert_eq!(unsafe{t::COUNT},count);
}

// Domain closure is separate from the retained complete trace-equality check.
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(aspis_core::field::M31::add,t::madd)]
#[kani::stub(aspis_core::field::M31::sub,t::msub)]
#[kani::stub(aspis_core::field::M31::mul,t::mmul)]
#[kani::stub(aspis_core::field::CM31::add,t::cadd)]
#[kani::stub(aspis_core::field::CM31::sub,t::csub)]
fn cached_multiplier_domain() {
 let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();for x in a {kani::assume(x<P);}for x in b {kani::assume(x<P);}
 let prepare:[[u32;8];32]=kani::any();let multiply:[[u32;8];32]=kani::any();
 for row in prepare {for x in row {kani::assume(x<P);}}
 for row in multiply {for x in row {kani::assume(x<P);}}
 t::begin(prepare);let right=PreparedQm31Multiplier::new(current(a));assert_eq!(unsafe{t::COUNT},4);
 t::begin(multiply);let output=raw(right.mul(current(b)));assert_eq!(unsafe{t::COUNT},29);
 for x in output {assert!(x<P);}
}
