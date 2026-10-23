//! Actual generic M31 inverse: zero guard and fixed 61-product source trace.
use aspis_core::{field::{M31,P},r0::CodeField};
use super::reference_field as r;
static mut REPLAY:bool=false;
static mut COUNT:usize=0;
static mut INPUTS:[[u32;2];64]=[[0;2];64];
static mut ANSWERS:[u32;64]=[0;64];
fn multiplication(a:u32,b:u32)->u32 {
    let i=unsafe{COUNT};assert!(i<64);
    if unsafe{REPLAY} {assert_eq!(unsafe{INPUTS[i]},[a,b]);} else {unsafe{INPUTS[i]=[a,b];}}
    unsafe{COUNT=i+1;ANSWERS[i]}
}
fn current_mul(a:M31,b:M31)->M31 {M31(multiplication(a.0,b.0))}
fn old_mul(a:r::M31,b:r::M31)->r::M31 {r::M31(multiplication(a.0,b.0))}
#[kani::proof]
#[kani::unwind(80)]
#[kani::stub(aspis_core::field::M31::mul,current_mul)]
#[kani::stub(r::M31::mul,old_mul)]
fn generic_inverse_guard_and_chain() {
    let x:u32=kani::any();kani::assume(x<P);
    let answers:[u32;64]=kani::any();for v in answers {kani::assume(v<P);}
    unsafe{COUNT=0;REPLAY=false;ANSWERS=answers;}
    let expected=if x==0 {None} else {Some(r::M31(x).pow(u64::from(P-2)).0)};
    let calls=unsafe{COUNT};assert_eq!(calls,if x==0 {0} else {61});
    unsafe{COUNT=0;REPLAY=true;}
    let actual=<M31 as CodeField>::try_inv(M31(x)).map(|v|v.0);
    assert_eq!(actual,expected);assert_eq!(unsafe{COUNT},calls);
}
