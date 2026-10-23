//! Parametric fixed-chain equivalence; base multiplication has retained CT gates.
use aspis_core::field::{M31,P};
use super::reference_field;
static mut REPLAY:bool=false;
static mut COUNT:usize=0;
static mut INPUTS:[[u32;2];64]=[[0;2];64];
static mut ANSWERS:[u32;64]=[0;64];
fn multiplication(a:u32,b:u32)->u32 {
    let i=unsafe{COUNT};assert!(i<64);
    if unsafe{REPLAY} {assert_eq!(unsafe{INPUTS[i]},[a,b]);}
    else {unsafe{INPUTS[i]=[a,b];}}
    unsafe{COUNT=i+1;ANSWERS[i]}
}
fn actual_mul(a:M31,b:M31)->M31 {M31(multiplication(a.0,b.0))}
fn reference_mul(a:reference_field::M31,b:reference_field::M31)->reference_field::M31 {
    reference_field::M31(multiplication(a.0,b.0))
}
#[kani::proof]
#[kani::unwind(80)]
#[kani::stub(aspis_core::field::M31::mul,actual_mul)]
#[kani::stub(reference_field::M31::mul,reference_mul)]
fn same_fixed_chain() {
    let x:u32=kani::any();kani::assume(x>0 && x<P);
    let answers:[u32;64]=kani::any();for v in answers {kani::assume(v<P);}
    unsafe{COUNT=0;REPLAY=false;ANSWERS=answers;}
    let expected=reference_field::M31(x).inv();
    let calls=unsafe{COUNT};assert_eq!(calls,38);
    unsafe{COUNT=0;REPLAY=true;}
    let actual=M31(x).inv();
    assert_eq!(actual.0,expected.0);assert_eq!(unsafe{COUNT},calls);
}
