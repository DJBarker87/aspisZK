//! Bounded public-exponent call-trace contract over checked QM31 kernels.
use aspis_core::field::{QM31 as Q,CM31,M31,P};
use super::reference_field as r;
static mut REPLAY:bool=false;
static mut COUNT:usize=0;
static mut INPUTS:[[u32;9];16]=[[0;9];16];
static mut ANSWERS:[[u32;4];16]=[[0;4];16];
fn raw(q:Q)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn old(q:r::QM31)->[u32;4] {[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn current(v:[u32;4])->Q {Q{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))}}
fn prior(v:[u32;4])->r::QM31 {r::QM31{c0:r::CM31::new(r::M31(v[0]),r::M31(v[1])),c1:r::CM31::new(r::M31(v[2]),r::M31(v[3]))}}
fn operation(tag:u32,a:[u32;4],b:[u32;4])->[u32;4] {
    let i=unsafe{COUNT};assert!(i<16);
    let call=[tag,a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]];
    if unsafe{REPLAY} {assert_eq!(unsafe{INPUTS[i]},call);} else {unsafe{INPUTS[i]=call;}}
    unsafe{COUNT=i+1;ANSWERS[i]}
}
fn c_mul(a:Q,b:Q)->Q {current(operation(1,raw(a),raw(b)))}
fn r_mul(a:r::QM31,b:r::QM31)->r::QM31 {prior(operation(1,old(a),old(b)))}
fn c_square(a:Q)->Q {current(operation(2,raw(a),[0;4]))}
fn r_square(a:r::QM31)->r::QM31 {prior(operation(2,old(a),[0;4]))}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(aspis_core::field::QM31::mul,c_mul)]
#[kani::stub(r::QM31::mul,r_mul)]
#[kani::stub(aspis_core::field::QM31::square,c_square)]
#[kani::stub(r::QM31::square,r_square)]
fn all_selected_exponents() {
    let x:[u32;4]=kani::any();for v in x {kani::assume(v<P);}
    let answers:[[u32;4];16]=kani::any();for q in answers {for v in q {kani::assume(v<P);}}
    unsafe{ANSWERS=answers;}
    let mut visited=0;
    // Exhaust the tiny public domain; all bases and oracle answers remain symbolic.
    for exponent in 0u64..28 {
        unsafe{COUNT=0;REPLAY=false;}
        let expected=prior(x).pow(exponent);let calls=unsafe{COUNT};assert!(calls<=10);
        unsafe{COUNT=0;REPLAY=true;}
        let actual=current(x).pow(exponent);
        assert_eq!(raw(actual),old(expected));assert_eq!(unsafe{COUNT},calls);
        visited+=1;
    }
    assert_eq!(visited,28);
}
