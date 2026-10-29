//! Finite memoized interpretation of one total pure function. Every new pair
//! gets an arbitrary output; repeat pairs get exactly the previous output.
//! No actual arithmetic callee or harness input is modified.
use aspis_core::field::QM31;
const CAP:usize=64;
static mut USED:usize=0;
static mut TAG:[u8;CAP]=[0;CAP];
static mut LEFT:[QM31;CAP]=[QM31::ZERO;CAP];
static mut RIGHT:[QM31;CAP]=[QM31::ZERO;CAP];
static mut OUTPUT:[QM31;CAP]=[QM31::ZERO;CAP];
pub fn mul(a:QM31,b:QM31)->QM31 {eval(0,a,b)}
pub fn square(a:QM31)->QM31 {eval(1,a,a)}
fn eval(tag:u8,a:QM31,b:QM31)->QM31 {unsafe {
 let mut i=0;while i<USED {if TAG[i]==tag && LEFT[i]==a && RIGHT[i]==b {return OUTPUT[i];}i+=1;}
 assert!(USED<CAP,"shared function table capacity");let r=super::equivalence16::q();
 TAG[USED]=tag;LEFT[USED]=a;RIGHT[USED]=b;OUTPUT[USED]=r;USED+=1;r
}}
/// Detect loss of any limb through the exact table key/output copy shape.
pub fn roundtrip16() {unsafe {let raw:[u32;4]=kani::any();let a=QM31{c0:aspis_core::field::CM31{a:aspis_core::field::M31(raw[0]),b:aspis_core::field::M31(raw[1])},c1:aspis_core::field::CM31{a:aspis_core::field::M31(raw[2]),b:aspis_core::field::M31(raw[3])}};
 USED=1;TAG[0]=0;LEFT[0]=QM31::ONE;RIGHT[0]=QM31::ZERO;OUTPUT[0]=a;
 let r=mul(QM31::ONE,QM31::ZERO);let words=[r.c0.a.0,r.c0.b.0,r.c1.a.0,r.c1.b.0];let k:usize=kani::any();kani::assume(k<4);assert_eq!(words[k],raw[k]);USED=0;
}}
