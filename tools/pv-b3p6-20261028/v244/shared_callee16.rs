//! Finite memoized interpretation of one total pure function. Every new pair
//! gets an arbitrary output; repeat pairs get exactly the previous output.
//! No actual arithmetic callee or harness input is modified.
use aspis_core::field::QM31;
const CAP:usize=64;
static mut USED:usize=0;
static mut LEFT:[QM31;CAP]=[QM31::ZERO;CAP];
static mut RIGHT:[QM31;CAP]=[QM31::ZERO;CAP];
static mut OUTPUT:[QM31;CAP]=[QM31::ZERO;CAP];
pub fn mul(a:QM31,b:QM31)->QM31 {unsafe {
 let mut i=0;while i<USED {if LEFT[i]==a && RIGHT[i]==b {return OUTPUT[i];}i+=1;}
 assert!(USED<CAP,"shared function table capacity");let r=super::equivalence16::q();
 LEFT[USED]=a;RIGHT[USED]=b;OUTPUT[USED]=r;USED+=1;r
}}
