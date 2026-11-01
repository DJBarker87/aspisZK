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
