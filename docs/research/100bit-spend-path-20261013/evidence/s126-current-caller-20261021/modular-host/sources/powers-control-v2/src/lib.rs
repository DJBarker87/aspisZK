#![allow(dead_code,static_mut_refs)]
use aspis_core::field::WideExact as E;
pub fn powers<const N:usize>(x:E)->[E;N] { let mut p=E::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
pub fn candidate_powers<const N:usize>(x:E)->[E;N]{
 let mut out=[E::ZERO;N];
 let mut p=E::ONE;
 let mut i=0usize;
 while i<N {
  out[i]=p;
  i+=1;
  if i==N { return out; }
  p=p.mul(x);
 }
 out
}
#[cfg(kani)] mod proofs {
use super::*;
static mut TABLE:[E;29]=[E::ZERO;29];
static mut X:E=E::ZERO;
static mut COUNT:usize=0;
// This stream overapproximates any total pure concrete multiplication. The
// original's final unused multiply is allowed; purity/totality must be supplied
// by the independently checked actual arithmetic before declaring equivalence.
pub fn stream_mul(left:E,right:E)->E {
 let i=unsafe{COUNT};assert!(i<29);
 assert!(right==unsafe{X});
 assert!(left==if i==0 {E::ONE}else{unsafe{TABLE[i-1]}});
 unsafe{COUNT=i+1;TABLE[i]}
}
fn certificate<const N:usize>() {
 let table:[[u32;8];29]=kani::any();let input:[u32;8]=kani::any();
 // Full actual enum-free field carriers; every u32 pattern is a valid Rust
 // value. Arithmetic invariants are intentionally not assumed by this control
 // certificate and are not established by this transmute.
 let table:[E;29]=unsafe{std::mem::transmute(table)};let x:E=unsafe{std::mem::transmute(input)};
 unsafe{TABLE=table;X=x;COUNT=0;}
 let original=powers::<N>(x);assert_eq!(unsafe{COUNT},N);
 unsafe{COUNT=0;}
 let candidate=candidate_powers::<N>(x);assert_eq!(unsafe{COUNT},N.saturating_sub(1));
 assert!(original==candidate);
 kani::cover!(input[0]==0,"zero leading limb reaches comparison");kani::cover!(input[0]==u32::MAX,"maximum leading limb reaches comparison");
}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,stream_mul)]
fn powers7_control(){certificate::<7>();}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,stream_mul)]
fn powers29_control(){certificate::<29>();}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,stream_mul)]
fn powers0_control(){certificate::<0>();}
}
