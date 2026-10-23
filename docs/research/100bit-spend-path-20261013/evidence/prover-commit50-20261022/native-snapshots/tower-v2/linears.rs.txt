
mod linear_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)]pub struct QM31(u32);
#[derive(Clone,Copy)]pub struct M31(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct Call(u8,u32,u32);
static mut ANSWERS:[u32;40]=[0;40];static mut CALLS:[Call;40]=[Call(0,0,0);40];static mut NEXT:usize=0;
fn reset(a:[u32;40]){unsafe{ANSWERS=a;CALLS=[Call(0,0,0);40];NEXT=0;}}
fn call(op:u8,a:QM31,b:QM31)->QM31{unsafe{let i=NEXT;assert!(i<40);NEXT+=1;CALLS[i]=Call(op,a.0,b.0);QM31(ANSWERS[i])}}
fn trace()->([Call;40],usize){unsafe{(CALLS,NEXT)}}
impl QM31{const ZERO:Self=QM31(0);fn square(self)->Self{call(0,self,Self::ZERO)}fn mul(self,b:Self)->Self{call(1,self,b)}fn add(self,b:Self)->Self{call(2,self,b)}fn mul_m31(self,b:M31)->Self{call(3,self,QM31(b.0))}}
mod field{pub use super::{QM31,M31};}
const STATE_ONLY_HIDING_SUMCHECK_ROUNDS:usize=10;
fn selected_mask_linears(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> (QM31, QM31) {
    let mut suffix = QM31::ZERO;
    let mut weighted = QM31::ZERO;
    for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {
        suffix = suffix.add(point[variable]);
        if variable != 0 {
            weighted = weighted.add(suffix);
        }
    }
    (
        suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
        suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))),
    )
}

fn mask_power_26(value: QM31) -> QM31 {
    let x2 = value.square();
    let x4 = x2.square();
    let x8 = x4.square();
    let x16 = x8.square();
    x16.mul(x8).mul(x2)
}

pub mod linear50 {
use super::field::{QM31 as K,M31};
pub fn go(point:[K;10],left:u8,suffix:K,weighted:K)->(K,K) {
 if left==0 {(suffix,weighted)} else {
  let n=left-1;let next=suffix.add(point[usize::from(n)]);
  let weighted=if n==0 {weighted} else {weighted.add(next)};
  go(point,n,next,weighted)
 }
}
pub fn eval(point:[K;10])->(K,K) {
 let (suffix,weighted)=go(point,10,K::ZERO,K::ZERO);
 (suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
  suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))))
}
pub fn power26(x:K)->K {
 let x2=x.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();
 x16.mul(x8).mul(x2)
}
}

#[cfg(kani)]mod proofs{use super::*;
 #[kani::proof] #[kani::unwind(44)]fn linears_power(){
 let raw:[u32;10]=kani::any();let p=raw.map(QM31);let answers=kani::any();
 reset(answers);let a=selected_mask_linears(&p);let ta=trace();
 reset(answers);let b=linear50::eval(p);let tb=trace();assert_eq!(a,b);assert_eq!(ta,tb);
 let x=QM31(kani::any());reset(answers);let a=mask_power_26(x);let ta=trace();
 reset(answers);let b=linear50::power26(x);let tb=trace();assert_eq!(a,b);assert_eq!(ta,tb);
 }
}
}
