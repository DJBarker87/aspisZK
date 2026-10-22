
mod eval_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub struct QM31(pub u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Call(u8,[u32;6]);
static mut ANSWERS:[u32;32]=[0;32];static mut CALLS:[Call;32]=[Call(0,[0;6]);32];static mut NEXT:usize=0;
fn reset(a:[u32;32]){unsafe{ANSWERS=a;CALLS=[Call(0,[0;6]);32];NEXT=0;}}
fn call(op:u8,a:[u32;6])->QM31{unsafe{let i=NEXT;assert!(i<32);NEXT+=1;CALLS[i]=Call(op,a);QM31(ANSWERS[i])}}
fn trace()->([Call;32],usize){unsafe{(CALLS,NEXT)}}
impl QM31{fn square(self)->Self{call(0,[self.0,0,0,0,0,0])} fn mul(self,b:Self)->Self{call(1,[self.0,b.0,0,0,0,0])} fn add(self,b:Self)->Self{call(2,[self.0,b.0,0,0,0,0])}}
struct PreparedQm31Multiplier(QM31);
impl PreparedQm31Multiplier{fn new(x:QM31)->Self{Self(call(3,[x.0,0,0,0,0,0]))} fn mul(&self,x:QM31)->QM31{call(4,[self.0.0,x.0,0,0,0,0])}}
type StateOnlySumcheckPolynomial=[QM31;28];
fn qm31_sum_products3(a:[QM31;3],b:[QM31;3])->QM31{call(5,[a[0].0,a[1].0,a[2].0,b[0].0,b[1].0,b[2].0])}
mod field{pub use super::QM31;}
mod run50{use super::*;pub fn run(a:[QM31;3],b:[QM31;3])->QM31{qm31_sum_products3(a,b)}}
mod prepared50{use super::*;pub fn prepare(x:QM31)->QM31{PreparedQm31Multiplier::new(x).0} pub fn mul(x:QM31,y:QM31)->QM31{PreparedQm31Multiplier(x).mul(y)}}
pub fn evaluate_state_only_polynomial(
    polynomial: &StateOnlySumcheckPolynomial,
    challenge: QM31,
) -> QM31 {
    let x2 = challenge.square();
    let x3 = challenge.mul(x2);
    let x4 = x2.square();
    let powers = [challenge, x2, x3];
    let prepared_x4 = PreparedQm31Multiplier::new(x4);
    let block_value = |block: usize| {
        let start = 4 * block;
        polynomial[start].add(qm31_sum_products3(
            powers,
            [
                polynomial[start + 1],
                polynomial[start + 2],
                polynomial[start + 3],
            ],
        ))
    };
    let mut accumulator = block_value(6);
    let mut block = 6usize;
    while block > 0 {
        block -= 1;
        accumulator = prepared_x4.mul(accumulator).add(block_value(block));
    }
    accumulator
}

pub mod eval50 {
use super::{field::{QM31 as K},run50,prepared50};
pub fn block(p:[K;28],powers:[K;3],j:usize)->K {
 let start=j.wrapping_mul(4);
 p[start].add(run50::run(powers,[p[start.wrapping_add(1)],p[start.wrapping_add(2)],p[start.wrapping_add(3)]]))
}
pub fn go(p:[K;28],powers:[K;3],prepared:K,left:u8,acc:K)->K {
 if left==0 {acc} else {
  let n=left-1;
  let product=prepared50::mul(prepared,acc);
  let value=block(p,powers,usize::from(n));
  go(p,powers,prepared,n,product.add(value))
 }
}
pub fn eval(p:[K;28],x:K)->K {
 let x2=x.square();let x3=x.mul(x2);let x4=x2.square();let powers=[x,x2,x3];
 let prepared=prepared50::prepare(x4);let acc=block(p,powers,6);
 go(p,powers,prepared,6,acc)
}
}

#[cfg(kani)] mod proofs{use super::*;
 #[kani::proof] #[kani::unwind(36)] fn evaluator(){
 let raw:[u32;28]=kani::any();let p=raw.map(QM31);let x=QM31(kani::any());let answers=kani::any();
 reset(answers);let a=evaluate_state_only_polynomial(&p,x);let ta=trace();
 reset(answers);let b=eval50::eval(p,x);let tb=trace();assert_eq!(a,b);assert_eq!(ta,tb);
 }
}
}
