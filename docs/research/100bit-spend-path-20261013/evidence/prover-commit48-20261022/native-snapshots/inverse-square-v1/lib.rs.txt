#![allow(dead_code,unexpected_cfgs)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct M31(u32);
const EMPTY:(u8,u32,u32)=(0,0,0);
static mut ANSWERS:[u32;64]=[0;64];static mut TRACE:[(u8,u32,u32);64]=[EMPTY;64];static mut NEXT:usize=0;
fn reset(a:[u32;64]) {unsafe {ANSWERS=a;TRACE=[EMPTY;64];NEXT=0;}}
fn call(tag:u8,a:u32,b:u32)->M31 {unsafe {let n=NEXT;assert!(n<64);TRACE[n]=(tag,a,b);NEXT+=1;M31(ANSWERS[n])}}
fn trace()->([(u8,u32,u32);64],usize) {unsafe {(TRACE,NEXT)}}
impl M31 {fn mul(self,b:Self)->Self {call(1,self.0,b.0)}
    pub fn inv(self) -> M31 {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::FInv);
        assert!(self.0 != 0, "inverse of zero");

        // Build x^(2^k - 1) at k = 2, 4, 8, 16, 24, 28, 29.
        // The final exponent is 4*(2^29 - 1) + 1 = 2^31 - 3 = P - 2.
        // This takes 38 M31 multiplications instead of the generic binary
        // exponentiation's 61 for this fixed exponent.
        let t2 = self.mul(self).mul(self);
        let t4 = square_n(t2, 2).mul(t2);
        let t8 = square_n(t4, 4).mul(t4);
        let t16 = square_n(t8, 8).mul(t8);
        let t24 = square_n(t16, 8).mul(t8);
        let t28 = square_n(t24, 4).mul(t4);
        let t29 = t28.mul(t28).mul(self);
        let t30 = t29.mul(t29);
        t30.mul(t30).mul(self)
    }

}
// Separately bound pure square-helper contract, abstract at this caller.
fn square_n(value:M31,count:usize)->M31 {call(2,value.0,count as u32)}
fn owner_inverse(x:M31)->M31 {
 assert!(x.0!=0);
 let t2=x.mul(x).mul(x);
 let t4=square_n(t2,2).mul(t2);
 let t8=square_n(t4,4).mul(t4);
 let t16=square_n(t8,8).mul(t8);
 let t24=square_n(t16,8).mul(t8);
 let t28=square_n(t24,4).mul(t4);
 let t29=t28.mul(t28).mul(x);
 let t30=t29.mul(t29);
 t30.mul(t30).mul(x)
}
fn native_square_step(mut value:M31)->M31 {value=value.mul(value);value}
fn owner_square_step(value:M31)->M31 {value.mul(value)}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(66)] fn fixed_chain_context() {
  let x=M31(kani::any());kani::assume(x.0!=0);let answers=kani::any();
  reset(answers);let a=x.inv();let ta=trace();
  reset(answers);let b=owner_inverse(x);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);
 }
 #[kani::proof] #[kani::unwind(66)] fn square_transition() {
  let x=M31(kani::any());let answers=kani::any();
  reset(answers);let a=native_square_step(x);let ta=trace();
  reset(answers);let b=owner_square_step(x);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,1);
 }
}
