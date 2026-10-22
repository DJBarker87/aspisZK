
mod prepared_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub struct M31(pub u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub struct CM31{pub a:M31,pub b:M31}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub struct QM31{pub c0:CM31,pub c1:CM31}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Call(u8,u32,u32);
static mut ANSWERS:[u32;48]=[0;48];static mut CALLS:[Call;48]=[Call(0,0,0);48];static mut NEXT:usize=0;
fn reset(a:[u32;48]){unsafe{ANSWERS=a;CALLS=[Call(0,0,0);48];NEXT=0;}}
fn call(op:u8,a:M31,b:M31)->M31{unsafe{let i=NEXT;assert!(i<48);NEXT+=1;CALLS[i]=Call(op,a.0,b.0);M31(ANSWERS[i])}}
fn trace()->([Call;48],usize){unsafe{(CALLS,NEXT)}}
impl M31{fn add(self,b:Self)->Self{call(1,self,b)} fn mul(self,b:Self)->Self{call(2,self,b)} fn sub(self,b:Self)->Self{call(3,self,b)}}
impl CM31{fn add(self,b:Self)->Self{Self{a:self.a.add(b.a),b:self.b.add(b.b)}} fn sub(self,b:Self)->Self{Self{a:self.a.sub(b.a),b:self.b.sub(b.b)}}}
fn mul_by_r(x:CM31)->CM31{CM31{a:call(4,x.a,x.b),b:call(5,x.a,x.b)}}
mod field{pub use super::{M31,CM31,QM31};}
mod dot50{use super::*;pub fn prepare_c(x:CM31)->[M31;3]{[x.a,x.b,x.a.add(x.b)]}}
mod reconstruction{use super::*;pub fn mul_r(x:CM31)->CM31{super::mul_by_r(x)}}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PreparedQm31Multiplier {
    components: [[M31; 3]; 3],
}

impl PreparedQm31Multiplier {
    #[inline(always)]
    pub fn new(value: QM31) -> Self {
        let prepare = |component: CM31| [component.a, component.b, component.a.add(component.b)];
        Self {
            components: [
                prepare(value.c0),
                prepare(value.c1),
                prepare(value.c0.add(value.c1)),
            ],
        }
    }

    #[inline(always)]
    pub fn mul(self, rhs: QM31) -> QM31 {
        let multiply = |left: [M31; 3], right: CM31| {
            let m0 = left[0].mul(right.a);
            let m1 = left[1].mul(right.b);
            let m2 = left[2].mul(right.a.add(right.b));
            CM31 {
                a: m0.sub(m1),
                b: m2.sub(m0).sub(m1),
            }
        };
        let m0 = multiply(self.components[0], rhs.c0);
        let m1 = multiply(self.components[1], rhs.c1);
        let m2 = multiply(self.components[2], rhs.c0.add(rhs.c1));
        QM31 {
            c0: m0.add(mul_by_r(m1)),
            c1: m2.sub(m0).sub(m1),
        }
    }
}

pub mod prepared50 {
use super::field::{M31,CM31 as C,QM31 as K};
pub fn prepare(x:K)->[[M31;3];3] {
 let a=super::dot50::prepare_c(x.c0);
 let b=super::dot50::prepare_c(x.c1);
 let c=super::dot50::prepare_c(x.c0.add(x.c1));
 [a,b,c]
}
pub fn cm(left:[M31;3],right:C)->C {
 let m0=left[0].mul(right.a);let m1=left[1].mul(right.b);
 let m2=left[2].mul(right.a.add(right.b));
 C{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
pub fn combine(m0:C,m1:C,m2:C)->K {
 K{c0:m0.add(super::reconstruction::mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
pub fn mul(left:[[M31;3];3],right:K)->K {
 let m0=cm(left[0],right.c0);let m1=cm(left[1],right.c1);
 let m2=cm(left[2],right.c0.add(right.c1));
 combine(m0,m1,m2)
}
}

#[cfg(kani)] mod proofs{
 use super::*;
 #[kani::proof] #[kani::unwind(52)] fn prepared(){
  let raw:[[u32;2];2]=kani::any();let x=QM31{c0:CM31{a:M31(raw[0][0]),b:M31(raw[0][1])},c1:CM31{a:M31(raw[1][0]),b:M31(raw[1][1])}};
  let answers:[u32;48]=kani::any();reset(answers);let a=PreparedQm31Multiplier::new(x);let ta=trace();
  reset(answers);let b=prepared50::prepare(x);let tb=trace();assert_eq!(a.components,b);assert_eq!(ta,tb);
  let raw:[[u32;3];3]=kani::any();let row=raw.map(|r|r.map(M31));
  reset(answers);let a=PreparedQm31Multiplier{components:row}.mul(x);let ta=trace();
  reset(answers);let b=prepared50::mul(row,x);let tb=trace();assert_eq!(a,b);assert_eq!(ta,tb);
 }
}
}
