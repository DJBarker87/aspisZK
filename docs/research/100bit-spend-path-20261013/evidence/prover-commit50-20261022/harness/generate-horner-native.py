from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent;owner=(E/'dot-owner/lib.rs').read_text();owner=owner[owner.index('pub mod mask_horner50'):].replace('[[M31;3];3]','K').replace('QM31 as K,M31','QM31 as K')
head='''
mod mask_horner_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)]pub struct QM31(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct Call(u8,u32,u32);
static mut ANSWERS:[u32;64]=[0;64];static mut CALLS:[Call;64]=[Call(0,0,0);64];static mut NEXT:usize=0;
fn reset(a:[u32;64]){unsafe{ANSWERS=a;CALLS=[Call(0,0,0);64];NEXT=0;}}
fn call(op:u8,a:QM31,b:QM31)->QM31{unsafe{let i=NEXT;assert!(i<64);NEXT+=1;CALLS[i]=Call(op,a.0,b.0);QM31(ANSWERS[i])}}
fn trace()->([Call;64],usize){unsafe{(CALLS,NEXT)}}
impl QM31{fn add(self,b:Self)->Self{call(2,self,b)}}
struct PreparedQm31Multiplier(QM31);
impl PreparedQm31Multiplier{fn new(x:QM31)->Self{Self(call(0,x,QM31(0)))}fn mul(&self,x:QM31)->QM31{call(1,self.0,x)}}
mod field{pub use super::QM31;}
mod prepared50{use super::*;pub fn prepare(x:QM31)->QM31{PreparedQm31Multiplier::new(x).0}pub fn mul(x:QM31,y:QM31)->QM31{PreparedQm31Multiplier(x).mul(y)}}
fn native(coefficients:&[QM31;27],linear:QM31)->QM31{
 let prepared_linear=PreparedQm31Multiplier::new(linear);
 let mut shared=coefficients[26];
 for exponent in (0..26).rev(){shared=prepared_linear.mul(shared).add(coefficients[exponent]);}
 shared
}
'''
tail='''
#[cfg(kani)]mod proofs{use super::*;
 #[kani::proof]#[kani::unwind(68)]fn horner(){
 let raw:[u32;27]=kani::any();let q=raw.map(QM31);let x=QM31(kani::any());let answers=kani::any();
 reset(answers);let a=native(&q,x);let ta=trace();reset(answers);let b=mask_horner50::eval(q,x);let tb=trace();
 assert_eq!(a,b);assert_eq!(ta,tb);
 }
}
}
'''
(E/'native/mask-horner.rs').write_text(head+owner+tail);p=E/'native/lib.rs';p.write_text(p.read_text()+'\ninclude!("mask-horner.rs");\n')
p=Path('crates/aspis-core/src/state_only_hiding.rs');(E/'pins/mask-horner-native-spans.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=[665,672],abstractions='Complete prepared-constructor/Horner caller on arbitrary 27-coefficient context. Prepared matrix is an opaque handle through separately verified constructor/mul interfaces; universal paired answers and complete arithmetic operands/order. Coefficient producer provenance remains separate.'),indent=2)+'\n')
