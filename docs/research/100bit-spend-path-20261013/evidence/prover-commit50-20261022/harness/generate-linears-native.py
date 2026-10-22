from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent;S=Path('crates/aspis-core/src/state_only_hiding.rs');s=S.read_text();a=s.index('fn selected_mask_linears(');b=s.index('\nfn mask_power(',a);linear=s[a:b];a=s.index('fn mask_power_26(');b=s.index('\nfn explicit_mask_factor',a);power=s[a:b]
owner=(E/'dot-owner/lib.rs').read_text();owner=owner[owner.index('pub mod linear50'):]
head='''
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
'''
tail='''
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
'''
(E/'native/linears.rs').write_text(head+linear+'\n'+power+'\n'+owner+tail);p=E/'native/lib.rs';p.write_text(p.read_text()+'\ninclude!("linears.rs");\n')
(E/'pins/linears-native-spans.json').write_text(json.dumps(dict(source=str(S),sha256=hashlib.sha256(S.read_bytes()).hexdigest(),verbatim_linear=linear,verbatim_power26=power,owner_sha256=hashlib.sha256((E/'dot-owner/lib.rs').read_bytes()).hexdigest(),abstractions='Full native reverse sufficient-statistic loop and scalar-combination caller, plus complete 26-power chain. Paired universal QM31 add/mul/square/mul_m31 answers, exact operation/operand order. Arithmetic value laws are separate Lean theorems.'),indent=2)+'\n')
