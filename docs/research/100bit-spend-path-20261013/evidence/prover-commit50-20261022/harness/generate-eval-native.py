from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent.parent;S=Path('crates/aspis-core/src/state_only_sumcheck.rs');s=S.read_text();a=s.index('pub fn evaluate_state_only_polynomial(\n');b=s.index('\n#[cfg(test)]',a);literal=s[a:b]
owner=(E/'dot-owner/lib.rs').read_text();owner=owner[owner.index('pub mod eval50'):].replace('[[M31;3];3]','K').replace('QM31 as K,M31','QM31 as K')
head='''
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
'''
tail='''
#[cfg(kani)] mod proofs{use super::*;
 #[kani::proof] #[kani::unwind(36)] fn evaluator(){
 let raw:[u32;28]=kani::any();let p=raw.map(QM31);let x=QM31(kani::any());let answers=kani::any();
 reset(answers);let a=evaluate_state_only_polynomial(&p,x);let ta=trace();
 reset(answers);let b=eval50::eval(p,x);let tb=trace();assert_eq!(a,b);assert_eq!(ta,tb);
 }
}
}
'''
(E/'native/eval.rs').write_text(head+literal+'\n'+owner+tail);p=E/'native/lib.rs';p.write_text(p.read_text()+'\ninclude!("eval.rs");\n')
(E/'pins/eval-native-spans.json').write_text(json.dumps(dict(source=str(S),sha256=hashlib.sha256(S.read_bytes()).hexdigest(),verbatim=literal,owner_sha256=hashlib.sha256((E/'dot-owner/lib.rs').read_bytes()).hexdigest(),abstractions='Complete seven-block caller with paired universal QM31 square/mul/add, sum-products3 and prepared constructor/mul callees. Exact call operands and order; prepared object represented by an opaque scalar handle, since only its separately verified constructor/mul interface is observed. Source p reference versus owned by-value array, and usize versus bounded u8 loop. Both have full 28-input context. No field or model value law inferred from stubs.'),indent=2)+'\n')
