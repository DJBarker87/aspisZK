from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent;S=Path('crates/aspis-core/src/field.rs');s=S.read_text();start=s.index('#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub struct PreparedQm31Multiplier');end=s.index('\n#[inline(always)]\nfn qm31_from_karatsuba',start);literal=s[start:end]
owner=(E/'dot-owner/lib.rs').read_text();owner=owner[owner.index('pub mod prepared50'):]
head='''
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
'''
tail='''
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
'''
(E/'native/prepared.rs').write_text(head+literal+'\n'+owner+tail)
p=E/'native/lib.rs';p.write_text(p.read_text()+'\ninclude!("prepared.rs");\n')
(E/'pins/prepared-native-spans.json').write_text(json.dumps(dict(source=str(S),sha256=hashlib.sha256(S.read_bytes()).hexdigest(),verbatim=literal,owner_sha256=hashlib.sha256((E/'dot-owner/lib.rs').read_bytes()).hexdigest(),abstractions='Paired universal M31 add/mul/sub answers; mul_by_r is a paired verified callee. Arbitrary full matrices and RHS. Exact complete output and arithmetic operation/operand sequence; all callee value laws separately proved.'),indent=2)+'\n')
