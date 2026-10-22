from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;p=Path('crates/aspis-core/src/field.rs');s=p.read_text()
a=s.index('    pub fn inv(self) -> M31 {');b=s.index('\n    #[inline(always)]\n    pub fn is_zero',a)
method=s[a:b]
text='''#![allow(dead_code,unexpected_cfgs)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct M31(u32);
const EMPTY:(u8,u32,u32)=(0,0,0);
static mut ANSWERS:[u32;64]=[0;64];static mut TRACE:[(u8,u32,u32);64]=[EMPTY;64];static mut NEXT:usize=0;
fn reset(a:[u32;64]) {unsafe {ANSWERS=a;TRACE=[EMPTY;64];NEXT=0;}}
fn call(tag:u8,a:u32,b:u32)->M31 {unsafe {let n=NEXT;assert!(n<64);TRACE[n]=(tag,a,b);NEXT+=1;M31(ANSWERS[n])}}
fn trace()->([(u8,u32,u32);64],usize) {unsafe {(TRACE,NEXT)}}
impl M31 {fn mul(self,b:Self)->Self {call(1,self.0,b.0)}
'''+method+'''
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
'''
(H/'lib.rs').write_text(text)
(H/'source-spans.json').write_text(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),method_sha256=hashlib.sha256(method.encode()).hexdigest(),square_body='value = value.mul(value);',generated_sha256=hashlib.sha256(text.encode()).hexdigest(),owner='Exact fixed-chain port corresponding to retained S7JoinInverseExecution; raw-zero assertion retained. Square-helper caller is abstract, and its iteration is independently checked.'),indent=2)+'\n')
