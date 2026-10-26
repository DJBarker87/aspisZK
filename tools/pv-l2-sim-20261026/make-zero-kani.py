"""Bind exact adopted-candidate zero predicates and canonical decoders.

No arithmetic/inversion stub is provided: these harnesses ONLY check the
listed complete predicates/decoders. Native inversion callers stay open.
"""
from pathlib import Path
import subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
rev='351c5c7f6b6ac0110459192ef1c55e25a6c80c67'
bindings=[]
def source(path):return subprocess.check_output(['git','show',f'{rev}:{path}'],text=True)
def item(path,marker,last=False):
 s=source(path);a=s.rindex(marker) if last else s.index(marker)
 if s[a:].startswith('pub struct M31('):out=s[a:s.index(';',a)+1]
 else:
  b=s.index('{',a);depth=1;i=b+1
  while depth:
   depth+=(s[i]=='{')-(s[i]=='}');i+=1
  out=s[a:i]
 bindings.append(dict(revision=rev,path=path,line=s[:a].count('\n')+1,
  item=marker,source_sha256=hashlib.sha256(s.encode()).hexdigest(),
  item_sha256=hashlib.sha256(out.encode()).hexdigest()))
 return out+'\n'
F='crates/aspis-core/src/field.rs';W='crates/aspis-core/src/field/wide_exact.rs';C='crates/aspis-core/src/field/ct.rs'
s='#![allow(dead_code,non_snake_case)]\nconst P:u32=0x7fffffff;\n'
for t,p in [('M31',F),('CM31',F),('QM31',F),('WideExact',W)]:
 s+='#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+item(p,'pub struct '+t)
s+='mod ct {\n'+item(C,'pub fn is_zero(')+'}\n'
# Include the exact CT implementations, with feature selection made explicit.
s+='impl M31 {\n'+item(F,'pub fn is_zero(self) -> bool { ct::is_zero(self.0) }')+'}\n'
# Single-line impl blocks have distinct markers.
for t in ['CM31','QM31']:
 s+=item(F,'impl '+t+' { #[inline(always)] pub fn is_zero',True)
s+='impl WideExact {\n'+item(W,'pub fn is_zero(self)',True)
s+='pub const LIMB_COUNT:usize=8;\npub const BYTE_LEN:usize=32;\n'
for marker in ['pub fn from_limbs(', 'pub const fn to_limbs(', 'pub fn from_le_bytes(', 'pub fn to_le_bytes(']:s+=item(W,marker)
s+='}\n'
s+='''
fn q(x:[u32;4])->QM31 {QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
#[cfg(kani)] mod PV_L2_zero {
use super::*;
#[kani::proof] fn m31_zero(){let x:u32=kani::any();assert_eq!(M31(x).is_zero(),x==0);}
#[kani::proof] fn cm31_zero(){let x:[u32;2]=kani::any();assert_eq!(CM31{a:M31(x[0]),b:M31(x[1])}.is_zero(),x==[0;2]);}
#[kani::proof] fn qm31_zero(){let x:[u32;4]=kani::any();assert_eq!(q(x).is_zero(),x==[0;4]);}
#[kani::proof] fn wide_zero(){let x:[u32;8]=kani::any();let w=WideExact{c0:q([x[0],x[1],x[2],x[3]]),c1:q([x[4],x[5],x[6],x[7]])};assert_eq!(w.is_zero(),(0..8).all(|i|x[i]==0));}
#[kani::proof] #[kani::unwind(10)] fn limbs_success_pointwise(){let x:[u32;8]=kani::any();if let Some(w)=WideExact::from_limbs(x){for i in 0..8{assert_eq!(w.to_limbs()[i],x[i]);}for v in x{assert!(v<P);}}}
#[kani::proof] #[kani::unwind(10)] fn limbs_complete(){let x:[u32;8]=kani::any();for v in x{kani::assume(v<P);}assert!(WideExact::from_limbs(x).is_some());}
#[kani::proof] #[kani::unwind(10)] fn limbs_zero(){let x:[u32;8]=kani::any();if let Some(w)=WideExact::from_limbs(x){assert_eq!(w.is_zero(),(0..8).all(|i|x[i]==0));}}
#[kani::proof] #[kani::unwind(34)] fn bytes_success(){let b:[u8;32]=kani::any();if let Some(w)=WideExact::from_le_bytes(&b){assert_eq!(w.to_le_bytes(),b);}}
#[kani::proof] #[kani::unwind(10)] fn bytes_canonical(){let b:[u8;32]=kani::any();if let Some(w)=WideExact::from_le_bytes(&b){for v in w.to_limbs(){assert!(v<P);}}}
#[kani::proof] #[kani::unwind(34)] fn bytes_zero(){let b:[u8;32]=kani::any();if let Some(w)=WideExact::from_le_bytes(&b){assert_eq!(w.is_zero(),b==[0;32]);}}
#[kani::proof] #[kani::unwind(10)] fn wrong_length(){let b:[u8;33]=kani::any();let n:usize=kani::any();kani::assume(n<=33&&n!=32);assert!(WideExact::from_le_bytes(&b[..n]).is_none());}
'''
for i in range(8):
 s+=f'''#[kani::proof] #[kani::unwind(10)] fn reject_limb_{i}(){{let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[{i}]=bad;assert!(WideExact::from_limbs(x).is_none());}}
'''
s+='''#[kani::proof] #[kani::unwind(10)] fn nonzero_limb(){let x:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8&&x[i]!=0);if let Some(w)=WideExact::from_limbs(x){assert!(!w.is_zero());}}
}\n'''
(D/'PV_L2_Zero_native.rs').write_text(s)
(D/'zero-source-binding.json').write_text(json.dumps(bindings,indent=2)+'\n')
print('pinned',rev,'items',len(bindings),'harnesses',s.count('#[kani::proof]'))
