#!/usr/bin/env python3
"""Generate scratch-only additive contracts and exact safe word references."""
from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
ref='''pub const P:u32=0x7fff_ffff;
pub fn add_word(x:u32,y:u32)->u32 {let s=x.wrapping_add(y);if s>=P {s.wrapping_sub(P)}else{s}}
pub fn sub_word(x:u32,y:u32)->u32 {let s=x.wrapping_add(P).wrapping_sub(y);if s>=P {s.wrapping_sub(P)}else{s}}
pub fn normalize_word(x:u32)->u32 {x%P}
'''
for op in ['add','sub']:
 for size in [2,4,8]:
  values=','.join(f'{op}_word(x[{i}],y[{i}])' for i in range(size))
  ref+=f'pub fn {op}{size}(x:[u32;{size}],y:[u32;{size}])->[u32;{size}] {{[{values}]}}\n'
(E/'NEB_additive_reference.rs').write_text(ref)
base='''use super::*;
#[path="NEB_additive_reference.rs"] pub mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
impl kani::Arbitrary for M31 {fn any()->Self{M31(kani::any::<u32>())}}
pub fn canon_m(x:M31)->bool{x.0<P}
pub fn canon_c(x:CM31)->bool{canon_m(x.a)&&canon_m(x.b)}
pub fn canon_q(x:QM31)->bool{canon_c(x.c0)&&canon_c(x.c1)}
pub fn any_m()->M31{M31(kani::any())}
pub fn any_c()->CM31{CM31{a:any_m(),b:any_m()}}
pub fn any_q()->QM31{QM31{c0:any_c(),c1:any_c()}}
pub fn words_c(x:CM31)->[u32;2]{[x.a.0,x.b.0]}
pub fn words_q(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
'''
shapes={'m':('M31','canon_m','any_m'),'c':('CM31','canon_c','any_c'),'q':('QM31','canon_q','any_q')}
attrs={}
for prefix,ops in [('m',['add','sub','double']),('c',['add','sub','double']),('q',['add','sub'])]:
 ty,canon,anyfn=shapes[prefix]
 for op in ops:
  args='x:'+ty if op=='double' else 'x:'+ty+',y:'+ty
  native_args='self' if op=='double' else 'self,rhs'
  pred=f'NEB_additive::{canon}(self)'+('' if op=='double' else f' && NEB_additive::{canon}(rhs)')
  post=f'post_{prefix}_{op}'
  if prefix=='m':
   want=f'reference.{op}_word(x.0,'+('x.0)' if op=='double' else 'y.0)')
   want=want.replace('reference.','reference::').replace('double_word','add_word')
   correct=f'r.0=={want} && canon_m(r)'
  else:
   n=2 if prefix=='c' else 4;wordfn='words_c' if prefix=='c' else 'words_q'
   refop='add' if op=='double' else op
   first=f'let want=reference::{refop}{n}({wordfn}(x),{wordfn}(x)' + (');' if op=='double' else f'.PLACEHOLDER);')
   if op!='double':first=f'let want=reference::{refop}{n}({wordfn}(x),{wordfn}(y));'
   fields=['r.a.0','r.b.0'] if prefix=='c' else ['r.c0.a.0','r.c0.b.0','r.c1.a.0','r.c1.b.0']
   correct=' && '.join(f'{field}==want[{i}]' for i,field in enumerate(fields))+f' && {canon}(r)'
   base+=f'pub fn {post}({args},r:{ty})->bool {{{first}let good={correct};if cfg!(NEB_wrong_{prefix}_{op}){{!good}}else{{good}}}}\n'
  if prefix=='m':base+=f'pub fn {post}({args},r:{ty})->bool {{let good={correct};if cfg!(NEB_wrong_{prefix}_{op}){{!good}}else{{good}}}}\n'
  attrs[(ty,op)]=f'    #[cfg_attr(kani,kani::requires({pred}))]\n    #[cfg_attr(kani,kani::ensures(|r| NEB_additive::{post}({native_args},*r)))]\n'
  target=ty+'::'+op
  stubs=[]
  if not(prefix=='m' and op in ['add','sub']):stubs=['M31::'+('sub' if op=='sub' else 'add')]
  base+=f'#[kani::proof_for_contract({target})] #[kani::unwind(66)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n'
  for stub in stubs:base+=f'#[kani::stub_verified({stub})]\n'
  variables=f'let x={anyfn}();kani::assume({canon}(x));'
  if op!='double':variables+=f'let y={anyfn}();kani::assume({canon}(y));'
  call=f'x.{op}('+('' if op=='double' else 'y')+')'
  base+=f'fn {prefix}_{op}(){{{variables}let _={call};}}\n'
# Fixed-array shape probes, before any array-valued contract is used.
base+='''#[kani::ensures(|r| r[0]==x)]
fn weak_array(x:u32)->[u32;8]{[x;8]}
#[kani::proof_for_contract(weak_array)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_weak(){let _=weak_array(kani::any());}
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_real(){let x:u32=kani::any();assert_eq!(weak_array(x)[7],x);}
#[kani::proof] #[kani::unwind(66)] #[kani::stub_verified(weak_array)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_unimplied(){let x:u32=kani::any();assert_eq!(weak_array(x)[7],x);}
#[kani::modifies(x)] #[kani::ensures(|r| r[0]==0)]
fn bad_array_frame(x:&mut u32,y:&mut u32)->[u32;8]{let _=x;*y=y.wrapping_add(1);[0;8]}
#[kani::proof_for_contract(bad_array_frame)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_frame(){let mut x:u32=kani::any();let mut y:u32=kani::any();let _=bad_array_frame(&mut x,&mut y);}
'''
(E/'NEB_additive.rs').write_text(base)
wide='''use super::*;
use crate::field::{NEB_additive as A,M31,CM31,QM31};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub fn canon(x:WideExact)->bool{A::canon_q(x.c0)&&A::canon_q(x.c1)}
fn any_e()->WideExact{WideExact{c0:A::any_q(),c1:A::any_q()}}
pub fn words(x:WideExact)->[u32;8]{[x.c0.c0.a.0,x.c0.c0.b.0,x.c0.c1.a.0,x.c0.c1.b.0,x.c1.c0.a.0,x.c1.c0.b.0,x.c1.c1.a.0,x.c1.c1.b.0]}
'''
wattrs={}
for op in ['add','sub']:
 fields=['r.c0.c0.a.0','r.c0.c0.b.0','r.c0.c1.a.0','r.c0.c1.b.0','r.c1.c0.a.0','r.c1.c0.b.0','r.c1.c1.a.0','r.c1.c1.b.0']
 good=' && '.join(f'{field}==want[{i}]' for i,field in enumerate(fields))+' && canon(r)'
 wide+=f'pub fn post_{op}(x:WideExact,y:WideExact,r:WideExact)->bool {{let want=A::reference::{op}8(words(x),words(y));let good={good};if cfg!(NEB_wrong_e_{op}){{!good}}else{{good}}}}\n'
 wide+=f'#[kani::proof_for_contract(WideExact::{op})] #[kani::unwind(66)]\n#[kani::stub_verified(M31::{op})]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\nfn e_{op}(){{let x=any_e();let y=any_e();kani::assume(canon(x)&&canon(y));let _=x.{op}(y);}}\n'
 wattrs[op]=f'    #[cfg_attr(kani,kani::requires(NEB_wide::canon(self) && NEB_wide::canon(rhs)))]\n    #[cfg_attr(kani,kani::ensures(|r| NEB_wide::post_{op}(self,rhs,*r)))]\n'
wide+='''pub fn limbs_post(x:WideExact,r:[u32;8])->bool{let good=r==words(x);if cfg!(NEB_wrong_limbs){!good}else{good}}
#[kani::proof_for_contract(WideExact::to_limbs)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn limbs(){let _=any_e().to_limbs();}
pub fn canonical_post(x:QM31,r:QM31)->bool {let good=r.c0.a.0==A::reference::normalize_word(x.c0.a.0)&&r.c0.b.0==A::reference::normalize_word(x.c0.b.0)&&r.c1.a.0==A::reference::normalize_word(x.c1.a.0)&&r.c1.b.0==A::reference::normalize_word(x.c1.b.0)&&A::canon_q(r);if cfg!(NEB_wrong_canonical){!good}else{good}}
#[kani::proof_for_contract(canonical_qm31)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn canonical(){let _=canonical_qm31(A::any_q());}
pub fn embed_post(x:QM31,r:WideExact)->bool{let good=canonical_post(x,r.c0)&&r.c1.c0.a.0==0&&r.c1.c0.b.0==0&&r.c1.c1.a.0==0&&r.c1.c1.b.0==0;if cfg!(NEB_wrong_embed){!good}else{good}}
#[kani::proof_for_contract(WideExact::from_qm31)] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn embed(){let _=WideExact::from_qm31(A::any_q());}
'''
(E/'NEB_wide.rs').write_text(wide)
# Start from the reducer overlay, then add only cfg(kani) attributes/modules.
field=subprocess.check_output(['git','show',F+':crates/aspis-core/src/field.rs'],text=True)
field=field.replace('fn reduce_u64(x: u64) -> u32 {','#[cfg_attr(kani,kani::ensures(|r| NEB_reducer::reduce_post(x,*r)))]\nfn reduce_u64(x: u64) -> u32 {',1).replace('    pub fn reduce_u64(value: u64) -> M31 {','    #[cfg_attr(kani,kani::ensures(|r| NEB_reducer::wrapper_post(value,*r)))]\n    pub fn reduce_u64(value: u64) -> M31 {',1)
for (ty,op),annotation in attrs.items():
 signature=f'    pub fn {op}(self'+('' if op=='double' else f', rhs: {ty}')+f') -> {ty} {{'
 assert field.count(signature)==1,signature
 field=field.replace(signature,annotation+signature)
field+='\n#[cfg(kani)] #[path="field/NEB_reducer.rs"] mod NEB_reducer;\n#[cfg(kani)] #[path="field/NEB_additive.rs"] mod NEB_additive;\n'
wfile='crates/aspis-core/src/field/wide_exact.rs';wsrc=subprocess.check_output(['git','show',F+':'+wfile],text=True)
for op,annotation in wattrs.items():
 signature=f'    pub fn {op}(self, rhs: Self) -> Self {{';assert wsrc.count(signature)==1;wsrc=wsrc.replace(signature,annotation+signature)
wsrc=wsrc.replace('    pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT] {','    #[cfg_attr(kani,kani::ensures(|r| NEB_wide::limbs_post(self,*r)))]\n    pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT] {')
assert 'NEB_wide::limbs_post' in wsrc,'to_limbs signature'
wsrc=wsrc.replace('fn canonical_qm31(value: QM31) -> QM31 {','#[cfg_attr(kani,kani::ensures(|r| NEB_wide::canonical_post(value,*r)))]\nfn canonical_qm31(value: QM31) -> QM31 {')
wsrc=wsrc.replace('    pub fn from_qm31(value: QM31) -> Self {','    #[cfg_attr(kani,kani::ensures(|r| NEB_wide::embed_post(value,*r)))]\n    pub fn from_qm31(value: QM31) -> Self {')
wsrc+='\n#[cfg(kani)] #[path="wide_exact/NEB_wide.rs"] mod NEB_wide;\n'
lib='crates/aspis-core/src/lib.rs';lsrc=subprocess.check_output(['git','show',F+':'+lib],text=True).replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')
files={'crates/aspis-core/src/field.rs':field,wfile:wsrc,lib:lsrc,'crates/aspis-core/src/field/NEB_additive.rs':base,'crates/aspis-core/src/field/NEB_additive_reference.rs':ref,'crates/aspis-core/src/field/wide_exact/NEB_wide.rs':wide,'crates/aspis-core/src/field/NEB_reducer.rs':(E/'NEB_reducer.rs').read_text()}
patch=''
for n,new in files.items():
 try:old=subprocess.check_output(['git','show',F+':'+n],text=True,stderr=subprocess.DEVNULL);frm='a/'+n
 except subprocess.CalledProcessError:old='';frm='/dev/null'
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=frm,tofile='b/'+n))
(E/'NEB_additive.patch').write_text(patch);(E/'NEB_ADDITIVE_FILES.json').write_text(json.dumps(files,indent=1)+'\n')
print(json.dumps(dict(files=len(files),patch_sha256=hashlib.sha256(patch.encode()).hexdigest())))
