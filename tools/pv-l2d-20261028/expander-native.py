"""Freeze the native expander and its committed owned reference for finite checks."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
sp=R/'crates/aspis-prover/src/state_only_entropy.rs';rp=R/'crates/aspis-prover/src/prover_commit_reference.rs';fp=R/'crates/aspis-core/src/field.rs';ep=R/'crates/aspis-prover/src/state_only_hiding.rs'
rows=[]
def take(p,start):
 s=p.read_text();a=s.index(start);i=s.index('{',a);depth=1;j=i+1
 while depth:
  if s[j]=='{':depth+=1
  if s[j]=='}':depth-=1
  j+=1
 b=s[a:j];rows.append(dict(path=str(p.relative_to(R)),start=start,sha256=hashlib.sha256(b.encode()).hexdigest()));return b
fields=[]
# Copy the exact field declarations and constructor. No arithmetic stand-ins.
ms=fp.read_text();m=ms[ms.index('pub struct M31('):];m=m[:m.index(';')+1]
fields.append('#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+m)
for n in ['CM31','QM31']:fields.append('#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+take(fp,'pub struct '+n+' {'))
fields.append('impl CM31 {\n'+take(fp,'pub fn new(a: M31, b: M31)')+'\n}')
fields.append('pub const P:u32=0x7fff_ffff;')
err='#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+take(ep,'pub enum StateOnlyMaskBuildError {')
source='\n'.join([take(sp,'struct Profile21SourceExpander {'),take(sp,'impl Profile21SourceExpander {'),take(sp,'impl Drop for Profile21SourceExpander {'),take(sp,'fn profile21_source_expander_block(')])
state='#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+take(rp,'pub(crate) struct State {')
host_hash=take(R/'crates/aspis-prover/src/lib.rs','pub fn host_hashv(')
reference='mod reference { use super::*;use crate::aspis_core;\n'+state+'\n'+'\n'.join(take(rp,sign) for sign in ['pub(crate) fn next(','pub(crate) fn limb_caller(','pub(crate) fn qm31_caller('])+'\n}'
header='''#![allow(unexpected_cfgs,dead_code)]
use zeroize::{Zeroize,Zeroizing};
use std::cell::{Cell,RefCell};
mod aspis_core {
 pub type HashFn=fn(&[&[u8]])->[u8;32];
 pub mod field {\n'''+ '\n'.join(fields)+'''\n }
}
use aspis_core::{HashFn,field::{M31,P}};
'''+err+'''
const PROFILE21_SOURCE_EXPAND_DOMAIN:&[u8]=b"aspis:state-only:profile21:source-expand:v1";
'''
tests=r'''
type Frame=Vec<Vec<u8>>;
thread_local!{static MODE:Cell<u8>=const{Cell::new(0)};static LOG:RefCell<Vec<Frame>>=const{RefCell::new(Vec::new())};}
fn reset(mode:u8){MODE.with(|m|m.set(mode));LOG.with(|l|l.borrow_mut().clear());}
fn log()->Vec<Frame>{LOG.with(|l|std::mem::take(&mut *l.borrow_mut()))}
fn hash(parts:&[&[u8]])->[u8;32]{
 LOG.with(|l|l.borrow_mut().push(parts.iter().map(|p|p.to_vec()).collect()));
 assert_eq!(parts.len(),3);assert_eq!(parts[0],PROFILE21_SOURCE_EXPAND_DOMAIN);
 let seed=parts[1];let ctr=u64::from_le_bytes(parts[2].try_into().unwrap());
 let mode=MODE.with(|m|m.get());let mut out=[0;32];
 for i in 0..8 {
  let at=ctr.wrapping_mul(8).wrapping_add(i as u64);
  let v=match mode {
   0=>0,1=>P,2=>if at%5==0 {P} else {(at as u32).wrapping_mul(719).wrapping_add(seed[i%32] as u32)&0x3fff_ffff},
   3..=6=>if at<(mode-3) as u64 {0} else {P},
   7=>if i%2==0 {P} else {u32::MAX},
   _=>(at as u32).wrapping_mul(0x9e37_79b9).wrapping_add(seed[i%32] as u32)
  };
  out[4*i..4*i+4].copy_from_slice(&v.to_le_bytes());
 }
 out
}
fn source(s:reference::State)->Profile21SourceExpander {
 Profile21SourceExpander{hash,seed:Zeroizing::new(s.seed),counter:s.counter,block:s.block,word:s.word}
}
fn snapshot(s:&Profile21SourceExpander)->reference::State {
 reference::State{seed:*s.seed,counter:s.counter,block:s.block,word:s.word}
}
fn check(s:reference::State,mode:u8)->usize {
 reset(mode);let mut a=source(s);let v=a.next_word();let after=snapshot(&a);let events=log();
 reset(mode);let (expected,b)=reference::next(hash,PROFILE21_SOURCE_EXPAND_DOMAIN,s);
 assert_eq!(v,expected);assert_eq!(after,b);assert_eq!(events,log());
 reset(mode);let mut a=source(s);let v=a.m31();let after=snapshot(&a);let events=log();
 reset(mode);let (expected,b)=reference::limb_caller(hash,PROFILE21_SOURCE_EXPAND_DOMAIN,s);
 assert_eq!(v,expected);assert_eq!(after,b);assert_eq!(events,log());
 reset(mode);let mut a=source(s);let v=a.qm31();let after=snapshot(&a);let events=log();
 reset(mode);let (expected,b)=reference::qm31_caller(hash,PROFILE21_SOURCE_EXPAND_DOMAIN,s);
 assert_eq!(v,expected);assert_eq!(after,b);assert_eq!(events,log());3
}
fn main(){
 let mut checks=0;
 for mode in 0..9 {for seed_case in 0..8 {for ctr in [0,1,u64::MAX] {for word in 0..=8 {for cache_case in 0..3 {
  let seed=std::array::from_fn(|i|(seed_case*31+i) as u8);let mut block=[0;32];
  for i in 0..8 {let v=match cache_case {0=>0,1=>P,_=>(i as u32).wrapping_mul(0x1e35_a7bd).wrapping_add(seed_case as u32)};block[4*i..4*i+4].copy_from_slice(&v.to_le_bytes());}
  checks+=check(reference::State{seed,counter:ctr,block,word},mode);
 }}}}}
 for fail_limb in 0..4 {
  reset(3+fail_limb);let mut a=Profile21SourceExpander::new(hash,[1;32]);
  assert_eq!(a.qm31(),Err(StateOnlyMaskBuildError::MaskSampleExhausted));
  let words=fail_limb as usize+16;
  assert_eq!(a.counter,((words+7)/8) as u64);
  assert_eq!(a.word,if words%8==0 {8}else{words%8});
  assert_eq!(log().len(),(words+7)/8);
 }
 for seed_case in 0..64 {
  let seed=std::array::from_fn(|i|(seed_case*17+i) as u8);
  let s=reference::State{seed,counter:0,block:[0;32],word:8};
  let mut a=Profile21SourceExpander::new(host_hashv,seed);
  let got=a.qm31();let (expected,after)=reference::qm31_caller(host_hashv,PROFILE21_SOURCE_EXPAND_DOMAIN,s);
  assert_eq!(got,expected);assert_eq!(snapshot(&a),after);assert!(got.is_ok());checks+=1;
 }
 if std::env::args().any(|a|a=="negative") {
  reset(0);let mut a=Profile21SourceExpander::new(hash,[2;32]);
  assert_eq!(a.m31(),Err(StateOnlyMaskBuildError::MaskSampleExhausted),"matched false control: all-zero words accept");
 }
 println!("{{\"method_checks\":{},\"directed_limb_failure_controls\":4,\"failed\":0}}",checks);
}
'''
out=R/'tools/pv-l2d-20261028/expander-native/src/main.rs';out.write_text(header+source+'\n'+host_hash+'\n'+reference+'\n'+tests)
(E/'expander-native-freeze.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bodies=rows,harness_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),zeroize_version='1.8.1',evidence_class='finite validation preparation; no deployed hash or whole-row trace credit',differences=['nominal enclosing aspis_core module; exact scalar/tower field declarations and CM31 constructor','public P constant has same 0x7fffffff value','extra Debug/Eq derives for comparisons; no source function body changed','test uses synthetic HashFn families plus 64 source-identical host_hashv cases under sha2 0.10.9; no ELF credit','reference next uses explicit four-byte array, source next uses slice try_into','reference scalar uses range loop; source scalar uses counted while','reference QM31 construction is delayed; source construction is nested; these observations need the separate trace model'],fidelity='next/refill use direct owned-state writes, no iterator backward continuation; reference emissions not claimed by this script',source_modifications_under_crates=False),indent=2)+'\n')
print('expander bodies frozen',len(rows),'bytes',out.stat().st_size)
