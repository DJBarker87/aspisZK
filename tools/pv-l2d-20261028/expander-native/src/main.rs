#![allow(unexpected_cfgs,dead_code)]
use zeroize::{Zeroize,Zeroizing};
use std::cell::{Cell,RefCell};
mod aspis_core {
 pub type HashFn=fn(&[&[u8]])->[u8;32];
 pub mod field {
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct M31(pub u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
impl CM31 {
pub fn new(a: M31, b: M31) -> CM31 {
        CM31 { a, b }
    }
}
pub const P:u32=0x7fff_ffff;
 }
}
use aspis_core::{HashFn,field::{M31,P}};
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum StateOnlyMaskBuildError {
    ZeroPrivateEntropy,
    ReusedMaskNonce,
    MaskSampleExhausted,
    TraceShape,
    Layout,
}
const PROFILE21_SOURCE_EXPAND_DOMAIN:&[u8]=b"aspis:state-only:profile21:source-expand:v1";
struct Profile21SourceExpander {
    hash: HashFn,
    seed: Zeroizing<[u8; 32]>,
    counter: u64,
    block: [u8; 32],
    word: usize,
}
impl Profile21SourceExpander {
    fn new(hash: HashFn, seed: [u8; 32]) -> Self {
        Self {
            hash,
            seed: Zeroizing::new(seed),
            counter: 0,
            block: [0; 32],
            word: 8,
        }
    }

    #[cfg_attr(kani, kani::requires(self.word <= 8))]
    #[cfg_attr(kani, kani::requires(self.hash == crate::HOST_HASH))]
    #[cfg_attr(kani, kani::requires(crate::prover_commit_oracle::expander_domain(
        b"aspis:state-only:profile21:source-expand:v1", *self.seed, self.counter, self.word)))]
    #[cfg_attr(kani, kani::modifies(&mut self.counter, &mut self.block, &mut self.word))]
    #[cfg_attr(kani, kani::ensures(|result| crate::prover_commit_reference::next_matches(
        b"aspis:state-only:profile21:source-expand:v1",
        crate::prover_commit_reference::State { seed: old(*self.seed), counter: old(self.counter), block: old(self.block), word: old(self.word) },
        *result,
        crate::prover_commit_reference::State { seed: *self.seed, counter: self.counter, block: self.block, word: self.word })))]
    fn next_word(&mut self) -> u32 {
        if self.word == 8 {
            let hash = self.hash;
            let seed: [u8; 32] = *self.seed;
            let counter = self.counter;
            self.block = profile21_source_expander_block(hash, seed, counter);
            self.counter = self.counter.wrapping_add(1);
            self.word = 0;
        }
        let start = 4 * self.word;
        self.word += 1;
        u32::from_le_bytes(self.block[start..start + 4].try_into().unwrap())
    }

    fn m31(&mut self) -> Result<aspis_core::field::M31, StateOnlyMaskBuildError> {
        let mut retry=0;
        while retry<16 {
            let candidate=self.next_word() & 0x7fff_ffff;
            if candidate<aspis_core::field::P {return Ok(aspis_core::field::M31(candidate));}
            retry+=1;
        }
        Err(StateOnlyMaskBuildError::MaskSampleExhausted)
    }

    fn qm31(&mut self) -> Result<aspis_core::field::QM31, StateOnlyMaskBuildError> {
        Ok(aspis_core::field::QM31 {
            c0: aspis_core::field::CM31::new(self.m31()?, self.m31()?),
            c1: aspis_core::field::CM31::new(self.m31()?, self.m31()?),
        })
    }
}
impl Drop for Profile21SourceExpander {
    fn drop(&mut self) {
        self.block.zeroize();
        self.counter.zeroize();
        self.word.zeroize();
    }
}
fn profile21_source_expander_block(hash: HashFn, seed: [u8;32], counter: u64) -> [u8;32] {
    hash(&[PROFILE21_SOURCE_EXPAND_DOMAIN, &seed, &counter.to_le_bytes()])
}
pub fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}
mod reference { use super::*;use crate::aspis_core;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct State {
    pub(crate) seed: [u8; 32],
    pub(crate) counter: u64,
    pub(crate) block: [u8; 32],
    pub(crate) word: usize,
}
pub(crate) fn next(hash: HashFn, domain: &[u8], mut state: State) -> (u32, State) {
    if state.word == 8 {
        state.block = hash(&[domain, &state.seed, &state.counter.to_le_bytes()]);
        state.counter = state.counter.wrapping_add(1);
        state.word = 0;
    }
    let offset = state.word * 4;
    let bytes = [state.block[offset], state.block[offset+1], state.block[offset+2], state.block[offset+3]];
    state.word += 1;
    (u32::from_le_bytes(bytes), state)
}
pub(crate) fn limb_caller(hash: HashFn, domain: &[u8], mut state: State)
    -> (Result<M31, StateOnlyMaskBuildError>, State)
{
    for _ in 0..16 {
        let (word, after) = next(hash, domain, state);
        state = after;
        let candidate = word & 0x7fff_ffff;
        if candidate < P { return (Ok(M31(candidate)), state); }
    }
    (Err(StateOnlyMaskBuildError::MaskSampleExhausted), state)
}
pub(crate) fn qm31_caller(hash: HashFn, domain: &[u8], state: State)
    -> (Result<aspis_core::field::QM31, StateOnlyMaskBuildError>, State)
{
    let (a, state) = limb_caller(hash, domain, state);
    let a = match a { Ok(v) => v, Err(e) => return (Err(e), state) };
    let (b, state) = limb_caller(hash, domain, state);
    let b = match b { Ok(v) => v, Err(e) => return (Err(e), state) };
    let (c, state) = limb_caller(hash, domain, state);
    let c = match c { Ok(v) => v, Err(e) => return (Err(e), state) };
    let (d, state) = limb_caller(hash, domain, state);
    let d = match d { Ok(v) => v, Err(e) => return (Err(e), state) };
    (Ok(aspis_core::field::QM31 { c0: aspis_core::field::CM31 { a, b },
        c1: aspis_core::field::CM31 { a: c, b: d } }), state)
}
}

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
