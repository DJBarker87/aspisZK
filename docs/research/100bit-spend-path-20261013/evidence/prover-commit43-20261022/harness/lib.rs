#![allow(unexpected_cfgs,dead_code,static_mut_refs)]
pub mod owner;
use std::ops::{Deref,DerefMut};
struct Zeroizing<T>(T);
impl<T> Zeroizing<T> {fn new(v:T)->Self {Self(v)}}
impl<T> Deref for Zeroizing<T> {type Target=T;fn deref(&self)->&T {&self.0}}
impl<T> DerefMut for Zeroizing<T> {fn deref_mut(&mut self)->&mut T {&mut self.0}}
impl<const N:usize> AsMut<[u8]> for Zeroizing<[u8;N]> {fn as_mut(&mut self)->&mut [u8] {&mut self.0}}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum StateOnlyAttemptEntropyError {Os(u32),RepeatedZeroBlock}
impl From<u32> for StateOnlyAttemptEntropyError {fn from(e:u32)->Self {Self::Os(e)}}
struct StateOnlyAttemptSecrets {mask_nonce:[u8;32],field_mask_entropy:Zeroizing<[u8;32]>,leaf_salt_seed:Zeroizing<[u8;32]>}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Env {status:bool,error:u32,raw:owner::Raw,calls:u8,draws:u8,retained:[u8;32]}
static mut ENV:Option<Env>=None;
fn with_env<T>(f:impl FnOnce(&mut Env)->T)->T {unsafe {f(ENV.as_mut().unwrap())}}
fn next(mut e:Env)->(Result<owner::Raw,u32>,Env) {
 e.calls+=1;
 if !e.status {return (Err(e.error),e)}
 e.draws+=1;(Ok(e.raw),e)
}
mod getrandom {
 use super::*;
 pub fn fill(out:&mut [u8])->Result<(),u32> {
  assert_eq!(out.len(),64);
  let (result,after)=next(with_env(|e|*e));with_env(|e|*e=after);
  let raw=result?;out[..32].copy_from_slice(&raw.field);out[32..].copy_from_slice(&raw.leaf);Ok(())
 }
}
include!("native-candidate.rs");
fn transition(nonce:[u8;32],e:Env)->(Option<Result<owner::Secret,owner::Error<u32>>>,Env) {
 let (result,after)=next(e);
 let out=match result {
  Err(e)=>Some(Err(owner::Error::Os(e))),
  Ok(raw)=>if !owner::zero(raw.field,0) && !owner::zero(raw.leaf,0) {Some(Ok(owner::Secret{nonce,raw}))} else {None}
 };(out,after)
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(100)]
 fn candidate_full_bytes() {
  let e=Env{status:kani::any(),error:kani::any(),raw:owner::Raw{field:kani::any(),leaf:kani::any()},calls:kani::any(),draws:kani::any(),retained:kani::any()};
  kani::assume(e.calls<16);kani::assume(e.draws<=e.calls);
  let nonce:[u8;32]=kani::any();unsafe {ENV=Some(e)};
  let actual=StateOnlyAttemptSecrets::candidate(nonce);
  let (expected,state)=transition(nonce,e);
  assert_eq!(with_env(|e|*e),state);
  match (actual,expected) {
   (None,None)=>(),
   (Some(Ok(a)),Some(Ok(b)))=>{assert_eq!(a.mask_nonce,b.nonce);assert_eq!(*a.field_mask_entropy,b.raw.field);assert_eq!(*a.leaf_salt_seed,b.raw.leaf)},
   (Some(Err(StateOnlyAttemptEntropyError::Os(a))),Some(Err(owner::Error::Os(b))))=>assert_eq!(a,b),
   _=>assert!(false)
  }
 }
}
