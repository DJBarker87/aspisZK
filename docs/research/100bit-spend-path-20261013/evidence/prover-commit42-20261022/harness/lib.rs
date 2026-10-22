#![allow(unexpected_cfgs,dead_code,static_mut_refs)]
pub mod owner;
#[path="owner-original.rs"] pub mod original;
use std::ops::{Deref,DerefMut};
struct Zeroizing<T>(T);
impl<T> Zeroizing<T> {fn new(v:T)->Self {Self(v)}}
impl<T> Deref for Zeroizing<T> {type Target=T;fn deref(&self)->&T {&self.0}}
impl<T> DerefMut for Zeroizing<T> {fn deref_mut(&mut self)->&mut T {&mut self.0}}
impl<const N:usize> AsMut<[u8]> for Zeroizing<[u8;N]> {fn as_mut(&mut self)->&mut [u8] {&mut self.0}}
const ENTROPY_RETRY_LIMIT:usize=16;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum StateOnlyAttemptEntropyError {Os,RepeatedZeroBlock}
impl From<()> for StateOnlyAttemptEntropyError {fn from(_:())->Self {Self::Os}}
struct StateOnlyAttemptSecrets {mask_nonce:[u8;32],field_mask_entropy:Zeroizing<[u8;32]>,leaf_salt_seed:Zeroizing<[u8;32]>}
#[derive(Clone,Copy)]
struct Env {status:[bool;16],raw:[[u8;64];16],calls:usize,draws:usize}
static mut ENV:Option<Env>=None;
fn with_env<T>(f:impl FnOnce(&mut Env)->T)->T {unsafe {f(ENV.as_mut().unwrap())}}
fn next(mut e:Env)->(Result<owner::Raw,()>,Env) {
 let i=e.calls;e.calls+=1;
 if !e.status[i] {return (Err(()),e)}
 e.draws+=1;let mut field=[0;32];let mut leaf=[0;32];field.copy_from_slice(&e.raw[i][..32]);leaf.copy_from_slice(&e.raw[i][32..]);
 (Ok(owner::Raw{field,leaf}),e)
}
struct Primitive;
impl owner::IO<Env,()> for Primitive {fn fill(e:Env)->(Result<owner::Raw,()>,Env) {next(e)}}
mod getrandom {
 use super::*;
 pub fn fill(out:&mut [u8])->Result<(),()> {
  assert_eq!(out.len(),64);
  let (result,after)=next(with_env(|e|*e));with_env(|e|*e=after);
  let raw=result?;out[..32].copy_from_slice(&raw.field);out[32..].copy_from_slice(&raw.leaf);Ok(())
 }
}
include!("native-generate.rs");
#[cfg(kani)]
mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(100)]
 fn selected_api_full_bytes_fast_zero() {
  let e=Env{status:kani::any(),raw:kani::any(),calls:0,draws:0};
  let nonce:[u8;32]=kani::any();unsafe {ENV=Some(e)};
  let actual=StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce);
  let after=with_env(|e|*e);
  let (expected,state)=owner::generate::<Env,(),Primitive>(nonce,e);
  assert_eq!(after.calls,state.calls);assert_eq!(after.draws,state.draws);
  match (actual,expected) {
   (Ok(a),Ok(b))=>{assert_eq!(a.mask_nonce,b.nonce);assert_eq!(*a.field_mask_entropy,b.raw.field);assert_eq!(*a.leaf_salt_seed,b.raw.leaf)},
   (Err(StateOnlyAttemptEntropyError::Os),Err(owner::Error::Os(())))=>(),
   (Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock),Err(owner::Error::RepeatedZero))=>(),
   _=>assert!(false)
  }
 }
 #[kani::proof] #[kani::unwind(100)]
 fn zero_helper_exact() {
  let bytes:[u8;32]=kani::any();
  assert_eq!(original::zero(bytes,0),owner::zero(bytes,0));
 }
 #[kani::proof] #[kani::unwind(100)]
 fn zero_nonce_no_call() {
  let e=Env{status:kani::any(),raw:kani::any(),calls:0,draws:0};unsafe {ENV=Some(e)};
  assert!(matches!(StateOnlyAttemptSecrets::generate_for_mask_nonce([0;32]),Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
  assert_eq!(with_env(|e|e.calls),0);
 }
}
