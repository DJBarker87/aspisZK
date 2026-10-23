#![allow(unexpected_cfgs,dead_code,non_snake_case)]
include!("source.rs");
#[cfg(kani)] mod RealR2_sampler {
use super::*;
static mut SEED:[u8;32]=[0;32];
static mut COUNTER:u64=0;
static mut BLOCKS:[[u8;32];2]=[[0;32];2];
// A fixed, arbitrary answer for each reachable refill coordinate, including
// u64 wrap. No per-read fresh randomness and no next-word or scalar stub.
fn oracle(parts:&[&[u8]])->[u8;32] {
 assert_eq!(parts.len(),3);
 assert_eq!(parts[0],b"aspis:state-only:private-mask-expand:v1");
 unsafe {
  assert_eq!(parts[1],SEED);
  let n=u64::from_le_bytes(parts[2].try_into().unwrap());
  if n==COUNTER {BLOCKS[0]}
  else {assert_eq!(n,COUNTER.wrapping_add(1));BLOCKS[1]}
 }
}
#[kani::requires(initial.word<=8)]
#[kani::requires(unsafe {initial.seed==SEED && initial.counter==COUNTER})]
#[kani::ensures(|out| *out == limb_caller(oracle,b"aspis:state-only:private-mask-expand:v1",initial))]
fn native_scalar(initial:State)->(Result<M31,StateOnlyMaskBuildError>,State) {
 let mut expander=SeedExpander{hash:oracle,seed:initial.seed,counter:initial.counter,block:initial.block,word:initial.word};
 let result=expander.m31();
 (result,State{seed:expander.seed,counter:expander.counter,block:expander.block,word:expander.word})
}
#[kani::proof_for_contract(native_scalar)]
#[kani::unwind(35)]
fn scalar_contract() {
 let initial:State=kani::any();kani::assume(initial.word<=8);
 unsafe {SEED=initial.seed;COUNTER=initial.counter;BLOCKS=kani::any();}
 let _=native_scalar(initial);
}
}
