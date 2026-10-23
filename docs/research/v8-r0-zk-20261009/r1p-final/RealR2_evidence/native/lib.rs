#![allow(unexpected_cfgs,dead_code)]
include!("source.rs");
#[cfg(kani)] mod RealR2_checks {
use super::*;
fn context()->StateOnlyHidingContext {StateOnlyHidingContext{statement_digest:kani::any(),mask_nonce:kani::any(),mask_layout_fingerprint:kani::any(),layout_factor_fingerprint:kani::any()}}
// Independently indexed owned frame. No source slice-copy operations.
fn encoded_byte(c:StateOnlyHidingContext,i:usize)->u8 {
 if i==0 {1} else if i<33 {c.statement_digest[i-1]}
 else if i<65 {c.mask_nonce[i-33]}
 else if i<73 {((c.mask_layout_fingerprint>>((i-65)*8))&255) as u8}
 else {((c.layout_factor_fingerprint>>((i-73)*8))&255) as u8}
}
#[kani::proof]
#[kani::unwind(82)]
fn context_frame() {
 let c=context();let i:usize=kani::any();kani::assume(i<81);
 assert_eq!(c.encode()[i],encoded_byte(c,i));
}
static mut CONTEXT:StateOnlyHidingContext=StateOnlyHidingContext{statement_digest:[0;32],mask_nonce:[0;32],mask_layout_fingerprint:0,layout_factor_fingerprint:0};
static mut BINDING:[u8;32]=[0;32];static mut ENTROPY:[u8;32]=[0;32];
static mut ANSWER:[u8;32]=[0;32];static mut CALLS:usize=0;
fn checked_oracle(parts:&[&[u8]])->[u8;32] {
 unsafe {
 CALLS+=1; assert_eq!(parts.len(),4);
 assert_eq!(parts[0],MASK_SEED_DOMAIN);
 assert_eq!(parts[1],BINDING);assert_eq!(parts[2].len(),81);
 for i in 0..81 {assert_eq!(parts[2][i],encoded_byte(CONTEXT,i));}
 assert_eq!(parts[3],ENTROPY);ANSWER
 }
}
#[kani::proof]
#[kani::unwind(83)]
fn seed_frame_and_zero_guard() {
 let c=context();let binding:[u8;32]=kani::any();let entropy:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
 unsafe {CONTEXT=c; BINDING=binding;ENTROPY=entropy;ANSWER=answer;CALLS=0;}
 let actual=derive_state_only_mask_seed_from_entropy_ref(checked_oracle,binding,c,&entropy);
 let mut nonzero=false;for b in entropy {nonzero|=b!=0;}
 if nonzero {assert_eq!(actual,Ok(answer));assert_eq!(unsafe{CALLS},1);}
 else {assert_eq!(actual,Err(StateOnlyMaskBuildError::ZeroPrivateEntropy));assert_eq!(unsafe{CALLS},0);}
}
}
