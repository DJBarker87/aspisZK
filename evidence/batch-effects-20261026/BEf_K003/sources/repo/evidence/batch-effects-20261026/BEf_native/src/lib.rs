#![allow(dead_code, unexpected_cfgs, non_snake_case)]
use aspis_r1_cost_probe::{compact::{self, OPENING, SLOT_NODES, SPLIT}, multiproof::{self, Arity},verifier::Error};
use aspis_core::{Digest32, state_only_private_merkle::private_leaf_hash_with_digest,r0::merkle};
include!("BEf_source.rs");
fn sha256(parts: &[&[u8]]) -> [u8;32] {
    use sha2::Digest;
    let mut hash=sha2::Sha256::new();
    for part in parts {hash.update(part);}
    hash.finalize().into()
}
fn padding_witness(which:usize) -> Result<(),Error> {
    let mut proof=vec![0u8;compact::PROOF_BYTES];
    proof[compact::slot_offset(3*which+1)-1]=1;
    batch_merkle_values(&proof,[0;22],[[0;32];3],which,aspis_core::digest::LegacyHashFn(sha256))
}
#[test]
fn BEf_tx1_nonzero_padding() { assert_eq!(padding_witness(0),Err(Error::Parse)); }
#[test]
fn BEf_tx2_nonzero_padding() { assert_eq!(padding_witness(1),Err(Error::Parse)); }
#[cfg(kani)]
mod BEf_proofs {
    use super::*;
    #[kani::proof]
    #[kani::unwind(1025)]
    fn BEf_tx1_padding() { assert_eq!(padding_witness(0),Err(Error::Parse)); }
    #[kani::proof]
    #[kani::unwind(1025)]
    fn BEf_tx2_padding() { assert_eq!(padding_witness(1),Err(Error::Parse)); }
}

#[derive(Clone,Copy)]
struct BEf_CountSha<'a>(&'a core::cell::Cell<usize>);
impl Digest32 for BEf_CountSha<'_> {
    fn digest(&self, parts: &[&[u8]]) -> [u8;32] {
        self.0.set(self.0.get()+1);
        sha256(parts)
    }
}
fn BEf_padding_effects(which:usize) -> (Result<(),Error>,usize) {
    let count=core::cell::Cell::new(0);
    let mut proof=vec![0u8;compact::PROOF_BYTES];
    proof[compact::slot_offset(3*which+1)-1]=1;
    let out=batch_merkle_values(&proof,[0;22],[[0;32];3],which,BEf_CountSha(&count));
    (out,count.get())
}
#[test]
fn BEf_tx1_effect_prefix() {assert_eq!(BEf_padding_effects(0),(Err(Error::Parse),10));}
#[test]
fn BEf_tx2_effect_prefix() {assert_eq!(BEf_padding_effects(1),(Err(Error::Parse),12));}

#[cfg(kani)]
mod BEf_tail_proofs {
    use super::*;
    fn check(which:usize) {
        let mut proof=vec![0u8;compact::PROOF_BYTES];
        let s=3*which;
        proof[compact::slot_offset(s+1)-1]=1;
        let mut idx:[u32;16]=kani::any();
        idx[0]=0;
        let mut val:[[u8;32];16]=kani::any();
        let before_idx=idx;
        let before_val=val;
        let count=core::cell::Cell::new(0);
        let result=BEf_source_tail(&proof,[0;32],s,&mut idx,&mut val,1,BEf_CountSha(&count));
        assert_eq!(result,Err(Error::Parse));
        assert_eq!(idx,before_idx);
        assert_eq!(val,before_val);
        assert_eq!(count.get(),0);
        kani::cover!(result==Err(Error::Parse));
    }
    #[kani::proof]
    #[kani::unwind(1025)]
    fn BEf_tail_tx1() {check(0);}
    #[kani::proof]
    #[kani::unwind(1025)]
    fn BEf_tail_tx2() {check(1);}
}
