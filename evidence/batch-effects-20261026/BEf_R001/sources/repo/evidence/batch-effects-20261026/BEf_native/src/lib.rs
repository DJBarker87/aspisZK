#![allow(dead_code, unexpected_cfgs)]
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
