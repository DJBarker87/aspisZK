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
        // The single occupied index 0 has exactly 18 sibling nodes.
        // Put nonzero padding in the first scanned word to isolate short-circuiting.
        proof[compact::slot_offset(s)+32*18]=1;
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

#[test]
fn BEf_reached_native_batches() {
    use aspis_r1_cost_probe::verifier;
    use aspis_statement::pool_v1::{self,PoolV1PairForestTerminalStatementV1 as Statement};
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    let fixture=std::env::var("BEF_FIXTURE_DIR").expect("pinned adopted compact fixture");
    let proof=std::fs::read(format!("{fixture}/r1-s2-proof.bin")).unwrap();
    let public=std::fs::read(format!("{fixture}/r1-s2-public-asf8.bin")).unwrap();
    let statement=pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public).unwrap();
    let semantic=match &statement {
        Statement::PrivateTransfer {common,public} => Public::Transfer(public,&common.lane_transition),
        Statement::Withdrawal {common,public} => Public::Withdrawal(public,&common.lane_transition),
    };
    let hash=aspis_core::digest::LegacyHashFn(sha256);
    let saved=verifier::tx1(semantic,&public,&proof,SPLIT,hash,None).expect("original TX1 accepts");
    assert_eq!(verifier::tx2_authenticated(&public,&proof,&saved,hash,None),Ok(()));
    let (prepared,_)=verifier::resume(&saved,&proof,&public,aspis_r1_cost_probe::transport::Variant::S2,hash).unwrap();
    let folded:[u8;32]=proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    let roots=[prepared.roots[0],prepared.roots[1],folded];
    for which in 0..2 {
        assert_eq!(batch_merkle_values(&proof,prepared.queries,roots,which,hash),Ok(()));
        let (lo,hi)=if which==0 {(0,SPLIT)} else {(SPLIT,22)};
        let mut live=prepared.queries[lo..hi].to_vec();
        live.sort_unstable();live.dedup();
        let nodes=multiproof::node_count(Arity::Two,&live).unwrap();
        assert!(nodes<SLOT_NODES[3*which]);
        let mut bad=proof.clone();
        let offset=compact::slot_offset(3*which)+32*nodes;
        assert_eq!(bad[offset],0);bad[offset]=1;
        let count=core::cell::Cell::new(0);
        assert_eq!(batch_merkle_values(&bad,prepared.queries,roots,which,BEf_CountSha(&count)),Err(Error::Parse));
        assert_eq!(count.get(),hi-lo,"all leaves precede the padding rejection; no parent hashes follow");
        if which==0 {
            assert_eq!(verifier::tx1(semantic,&public,&bad,SPLIT,hash,None),Err(Error::Parse));
        } else {
            // TX1 binds the changed proof and succeeds before TX2 reaches its own malformed padding.
            let saved_bad=verifier::tx1(semantic,&public,&bad,SPLIT,hash,None).expect("TX1 with only batch1 padding changed accepts");
            assert_eq!(verifier::tx2_authenticated(&public,&bad,&saved_bad,hash,None),Err(Error::Parse));
        }
        eprintln!("BEf reached batch={which} nodes={nodes} corrupted_offset={offset} attempted_leaf_hashes={}",count.get());
    }
}
