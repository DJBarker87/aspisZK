#![allow(dead_code, unexpected_cfgs, non_snake_case)]
use aspis_r1_cost_probe::{compact::{self, OPENING, SLOT_NODES, SPLIT}, multiproof::{self, Arity},verifier::Error};
use aspis_core::{Digest32, state_only_private_merkle::private_leaf_hash_with_digest,r0::merkle};
include!("BEg_source.rs");
fn BEg_sha(parts: &[&[u8]]) -> [u8;32] {
    use sha2::Digest;
    let mut h=sha2::Sha256::new();
    for p in parts { h.update(p); }
    h.finalize().into()
}
#[derive(Clone,Copy)]
struct BEg_Hash<'a>(&'a core::cell::Cell<usize>);
impl Digest32 for BEg_Hash<'_> {
    fn digest(&self,parts:&[&[u8]]) -> [u8;32] {
        self.0.set(self.0.get()+1);
        BEg_sha(parts)
    }
}
// Independently written loop/reference. It invokes the actual P6 and leaf
// children; no child call or digest is replaced or abstracted.
fn BEg_reference_tree<H:Digest32>(proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,tree:usize,
    idx:&mut [u32;16],val:&mut [[u8;32];16],hash:H)->Result<(),Error> {
    let lo=if batch==0 {0} else {SPLIT};
    let n=if batch==0 {SPLIT} else {22-SPLIT};
    let s=3*batch+tree;
    let keys=sort_batch_keys(batch_keys(&queries,lo,n,tree),n);
    let mut distinct=0;
    for position in 0..n {
        let key=keys[position];
        let index=(key>>8) as u32;
        let value=batch_leaf(hash,tree,opening(proof,lo+(key&255) as usize));
        if distinct!=0 && idx[distinct-1]==index {
            if val[distinct-1]!=value {return Err(Error::Merkle);}
        } else {
            idx[distinct]=index;val[distinct]=value;distinct+=1;
        }
    }
    let count=match multiproof::node_count(Arity::Two,&idx[..distinct]) {
        Some(count)=>count,None=>return Err(Error::Merkle),
    };
    let nodes=slot(proof,s);
    if count>SLOT_NODES[s] {return Err(Error::Parse);}
    for word in nodes[32*count..].chunks_exact(8) {
        if u64::from_le_bytes(word.try_into().unwrap())!=0 {return Err(Error::Parse);}
    }
    if multiproof::verify_in_place(hash,Arity::Two,&root,idx,val,distinct,&nodes[..32*count]) {
        Ok(())
    } else {Err(Error::Merkle)}
}
fn BEg_reference<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],batch:usize,hash:H)->Result<(),Error> {
    let mut idx=[0;16];let mut val=[[0;32];16];
    for tree in 0..3 { BEg_reference_tree(proof,queries,roots[tree],batch,tree,&mut idx,&mut val,hash)?; }
    Ok(())
}
fn BEg_zero_roots()->[[u8;32];3] {
    let mut roots=[[0u8;32];3];
    for tree in 0..3 {
        let mut root=batch_leaf(aspis_core::digest::LegacyHashFn(BEg_sha),tree,&[0;832]);
        for _ in 0..18 {root=multiproof::binary_parent(aspis_core::digest::LegacyHashFn(BEg_sha),&root,&[0;32]);}
        roots[tree]=root;
    }
    roots
}
#[test]
fn BEg_accepted_zero_pair() {
    let proof=vec![0;compact::PROOF_BYTES];let roots=BEg_zero_roots();
    for batch in 0..2 {
        let actual=core::cell::Cell::new(0);let reference=core::cell::Cell::new(0);
        assert_eq!(batch_merkle_values(&proof,[0;22],roots,batch,BEg_Hash(&actual)),Ok(()));
        assert_eq!(BEg_reference(&proof,[0;22],roots,batch,BEg_Hash(&reference)),Ok(()));
        assert_eq!(actual.get(),reference.get());
        assert_eq!(actual.get(),if batch==0 {84} else {90});
    }
}
#[cfg(kani)]
mod BEg_proofs {
    use super::*;
    // Full real-SHA accepted body. The native test is the preliminary witness.
    #[kani::proof]
    #[kani::unwind(1025)]
    fn BEg_accepted_tx1() {
        let proof=vec![0;compact::PROOF_BYTES];let roots=BEg_zero_roots();
        let actual=core::cell::Cell::new(0);let reference=core::cell::Cell::new(0);
        let out=batch_merkle_values(&proof,[0;22],roots,0,BEg_Hash(&actual));
        let expected=BEg_reference(&proof,[0;22],roots,0,BEg_Hash(&reference));
        assert_eq!(out,expected);assert_eq!(out,Ok(()));
        assert_eq!(actual.get(),reference.get());
        kani::cover!(out==Ok(()));
    }
}
