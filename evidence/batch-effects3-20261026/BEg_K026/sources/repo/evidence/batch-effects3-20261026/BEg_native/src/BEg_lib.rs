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
#[test]
fn BEg_print_roots() {eprintln!("BEg zero roots={:?}",BEg_zero_roots());}
#[derive(Clone,Copy)]
struct BEg_LogHash<'a>(&'a core::cell::RefCell<Vec<Vec<Vec<u8>>>>);
impl Digest32 for BEg_LogHash<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        self.0.borrow_mut().push(parts.iter().map(|x|x.to_vec()).collect());
        BEg_sha(parts)
    }
}
#[test]
fn BEg_native_scratch_and_logs() {
    let proof=vec![0;compact::PROOF_BYTES];let original=proof.clone();let roots=BEg_zero_roots();
    for batch in 0..2 {for tree in 0..3 {
        let mut li=[0x12345678;16];let mut ri=li;
        let mut lv=[[0x5au8;32];16];let mut rv=lv;
        let before_idx=li;let before_val=lv;
        let lh=core::cell::RefCell::new(Vec::new());let rh=core::cell::RefCell::new(Vec::new());
        let l=batch_tree(&proof,[0;22],roots[tree],batch,tree,&mut li,&mut lv,BEg_LogHash(&lh));
        let r=BEg_reference_tree(&proof,[0;22],roots[tree],batch,tree,&mut ri,&mut rv,BEg_LogHash(&rh));
        assert_eq!(l,Ok(()));assert_eq!(l,r);assert_eq!(li,ri);assert_eq!(lv,rv);
        assert_eq!(*lh.borrow(),*rh.borrow(),"ordered parts and duplicate hashes");
        assert_eq!(&li[1..],&before_idx[1..]);assert_eq!(&lv[1..],&before_val[1..]);
    }}
    assert_eq!(proof,original);
}
#[test]
fn BEg_native_rejected_prefix_logs() {
    let roots=BEg_zero_roots();
    for batch in 0..2 {for tree in 0..3 {
        let mut proof=vec![0;compact::PROOF_BYTES];
        // All selected queries are index0. Exactly18 siblings are required.
        // Test first and last padding bytes, and a mismatched real Merkle node.
        for offset in [compact::slot_offset(3*batch+tree)+32*18,
            compact::slot_offset(3*batch+tree)+32*SLOT_NODES[3*batch+tree]-1,
            compact::slot_offset(3*batch+tree)] {
            proof[offset]=1;
            let mut li=[0;16];let mut ri=li;let mut lv=[[0;32];16];let mut rv=lv;
            let lh=core::cell::RefCell::new(Vec::new());let rh=core::cell::RefCell::new(Vec::new());
            let l=batch_tree(&proof,[0;22],roots[tree],batch,tree,&mut li,&mut lv,BEg_LogHash(&lh));
            let r=BEg_reference_tree(&proof,[0;22],roots[tree],batch,tree,&mut ri,&mut rv,BEg_LogHash(&rh));
            assert!(l.is_err());assert_eq!(l,r);assert_eq!(li,ri);assert_eq!(lv,rv);
            assert_eq!(*lh.borrow(),*rh.borrow());proof[offset]=0;
        }
    }}
}
#[cfg(kani)]
mod BEg_split {
    use super::*;
    fn padding(s:usize,mode:usize) {
        let cap=SLOT_NODES[s];
        let mut nodes=vec![0u8;32*cap];
        let tail:[u8;32]=kani::any();
        for i in 0..32 {nodes[32*(cap-1)+i]=tail[i];}
        let count=cap+mode-1;
        let out=BEg_source_padding_guard(&nodes,s,count);
        let mut zero=true;
        for b in tail {if b!=0 {zero=false;}}
        let expected=if mode==0 {if zero {Ok(())}else{Err(Error::Parse)}}
          else if mode==1 {Ok(())}else{Err(Error::Parse)};
        assert_eq!(out,expected);
        kani::cover!(out==Ok(()));
        if mode!=1 {kani::cover!(out==Err(Error::Parse));}
    }
    macro_rules! pad {
        ($name:ident,$s:expr,$mode:expr)=>{
            #[kani::proof] #[kani::unwind(65)] fn $name(){padding($s,$mode);}
        };
    }
    pad!(BEg_pad0_tail,0,0);pad!(BEg_pad1_tail,1,0);pad!(BEg_pad2_tail,2,0);
    pad!(BEg_pad3_tail,3,0);pad!(BEg_pad4_tail,4,0);pad!(BEg_pad5_tail,5,0);
    pad!(BEg_pad0_exact,0,1);pad!(BEg_pad1_exact,1,1);pad!(BEg_pad2_exact,2,1);
    pad!(BEg_pad3_exact,3,1);pad!(BEg_pad4_exact,4,1);pad!(BEg_pad5_exact,5,1);
    // Overflow-count branch has no accepted cover: acceptance is impossible.
    fn overflow(s:usize) {
        let nodes:[u8;8]=kani::any();
        let out=BEg_source_padding_guard(&nodes,s,SLOT_NODES[s]+1);
        assert_eq!(out,Err(Error::Parse));kani::cover!(out==Err(Error::Parse));
    }
    macro_rules! over {
        ($name:ident,$s:expr)=>{#[kani::proof] #[kani::unwind(65)] fn $name(){overflow($s);}};}
    over!(BEg_pad0_over,0);over!(BEg_pad1_over,1);over!(BEg_pad2_over,2);
    over!(BEg_pad3_over,3);over!(BEg_pad4_over,4);over!(BEg_pad5_over,5);
    fn keys(batch:usize,tree:usize) {
        let q:[u32;22]=kani::any();let lo=if batch==0{0}else{10};let n=if batch==0{10}else{12};
        let actual=batch_keys(&q,lo,n,tree);
        for j in 0..16 {
            let expected=if j<n {let index=if tree==2{q[lo+j]/4}else{q[lo+j]};
                ((index as u64)*256)+(j as u64)}else{0};
            assert_eq!(actual[j],expected);
        }
        kani::cover!(actual[0]==0);
    }
    macro_rules! key {
        ($name:ident,$b:expr,$t:expr)=>{#[kani::proof] #[kani::unwind(65)] fn $name(){keys($b,$t);}};}
    key!(BEg_keys00,0,0);key!(BEg_keys01,0,1);key!(BEg_keys02,0,2);
    key!(BEg_keys10,1,0);key!(BEg_keys11,1,1);key!(BEg_keys12,1,2);
    #[kani::proof] #[kani::unwind(65)]
    fn BEg_same_index() {
        let x:[u32;16]=kani::any();let j:usize=kani::any();kani::assume(j<16);
        let y:u32=kani::any();assert_eq!(same_batch_index(&x,j,y),x[j]==y);
        kani::cover!(same_batch_index(&x,j,y));kani::cover!(!same_batch_index(&x,j,y));
    }
    #[kani::proof] #[kani::unwind(65)]
    fn BEg_same_leaf() {
        let x:[[u8;32];16]=kani::any();let j:usize=kani::any();kani::assume(j<16);
        let y:[u8;32]=kani::any();let mut equal=true;
        for k in 0..32 {if x[j][k]!=y[k] {equal=false;}}
        assert_eq!(same_batch_leaf(&x,j,y),equal);
        kani::cover!(equal);kani::cover!(!equal);
    }
    #[kani::proof] #[kani::unwind(65)]
    fn BEg_key_at() {
        let x:[u64;16]=kani::any();let j:usize=kani::any();kani::assume(j<16);
        assert_eq!(batch_key_at(&x,j),x[j]);kani::cover!(batch_key_at(&x,j)==u64::MAX);
    }
}
