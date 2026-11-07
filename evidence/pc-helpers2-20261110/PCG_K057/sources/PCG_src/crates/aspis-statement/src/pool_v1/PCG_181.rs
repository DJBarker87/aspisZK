extern crate alloc;
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(1100)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn owned_window(){
 let inner:IncrementalMerkleTreeV1=kani::any();let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<8&&j<POOL_V1_TREE_DEPTH);
 let n=inner.next_leaf_index;let r=inner.root[i].0;let f=inner.frontier[j][i].0;
 let out=ValidatedIncrementalMerkleTreeV1{inner,empty:&empty}.into_inner();
 assert_eq!(out.next_leaf_index,n);assert_eq!(out.frontier[j][i].0,f);
 assert!((out.root[i].0==r)!=cfg!(PCG_NEG_OWNED));
}
