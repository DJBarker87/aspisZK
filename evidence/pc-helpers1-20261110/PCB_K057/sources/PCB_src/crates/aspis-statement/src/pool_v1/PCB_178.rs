use super::*;
const WRONG_TREE:IncrementalMerkleTreeV1=IncrementalMerkleTreeV1 {next_leaf_index:0,root:[M31::ZERO;8],frontier:[[M31::ZERO;8];POOL_V1_TREE_DEPTH]};
fn correct<'a,'b>(x:&'a ValidatedIncrementalMerkleTreeV1<'b>)->&'a IncrementalMerkleTreeV1 {&x.inner}
fn wrong<'a,'b>(_:&'a ValidatedIncrementalMerkleTreeV1<'b>)->&'a IncrementalMerkleTreeV1 {&WRONG_TREE}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,correct)]
fn tree_correct(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(x.as_tree(),&x.inner));}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,wrong)]
fn tree_wrong(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(x.as_tree(),&x.inner));}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,correct)]
fn deref_correct(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&x.inner));}
#[kani::proof] #[kani::stub(ValidatedIncrementalMerkleTreeV1::as_tree,wrong)]
fn deref_wrong(){let empty=[[M31::ZERO;8];POOL_V1_TREE_DEPTH+1];let mut inner=WRONG_TREE;inner.next_leaf_index=kani::any();let x=ValidatedIncrementalMerkleTreeV1 {inner,empty:&empty};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&x.inner));}
