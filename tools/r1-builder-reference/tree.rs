//! Owned validated-tree P6 reference. Excluded from production builds.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OwnedTree {
    pub inner: IncrementalMerkleTreeV1,
    pub empty: [Digest; POOL_V1_TREE_DEPTH + 1],
}
impl OwnedTree {
    pub fn from_parts(next_leaf_index: u64, root: Digest,
        frontier: [Digest; POOL_V1_TREE_DEPTH], empty: [Digest; POOL_V1_TREE_DEPTH+1])
        -> Result<Self, PoolV1TreeError> {
        let inner = IncrementalMerkleTreeV1 { next_leaf_index, root, frontier };
        inner.validate_with_empty_roots(&empty)?;
        Ok(Self { inner, empty })
    }
    pub fn into_inner(self) -> IncrementalMerkleTreeV1 { self.inner }
    pub fn as_tree(&self) -> &IncrementalMerkleTreeV1 { &self.inner }
    pub fn append_one(self, leaf: Digest) -> Result<(Self, AppendOneV1), PoolV1TreeError> {
        if self.inner.next_leaf_index == POOL_V1_LEAF_CAPACITY {
            return Err(PoolV1TreeError::TreeFull);
        }
        let leaf_index = self.inner.next_leaf_index;
        let mut frontier = self.inner.frontier;
        let mut carry = leaf;
        let mut carry_level = 0usize;
        while carry_level < POOL_V1_TREE_DEPTH && (leaf_index >> carry_level) & 1 == 1 {
            carry = pool_v1_tree_parent(&frontier[carry_level], &carry);
            frontier[carry_level] = self.empty[carry_level];
            carry_level += 1;
        }
        let next_leaf_index = leaf_index + 1;
        let root = if carry_level == POOL_V1_TREE_DEPTH {
            carry
        } else {
            frontier[carry_level] = carry;
            let provisional = IncrementalMerkleTreeV1 {
                next_leaf_index,
                root: [M31::ZERO; DIGEST_ELEMS],
                frontier,
            };
            // All lower bits were cleared by the carry, so the subtree below
            // `carry_level` is exactly the pinned recursive empty root at that
            // level. Starting there avoids recomputing `carry_level` known
            // empty parents and makes one append use exactly depth parent
            // hashes regardless of the cursor's trailing-one count.
            provisional.reconstruct_nonfull_root_from_level(&self.empty, carry_level)?
        };
        let next = Self {
            inner: IncrementalMerkleTreeV1 {
                next_leaf_index,
                root,
                frontier,
            },
            empty: self.empty,
        };
        let receipt = AppendOneV1 {
            leaf_index,
            root_sequence: next_leaf_index,
            root,
            history: root_history_location(next_leaf_index),
        };
        Ok((next, receipt))
    }

    pub fn append_two(self, first_leaf: Digest, second_leaf: Digest)
        -> Result<(Self, AppendTwoV1), PoolV1TreeError> {
        if POOL_V1_LEAF_CAPACITY.checked_sub(self.inner.next_leaf_index)
            .ok_or(PoolV1TreeError::IndexOutOfRange)? < 2 {
            return Err(PoolV1TreeError::InsufficientCapacity);
        }
        let (after_first, first) = self.append_one(first_leaf)?;
        let (after_second, second) = after_first.append_one(second_leaf)?;
        Ok((after_second, AppendTwoV1 { first, second }))
    }
}

fn parent_owned(left: Digest, right: Digest) -> Digest {
    pool_v1_tree_parent(&left,&right)
}

/// Generic owned carry, isolated from hashing and borrowed capabilities.
pub fn carry_owned_with<H>(mut frontier: [Digest;20], empty: [Digest;21],
    mut carry: Digest, index: u64, mut level: usize, mut parent: H)
    -> ([Digest;20],Digest,usize)
where H: FnMut(Digest,Digest) -> Digest {
    while level < 20 && (index >> level)&1 == 1 {
        carry=parent(frontier[level],carry);
        frontier[level]=empty[level];
        level+=1;
    }
    (frontier,carry,level)
}

pub fn carry_step_owned<H>(frontier_node: Digest, empty_node: Digest, carry: Digest,
    level: usize, mut parent: H) -> (Digest,Digest,usize)
where H: FnMut(Digest,Digest) -> Digest {
    (parent(frontier_node,carry),empty_node,level+1)
}

pub fn append_owned(tree: OwnedTree, leaf: Digest) -> Result<(OwnedTree,AppendOneV1),PoolV1TreeError> {
    tree.append_one(leaf)
}

#[cfg(kani)]
mod proofs {
    use super::*;
    static mut LEFT: Digest = [M31::ZERO;8];
    static mut RIGHT: Digest = [M31::ZERO;8];
    static mut ANSWER: Digest = [M31::ZERO;8];
    static mut CALLS: usize = 0;
    fn parent(left: &Digest,right: &Digest) -> Digest {
        unsafe {
            if CALLS==0 { LEFT=*left;RIGHT=*right;ANSWER=kani::any::<[u32;8]>().map(M31); }
            else {
                assert_eq!(CALLS,1);
                for j in 0..8 { assert_eq!(LEFT[j],left[j]);assert_eq!(RIGHT[j],right[j]); }
            }
            CALLS+=1;ANSWER
        }
    }
    #[kani::proof]
    #[kani::unwind(10)]
    #[kani::stub(super::super::pool_v1_tree_parent,parent)]
    fn owned_carry_projected_step() {
        let frontier_node=kani::any::<[u32;8]>().map(M31);
        let empty_node=kani::any::<[u32;8]>().map(M31);
        let mut carry=kani::any::<[u32;8]>().map(M31);
        let mut carry_level=kani::any::<usize>();kani::assume(carry_level<20);
        let before=carry;let level=carry_level;
        unsafe { CALLS=0; }
        // The source step after the two array reads are projected to values.
        // Array read/update and frame identities are checked in Lean.
        carry=pool_v1_tree_parent(&frontier_node,&carry);
        let cleared_node=empty_node;
        carry_level+=1;
        let (next,cleared,next_level)=carry_step_owned(frontier_node,empty_node,before,level,
            |l,r|pool_v1_tree_parent(&l,&r));
        for j in 0..8 { assert_eq!(carry[j],next[j]);assert_eq!(cleared_node[j],cleared[j]); }
        assert_eq!(carry_level,next_level);
        assert_eq!(unsafe { CALLS },2);
    }
}

/// Control-flow reference for the validator. Carry the first frontier error
/// through the loop condition; root checks retain their original order.
pub fn validate_owned(tree: IncrementalMerkleTreeV1,
    empty: [Digest; POOL_V1_TREE_DEPTH+1]) -> Result<(),PoolV1TreeError> {
    if tree.next_leaf_index > POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1TreeError::IndexOutOfRange);
    }
    let mut result = Ok(());
    let mut level = 0;
    while level < POOL_V1_TREE_DEPTH && result.is_ok() {
        if (tree.next_leaf_index >> level) & 1 == 0 && tree.frontier[level] != empty[level] {
            result = Err(PoolV1TreeError::NonCanonicalFrontier);
        }
        level += 1;
    }
    result?;
    if tree.next_leaf_index == 0 {
        return if tree.root == empty[POOL_V1_TREE_DEPTH] {
            Ok(())
        } else {
            Err(PoolV1TreeError::RootMismatch)
        };
    }
    if tree.next_leaf_index < POOL_V1_LEAF_CAPACITY
        && tree.reconstruct_nonfull_root(&empty)? != tree.root {
        return Err(PoolV1TreeError::RootMismatch);
    }
    Ok(())
}

#[cfg(kani)]
mod validator_proofs {
    use super::*;
    static mut ROOT_CALLS: u8 = 0;
    static mut ROOT_RESULT: Result<Digest, PoolV1TreeError> =
        Err(PoolV1TreeError::RootMismatch);
    static mut ROOT_TREE: IncrementalMerkleTreeV1 = IncrementalMerkleTreeV1 {
        next_leaf_index: 0, root: [M31::ZERO;8], frontier: [[M31::ZERO;8];20],
    };
    static mut ROOT_EMPTY: [Digest;21] = [[M31::ZERO;8];21];
    fn shared_root(tree: &IncrementalMerkleTreeV1, empty: &[Digest;21])
        -> Result<Digest,PoolV1TreeError> {
        unsafe {
            if ROOT_CALLS == 0 {
                ROOT_TREE = *tree; ROOT_EMPTY = *empty;
                ROOT_RESULT = if kani::any() { Ok(kani::any::<[u32;8]>().map(M31)) }
                    else { Err(PoolV1TreeError::RootMismatch) };
            } else {
                assert_eq!(ROOT_CALLS,1);
                assert_eq!(ROOT_TREE.next_leaf_index,tree.next_leaf_index);
                for i in 0..8 { assert_eq!(ROOT_TREE.root[i].0,tree.root[i].0); }
                for l in 0..20 { for i in 0..8 {
                    assert_eq!(ROOT_TREE.frontier[l][i].0,tree.frontier[l][i].0);
                } }
                for l in 0..21 { for i in 0..8 { assert_eq!(ROOT_EMPTY[l][i].0,empty[l][i].0); } }
            }
            ROOT_CALLS += 1; ROOT_RESULT
        }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(IncrementalMerkleTreeV1::reconstruct_nonfull_root,shared_root)]
    fn tree_validate_control_flow() {
        let tree = IncrementalMerkleTreeV1 {
            next_leaf_index: kani::any(),
            root: kani::any::<[u32;8]>().map(M31),
            frontier: kani::any::<[[u32;8];20]>().map(|d|d.map(M31)),
        };
        let empty = kani::any::<[[u32;8];21]>().map(|d|d.map(M31));
        let actual = tree.validate_with_empty_roots(&empty);
        let calls = unsafe { ROOT_CALLS };
        let reference = validate_owned(tree,empty);
        assert_eq!(actual,reference);
        assert_eq!(unsafe { ROOT_CALLS },calls*2);
    }
}

#[cfg(kani)]
mod validator_projection {
    use super::*;
    // The two callers pass the same immutable tree and empty table, unchanged.
    // Project their common pure helper result; no helper implementation proof.
    static mut ANSWER: Result<Digest,PoolV1TreeError> = Err(PoolV1TreeError::RootMismatch);
    static mut CALLS: u8 = 0;
    fn root_projection(_: &IncrementalMerkleTreeV1, _: &[Digest;21])
        -> Result<Digest,PoolV1TreeError> {
        unsafe { CALLS += 1; ANSWER }
    }
    #[kani::proof]
    #[kani::unwind(34)]
    #[kani::stub(IncrementalMerkleTreeV1::reconstruct_nonfull_root,root_projection)]
    fn tree_validate_projected_root() {
        let tree = IncrementalMerkleTreeV1 {
            next_leaf_index: kani::any(), root: kani::any::<[u32;8]>().map(M31),
            frontier: kani::any::<[[u32;8];20]>().map(|d|d.map(M31)),
        };
        let empty = kani::any::<[[u32;8];21]>().map(|d|d.map(M31));
        unsafe { ANSWER=if kani::any() { Ok(kani::any::<[u32;8]>().map(M31)) }
            else { Err(PoolV1TreeError::RootMismatch) }; }
        let actual=tree.validate_with_empty_roots(&empty);
        let calls=unsafe { CALLS };
        let reference=validate_owned(tree,empty);
        assert_eq!(actual,reference);
        assert_eq!(unsafe { CALLS },calls*2);
    }
}
