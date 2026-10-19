//! Eight-way SHA-256 authentication, R101/R102 -> R549/R552 lineage.
//!
//! Reuses the child-major 0x18 node grammar and bottom-up source-order
//! sibling traversal from tools/r101_merkle.rs and tools/r102_tree.rs in
//! docs/research/v8-full-view-zk-20260912. R0 P1 widens their truncated
//! 26-byte digest to the full 32 bytes. Leaves reuse the 0x10 || tree_tag
//! grammar (R552 leafInput), with canonical fixed-width bytes and no salt.
//! The old 26-byte Lean theorem is NOT a refinement proof of this adapter.
use super::{domain::FibreIndex, Error, FIBRE_COUNT};
use crate::HashFn;
use alloc::vec::Vec;

pub type Digest = [u8; 32];
pub type Path = [[Digest; 7]; 6];
pub const C1_TAG: u8 = 0x71;
pub const C2_TAG: u8 = 0xf1;
pub fn leaf(hash: HashFn, tag: u8, values: &[u8]) -> Digest {
    hash(&[&[0x10, tag], values])
}
pub fn parent(hash: HashFn, children: &[Digest; 8]) -> Digest {
    hash(&[
        &[0x18],
        &children[0],
        &children[1],
        &children[2],
        &children[3],
        &children[4],
        &children[5],
        &children[6],
        &children[7],
    ])
}
pub(crate) fn filled<T: Clone>(n: usize, value: T) -> Result<Vec<T>, Error> {
    let mut v = Vec::new();
    v.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
    v.resize(n, value);
    Ok(v)
}
/// Complete six-level tree, exactly 8^6 fibres. Retained for opening paths.
pub struct Tree {
    levels: Vec<Vec<Digest>>,
}
impl Tree {
    pub fn new(hash: HashFn, leaves: Vec<Digest>) -> Result<Self, Error> {
        if leaves.len() != FIBRE_COUNT {
            return Err(Error::WrongLength);
        }
        let mut levels = Vec::new();
        levels.try_reserve_exact(7).map_err(|_| Error::Allocation)?;
        levels.push(leaves);
        for depth in 0..6 {
            let mut next = filled(levels[depth].len() / 8, [0; 32])?;
            for (dst, chunk) in next.iter_mut().zip(levels[depth].chunks_exact(8)) {
                let children = core::array::from_fn(|s| chunk[s]);
                *dst = parent(hash, &children);
            }
            levels.push(next);
        }
        Ok(Self { levels })
    }
    pub fn root(&self) -> Digest {
        self.levels[6][0]
    }
    /// At each level, seven siblings in ascending slot order, omitting u%8.
    pub fn path(&self, u: FibreIndex) -> Path {
        let mut index = u.get();
        core::array::from_fn(|depth| {
            let start = index / 8 * 8;
            let skip = index % 8;
            let row =
                core::array::from_fn(|j| self.levels[depth][start + j + usize::from(j >= skip)]);
            index /= 8;
            row
        })
    }
}
/// Single-query specialization of R101's paired frontier verifier, six
/// levels. Each fixed path consumes exactly 42 child-major digests.
pub fn verify_pair(
    hash: HashFn,
    roots: &[Digest; 2],
    u: FibreIndex,
    leaves: [Digest; 2],
    paths: &[Path; 2],
) -> bool {
    let mut current = leaves;
    let mut index = u.get();
    for depth in 0..6 {
        let slot = index % 8;
        for tree in 0..2 {
            let children = core::array::from_fn(|s| {
                if s == slot {
                    current[tree]
                } else {
                    paths[tree][depth][s - usize::from(s > slot)]
                }
            });
            current[tree] = parent(hash, &children);
        }
        index /= 8;
    }
    current == *roots && index == 0
}
