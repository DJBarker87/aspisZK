extern crate alloc;
use alloc::vec::Vec;
use alloc::collections::BTreeMap;
pub const LEAF_BITS: u32 = 18;
/// New domain separator for binary parent nodes (leaves use 0x10, eight-way
/// parents 0x18). UNPROVED: its disjointness is one of the obligations.
pub const BINARY_NODE_TAG: u8 = 0x12;
/// Largest index set one multiproof call accepts (one transaction batch).
pub const MAX_BATCH: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arity {
    Two,
    Eight,
}
impl Arity {
    #[inline(always)]
    pub const fn bits(self) -> u32 {
        match self {
            Self::Two => 1,
            Self::Eight => 3,
        }
    }
    #[inline(always)]
    pub const fn width(self) -> usize {
        1 << self.bits()
    }
    #[inline(always)]
    pub const fn levels(self) -> u32 {
        LEAF_BITS / self.bits()
    }
}

/// Strictly increasing and inside the leaf domain.
fn well_formed(indices: &[u32]) -> bool {
    !indices.is_empty()
        && indices.len() <= MAX_BATCH
        && indices.windows(2).all(|w| w[0] < w[1])
        && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}

#[inline(always)]
fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
    indices[index]
}

/// Number of supplied sibling nodes for a strictly increasing index set:
/// at each level, (width x distinct parents) - occupied nodes.
pub fn node_count(arity: Arity, indices: &[u32]) -> Option<usize> {
    if !well_formed(indices) {
        return None;
    }
    let mut level = [0u32; MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n = indices.len();
    let mut count = 0;
    for _ in 0..arity.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }
            count += arity.width() - (j - i);
            level[w] = parent;
            w += 1;
            i = j;
        }
        n = w;
    }
    Some(count)
}

/// Prover side: emit the canonical node sequence. `node(level, index)` returns
/// the stored digest of node `index` at `level` (0 = leaves).
pub fn generate(
    arity: Arity,
    indices: &[u32],
    mut node: impl FnMut(u32, u32) -> [u8; 32],
) -> Option<Vec<u8>> {
    let count = node_count(arity, indices)?;
    let mut out = Vec::with_capacity(32 * count);
    let mut level: Vec<u32> = indices.to_vec();
    for depth in 0..arity.levels() {
        let mut next = Vec::new();
        let mut i = 0;
        while i < level.len() {
            let parent = level[i] >> arity.bits();
            for slot in 0..arity.width() as u32 {
                let child = (parent << arity.bits()) | slot;
                if i < level.len() && level[i] == child {
                    i += 1;
                } else {
                    out.extend_from_slice(&node(depth, child));
                }
            }
            next.push(parent);
        }
        level = next;
    }
    (out.len() == 32 * count).then_some(out)
}


#[derive(Debug)]
pub enum Error { Merkle }
struct ProgrammedTree { children: Vec<BTreeMap<usize, [[u8;32];2]>> }
impl ProgrammedTree {
    fn multiproof(&self, indices:&[u32])->Result<Vec<u8>,Error> {
        generate(Arity::Two,indices,|depth,index| {
            self.children[depth as usize][&(index as usize/2)][index as usize%2]
        }).ok_or(Error::Merkle)
    }
}


pub fn publish(children:Vec<BTreeMap<usize,[[u8;32];2]>>,indices:&[u32])->Result<Vec<u8>,Error> { ProgrammedTree{children}.multiproof(indices) }
