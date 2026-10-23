//! Owned host tree driver. Parent hashing is the unchanged framed leaf kernel.
use alloc::vec::Vec;
use aspis_core::Digest32;
use crate::multiproof::{binary_parent, LEAF_BITS, MAX_BATCH};

pub(crate) struct BinaryTree { levels:Vec<Vec<[u8;32]>> }
impl BinaryTree {
    pub(crate) fn new<H:Digest32>(hash:H,leaves:Vec<[u8;32]>)->Option<Self> {
        if leaves.len()!=1<<LEAF_BITS {return None;}
        let mut levels=Vec::with_capacity(LEAF_BITS as usize+1);
        levels.push(leaves);
        let levels=append_levels(hash,levels,0);
        Some(Self{levels})
    }
    pub(crate) fn root(&self)->[u8;32] {self.levels[LEAF_BITS as usize][0]}
    pub(crate) fn multiproof(&self,indices:&[u32])->Option<Vec<u8>> {
        let count=node_count(indices)?;
        let mut out=Vec::with_capacity(32*count);
        let mut level=indices.to_vec();
        let mut depth=0;
        while depth<LEAF_BITS as usize {
            let mut next=Vec::new();
            let mut i=0;
            while i<level.len() {
                let parent=level[i]>>1;
                let mut slot=0;
                while slot<2 {
                    let child=(parent<<1)|slot;
                    if i<level.len() && level[i]==child {i+=1;}
                    else {out.extend_from_slice(&self.levels[depth][child as usize]);}
                    slot+=1;
                }
                next.push(parent);
            }
            level=next;
            depth+=1;
        }
        if out.len()==32*count {Some(out)} else {None}
    }
}
fn next_level<H:Digest32>(hash:H,previous:&[[u8;32]])->Vec<[u8;32]> {
    let n=previous.len()/2;
    let mut next=Vec::with_capacity(n);
    let mut i=0;
    while i<n {let parent=binary_parent(hash,&previous[2*i],&previous[2*i+1]);next.push(parent);i+=1;}
    next
}
fn append_levels<H:Digest32>(hash:H,mut levels:Vec<Vec<[u8;32]>>,depth:usize)->Vec<Vec<[u8;32]>> {
    if depth==LEAF_BITS as usize {return levels;}
    let next=next_level(hash,&levels[depth]);
    levels.push(next);
    append_levels(hash,levels,depth+1)
}

fn node_count(indices:&[u32])->Option<usize> {
    if indices.is_empty() || indices.len()>MAX_BATCH {return None;}
    let mut i=0;
    while i<indices.len() {
        if indices[i]>=1<<LEAF_BITS || (i>0 && indices[i-1]>=indices[i]) {return None;}
        i+=1;
    }
    let mut level=[0u32;MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n=indices.len();
    let mut count=0;
    let mut depth=0;
    while depth<LEAF_BITS {
        let mut w=0;
        i=0;
        while i<n {
            let parent=level[i]>>1;
            let mut j=i;
            while j<n && level[j]>>1==parent {j+=1;}
            count+=2-(j-i);
            level[w]=parent;
            w+=1;
            i=j;
        }
        n=w;
        depth+=1;
    }
    Some(count)
}
