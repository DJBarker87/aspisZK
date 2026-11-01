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
        let bits=LEAF_BITS as usize;

        let count=node_count(indices)?;
        let out=Vec::with_capacity(32*count);
        let level=indices.to_vec();
        let out=multiproof_levels(self,out,level,0,bits);
        if out.len()==32*count {Some(out)} else {None}
    }
}
fn multiproof_levels(tree:&BinaryTree,out:Vec<u8>,level:Vec<u32>,depth:usize,bits:usize)->Vec<u8> {
    if depth==bits {return out;}
    let (out,next)=multiproof_level(&tree.levels[depth],&level,out);
    drop(level);
    multiproof_levels(tree,out,next,depth+1,bits)
}
fn multiproof_level(nodes:&[[u8;32]],level:&[u32],mut out:Vec<u8>)->(Vec<u8>,Vec<u32>) {
    let mut next=Vec::new();let count=level.len();let mut i=0;
    while i<count {
        let parent=level[i]>>1;
        (out,i)=multiproof_child(nodes,level,out,i,parent<<1);
        (out,i)=multiproof_child(nodes,level,out,i,(parent<<1)|1);
        next.push(parent);
    }
    (out,next)
}
fn multiproof_child(nodes:&[[u8;32]],level:&[u32],mut out:Vec<u8>,i:usize,child:u32)->(Vec<u8>,usize) {
    if i<level.len() && level[i]==child {(out,i+1)}
    else {out.extend_from_slice(&nodes[child as usize]);(out,i)}
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

fn check_indices(indices:&[u32])->Option<()> {
    if indices.is_empty() || indices.len()>MAX_BATCH {return None;}
    let mut i=0;
    while i<indices.len() {
        if indices[i]>=1<<LEAF_BITS || (i>0 && indices[i-1]>=indices[i]) {return None;}
        i+=1;
    }
    Some(())
}

fn node_count(indices:&[u32])->Option<usize> {
    check_indices(indices)?;
    let mut level=[0u32;MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    Some(count_levels(level,indices.len(),0,0,LEAF_BITS))
}
fn count_levels(level:[u32;MAX_BATCH],n:usize,depth:u32,count:usize,bits:u32)->usize {
    if depth==bits {return count;}
    let (level,n,missing)=count_level(level,n);
    count_levels(level,n,depth+1,count+missing,bits)
}
fn count_level(mut level:[u32;MAX_BATCH],n:usize)->([u32;MAX_BATCH],usize,usize) {
    let mut i=0;let mut w=0;let mut missing=0;
    while i<n {
        let (parent,take)=count_parent(&level,i,n);
        level[w]=parent;w+=1;i+=take;missing+=2-take;
    }
    (level,w,missing)
}
fn count_parent(level:&[u32;MAX_BATCH],i:usize,n:usize)->(u32,usize) {
    let parent=level[i]>>1;
    let take=if i+1<n && level[i+1]>>1==parent {2} else {1};
    (parent,take)
}
