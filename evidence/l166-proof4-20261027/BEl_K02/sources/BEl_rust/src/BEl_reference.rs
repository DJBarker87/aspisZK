//! Owned safe reference and explicit attempted-call recorder. No stubs.
use super::*;
use std::cell::RefCell;
use shipped::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Attempt {
    // Oracle address is the concatenated input; part boundaries also retained.
    address: Vec<u8>,
    input: Vec<Vec<u8>>,
    // None records an attempt whose backend has not returned.
    returned: Option<Result<[u8;32], ()>>,
}
#[derive(Clone,Copy)]
struct Recording<'a,H:Digest32> { backend:H, log:&'a RefCell<Vec<Attempt>> }
impl<H:Digest32> Digest32 for Recording<'_,H> {
    fn digest(&self, parts:&[&[u8]])->[u8;32] {
        let position=self.log.borrow().len();
        let input:Vec<Vec<u8>>=parts.iter().map(|p|p.to_vec()).collect();
        let address=parts.iter().flat_map(|p|p.iter().copied()).collect();
        self.log.borrow_mut().push(Attempt {address,input,returned:None});
        let answer=self.backend.digest(parts);
        self.log.borrow_mut()[position].returned=Some(Ok(answer));
        answer
    }
}
#[derive(Clone,Copy)]
struct Reply([u8;32]);
impl Digest32 for Reply {
    fn digest(&self,_:&[&[u8]])->[u8;32] { self.0 }
}

fn leaf<H:Digest32>(hash:H,tree:usize,q:&[u8])->[u8;32] {
    let (tag,start,end,salt)=match tree {
        0=>(0x71,0,480,608),
        1=>(0xf1,480,608,640),
        _=>(0x72,672,800,800),
    };
    hash.digest(&[&[0x10,tag],&q[start..end],&q[salt..salt+32]])
}

fn tree<H:Digest32>(proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,
    tree:usize,idx:&mut [u32;16],val:&mut [[u8;32];16],hash:H)->Result<(),Error> {
    let lo=if batch==0 {0} else {compact::SPLIT};
    let n=if batch==0 {compact::SPLIT} else {22-compact::SPLIT};
    let slot=3*batch+tree;
    let keys=shipped::sort_batch_keys(shipped::batch_keys(&queries,lo,n,tree),n);
    let mut used=0;
    for position in 0..n {
        let key=keys[position];
        let index=(key>>8) as u32;
        let selected=lo+(key&255) as usize;
        let at=compact::OFF_OPENINGS+selected*compact::OPENING;
        let digest=leaf(hash,tree,&proof[at..at+compact::OPENING]);
        if used>0 && idx[used-1]==index {
            if val[used-1]!=digest { return Err(Error::Merkle) }
        } else {
            idx[used]=index; val[used]=digest; used+=1;
        }
    }
    let count=multiproof::node_count(multiproof::Arity::Two,&idx[..used]).ok_or(Error::Merkle)?;
    let nodes=&proof[compact::slot_offset(slot)..compact::slot_offset(slot+1)];
    if count>compact::SLOT_NODES[slot] {return Err(Error::Parse)}
    for word in nodes[32*count..].chunks_exact(8) {
        if u64::from_le_bytes(word.try_into().unwrap())!=0 {return Err(Error::Parse)}
    }
    if multiproof::verify_in_place(hash,multiproof::Arity::Two,&root,idx,val,used,&nodes[..32*count]) {
        Ok(())
    } else {Err(Error::Merkle)}
}
fn batch<H:Digest32>(proof:&[u8],queries:[u32;22],roots:[[u8;32];3],ordinal:usize,hash:H)->Result<(),Error> {
    let mut idx=[0u32;16]; let mut val=[[0u8;32];16];
    for slot in 0..3 {tree(proof,queries,roots[slot],ordinal,slot,&mut idx,&mut val,hash)?;}
    Ok(())
}

fn check_leaf(tree:usize) {
    let q:[u8;832]=kani::any(); let answer:[u8;32]=kani::any();
    let original=RefCell::new(Vec::new()); let reference=RefCell::new(Vec::new());
    let a=shipped::batch_leaf(Recording {backend:Reply(answer),log:&original},tree,&q);
    let b=leaf(Recording {backend:Reply(answer),log:&reference},tree,&q);
    assert_eq!(a,b); assert_eq!(*original.borrow(),*reference.borrow());
    assert_eq!(original.borrow().len(),1);
    kani::cover!(original.borrow()[0].returned==Some(Ok(answer)));
}
#[kani::proof] #[kani::unwind(835)] fn leaf_c1(){check_leaf(0)}
#[kani::proof] #[kani::unwind(835)] fn leaf_c2(){check_leaf(1)}
#[kani::proof] #[kani::unwind(835)] fn leaf_folded(){check_leaf(2)}

#[kani::proof] #[kani::unwind(835)]
fn whole_batch() {
    let proof:[u8;57607]=kani::any();
    let queries:[u32;22]=kani::any(); let roots:[[u8;32];3]=kani::any();
    let ordinal:usize=kani::any(); kani::assume(ordinal<2);
    let answer:[u8;32]=kani::any();
    let original=RefCell::new(Vec::new()); let reference=RefCell::new(Vec::new());
    let a=shipped::batch_merkle_values(&proof,queries,roots,ordinal,Recording {backend:Reply(answer),log:&original});
    let b=batch(&proof,queries,roots,ordinal,Recording {backend:Reply(answer),log:&reference});
    assert_eq!(a,b); assert_eq!(*original.borrow(),*reference.borrow());
}
