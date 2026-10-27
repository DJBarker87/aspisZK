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
        let mut input=Vec::with_capacity(parts.len());
        let mut address=Vec::new();
        for part in parts {input.push(part.to_vec());address.extend_from_slice(part);}
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
        if word.iter().any(|b|*b!=0) {return Err(Error::Parse)}
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
    assert_eq!(original.borrow()[0].returned,Some(Ok(answer)));
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

// A coordinate observation is used only for splitting the recorder-copy loops.
// Universal equality of these projections reconstructs complete ordered logs;
// it is NOT itself a whole-batch/physical correspondence certificate.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Coordinate {
    calls:usize,
    part_lengths:[usize;3],
    byte:Option<u8>,
    returned:Option<[u8;32]>,
}
#[derive(Clone,Copy)]
struct At<'a> {
    state:&'a RefCell<Coordinate>, selected_call:usize,
    selected_part:usize, selected_byte:usize, answer:[u8;32],
}
impl Digest32 for At<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let mut s=self.state.borrow_mut();
        if s.calls==self.selected_call {
            assert_eq!(parts.len(),3);
            s.part_lengths=[parts[0].len(),parts[1].len(),parts[2].len()];
            s.byte=parts.get(self.selected_part).and_then(|p|p.get(self.selected_byte)).copied();
            s.returned=Some(self.answer);
        }
        s.calls+=1;
        self.answer
    }
}
fn zero()->Coordinate {Coordinate {calls:0,part_lengths:[0;3],byte:None,returned:None}}
fn check_leaf_coordinate(tree:usize) {
    let q:[u8;832]=kani::any(); let answer:[u8;32]=kani::any();
    let part:usize=kani::any(); let byte:usize=kani::any(); let selected:usize=kani::any();
    let a=RefCell::new(zero()); let b=RefCell::new(zero());
    let original=shipped::batch_leaf(At {state:&a,selected_call:selected,selected_part:part,selected_byte:byte,answer},tree,&q);
    let reference=leaf(At {state:&b,selected_call:selected,selected_part:part,selected_byte:byte,answer},tree,&q);
    assert_eq!(original,reference); assert_eq!(*a.borrow(),*b.borrow());
    assert_eq!(a.borrow().calls,1);
    if selected==0 && part==1 && byte==0 {assert!(a.borrow().byte.is_some());}
}
#[kani::proof] #[kani::unwind(65)] fn leaf_c1_coordinate(){check_leaf_coordinate(0)}
#[kani::proof] #[kani::unwind(65)] fn leaf_c2_coordinate(){check_leaf_coordinate(1)}
#[kani::proof] #[kani::unwind(65)] fn leaf_folded_coordinate(){check_leaf_coordinate(2)}

fn leaf_step<H:Digest32>(keys:[u64;16],position:usize,lo:usize,tree:usize,q:&[u8],idx:&mut [u32;16],val:&mut [[u8;32];16],used:usize,hash:H)->(bool,usize,usize,usize) {
    let key=keys[position]; let index=(key>>8) as u32;
    let selected=lo+(key&255) as usize;
    let digest=leaf(hash,tree,q);
    if used>0 && idx[used-1]==index {
        (val[used-1]==digest,position+1,selected,used)
    } else {
        idx[used]=index;val[used]=digest;
        (true,position+1,selected,used+1)
    }
}
fn check_leaf_step(tree:usize) {
    let keys:[u64;16]=kani::any(); let position:usize=kani::any();
    kani::assume(position<12);
    let lo:usize=kani::any(); kani::assume(lo==0 || lo==10);
    let used:usize=kani::any(); kani::assume(used<=position);
    let mut idx_a:[u32;16]=kani::any(); let mut val_a:[[u8;32];16]=kani::any();
    let mut idx_b=idx_a;let mut val_b=val_a;
    let q:[u8;832]=kani::any();let answer:[u8;32]=kani::any();
    let part:usize=kani::any();let byte:usize=kani::any();let selected:usize=kani::any();
    let a=RefCell::new(zero());let b=RefCell::new(zero());
    let ra=shipped::leaf_step(keys,position,lo,tree,&q,&mut idx_a,&mut val_a,used,At{state:&a,selected_call:selected,selected_part:part,selected_byte:byte,answer});
    let rb=leaf_step(keys,position,lo,tree,&q,&mut idx_b,&mut val_b,used,At{state:&b,selected_call:selected,selected_part:part,selected_byte:byte,answer});
    let si:usize=kani::any();let sb:usize=kani::any();kani::assume(si<16 && sb<32);
    assert_eq!(ra,rb);assert_eq!(idx_a[si],idx_b[si]);assert_eq!(val_a[si][sb],val_b[si][sb]);
    assert_eq!(*a.borrow(),*b.borrow());assert_eq!(a.borrow().calls,1);
}
#[kani::proof] #[kani::unwind(65)] fn leaf_step_c1(){check_leaf_step(0)}
#[kani::proof] #[kani::unwind(65)] fn leaf_step_c2(){check_leaf_step(1)}
#[kani::proof] #[kani::unwind(65)] fn leaf_step_folded(){check_leaf_step(2)}

#[derive(Clone,Copy)]
struct Tape<'a> {answers:&'a [u8;21888],cursor:&'a std::cell::Cell<usize>}
impl Digest32 for Tape<'_> {
    fn digest(&self,_:&[&[u8]])->[u8;32] {
        let index=self.cursor.get();
        assert!(index<684); self.cursor.set(index+1); self.answers[index*32..(index+1)*32].try_into().unwrap()
    }
}
// This is the whole-body target with an arbitrary chronological reply tape.
// 684 = 3*(12 +18*12), before using the sharper accepted P6 bound.
#[kani::proof] #[kani::unwind(835)]
fn whole_batch_tape() {
    let proof:[u8;57607]=kani::any(); let queries:[u32;22]=kani::any();
    let roots:[[u8;32];3]=kani::any(); let ordinal:usize=kani::any();kani::assume(ordinal<2);
    let answers:[u8;21888]=kani::any();
    let ca=std::cell::Cell::new(0);let cb=std::cell::Cell::new(0);
    let original=RefCell::new(Vec::new());let reference=RefCell::new(Vec::new());
    let ra=shipped::batch_merkle_values(&proof,queries,roots,ordinal,Recording{backend:Tape{answers:&answers,cursor:&ca},log:&original});
    let rb=batch(&proof,queries,roots,ordinal,Recording{backend:Tape{answers:&answers,cursor:&cb},log:&reference});
    assert_eq!(ra,rb);assert_eq!(ca.get(),cb.get());assert_eq!(*original.borrow(),*reference.borrow());
}

// Padding loop split: one exact8-byte source predicate. The reference scans
// bytes, so this cut proves the per-word replacement without unrolling688words.
#[kani::proof] #[kani::unwind(9)]
fn padding_word() {
    let word:[u8;8]=kani::any();
    let shipped=u64::from_le_bytes(word)!=0;
    let reference=word.iter().any(|b|*b!=0);
    assert_eq!(shipped,reference);
}

#[derive(Clone,Copy)]
struct Point<'a,H:Digest32> {
    state:&'a RefCell<Coordinate>, backend:H, selected_call:usize,
    selected_part:usize,selected_byte:usize,
}
impl<H:Digest32> Digest32 for Point<'_,H> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let selected;
        {
            let mut s=self.state.borrow_mut();
            selected=s.calls==self.selected_call;
            if selected {
                assert_eq!(parts.len(),3);
                s.part_lengths=[parts[0].len(),parts[1].len(),parts[2].len()];
                s.byte=parts.get(self.selected_part).and_then(|p|p.get(self.selected_byte)).copied();
            }
            s.calls+=1;
        }
        let answer=self.backend.digest(parts);
        if selected {self.state.borrow_mut().returned=Some(answer);}
        answer
    }
}
#[kani::proof] #[kani::unwind(33)]
fn whole_batch_tape_coordinate() {
    let proof:[u8;57607]=kani::any();let queries:[u32;22]=kani::any();
    let roots:[[u8;32];3]=kani::any();let ordinal:usize=kani::any();kani::assume(ordinal<2);
    let answers:[u8;21888]=kani::any();
    let part:usize=kani::any();let byte:usize=kani::any();let selected:usize=kani::any();
    let ca=std::cell::Cell::new(0);let cb=std::cell::Cell::new(0);
    let a=RefCell::new(zero());let b=RefCell::new(zero());
    let ra=shipped::batch_merkle_values(&proof,queries,roots,ordinal,Point{state:&a,backend:Tape{answers:&answers,cursor:&ca},selected_call:selected,selected_part:part,selected_byte:byte});
    let rb=batch(&proof,queries,roots,ordinal,Point{state:&b,backend:Tape{answers:&answers,cursor:&cb},selected_call:selected,selected_part:part,selected_byte:byte});
    assert_eq!(ra,rb);assert_eq!(ca.get(),cb.get());assert_eq!(*a.borrow(),*b.borrow());
}

fn leaf_loop<H:Digest32>(proof:&[u8],keys:[u64;16],lo:usize,n:usize,tree:usize,idx:&mut [u32;16],val:&mut [[u8;32];16],hash:H)->(Result<(),Error>,usize) {
    let mut used=0;
    for position in 0..n {
        let key=keys[position];let index=(key>>8) as u32;
        let selected=lo+(key&255) as usize;
        let at=compact::OFF_OPENINGS+selected*compact::OPENING;
        let digest=leaf(hash,tree,&proof[at..at+compact::OPENING]);
        if used>0 && idx[used-1]==index {
            if val[used-1]!=digest {return (Err(Error::Merkle),used)}
        } else {idx[used]=index;val[used]=digest;used+=1;}
    }
    (Ok(()),used)
}
fn check_leaf_loop(tree:usize) {
    let ordinal:usize=kani::any();kani::assume(ordinal<2);
    let (lo,n)=if ordinal==0 {(0,10)} else {(10,12)};
    let keys:[u64;16]=kani::any();
    for j in 0..n {kani::assume((keys[j]&255) < n as u64);}
    let proof:[u8;57607]=kani::any();let answers:[u8;21888]=kani::any();
    let mut ia:[u32;16]=kani::any();let mut va:[[u8;32];16]=kani::any();
    let mut ib=ia;let mut vb=va;
    let pa=RefCell::new(zero());let pb=RefCell::new(zero());
    let ca=std::cell::Cell::new(0);let cb=std::cell::Cell::new(0);
    let selected:usize=kani::any();let part:usize=kani::any();let byte:usize=kani::any();
    let a=shipped::leaf_loop(&proof,keys,lo,n,tree,&mut ia,&mut va,Point{state:&pa,backend:Tape{answers:&answers,cursor:&ca},selected_call:selected,selected_part:part,selected_byte:byte});
    let b=leaf_loop(&proof,keys,lo,n,tree,&mut ib,&mut vb,Point{state:&pb,backend:Tape{answers:&answers,cursor:&cb},selected_call:selected,selected_part:part,selected_byte:byte});
    let si:usize=kani::any();let sb:usize=kani::any();kani::assume(si<16 && sb<32);
    assert_eq!(a,b);assert_eq!(ia[si],ib[si]);assert_eq!(va[si][sb],vb[si][sb]);
    assert_eq!(*pa.borrow(),*pb.borrow());assert_eq!(ca.get(),cb.get());
}
#[kani::proof] #[kani::unwind(33)] fn leaf_loop_c1(){check_leaf_loop(0)}
#[kani::proof] #[kani::unwind(33)] fn leaf_loop_c2(){check_leaf_loop(1)}
#[kani::proof] #[kani::unwind(33)] fn leaf_loop_folded(){check_leaf_loop(2)}

// Split the explicit recorder's full equality comparison at a universally
// selected byte. This tests the actual owned Vec log, rather than assigning it.
#[kani::proof] #[kani::unwind(65)]
fn recorder_projection() {
    let q:[u8;832]=kani::any();let answer:[u8;32]=kani::any();
    let tree:usize=kani::any();kani::assume(tree<3);
    let part:usize=kani::any();let byte:usize=kani::any();
    let log=RefCell::new(Vec::new());let point=RefCell::new(zero());
    let a=shipped::batch_leaf(Recording{backend:Reply(answer),log:&log},tree,&q);
    let b=shipped::batch_leaf(Point{state:&point,backend:Reply(answer),selected_call:0,selected_part:part,selected_byte:byte},tree,&q);
    assert_eq!(a,b);assert_eq!(log.borrow().len(),1);
    let full=log.borrow();let event=&full[0];let projected=point.borrow();
    assert_eq!(projected.calls,1);assert_eq!(event.input.len(),3);
    for p in 0..3 {assert_eq!(event.input[p].len(),projected.part_lengths[p]);}
    assert_eq!(event.input.get(part).and_then(|p|p.get(byte)).copied(),projected.byte);
    assert_eq!(event.returned,projected.returned.map(Ok));
    let flat:usize=kani::any();
    // Derive concatenation coordinate by the actual recorded part boundaries.
    let address=if flat<event.input[0].len() {event.input[0].get(flat).copied()}
      else if flat<event.input[0].len()+event.input[1].len() {event.input[1].get(flat-event.input[0].len()).copied()}
      else {event.input[2].get(flat-event.input[0].len()-event.input[1].len()).copied()};
    assert_eq!(event.address.get(flat).copied(),address);
}
