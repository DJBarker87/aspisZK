include!("BEm_owned.rs");

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
    drop(projected);drop(full);
    // Stop at the recorder cut; do not model destruction of the dead audit log.
    std::mem::forget(log);
}

// Observe the recorder at backend entry, before a reply exists. A backend
// may stop after this cut; this gate does not fabricate a Rust Err return.
#[derive(Clone,Copy)]
struct EntryProbe<'a> {
    log:&'a RefCell<Vec<Attempt>>, entered:&'a std::cell::Cell<bool>,
    part:usize,byte:usize,answer:[u8;32],
}
impl Digest32 for EntryProbe<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let log=self.log.borrow();assert_eq!(log.len(),1);
        let attempt=&log[0];assert_eq!(attempt.returned,None);
        assert_eq!(attempt.input.len(),parts.len());
        for p in 0..3 {assert_eq!(attempt.input[p].len(),parts[p].len());}
        assert_eq!(attempt.input.get(self.part).and_then(|p|p.get(self.byte)).copied(),parts.get(self.part).and_then(|p|p.get(self.byte)).copied());
        self.entered.set(true);self.answer
    }
}
#[kani::proof] #[kani::unwind(65)]
fn recorder_entry() {
    let q:[u8;832]=kani::any();let tree:usize=kani::any();kani::assume(tree<3);
    let answer:[u8;32]=kani::any();let part:usize=kani::any();let byte:usize=kani::any();
    let log=RefCell::new(Vec::new());let entered=std::cell::Cell::new(false);
    let out=shipped::batch_leaf(Recording{backend:EntryProbe{log:&log,entered:&entered,part,byte,answer},log:&log},tree,&q);
    assert!(entered.get());assert_eq!(out,answer);assert_eq!(log.borrow()[0].returned,Some(Ok(answer)));
    std::mem::forget(log);
}

#[kani::proof] #[kani::unwind(33)]
fn opening_geometry() {
    let proof:[u8;57607]=kani::any();let ordinal:usize=kani::any();kani::assume(ordinal<2);
    let (lo,n)=if ordinal==0 {(0,10)} else {(10,12)};
    let key:u64=kani::any();kani::assume((key&255)<n as u64);
    let original=shipped::opening(&proof,lo+(key&255) as usize);
    let at=compact::OFF_OPENINGS+(lo+(key&255) as usize)*compact::OPENING;
    let reference=&proof[at..at+compact::OPENING];
    assert_eq!(original.len(),832);assert_eq!(original.as_ptr(),reference.as_ptr());
    assert_eq!(original.len(),reference.len());
    // Both slices borrow the SAME allocation; byte equality follows from
    // equal offset/extent. Avoid enumerating a symbolic57607-byte array.
}

// New physical step gate: full owned logs, arbitrary stateful replies, original
// same-allocation opening and every live scratch coordinate. No helper stub.
#[derive(Clone,Copy)]
struct Stateful<'a> { replies:&'a [[u8;32];2], cursor:&'a std::cell::Cell<usize> }
impl Digest32 for Stateful<'_> {
    fn digest(&self,_:&[&[u8]])->[u8;32] {
        let i=self.cursor.get();self.cursor.set(i+1); self.replies[i%2]
    }
}
fn physical_step(tree:usize) {
    let keys:[u64;16]=kani::any();let position:usize=kani::any();kani::assume(position<12);
    let used:usize=kani::any();kani::assume(used<=position);
    let lo:usize=kani::any();kani::assume(lo==0 || lo==10);
    let q:[u8;832]=kani::any();let replies:[[u8;32];2]=kani::any();
    let initial:usize=kani::any();kani::assume(initial<1024);
    let ca=std::cell::Cell::new(initial);let cb=std::cell::Cell::new(initial);
    let mut ia:[u32;16]=kani::any();let mut va:[[u8;32];16]=kani::any();let mut ib=ia;let mut vb=va;
    let a=RefCell::new(Vec::new());let b=RefCell::new(Vec::new());
    let ra=shipped::leaf_step(keys,position,lo,tree,&q,&mut ia,&mut va,used,Recording{backend:Stateful{replies:&replies,cursor:&ca},log:&a});
    let rb=leaf_step(keys,position,lo,tree,&q,&mut ib,&mut vb,used,Recording{backend:Stateful{replies:&replies,cursor:&cb},log:&b});
    let si:usize=kani::any();let sb:usize=kani::any();kani::assume(si<16 && sb<32);
    assert_eq!(ra,rb);assert_eq!(ia[si],ib[si]);assert_eq!(va[si][sb],vb[si][sb]);assert_eq!(ca.get(),cb.get());
    assert_eq!(a.borrow().len(),1);assert_eq!(b.borrow().len(),1);
    let pa:usize=kani::any();let by:usize=kani::any();
    {
        let aa=a.borrow();let bb=b.borrow();
        assert_eq!(aa[0].input.len(),bb[0].input.len());
        assert_eq!(aa[0].input.get(pa).map(|x|x.len()),bb[0].input.get(pa).map(|x|x.len()));
        assert_eq!(aa[0].input.get(pa).and_then(|x|x.get(by)),bb[0].input.get(pa).and_then(|x|x.get(by)));
        assert_eq!(aa[0].address.len(),bb[0].address.len());
        assert_eq!(aa[0].address.get(by),bb[0].address.get(by));
        assert_eq!(aa[0].returned,bb[0].returned);
    }
    std::mem::forget(a);std::mem::forget(b);
}
#[kani::proof] #[kani::unwind(481)] fn physical_step_c1(){physical_step(0)}
#[kani::proof] #[kani::unwind(129)] fn physical_step_c2(){physical_step(1)}
#[kani::proof] #[kani::unwind(129)] fn physical_step_folded(){physical_step(2)}

fn physical_loop(tree:usize,ordinal:usize) {
    let (lo,n)=if ordinal==0 {(0,10)} else {(10,12)};
    let keys:[u64;16]=kani::any();for j in 0..n {kani::assume((keys[j]&255)<n as u64);}
    let proof:[u8;57607]=kani::any();let replies:[[u8;32];2]=kani::any();
    let initial:usize=kani::any();kani::assume(initial<1024);
    let ca=std::cell::Cell::new(initial);let cb=std::cell::Cell::new(initial);
    let mut ia:[u32;16]=kani::any();let mut va:[[u8;32];16]=kani::any();let mut ib=ia;let mut vb=va;
    let a=RefCell::new(zero());let b=RefCell::new(zero());
    let selected:usize=kani::any();let part:usize=kani::any();let byte:usize=kani::any();
    let ra=shipped::leaf_loop(&proof,keys,lo,n,tree,&mut ia,&mut va,Point{state:&a,backend:Stateful{replies:&replies,cursor:&ca},selected_call:selected,selected_part:part,selected_byte:byte});
    let rb=leaf_loop(&proof,keys,lo,n,tree,&mut ib,&mut vb,Point{state:&b,backend:Stateful{replies:&replies,cursor:&cb},selected_call:selected,selected_part:part,selected_byte:byte});
    let si:usize=kani::any();let sb:usize=kani::any();kani::assume(si<16 && sb<32);
    assert_eq!(ra,rb);assert_eq!(ia[si],ib[si]);assert_eq!(va[si][sb],vb[si][sb]);
    assert_eq!(ca.get(),cb.get());assert_eq!(*a.borrow(),*b.borrow());
}
#[kani::proof] #[kani::unwind(129)] fn physical_loop_c2_0(){physical_loop(1,0)}
#[kani::proof] #[kani::unwind(129)] fn physical_loop_c2_1(){physical_loop(1,1)}
#[kani::proof] #[kani::unwind(129)] fn physical_loop_folded_0(){physical_loop(2,0)}
#[kani::proof] #[kani::unwind(129)] fn physical_loop_folded_1(){physical_loop(2,1)}
#[kani::proof] #[kani::unwind(481)] fn physical_loop_c1_0(){physical_loop(0,0)}
#[kani::proof] #[kani::unwind(481)] fn physical_loop_c1_1(){physical_loop(0,1)}

#[kani::proof] #[kani::unwind(65)]
fn parent_owned_record() {
    let left:[u8;32]=kani::any();let right:[u8;32]=kani::any();let replies:[[u8;32];2]=kani::any();
    let initial:usize=kani::any();kani::assume(initial<1024);
    let ca=std::cell::Cell::new(initial);let cb=std::cell::Cell::new(initial);
    let log=RefCell::new(Vec::new());let point=RefCell::new(zero());
    let part:usize=kani::any();let byte:usize=kani::any();
    let a=multiproof::binary_parent(Recording{backend:Stateful{replies:&replies,cursor:&ca},log:&log},&left,&right);
    let b=multiproof::binary_parent(Point{state:&point,backend:Stateful{replies:&replies,cursor:&cb},selected_call:0,selected_part:part,selected_byte:byte},&left,&right);
    assert_eq!(a,b);assert_eq!(ca.get(),cb.get());assert_eq!(log.borrow().len(),1);
    {
        let l=log.borrow();let p=point.borrow();
        assert_eq!(p.calls,1);assert_eq!(l[0].input.len(),3);
        for j in 0..3 {assert_eq!(l[0].input[j].len(),p.part_lengths[j]);}
        assert_eq!(l[0].input.get(part).and_then(|p|p.get(byte)).copied(),p.byte);
        assert_eq!(l[0].returned,p.returned.map(Ok));
        assert_eq!(l[0].address.len(),65);
        let expected=if byte==0 {Some(0x12)} else if byte<=32 {left.get(byte-1).copied()} else {right.get(byte.wrapping_sub(33)).copied()};
        assert_eq!(l[0].address.get(byte).copied(),expected);
    }
    std::mem::forget(log);
}
