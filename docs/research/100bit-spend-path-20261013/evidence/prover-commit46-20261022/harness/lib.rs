//! Native RefCell body verbatim; BTreeMap is the D133 per-key insert contract.
//! Arbitrary previous value and untouched frame; no B-tree internals asserted.
mod owned;
use std::cell::RefCell;
trait Digest32 {fn digest(&self,parts:&[&[u8]])->[u8;32];}
#[derive(Clone,Debug,PartialEq)]
struct Table { previous:Option<[u8;32]>, written:Option<(Vec<u8>,[u8;32])>, frame:[u8;32] }
impl Table {
 fn insert(&mut self,key:Vec<u8>,answer:[u8;32])->Option<[u8;32]> {
  let old=self.previous; self.previous=Some(answer); self.written=Some((key,answer)); old
 }
}
impl owned::Recording for Table {
 fn insert(mut self,parts:&[&[u8]],answer:[u8;32])->(Option<[u8;32]>,Self) {
  let old=self.previous; self.previous=Some(answer); self.written=Some((concat(parts),answer)); (old,self)
 }
}
fn concat(parts:&[&[u8]])->Vec<u8> {
    let mut a=Vec::with_capacity(parts.iter().map(|p|p.len()).sum());
    for p in parts {a.extend_from_slice(p);}
    a
}

/// Programs exactly one read: records (address, answer) and returns answer.
#[derive(Clone,Copy)]
struct ProgramOne<'a>{ table:&'a RefCell<(Table,bool)>, answer:[u8;32] }
impl Digest32 for ProgramOne<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let mut t=self.table.borrow_mut();
        if let Some(prev)=t.0.insert(concat(parts),self.answer) { if prev!=self.answer {t.1=true;} }
        self.answer
    }
}


#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(36)]
 fn program_one_transition() {
  let previous:Option<[u8;32]>=kani::any();
  let answer:[u8;32]=kani::any(); let collision:bool=kani::any();
  let frame:[u8;32]=kani::any();let address:[u8;1]=kani::any();let parts:[&[u8];1]=[&address];
  let table=Table{previous,written:None,frame};
  let heap=RefCell::new((table.clone(),collision));
  let actual=ProgramOne{table:&heap,answer}.digest(&parts);
  // A fresh mutable borrow after the call checks that the RefMut was released.
  {let _released=heap.borrow_mut();}
  let (expected,state)=owned::program(owned::ProgramState{table,collision},answer,&parts);
  let (result,flag)=heap.into_inner();
  assert_eq!(actual,expected);assert_eq!(result,state.table);assert_eq!(flag,state.collision);
 }
}
