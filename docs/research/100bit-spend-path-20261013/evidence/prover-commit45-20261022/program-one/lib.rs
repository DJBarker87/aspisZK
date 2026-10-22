extern crate alloc;
use alloc::{vec::Vec,collections::BTreeMap};
use core::cell::RefCell;
pub trait Digest32 { fn digest(&self,parts:&[&[u8]])->[u8;32]; }
pub type Table = BTreeMap<Vec<u8>,[u8;32]>;
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


pub fn program(table:&RefCell<(Table,bool)>,answer:[u8;32],parts:&[&[u8]])->[u8;32] { ProgramOne{table,answer}.digest(parts) }
