use crate::field::{QM31 as K, WideExact as E};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error { Parse, Semantic, Transcript, Relation, Merkle, Query, Checkpoint, Allocation }

fn echeck(b:&[u8],k:bool)->Result<(),Error> {
    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}
    Ok(())
}

pub fn echeck_round1(b: &[u8]) -> Result<(), Error> { echeck(b, false) }
