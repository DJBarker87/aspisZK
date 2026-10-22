//! Native source/API diagnostic. BTreeMap internals stay opaque (D145).
use std::collections::BTreeMap;
#[derive(Debug)] pub enum Error {Merkle}
pub fn root_guard(level:&BTreeMap<usize,[u8;32]>,root:[u8;32])->Result<(),Error> {
    if level.len()!=1||level.get(&0)!=Some(&root) {return Err(Error::Merkle);}
    Ok(())
}
