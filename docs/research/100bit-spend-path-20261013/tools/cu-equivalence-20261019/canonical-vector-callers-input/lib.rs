extern crate self as aspis_core;
pub mod field;pub mod old_pairing;pub mod new_pairing;
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }
pub fn claim_scalar(_:usize)->field::QM31{unreachable!()}
pub mod old_callers;pub mod new_callers;
