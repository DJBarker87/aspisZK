#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation }