//! Exact error carriers and Slice D prefix projections; no whole verifier model.
#[derive(Clone,Copy)]
pub enum WireError{Allocation,RowOrder{expected:u8,actual:u8},InvalidRow,Tag{row:u8},Length{row:u8},NonCanonical{row:u8,value:usize},Boundary{round:usize},Terminal,EqualCirclePoints,TrailingBytes,Public}
#[derive(Clone,Copy)]
pub enum VerifierError{Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation}
pub fn prefix_error_ref(e:WireError)->Result<(),WireError>{Err(e)}
pub fn semantic_error_ref(_:WireError)->VerifierError{VerifierError::Semantic}
pub fn split_error_ref(k:usize)->Option<VerifierError>{if k==10{None}else{Some(VerifierError::Parse)}}
pub fn resume_error_ref()->VerifierError{VerifierError::Checkpoint}
