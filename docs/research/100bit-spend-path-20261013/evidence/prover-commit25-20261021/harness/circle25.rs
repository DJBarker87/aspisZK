#[cfg(any(kani,aeneas_ref))]
pub mod circle25 {
    use alloc::vec::Vec;
    use aspis_core::{Digest32,field::QM31};
    use super::{Error,SemanticTranscript,semantic20};
    pub trait Policy { fn point(block: [u8;32], second: bool) -> [QM31;2]; }
    pub fn point<H:Digest32,P:Policy>(mut state:SemanticTranscript<H>,row:u8,record:Vec<u8>)
        ->(Result<[QM31;2],Error>,SemanticTranscript<H>) {
        let second=match row {25=>false,26=>true,_=>return (Err(Error::InvalidRow),state)};
        if row!=state.next_row {return (Err(Error::RowOrder{expected:state.next_row,actual:row}),state);}
        match semantic20::checked(row,&record) {Ok(())=>(),Err(e)=>return (Err(e),state)}
        let block=match state.sample_block_validated(row,&record) {Ok(b)=>b,Err(e)=>return (Err(e),state)};
        (Ok(P::point(block,second)),state)
    }
}
