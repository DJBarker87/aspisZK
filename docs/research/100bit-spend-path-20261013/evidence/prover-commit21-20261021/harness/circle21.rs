#[cfg(any(kani,aeneas_ref))]
pub mod circle21 {
    use alloc::vec::Vec;
    use aspis_core::{Digest32,circle::SecureCirclePoint};
    use super::{Error,SemanticTranscript,semantic20};
    use crate::sampler::{circle_sample,CircleRow};
    pub fn point<H:Digest32>(mut state:SemanticTranscript<H>,row:u8,record:Vec<u8>)
        ->(Result<SecureCirclePoint,Error>,SemanticTranscript<H>) {
        let circle_row=match row {25=>CircleRow::First,26=>CircleRow::Second,_=>return (Err(Error::InvalidRow),state)};
        if row!=state.next_row {return (Err(Error::RowOrder{expected:state.next_row,actual:row}),state);}
        match semantic20::checked(row,&record) {Ok(())=>(),Err(e)=>return (Err(e),state)}
        let block=match state.sample_block_validated(row,&record) {Ok(b)=>b,Err(e)=>return (Err(e),state)};
        (Ok(circle_sample(&block,circle_row)),state)
    }
}
