// Fresh owned transcript state for every row. Hash reads still use the
// unchanged source sample_block_validated; no new hash implementation.
#[cfg(any(kani,aeneas_ref))]
pub mod semantic20 {
    use alloc::vec::Vec;
    use aspis_core::{Digest32,field::QM31};
    use super::{Error,SemanticTranscript,row_shape,fields20};
    pub fn checked(row:u8,record:&[u8])->Result<(),Error> {
        let (tag,size)=match row_shape(row) {Some(shape)=>shape,None=>return Err(Error::InvalidRow)};
        if record.len()!=5+size {return Err(Error::Length{row});}
        if record[0]!=tag {return Err(Error::Tag{row});}
        if u32::from_le_bytes([record[1],record[2],record[3],record[4]]) as usize !=size {
            return Err(Error::Length{row});
        }
        if row>=14 {
            match fields20::validate(row,record[5..].to_vec(),0) {Ok(())=>(),Err(e)=>return Err(e)}
        }
        Ok(())
    }
    pub fn semantic<H:Digest32>(mut state:SemanticTranscript<H>,row:u8,record:Vec<u8>)
        ->(Result<QM31,Error>,SemanticTranscript<H>) {
        if row>24 {return (Err(Error::InvalidRow),state);}
        if row!=state.next_row {
            return (Err(Error::RowOrder{expected:state.next_row,actual:row}),state);
        }
        match checked(row,&record) {Ok(())=>(),Err(e)=>return (Err(e),state)}
        let block=match state.sample_block_validated(row,&record) {
            Ok(block)=>block,Err(e)=>return (Err(e),state)
        };
        (Ok(crate::sampler::qm31_sample(&block)),state)
    }
    pub fn rows<H:Digest32>(state:SemanticTranscript<H>,records:Vec<Vec<u8>>,row:usize,
        mut sem:[QM31;25])->(Result<[QM31;25],Error>,SemanticTranscript<H>) {
        if row==25 {return (Ok(sem),state);}
        let (value,state)=semantic(state,row as u8,records[row].clone());
        match value {
            Err(e)=>(Err(e),state),
            Ok(value)=>{sem[row]=value;rows(state,records,row.wrapping_add(1),sem)}
        }
    }
}
