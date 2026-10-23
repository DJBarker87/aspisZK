//! Host compact publication owner; shared verifier codec remains frozen.
use alloc::vec::Vec;
use crate::r1_wire::row_shape;
pub use crate::compact::*;
fn compact_row(row:u8)->bool {row>=14}

pub fn compact_semantic(logical: &[u8], out: &mut Vec<u8>) -> Result<(), CodecError> {
    if logical.len() != LOGICAL_SEMANTIC {
        return Err(CodecError::Length);
    }
    out.extend_from_slice(&logical[..32]);
    let mut at = 32;
    let mut row=0;
    while row<SEMANTIC_ROWS {
        let size = row_shape(row).ok_or(CodecError::Length)?.1;
        out.extend_from_slice(&logical[at..at + 5]);
        at += 5;
        if compact_row(row) {
            compact_values(&logical[at..at + size], out)?;
        } else {
            out.extend_from_slice(&logical[at..at + size]);
        }
        at += size;
        row+=1;
    }
    if at != logical.len() {
        return Err(CodecError::Length);
    }
    Ok(())
}

pub fn compact_values(logical: &[u8], out: &mut Vec<u8>) -> Result<(), CodecError> {
    if logical.len() % 32 != 0 {
        return Err(CodecError::Length);
    }
    let mut at=0;
    while at<logical.len() {
        let mut high=16;
        while high<32 {
            if logical[at+high]!=0 {return Err(CodecError::NonZeroHigh);}
            high+=1;
        }
        out.extend_from_slice(&logical[at..at+16]);
        at+=32;
    }
    Ok(())
}

