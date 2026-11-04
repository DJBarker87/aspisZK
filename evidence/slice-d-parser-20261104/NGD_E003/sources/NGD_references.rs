// Safe references for remaining caller composition. No field arithmetic,
// pointers, callbacks, allocation, statics, or production-source edits.
#[derive(Clone,Copy)]
pub enum Error { Allocation, RowOrder{expected:u8,actual:u8}, InvalidRow, Tag{row:u8}, Length{row:u8}, NonCanonical{row:u8,value:usize}, Boundary{round:usize}, Terminal, EqualCirclePoints, TrailingBytes, Public }
pub fn shape(row:u8)->Option<(u8,usize)>{match row{0|1|3..=13=>Some((0,0)),2=>Some((1,32)),14=>Some((3,32)),15..=24=>Some((2,896)),25=>Some((4,3712)),26=>Some((5,928)),_=>None}}
// The validation reply is a complete value supplied at the original cut.
pub fn parse_g(row:u8,record:&[u8],reply:Result<(),Error>)->Result<&[u8],Error>{
 let(tag,size)=shape(row).ok_or(Error::InvalidRow)?;
 if record.len()!=5+size{return Err(Error::Length{row});}
 if record[0]!=tag{return Err(Error::Tag{row});}
 if u32::from_le_bytes([record[1],record[2],record[3],record[4]])as usize!=size{return Err(Error::Length{row});}
 let payload=&record[5..];if row>=14{reply?;}Ok(payload)
}
pub fn parse_at_g(bytes:&[u8],row:u8,offset:usize,reply:Result<(),Error>)->Result<(&[u8],usize),Error>{
 let length=5+shape(row).unwrap().1;
 let framed=bytes.get(offset..offset+length).ok_or(Error::Length{row})?;
 parse_g(row,framed,reply)?;Ok((framed,offset+length))
}
pub const SLOT_NODES:[usize;6]=[146,146,128,172,172,150];
pub const OFF_NODES:usize=28359;
pub const fn slot_offset(slot:usize)->usize{let mut at=OFF_NODES;let mut i=0;while i<slot{at+=32*SLOT_NODES[i];i+=1;}at}

#[derive(Clone,Copy)]pub enum CodecError{Length,NonZeroHigh,NonCanonical}
pub const SEMANTIC_ROWS:u8=27;
pub const COMPACT_SEMANTIC:usize=7015;
pub const LOGICAL_SEMANTIC:usize=13831;
fn row_shape(row:u8)->Option<(u8,usize)>{shape(row)}
fn compact_row(row:u8)->bool{row>=14}
pub fn expand_values(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
    if compact.len() % 16 != 0 || out.len() != 2 * compact.len() {
        return Err(CodecError::Length);
    }
    for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
        o[..16].copy_from_slice(c);
        o[16..].fill(0);
    }
    Ok(())
}
pub fn expand_semantic(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
    if compact.len() != COMPACT_SEMANTIC || out.len() != LOGICAL_SEMANTIC {
        return Err(CodecError::Length);
    }
    out[..32].copy_from_slice(&compact[..32]);
    let (mut src, mut dst) = (32, 32);
    for row in 0..SEMANTIC_ROWS {
        let size = row_shape(row).ok_or(CodecError::Length)?.1;
        out[dst..dst + 5].copy_from_slice(&compact[src..src + 5]);
        src += 5;
        dst += 5;
        if compact_row(row) {
            expand_values(&compact[src..src + size / 2], &mut out[dst..dst + size])?;
            src += size / 2;
        } else {
            out[dst..dst + size].copy_from_slice(&compact[src..src + size]);
            src += size;
        }
        dst += size;
    }
    if src != compact.len() || dst != out.len() {
        return Err(CodecError::Length);
    }
    Ok(())
}
