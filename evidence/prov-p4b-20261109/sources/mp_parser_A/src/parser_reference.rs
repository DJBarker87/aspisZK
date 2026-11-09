//! Whole owned compact parser; stored bytes remain the caller's immutable input.
use alloc::vec::Vec;
use super::reference::{canonical_word,check_values,expand_rows,row_shape};
pub fn canonical_words(bytes:&[u8])->bool {
    if bytes.is_empty() {return true;}
    if bytes.len()<4 {return false;}
    canonical_word([bytes[0],bytes[1],bytes[2],bytes[3]]) && canonical_words(&bytes[4..])
}
pub fn opening_scan(bytes:&[u8])->bool {
    bytes.len()==832 && canonical_words(&bytes[..608]) && canonical_words(&bytes[672..800])
}
pub fn opening_rows(bytes:&[u8],remaining:u8)->bool {
    if remaining==0 {return bytes.is_empty();}
    if bytes.len()<832 {return false;}
    opening_scan(&bytes[..832]) && opening_rows(&bytes[832..],remaining-1)
}
pub fn scan(bytes:&[u8])->bool {
    if bytes.len()!=57607 {return false;}
    check_values(&bytes[7031..7495]) && canonical_words(&bytes[7495..7751]) &&
    canonical_words(&bytes[7783..10055]) && opening_rows(&bytes[10055..28359],22)
}
pub fn header(bytes:&[u8])->bool {
    bytes.len()==57607 && bytes[0]==82 && bytes[1]==49 && bytes[2]==80 && bytes[3]==51 &&
    bytes[4]==67 && bytes[5]==66 && bytes[6]==49 && bytes[7]==56 && bytes[8]==2 &&
    bytes[9]==0 && bytes[10]==0 && bytes[11]==0 && bytes[12]==0 && bytes[13]==0 && bytes[14]==0 && bytes[15]==0
}
pub fn semantic_rows(row:u8,bytes:&[u8],mut rows:Vec<Vec<u8>>)->Option<Vec<Vec<u8>>> {
    if row>=27 {return if bytes.is_empty(){Some(rows)}else{None};}
    let (tag,size)=match row_shape(row) {Some(shape)=>shape,None=>return None};
    let stored=if row>=14 {size/2}else{size};
    if bytes.len()<5+stored {return None;}
    if bytes[0]!=tag || [bytes[1],bytes[2],bytes[3],bytes[4]]!=(size as u32).to_le_bytes() {return None;}
    let payload=&bytes[5..5+stored];
    if row>=14 && !check_values(payload) {return None;}
    let logical=if row>=14 {match expand_rows(payload,Vec::new()){Some(x)=>x,None=>return None}}else{payload.to_vec()};
    let mut framed=bytes[..5].to_vec();framed.extend_from_slice(&logical);
    rows.push(framed);semantic_rows(row+1,&bytes[5+stored..],rows)
}
pub fn parse(bytes:&[u8])->Option<Vec<Vec<u8>>> {
    if !header(bytes) || !scan(bytes) {return None;}
    semantic_rows(0,&bytes[48..7031],Vec::new())
}
