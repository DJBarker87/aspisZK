// Owned whole-scan reference. Recursive bodies reused byte-for-byte from the
// existing MultiproofParserRef extraction; no shipped source is changed.
pub mod reference {
pub fn canonical_word(b:[u8;4])->bool {u32::from_le_bytes(b)<0x7fffffff}
pub fn canonical_qm(b:[u8;16])->bool {
    canonical_word([b[0],b[1],b[2],b[3]]) &&
    canonical_word([b[4],b[5],b[6],b[7]]) &&
    canonical_word([b[8],b[9],b[10],b[11]]) &&
    canonical_word([b[12],b[13],b[14],b[15]])
}
pub fn check_values(bytes:&[u8])->bool {
    if bytes.len()<16 {return true;}
    let chunk=read16(bytes);
    canonical_qm(chunk) && check_values(&bytes[16..])
}
pub fn read16(bytes:&[u8])->[u8;16] {[bytes[0],bytes[1],bytes[2],bytes[3],bytes[4],bytes[5],bytes[6],bytes[7],bytes[8],bytes[9],bytes[10],bytes[11],bytes[12],bytes[13],bytes[14],bytes[15]]}
}
pub mod parser_reference {
use super::reference::{canonical_word,check_values};
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
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Error { Parse }
pub fn canonical_scan(bytes:&[u8])->Result<(),Error> {
    if parser_reference::scan(bytes) {Ok(())} else {Err(Error::Parse)}
}
