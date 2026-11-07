pub type Key=[u8;32];
#[derive(Clone,Copy)]
pub struct Request{pub program:Key,pub seeds:[Key;4],pub lengths:[usize;4],pub count:usize}
pub fn request_318(program:Key,mint:Key,bump:u8)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 109, 97, 115, 116, 101, 114, 45, 118, 49, 0, 0, 0, 0, 0],mint,[bump,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0;32]],lengths:[27,32,1,0],count:3}}
