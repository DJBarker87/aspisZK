pub type Key=[u8;32];
#[derive(Clone,Copy)]
pub struct Request{pub program:Key,pub seeds:[Key;4],pub lengths:[usize;4],pub count:usize}
pub fn le_padded(x:u64)->Key{let b=x.to_le_bytes();[b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]}
pub fn request280(program:Key,pool:Key,page:u64)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 112, 111, 111, 108, 45, 114, 111, 111, 116, 45, 112, 97, 103, 101, 45, 118, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0],pool,le_padded(page),[0;32]],lengths:[23,32,8,0],count:3}}
