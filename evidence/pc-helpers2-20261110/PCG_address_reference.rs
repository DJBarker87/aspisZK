pub type Key=[u8;32];
#[derive(Clone,Copy)]
pub struct Request{pub program:Key,pub seeds:[Key;4],pub lengths:[usize;4],pub count:usize}
pub fn request_374(program:Key,pool:Key,profile:Key,release:Key)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 101, 110, 116, 114, 121, 45, 118, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0],pool,profile,release],lengths:[23, 32, 32, 32],count:4}}
pub fn request_375(program:Key,pool:Key,profile:Key,release:Key)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 101, 110, 116, 114, 121, 45, 118, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0],pool,profile,release],lengths:[23, 32, 32, 32],count:4}}
pub fn request_376(program:Key,pool:Key)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 114, 101, 103, 105, 115, 116, 114, 121, 45, 118, 49, 0, 0, 0, 0, 0, 0],pool,[0;32],[0;32]],lengths:[26, 32, 0, 0],count:2}}
pub fn request_377(program:Key,pool:Key)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 118, 101, 114, 105, 102, 105, 101, 114, 45, 114, 101, 103, 105, 115, 116, 114, 121, 45, 118, 50, 0, 0, 0, 0, 0, 0],pool,[0;32],[0;32]],lengths:[26, 32, 0, 0],count:2}}
pub fn request_390(program:Key,pool:Key)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 112, 111, 111, 108, 45, 118, 97, 117, 108, 116, 45, 97, 117, 116, 104, 111, 114, 105, 116, 121, 45, 118, 49, 0, 0, 0],pool,[0;32],[0;32]],lengths:[29, 32, 0, 0],count:2}}
pub fn request_391(program:Key,pool:Key)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 112, 111, 111, 108, 45, 118, 97, 117, 108, 116, 45, 116, 111, 107, 101, 110, 45, 118, 49, 0, 0, 0, 0, 0, 0, 0],pool,[0;32],[0;32]],lengths:[25, 32, 0, 0],count:2}}
pub fn request_323(program:Key,pool:Key,sequence:u64)->Request{Request{program,seeds:[[97, 115, 112, 105, 115, 45, 112, 97, 105, 114, 45, 102, 111, 114, 101, 115, 116, 45, 99, 104, 101, 99, 107, 112, 111, 105, 110, 116, 45, 118, 49, 0],pool,le_padded(sequence),[0;32]],lengths:[31, 32, 8, 0],count:3}}
pub fn le_padded(x:u64)->Key{let b=x.to_le_bytes();[b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]}
#[derive(Clone,Copy)]
pub enum PdaError{MaxSeedLengthExceeded,InvalidSeeds,IllegalOwner}
pub fn stored_matches(reply:Result<Key,PdaError>,key:Key)->bool{match reply{Ok(address)=>address==key,Err(_)=>false}}
