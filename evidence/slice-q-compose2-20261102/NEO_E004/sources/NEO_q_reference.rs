pub const P:u32=2147483647;
pub fn from_limbs(x:[u32;4])->Option<[u32;4]> {let [a,b,c,d]=x;if a<P&&b<P&&c<P&&d<P{Some([a,b,c,d])}else{None}}
pub fn limbs(x:[u32;4])->[u32;4] {x}
pub fn from_wide(x:[u32;8])->[[u32;4];2] {let [a,b,c,d,e,f,g,h]=x;[[a,b,c,d],[e,f,g,h]]}
pub fn limbs_of(x:[u32;4])->[u32;4] {x}
pub fn checked(x:[u32;4])->Result<[u32;4],()> {match from_limbs(x){Some(q)=>Ok(q),None=>Err(())}}
