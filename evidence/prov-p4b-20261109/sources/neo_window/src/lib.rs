// Independent safe parser references: scalar byte order is the std primitive.
pub const P:u32=2147483647;
pub fn word(b:&[u8],i:usize)->u32 {u32::from_le_bytes([b[i],b[i+1],b[i+2],b[i+3]])}
pub fn complex(b:&[u8])->Option<[u32;2]> {let a=word(b,0);if a>=P{return None;}let c=word(b,4);if c>=P{return None;}Some([a,c])}
pub fn quadratic(b:&[u8])->Option<[u32;4]> {let a=match complex(&b[0..8]){Some(x)=>x,None=>return None};let c=match complex(&b[8..16]){Some(x)=>x,None=>return None};Some([a[0],a[1],c[0],c[1]])}
pub fn wide(b:&[u8])->Option<[u32;8]> {
 if b.len()!=32{return None;}
 let a=word(b,0);let c=word(b,4);let d=word(b,8);let e=word(b,12);let f=word(b,16);let g=word(b,20);let h=word(b,24);let k=word(b,28);
 if a>=P||c>=P||d>=P||e>=P||f>=P||g>=P||h>=P||k>=P{None}else{Some([a,c,d,e,f,g,h,k])}
}
