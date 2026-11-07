#[derive(Clone,Copy,PartialEq,Eq)] pub struct M31(pub u32);
#[derive(Clone,Copy,PartialEq,Eq)] pub struct CM31 {pub a:M31,pub b:M31}
#[derive(Clone,Copy,PartialEq,Eq)] pub struct QM31 {pub c0:CM31,pub c1:CM31}
pub fn NGO_decode_le(bytes:&[u8])->Option<QM31>{
 assert_eq!(bytes.len(),16);
 fn word(b:&[u8],i:usize)->u32{u32::from(b[i])|(u32::from(b[i+1])<<8)|(u32::from(b[i+2])<<16)|(u32::from(b[i+3])<<24)}
 let a=word(bytes,0);let b=word(bytes,4);let c=word(bytes,8);let d=word(bytes,12);
 if a>=0x7fffffff||b>=0x7fffffff||c>=0x7fffffff||d>=0x7fffffff{return None;}
 Some(QM31{c0:CM31{a:M31(a),b:M31(b)},c1:CM31{a:M31(c),b:M31(d)}})
}
