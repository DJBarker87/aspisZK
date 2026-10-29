pub const LIVE_BINDING:[u8;32]=[65,83,80,80,65,73,82,49,1,20,21,7,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
pub fn live_header_ref(length:usize,bytes:&[u8;48])->u8 {
 if length!=800{return 1;}
 if bytes[..8]!=*b"ASPLIVE1"{return 2;}
 if bytes[8]!=1{return 3;}
 if bytes[9]!=0 || bytes[10]!=0 || bytes[11]!=0 || bytes[12]!=0 || bytes[13]!=0 || bytes[14]!=0 || bytes[15]!=0{return 4;}
 if bytes[16..48]!=LIVE_BINDING[..]{return 5;}
 0
}
