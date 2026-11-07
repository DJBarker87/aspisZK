#[derive(Clone,Copy)]
pub struct Decoded{pub tag:u8,pub owner:[u32;8],pub amount:u32,pub salt:[u32;8],pub payload_len:usize}
fn error(tag:u8)->Decoded{Decoded{tag,owner:[0;8],amount:0,salt:[0;8],payload_len:0}}
pub fn word(h:&[u8;80],at:usize)->u32{u32::from_le_bytes([h[at],h[at+1],h[at+2],h[at+3]])}
pub fn words(h:&[u8;80],at:usize)->[u32;8]{[word(h,at+0),word(h,at+4),word(h,at+8),word(h,at+12),word(h,at+16),word(h,at+20),word(h,at+24),word(h,at+28)]}
pub fn canonical(d:[u32;8])->bool{d[0]<2147483647&&d[1]<2147483647&&d[2]<2147483647&&d[3]<2147483647&&d[4]<2147483647&&d[5]<2147483647&&d[6]<2147483647&&d[7]<2147483647}
pub fn decode_reference(h:&[u8;80],len:usize,magic:[u8;4])->Decoded{
 if len<80||len>592{return error(1)}
 if [h[0],h[1],h[2],h[3]]!=magic{return error(2)}
 if h[4]!=1{return error(3)}
 if h[5]!=0||[h[44],h[45],h[46],h[47]]!=[0;4]{return error(4)}
 let declared=u16::from_le_bytes([h[6],h[7]]) as usize;
 if declared>512{return error(6)}
 if len!=80+declared{return error(1)}
 let owner=words(h,8);if !canonical(owner){return error(7)}
 let salt=words(h,48);if !canonical(salt){return error(7)}
 let amount=word(h,40);if amount==0||amount>=1073741824{return error(5)}
 Decoded{tag:0,owner,amount,salt,payload_len:len-80}
}
