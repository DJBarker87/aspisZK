pub fn range_ref(i:usize)->(usize,usize){(i*32,(i+1)*32)}
pub fn decode_ref(bytes:&[u8])->[u32;8]{[
 u32::from_le_bytes([bytes[0],bytes[1],bytes[2],bytes[3]]),
 u32::from_le_bytes([bytes[4],bytes[5],bytes[6],bytes[7]]),
 u32::from_le_bytes([bytes[8],bytes[9],bytes[10],bytes[11]]),
 u32::from_le_bytes([bytes[12],bytes[13],bytes[14],bytes[15]]),
 u32::from_le_bytes([bytes[16],bytes[17],bytes[18],bytes[19]]),
 u32::from_le_bytes([bytes[20],bytes[21],bytes[22],bytes[23]]),
 u32::from_le_bytes([bytes[24],bytes[25],bytes[26],bytes[27]]),
 u32::from_le_bytes([bytes[28],bytes[29],bytes[30],bytes[31]])]}
pub fn field_ref(bytes:&[u8],i:usize)->[u32;8]{decode_ref(&bytes[i*32..(i+1)*32])}
