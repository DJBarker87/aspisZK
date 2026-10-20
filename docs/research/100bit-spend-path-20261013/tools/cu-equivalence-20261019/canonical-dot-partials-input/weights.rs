use crate::field::WideExact as E;
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
