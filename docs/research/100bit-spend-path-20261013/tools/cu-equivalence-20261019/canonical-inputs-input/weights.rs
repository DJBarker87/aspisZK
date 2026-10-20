use crate::field::WideExact as E;
pub fn powers<const N:usize>(x:E)->[E;N] { let mut p=E::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
