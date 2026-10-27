use aspis_core::field::WideExact as E;
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
pub fn polynomial(bytes:&[u8],x:E)->E {(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))}
pub struct Native;
impl super::FIn_reference::Arithmetic for Native {
 type E=E;
 fn zero()->E {E::ZERO}
 fn mul(a:E,x:E)->E {a.mul(x)}
 fn add(a:E,c:E)->E {a.add(c)}
 fn field(bytes:&[u8],i:usize)->E {field(bytes,i)}
}
