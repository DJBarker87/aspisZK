use aspis_core::{field::WideExact as E,r0::CodeField};
pub fn powers<const N:usize>(x:E)->[E;N]{
 let mut out=[E::ZERO;N];
 let mut p=E::ONE;
 let mut i=0usize;
 while i<N {
  out[i]=p;
  i+=1;
  if i==N { return out; }
  p=p.mul(x);
 }
 out
}
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
