#![allow(dead_code,unexpected_cfgs)]
mod field;
use field::WideExact as E;
use std::io::Read;
fn old_powers<const N:usize>(x:E)->[E;N] { let mut p=E::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
fn loop_powers<const N:usize>(x:E)->[E;N]{
 let mut out=[E::ONE;N];
 let mut p=E::ONE;
 let mut i=0usize;
 while i<N {
  out[i]=p;
  p=p.mul(x);
  i+=1;
 }
 out
}
fn check<const N:usize>(x:E){ assert_eq!(old_powers::<N>(x),loop_powers::<N>(x)); }
fn main(){
 let mut values=vec![E::ZERO,E::ONE,E::V,E::from_limbs([field::P-1;8]).unwrap()];
 for i in 0..8 {let mut limbs=[0u32;8];limbs[i]=1;values.push(E::from_limbs(limbs).unwrap());}
 let mut random=[0u8;8192];std::fs::File::open("/dev/urandom").unwrap().read_exact(&mut random).unwrap();
 for bytes in random.chunks_exact(32){let mut limbs=[0u32;8];for i in 0..8 {limbs[i]=u32::from_le_bytes(bytes[i*4..i*4+4].try_into().unwrap())%field::P;}values.push(E::from_limbs(limbs).unwrap());}
 std::fs::write("sample-inputs.json",format!("{:?}\n",values.iter().map(|x|x.to_limbs()).collect::<Vec<_>>())).unwrap();
 let count=values.len(); for x in values {check::<0>(x);check::<1>(x);check::<3>(x);check::<10>(x);check::<29>(x);check::<32>(x);}
 println!("PASS {count} full-field inputs x 6 lengths; original frozen powers equals isolated explicit-loop candidate");
}
