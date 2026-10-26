use aspis_core::field::{M31,CM31,QM31,WideExact};
pub fn load_words_shipped(block:&[u8;32])->[u32;8] {
    core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()))
}
pub fn load_words_owned(block:&[u8;32])->[u32;8] {
    let mut out=[0u32;8];let mut i=0usize;
    while i<8 {let start=4*i;out[i]=u32::from_le_bytes([block[start],block[start+1],block[start+2],block[start+3]]);i+=1;}
    out
}
pub fn decode8_shipped(digits:[u32;8])->WideExact {
    WideExact::new(
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        },
        QM31 {
            c0: CM31::new(M31(digits[4]), M31(digits[5])),
            c1: CM31::new(M31(digits[6]), M31(digits[7])),
        },
    )
}
#[cfg(kani)]
mod checks {
 use super::*;
 #[kani::proof] #[kani::unwind(6)]
 fn sampler_load_word_step() {
  let block:[u8;32]=kani::any();let i:usize=kani::any();kani::assume(i<8);
  let start=4*i;
  let a=u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap());
  let b=u32::from_le_bytes([block[start],block[start+1],block[start+2],block[start+3]]);
  assert_eq!(a,b);
 }
 #[kani::proof] #[kani::unwind(34)]
 fn sampler_load_words_all() {
  let block:[u8;32]=kani::any();let a=load_words_shipped(&block);let b=load_words_owned(&block);
  let mut i=0usize;while i<8 {assert_eq!(a[i],b[i]);i+=1;}
 }
 #[kani::proof] #[kani::unwind(10)]
 fn sampler_decode_words() {
  let digits:[u32;8]=kani::any();let a=decode8_shipped(digits);let b=crate::sampler_owned::decode8(digits);
  assert_eq!(a.c0().c0.a.0,b.c0().c0.a.0);assert_eq!(a.c0().c0.b.0,b.c0().c0.b.0);
  assert_eq!(a.c0().c1.a.0,b.c0().c1.a.0);assert_eq!(a.c0().c1.b.0,b.c0().c1.b.0);
  assert_eq!(a.c1().c0.a.0,b.c1().c0.a.0);assert_eq!(a.c1().c0.b.0,b.c1().c0.b.0);
  assert_eq!(a.c1().c1.a.0,b.c1().c1.a.0);assert_eq!(a.c1().c1.b.0,b.c1().c1.b.0);
 }
}
