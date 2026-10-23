#![allow(dead_code,unexpected_cfgs)]
pub mod field;
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(1030)] fn base_column() {
  let raw:[[u32;8];1024]=kani::any();let input:[field::WideExact;1024]=unsafe{std::mem::transmute(raw)};
  let output:[field::M31;1024]=input.map(|x|field::M31(x.to_limbs()[0]));
  let k:u16=kani::any();kani::assume(k<1024);assert_eq!(output[k as usize].0,raw[k as usize][0]);
 }
 #[kani::proof] #[kani::unwind(1030)] fn extension_column() {
  let raw:[[u32;8];1024]=kani::any();let input:[field::WideExact;1024]=unsafe{std::mem::transmute(raw)};
  let output:[field::QM31;1024]=input.map(|x|x.c0());
  let k:u16=kani::any();let w:u8=kani::any();kani::assume(k<1024);kani::assume(w<4);
  let q=output[k as usize];let limbs=[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];
  assert_eq!(limbs[w as usize],raw[k as usize][w as usize]);
 }
}
