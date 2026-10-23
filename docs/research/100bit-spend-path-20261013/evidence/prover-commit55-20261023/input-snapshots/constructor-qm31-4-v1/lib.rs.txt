#![allow(dead_code,unexpected_cfgs)]
pub mod field;
fn owner<T:Copy,const N:usize>(init:T,mut f:impl FnMut(usize)->T)->[T;N] {
 let mut out=[init;N];let mut i=0;while i<N {out[i]=f(i);i+=1;}out
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(100)] fn m31_4() {
  let raw:[[u32;1];4]=kani::any();let input:[field::M31;4]=unsafe{std::mem::transmute(raw)};
  let mut nt=[99usize;4];let mut ct=nt;let mut nn=0;let mut cn=0;
  let native:[field::M31;4]=core::array::from_fn(|i|{nt[nn]=i;nn+=1;input[i]});
  let copy:[field::M31;4]=owner(field::M31::ZERO,|i|{ct[cn]=i;cn+=1;input[i]});
  let k:u8=kani::any();kani::assume((k as usize)<4);
  assert_eq!(native[k as usize],copy[k as usize]);assert_eq!(native[k as usize],input[k as usize]);
  assert_eq!(nn,4);assert_eq!(cn,4);assert_eq!(nt[k as usize],k as usize);assert_eq!(ct[k as usize],k as usize);
 }
 #[kani::proof] #[kani::unwind(100)] fn qm31_4() {
  let raw:[[u32;4];4]=kani::any();let input:[field::QM31;4]=unsafe{std::mem::transmute(raw)};
  let mut nt=[99usize;4];let mut ct=nt;let mut nn=0;let mut cn=0;
  let native:[field::QM31;4]=core::array::from_fn(|i|{nt[nn]=i;nn+=1;input[i]});
  let copy:[field::QM31;4]=owner(field::QM31::ZERO,|i|{ct[cn]=i;cn+=1;input[i]});
  let k:u8=kani::any();kani::assume((k as usize)<4);
  assert_eq!(native[k as usize],copy[k as usize]);assert_eq!(native[k as usize],input[k as usize]);
  assert_eq!(nn,4);assert_eq!(cn,4);assert_eq!(nt[k as usize],k as usize);assert_eq!(ct[k as usize],k as usize);
 }
 #[kani::proof] #[kani::unwind(100)] fn wideexact_4() {
  let raw:[[u32;8];4]=kani::any();let input:[field::WideExact;4]=unsafe{std::mem::transmute(raw)};
  let mut nt=[99usize;4];let mut ct=nt;let mut nn=0;let mut cn=0;
  let native:[field::WideExact;4]=core::array::from_fn(|i|{nt[nn]=i;nn+=1;input[i]});
  let copy:[field::WideExact;4]=owner(field::WideExact::ZERO,|i|{ct[cn]=i;cn+=1;input[i]});
  let k:u8=kani::any();kani::assume((k as usize)<4);
  assert_eq!(native[k as usize],copy[k as usize]);assert_eq!(native[k as usize],input[k as usize]);
  assert_eq!(nn,4);assert_eq!(cn,4);assert_eq!(nt[k as usize],k as usize);assert_eq!(ct[k as usize],k as usize);
 }
 #[kani::proof] #[kani::unwind(100)] fn m31_9() {
  let raw:[[u32;1];9]=kani::any();let input:[field::M31;9]=unsafe{std::mem::transmute(raw)};
  let mut nt=[99usize;9];let mut ct=nt;let mut nn=0;let mut cn=0;
  let native:[field::M31;9]=core::array::from_fn(|i|{nt[nn]=i;nn+=1;input[i]});
  let copy:[field::M31;9]=owner(field::M31::ZERO,|i|{ct[cn]=i;cn+=1;input[i]});
  let k:u8=kani::any();kani::assume((k as usize)<9);
  assert_eq!(native[k as usize],copy[k as usize]);assert_eq!(native[k as usize],input[k as usize]);
  assert_eq!(nn,9);assert_eq!(cn,9);assert_eq!(nt[k as usize],k as usize);assert_eq!(ct[k as usize],k as usize);
 }
 #[kani::proof] #[kani::unwind(100)] fn qm31_10() {
  let raw:[[u32;4];10]=kani::any();let input:[field::QM31;10]=unsafe{std::mem::transmute(raw)};
  let mut nt=[99usize;10];let mut ct=nt;let mut nn=0;let mut cn=0;
  let native:[field::QM31;10]=core::array::from_fn(|i|{nt[nn]=i;nn+=1;input[i]});
  let copy:[field::QM31;10]=owner(field::QM31::ZERO,|i|{ct[cn]=i;cn+=1;input[i]});
  let k:u8=kani::any();kani::assume((k as usize)<10);
  assert_eq!(native[k as usize],copy[k as usize]);assert_eq!(native[k as usize],input[k as usize]);
  assert_eq!(nn,10);assert_eq!(cn,10);assert_eq!(nt[k as usize],k as usize);assert_eq!(ct[k as usize],k as usize);
 }
}
