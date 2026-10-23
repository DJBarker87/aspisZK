#![allow(dead_code,unexpected_cfgs)]
pub mod field;
// Exact allocation/collection expressions from sim.rs:218-219.
fn split<T:Copy>(c:&[T])->(Vec<T>,Vec<T>) {
 (c.iter().step_by(2).copied().collect(),c.iter().skip(1).step_by(2).copied().collect())
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(260)] fn m_split_256() {
  let raw:[u32;256]=kani::any();let c:[field::M31;256]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume(k<128);
  assert_eq!(a.len(),128);assert_eq!(b.len(),128);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
}

#[cfg(kani)] mod collections {
 use super::*;
 macro_rules! split_check {
  ($name:ident,$ty:ty,$n:expr) => {
   #[kani::proof] #[kani::unwind(260)] fn $name() {
    let c:[$ty;$n]=kani::any();let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<$n/2);
    assert_eq!(a.len(),$n/2);assert_eq!(b.len(),$n/2);
    assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
   }
  }
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_2() {
  let raw:[[u32;1];2]=kani::any();let c:[field::M31;2]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<2/2);
  assert_eq!(a.len(),2/2);assert_eq!(b.len(),2/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_4() {
  let raw:[[u32;1];4]=kani::any();let c:[field::M31;4]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<4/2);
  assert_eq!(a.len(),4/2);assert_eq!(b.len(),4/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_8() {
  let raw:[[u32;1];8]=kani::any();let c:[field::M31;8]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<8/2);
  assert_eq!(a.len(),8/2);assert_eq!(b.len(),8/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_16() {
  let raw:[[u32;1];16]=kani::any();let c:[field::M31;16]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<16/2);
  assert_eq!(a.len(),16/2);assert_eq!(b.len(),16/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_32() {
  let raw:[[u32;1];32]=kani::any();let c:[field::M31;32]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<32/2);
  assert_eq!(a.len(),32/2);assert_eq!(b.len(),32/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_64() {
  let raw:[[u32;1];64]=kani::any();let c:[field::M31;64]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<64/2);
  assert_eq!(a.len(),64/2);assert_eq!(b.len(),64/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn m_split_128() {
  let raw:[[u32;1];128]=kani::any();let c:[field::M31;128]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<128/2);
  assert_eq!(a.len(),128/2);assert_eq!(b.len(),128/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_2() {
  let raw:[[u32;4];2]=kani::any();let c:[field::QM31;2]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<2/2);
  assert_eq!(a.len(),2/2);assert_eq!(b.len(),2/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_4() {
  let raw:[[u32;4];4]=kani::any();let c:[field::QM31;4]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<4/2);
  assert_eq!(a.len(),4/2);assert_eq!(b.len(),4/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_8() {
  let raw:[[u32;4];8]=kani::any();let c:[field::QM31;8]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<8/2);
  assert_eq!(a.len(),8/2);assert_eq!(b.len(),8/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_16() {
  let raw:[[u32;4];16]=kani::any();let c:[field::QM31;16]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<16/2);
  assert_eq!(a.len(),16/2);assert_eq!(b.len(),16/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_32() {
  let raw:[[u32;4];32]=kani::any();let c:[field::QM31;32]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<32/2);
  assert_eq!(a.len(),32/2);assert_eq!(b.len(),32/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_64() {
  let raw:[[u32;4];64]=kani::any();let c:[field::QM31;64]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<64/2);
  assert_eq!(a.len(),64/2);assert_eq!(b.len(),64/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_128() {
  let raw:[[u32;4];128]=kani::any();let c:[field::QM31;128]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<128/2);
  assert_eq!(a.len(),128/2);assert_eq!(b.len(),128/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn q_split_256() {
  let raw:[[u32;4];256]=kani::any();let c:[field::QM31;256]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<256/2);
  assert_eq!(a.len(),256/2);assert_eq!(b.len(),256/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_2() {
  let raw:[[u32;8];2]=kani::any();let c:[field::WideExact;2]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<2/2);
  assert_eq!(a.len(),2/2);assert_eq!(b.len(),2/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_4() {
  let raw:[[u32;8];4]=kani::any();let c:[field::WideExact;4]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<4/2);
  assert_eq!(a.len(),4/2);assert_eq!(b.len(),4/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_8() {
  let raw:[[u32;8];8]=kani::any();let c:[field::WideExact;8]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<8/2);
  assert_eq!(a.len(),8/2);assert_eq!(b.len(),8/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_16() {
  let raw:[[u32;8];16]=kani::any();let c:[field::WideExact;16]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<16/2);
  assert_eq!(a.len(),16/2);assert_eq!(b.len(),16/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_32() {
  let raw:[[u32;8];32]=kani::any();let c:[field::WideExact;32]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<32/2);
  assert_eq!(a.len(),32/2);assert_eq!(b.len(),32/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_64() {
  let raw:[[u32;8];64]=kani::any();let c:[field::WideExact;64]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<64/2);
  assert_eq!(a.len(),64/2);assert_eq!(b.len(),64/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_128() {
  let raw:[[u32;8];128]=kani::any();let c:[field::WideExact;128]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<128/2);
  assert_eq!(a.len(),128/2);assert_eq!(b.len(),128/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
 #[kani::proof] #[kani::unwind(260)] fn e_split_256() {
  let raw:[[u32;8];256]=kani::any();let c:[field::WideExact;256]=unsafe{std::mem::transmute(raw)};
  let (a,b)=split(&c);let k:u8=kani::any();kani::assume((k as usize)<256/2);
  assert_eq!(a.len(),256/2);assert_eq!(b.len(),256/2);
  assert_eq!(a[k as usize],c[2*k as usize]);assert_eq!(b[k as usize],c[2*k as usize+1]);
 }
}
