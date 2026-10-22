include!("production.rs");
#[cfg(test)] mod tests {
 use super::*;
 #[test] fn fixed_sequence_matches_every_insert() {
  let mut seed=0x123456789abcdef_u64;
  let mut word=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;(seed%PU as u64)as u32};
  for trial in 0..1000 {
   let width=1+word()as usize%24;
   let mut original=TagEch::new(width);let mut candidate=TagEch::new(width);
   for row in 0..width+5 {
    let v:Vec<_>=(0..width).map(|i|if trial%3==0 && i<row {0}else{word()}).collect();
    let got=if !candidate.rows.is_empty() && candidate.cols.windows(2).all(|w|w[0]<w[1]) {candidate.insert_fixed(v.clone())}else{candidate.insert_serial(v.clone())};
    let expected=original.insert_serial(v);
    assert_eq!(got,expected);assert_eq!(candidate,original);
   }
  }
 }
}
#[cfg(kani)] mod proofs {
 #[kani::proof] fn fixed_coordinate_sequence() {
  // Per-step transport: a chunk visits exactly the same coordinate and
  // pivot sequence. Arithmetic sub_product obligations are reused unchanged.
  let total:usize=kani::any();let k:usize=kani::any();kani::assume(k<4);
  let a=total/4*k+core::cmp::min(k,total%4);
  let b=a+total/4+(k<total%4)as usize;
  assert!(a<=b && b<=total);
  if k==0 {assert_eq!(a,0);}
  if k==3 {assert_eq!(b,total);}else{assert_eq!(b,total/4*(k+1)+core::cmp::min(k+1,total%4));}
  let width:usize=kani::any();let taglen:usize=kani::any();kani::assume(width<=total);kani::assume(taglen<=total-width);
  let i:usize=kani::any();kani::assume(a<=i && i<b);
  let pivot:usize=kani::any();kani::assume(pivot<=width);
  let va=core::cmp::max(a,pivot);let vb=core::cmp::min(b,width);
  assert_eq!(va<=i && i<vb,i>=pivot && i<width);
  let ta=core::cmp::max(a,width);let tb=core::cmp::min(b,width+taglen);
  assert_eq!(ta<=i && i<tb,i>=width && i<width+taglen);
 }
}
