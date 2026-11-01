use aspis_core::field::{M31,CM31,QM31,P};
mod reference_field;
fn q(n:u32)->QM31 {QM31{c0:CM31{a:M31(n),b:M31(n.rotate_left(7))},c1:CM31{a:M31(n.rotate_left(13)),b:M31(n.rotate_left(23))}}}
fn main(){
 assert!(!cfg!(debug_assertions));
 assert!(!std::mem::needs_drop::<std::ops::Range<usize>>());
 assert!(!std::mem::needs_drop::<std::ops::RangeInclusive<usize>>());
 assert!(!std::mem::needs_drop::<[QM31;3]>());
 assert!(!std::mem::needs_drop::<[[u64;3];3]>());
 let negative=std::env::args().any(|a|a=="--negative");
 let seeds=[0,1,7,19,P-1,P,P+1,u32::MAX,0x80000000,0xabcdef01];
 let mut entries=0usize;let mut changed=0usize;
 for (case,seed) in seeds.into_iter().enumerate(){
  let l:[QM31;3]=core::array::from_fn(|i|q(seed.wrapping_add((i as u32).wrapping_mul(131))));
  let r=core::array::from_fn(|i|q(seed.wrapping_add((i as u32).wrapping_mul(173))));
  let left=core::array::from_fn(|i|reference_field::PreparedQm31Multiplier::new(l[i]));
  let native_left=core::array::from_fn(|i|aspis_core::field::PreparedQm31Multiplier::new(l[i]));
  let native=aspis_core::field::qm31_sum_products3_prepared(&native_left,&r);
  let reference=reference_field::qm31_sum_products3_prepared(&left,&r);
  assert_eq!(native,reference,"final result case {case}");
  let source=reference_field::source_trace13(&left,&r);
  let mut owned=reference_field::owned_trace13(&left,&r);
  assert_eq!(source.len(),27);assert_eq!(owned.len(),27);
  if negative { owned[26][2][2]^=1; }
  for step in 0..27 {for c in 0..3 {for k in 0..3 {
   assert_eq!(source[step][c][k],owned[step][c][k],"matrix case {case} step {step} cell {c},{k}");entries+=1;
  }}}
  if source[26]!=[[0u64;3];3] {changed+=1;}
 }
 assert!(changed>0);
 println!("cases=10 store_snapshots=270 matrix_entries_compared={entries} changed_cases={changed} final_deployed_results=10 needs_drop_false=4");
}
