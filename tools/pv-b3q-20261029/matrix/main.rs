mod field;
use field::{M31,CM31,QM31,PreparedQm31Multiplier,P};
fn q(n:u32)->QM31 { QM31 {c0:CM31{a:M31(n),b:M31(n.rotate_left(7))},c1:CM31{a:M31(n.rotate_left(13)),b:M31(n.rotate_left(23))}} }
fn main(){
 assert!(!cfg!(debug_assertions));
 let negative=std::env::args().any(|a|a=="--negative");
 let seeds=[0,1,7,19,P-1,P,P+1,u32::MAX,0x80000000,0xabcdef01];
 for (case,seed) in seeds.into_iter().enumerate(){
  let l:[QM31;3]=core::array::from_fn(|i|q(seed.wrapping_add((i as u32).wrapping_mul(131))));
  let right:[QM31;3]=core::array::from_fn(|i|q(seed.wrapping_add((i as u32).wrapping_mul(173))));
  let left=l.map(PreparedQm31Multiplier::new);
  let (observed,matrix)=field::observed_matrix(&left,&right);
  assert_eq!(observed,field::qm31_sum_products3_prepared(&left,&right));
  // Independent per-cell expression; only wrapping primitives mirror release.
  let mut expected=[[0u64;3];3];
  for c in 0..3 {for k in 0..3 {
   for i in 0..3 {
    let r=right[i];let s=r.c0.add(r.c1);
    let rc=[[r.c0.a,r.c0.b,r.c0.a.add(r.c0.b)], [r.c1.a,r.c1.b,r.c1.a.add(r.c1.b)], [s.a,s.b,s.a.add(s.b)]];
    expected[c][k]=expected[c][k].wrapping_add((field::observed_components(&left[i])[c][k].0 as u64).wrapping_mul(rc[c][k].0 as u64));
   }
  }}
  if negative && case==0 {expected[2][2]^=1;}
  for c in 0..3 {for k in 0..3 {assert_eq!(matrix[c][k],expected[c][k],"case {case}, cell {c},{k}");}}
  println!("case={case} matrix={matrix:?}");
 }
 println!("direct_source_matrices=10 all_nine_entry_comparisons=90 original_results=10");
}
