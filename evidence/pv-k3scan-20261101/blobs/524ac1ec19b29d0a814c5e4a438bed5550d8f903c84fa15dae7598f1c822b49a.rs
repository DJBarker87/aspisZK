use aspis_core::field::{QM31,CM31,M31,P};
use pv_b3p6_reference227::{source_equality13,equality_value13,flat_equality13};
fn q(n:u32)->QM31 {QM31{c0:CM31{a:M31(n),b:M31(n.rotate_left(7))},c1:CM31{a:M31(n.rotate_left(13)),b:M31(n.rotate_left(23))}}}
fn main(){
 assert!(!cfg!(debug_assertions));
 if std::env::args().any(|a|a=="--mask-source-zero") {
  let value=pv_b3p6_reference227::source_mask13(&[QM31::ZERO;16],0);
  assert_eq!(value,QM31::ZERO);println!("source_mask_zero=ZERO normal_return=true");return;
 }
 if std::env::args().any(|a|a=="--mask-owned-zero") {
  let _=pv_b3p6_reference227::owned_mask13([QM31::ZERO;16],0);
  panic!("unexpected owned normal return");
 }
 if std::env::args().any(|a|a=="--frozen-masks"||a=="--negative-frozen-masks") {
  let negative=std::env::args().any(|a|a=="--negative-frozen-masks");
  let mut checks=0usize;
  for seed in [0u32,1,7,19,P-1,P,P+1,u32::MAX,0x80000000,0xabcdef01] {
   let values=core::array::from_fn(|i|q(seed.wrapping_add(131*i as u32)));
   for mask in [1749u16,2048,2049,4097,6144,6145,26214] {
    let source=pv_b3p6_reference227::source_mask13(&values,mask);
    let mut owned=pv_b3p6_reference227::owned_mask13(values,mask);
    if negative {owned.c0.a.0^=1;}
    assert_eq!(source,owned,"frozen mask {mask} seed {seed}");checks+=1;
   }
  }
  println!("frozen_mask_cases={checks} source_owned_equal=true");return;
 }
 let negative=std::env::args().any(|a|a=="--negative");
 let mut changed=0usize;
 for (case,seed) in [0u32,1,7,19,P-1,P,P+1,u32::MAX,0x80000000,0xabcdef01].into_iter().enumerate(){
  let left=core::array::from_fn(|i|q(seed.wrapping_add(131*i as u32)));
  let right=core::array::from_fn(|i|q(seed.wrapping_add(173*i as u32)));
  let source=source_equality13(&left,&right);
  let value=equality_value13(left,right);
  let mut flat=flat_equality13(&left,&right);
  if negative {flat.c0.a.0^=1;}
  assert_eq!(source,value,"borrow/value case {case}");
  assert_eq!(source,flat,"loop/unroll case {case}");
  if source!=QM31::ZERO {changed+=1;}
 }
 assert!(changed>0);
 println!("cases=10 borrowed_value_comparisons=10 loop_unroll_comparisons=10 nonzero_results={changed}");
}
