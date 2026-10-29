mod field;
use field::{M31,CM31,QM31,PreparedQm31Multiplier};
fn q(n:u32)->QM31 {QM31{c0:CM31{a:M31(n),b:M31(n*17)},c1:CM31{a:M31(n*31),b:M31(n*47)}}}
fn main(){assert!(!cfg!(debug_assertions));for seed in [0u32,1,7,19] {
 let left=core::array::from_fn(|i|PreparedQm31Multiplier::new(q((seed+1)*31+i as u32)));
 let right=core::array::from_fn(|i|q((seed+1)*43+i as u32));
 let (result,matrix)=field::observed_matrix(&left,&right);
 assert_eq!(result,field::qm31_sum_products3_prepared(&left,&right));
 assert_ne!(matrix,[[0u64;3];3]);
 let words:Vec<u64>=matrix.into_iter().flatten().collect();
 println!("{{\"function\":\"prepared_matrix\",\"seed\":{seed},\"limbs\":{words:?}}}");
}}
