#![allow(dead_code,unexpected_cfgs)]
#![cfg_attr(kani,feature(stmt_expr_attributes,proc_macro_hygiene))]
extern crate alloc;
mod aspis_core {pub mod field {include!("field.rs");}}
use alloc::vec::Vec;
use aspis_core::field::{M31,CM31,QM31,QM31 as K};
include!("../../src/frozen.rs");
include!("../../src/owned.rs");
fn reduce_spec(x:u64)->u32 {
 let a=(x&0x7fffffff)+(x>>31);
 let b=((a&0x7fffffff)+(a>>31)) as u32;
 if b>=0x7fffffff {b-0x7fffffff} else {b}
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(aspis_core::field::M31::reduce_u64)]
 #[kani::unwind(6)]
 fn reducer_contract() {
  let x:u64=kani::any();let got=M31::reduce_u64(x);
  assert_eq!(got.0,field_external::field::M31::reduce_u64(x).0);
 }
 #[kani::proof]
 #[kani::stub_verified(aspis_core::field::M31::reduce_u64)]
 #[kani::unwind(70)]
 fn finish64_with_verified_reducer() {
  let rows:[[u64;4];64]=kani::any();
  let pending=BatchedWeights{raw:rows.to_vec(),terms:kani::any()};
  let mut weights=vec![K::default();64];pending.finish(&mut weights);
  let result=finish_owned(rows.to_vec(),vec![K::default();64]);
  for j in 0..64 {
   assert_eq!(weights[j].c0.a.0,result[j].c0.a.0);
   assert_eq!(weights[j].c0.b.0,result[j].c0.b.0);
   assert_eq!(weights[j].c1.a.0,result[j].c1.a.0);
   assert_eq!(weights[j].c1.b.0,result[j].c1.b.0);
  }
 }
}

#[cfg(all(kani,feature="iterator-contract-probe"))] mod iterator_contract;
