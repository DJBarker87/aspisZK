use super::*;
use crate::field::{P,M31};
pub(super) fn reference(a:u32,b:u32)->(u32,u32){
 let aa=a+a;let aa=if aa>=P{aa-P}else{aa};
 let bb=b+b;let bb=if bb>=P{bb-P}else{bb};
 ((((aa as u64)+(P as u64)-(b as u64))%(P as u64))as u32,(((a as u64)+(bb as u64))%(P as u64))as u32)
}
#[kani::proof_for_contract(cm31_mul_r)]
fn linear_contract(){let value=CM31{a:M31(kani::any()),b:M31(kani::any())};kani::assume(value.a.0<P&&value.b.0<P);let _=cm31_mul_r(value);}
