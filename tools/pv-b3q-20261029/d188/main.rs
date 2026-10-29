extern crate alloc;
use aspis_core::field::{M31,CM31,QM31};
use aspis_statement::state_only_poseidon::StateOnlyPoseidonOpenings;
#[path="/home/dombarker/project-offloads/codex-pv-b3p6-20261028/source/tools/pv-b3p6-20261028/v244/host_terminal_field.rs"] mod host_terminal_field;
#[path="/home/dombarker/project-offloads/codex-pv-b3p6-20261028/source/tools/pv-b3p6-20261028/v244/reference_field.rs"] mod reference_field;
mod reference_terminal;
mod reference_copy_terminal;
mod reference_poseidon;
fn q(n:u32)->QM31 {QM31{c0:CM31::new(M31(n),M31(n*17)),c1:CM31::new(M31(n*31),M31(n*47))}}
fn openings(n:u32)->StateOnlyPoseidonOpenings {StateOnlyPoseidonOpenings{z:core::array::from_fn(|i|q(n+i as u32)),succ_z:core::array::from_fn(|i|q(n+20+i as u32)),xor12_z:core::array::from_fn(|i|q(n+40+i as u32))}}
fn selectors(n:u32)->reference_copy_terminal::Selectors {reference_copy_terminal::Selectors{high:core::array::from_fn(|i|q(n+100+i as u32)),low:core::array::from_fn(|i|q(n+i as u32))}}
fn emit(name:&str,seed:u32,values:&[QM31]) {let words:Vec<u64>=values.iter().flat_map(|q|[q.c0.a.0 as u64,q.c0.b.0 as u64,q.c1.a.0 as u64,q.c1.b.0 as u64]).collect();emit_words(name,seed,&words);}
fn emit_words(name:&str,seed:u32,values:&[u64]) {println!("{{\"function\":\"{name}\",\"seed\":{seed},\"limbs\":{values:?}}}");}
fn main(){assert!(!cfg!(debug_assertions));for seed in [0,1,7,19] {reference_terminal::observe(seed);reference_poseidon::observe(seed);reference_copy_terminal::observe(seed);reference_terminal::observe_more(seed);
 let n=(seed+1)*131;let values:[QM31;4]=core::array::from_fn(|i|q(n+i as u32));
 for length in 0..=4 {let h=host_terminal_field::qm31_pack_base4(&values[..length]);let r=reference_field::qm31_pack_base4(&values[..length]);assert_eq!(h,r);if length>0 {assert_ne!(r,QM31::ZERO);}
 emit(&format!("host_terminal_field_pack{length}"),seed,&[h]);emit(&format!("reference_field_pack{length}"),seed,&[r]);}
}}
