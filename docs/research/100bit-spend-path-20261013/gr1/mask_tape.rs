//! Audit the complete cost-test tape, using exactly prove_masked_fixture's derivation.
use aspis_core::{field::{M31, QM31}, state_only_hiding::StateOnlyHidingContext};
use aspis_prover::{HOST_HASH, state_only_entropy::StateOnlyAttemptSecrets, state_only_hiding::{InMemoryStateOnlyMaskNonceStore,apply_pool_v1_pair_forest_mask_material_v1}};
use aspis_statement::pool_v1::{pool_v1_pair_forest_relation_free_mask_cells_v1,pool_v1_pair_forest_copy_active_row_masks_v1};
use serde_json::json;
use sha2::{Digest,Sha256};
fn sha(b:&[u8])->String {format!("{:x}",Sha256::digest(b))}
fn km(v:&[QM31])->Vec<u8>{v.iter().flat_map(|x|{let mut b=[0;16];x.write_le_bytes(&mut b);b}).collect()}
fn main(){
 assert!(!cfg!(debug_assertions));let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),3);
 let seed:[u8;32]=core::array::from_fn(|i|u8::from_str_radix(&a[2][2*i..2*i+2],16).unwrap());
 let cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();let masks=pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
 let active=|r:usize|masks[r>>4]&(1<<(r&15))!=0;let inactive=(0..1024).filter(|r|!active(*r)).count();let mut result=vec![];
 for (w,name) in [(false,"transfer"),(true,"withdrawal")] {
  let f=aspis_prover::r0_fixture::prepare(w);let public=f.public().public_bytes().unwrap();
  let secret=|domain:&[u8]|HOST_HASH(&[domain,&seed,&public,&[2]]);
  let context=StateOnlyHidingContext::pool_v1_pair_forest_v1(HOST_HASH(&[&public]),secret(b"UNPROVED:R1:fixture-mask-nonce"));
  let binding=HOST_HASH(&[b"UNPROVED:R1:full-mask-fixture",&public,&[2],&context.encode()]);
  let attempt=StateOnlyAttemptSecrets::deterministic_spend_fixture(context.mask_nonce,secret(b"UNPROVED:R1:fixture-field-entropy"),secret(b"UNPROVED:R1:fixture-leaf-seed"));
  let (reserved,material)=attempt.reserve_and_build_pool_v1_pair_forest_mask_material_v1(HOST_HASH,binding,context,&mut InMemoryStateOnlyMaskNonceStore::default()).unwrap();
  let mut c1=f.compiled.semantic_c1.clone();let applied=apply_pool_v1_pair_forest_mask_material_v1(&mut c1,material).unwrap();
  let d=reserved.derive_pool_v1_pair_forest_zero_factor_d(HOST_HASH,context).unwrap();assert_eq!(d.len(),1024);
  let deltas:Vec<_>=cells.iter().map(|c|c1.c1[c.column as usize][c.row as usize].sub(f.compiled.semantic_c1.c1[c.column as usize][c.row as usize])).collect();
  assert_eq!(deltas.iter().filter(|x|**x!=M31::ZERO).count(),cells.len());
  assert!(applied.h1_padding.iter().enumerate().all(|(r,x)|if active(r){*x==QM31::ZERO}else{*x!=QM31::ZERO}));
  assert!(applied.g.iter().all(|x|*x!=QM31::ZERO)&&d.iter().all(|x|*x!=QM31::ZERO));
  assert!(applied.mask_only_c1.iter().flatten().all(|x|*x!=M31::ZERO));
  let delta_bytes:Vec<_>=deltas.iter().flat_map(|x|x.0.to_le_bytes()).collect();
  let mask_bytes:Vec<_>=applied.mask_only_c1.iter().flatten().flat_map(|x|x.0.to_le_bytes()).collect();
  result.push(json!({"fixture":name,"eligible_noise_cells":cells.len(),"eligible_noise_changed_cells":deltas.len(),"eligible_delta_sha256":sha(&delta_bytes),"mask_only_cells":10240,"mask_only_sha256":sha(&mask_bytes),"G_rows":1024,"G_sha256":sha(&km(&applied.g)),"D_rows":d.len(),"D_sha256":sha(&km(&d)),"H1_padding_inactive_rows":inactive,"H1_padding_free_samples":inactive-1,"H1_padding_sha256":sha(&km(&applied.h1_padding)),"all_eligible_and_full_word_cells_nonzero_for_this_seed":true,"active_H1_padding_zero":true}));
 }
 let p=std::path::Path::new(&a[1]);assert!(!p.exists());std::fs::write(p,serde_json::to_string_pretty(&json!({"seed_hex":a[2],"fixtures":result})).unwrap()+"\n").unwrap();
}
