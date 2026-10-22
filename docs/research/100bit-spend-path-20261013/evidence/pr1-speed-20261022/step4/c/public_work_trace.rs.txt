//! Audit only: two independent masks at one identical public statement/shape.
use aspis_core::{digest::LegacyHashFn,HashFn};
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{host_work,prover,transport::Variant,verifier};
use sha2::{Digest,Sha256};
use serde_json::json;
fn main() {
 assert!(!cfg!(debug_assertions));
 let out=std::env::args().nth(1).unwrap();
 let hash:HashFn=HOST_HASH;
 let fixture=aspis_prover::r0_fixture::prepare(false);
 let public=aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
 let mut runs=Vec::new();let mut expected=None;
 for secret_seed in [0u8,1] {
  assert!(host_work::take_trace().is_empty());
  let seed=hash(&[b"UNPROVED:public-work-two-run",&public,&[secret_seed]]);
  let (proof,_)=prover::prove_masked_fixture(fixture.public(),&fixture.compiled,Variant::S2,hash,&seed).unwrap();
  let trace=host_work::take_trace();assert!(!trace.is_empty());
  for &[_,n,k,a,b,completed] in &trace {
   assert!(k<16);let q=n/16;let r=n%16;
   assert_eq!(a,q*k+std::cmp::min(k,r));assert_eq!(b,a+q+(k<r)as usize);assert_eq!(completed,b-a);
  }
  if let Some(previous)=&expected {assert_eq!(&trace,previous);}else{expected=Some(trace.clone());}
  verifier::tx1(fixture.public(),&public,&proof,verifier::SPLIT,LegacyHashFn(hash),None).and_then(|checkpoint|verifier::tx2(&public,&proof,&checkpoint,LegacyHashFn(hash),None)).unwrap();
  aspis_r1_cost_probe::dense::verify(fixture.public(),&proof,hash).unwrap();
  runs.push(json!({"secret_mask_seed_fixture_id":secret_seed,"proof_sha256":format!("{:x}",Sha256::digest(&proof)),"public_sha256":format!("{:x}",Sha256::digest(&public)),"events":trace}));
 }
 assert_ne!(runs[0]["proof_sha256"],runs[1]["proof_sha256"]);
 std::fs::write(out,serde_json::to_vec_pretty(&json!({"measurement_only":true,"same_public_shape":true,"different_secret_masks":true,"partition_and_completed_callbacks_equal":true,"runs":runs})).unwrap()).unwrap();
}
