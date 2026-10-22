use aspis_prover::{state_only_entropy::{DurableStateOnlyMaskNonceStore,StateOnlyAttemptSecrets},HOST_HASH};
use aspis_r1_cost_probe::{prover,transport::Variant,verifier,dense,speed_prof};
use aspis_core::digest::LegacyHashFn;
use std::{time::Instant,path::Path};
use serde_json::json;
fn main(){
 assert!(!cfg!(debug_assertions));
 let args:Vec<_>=std::env::args().collect();let n:usize=args[1].parse().unwrap();let out=Path::new(&args[2]);std::fs::create_dir(out).unwrap();
 let mut rows=vec![];
 for i in 0..n {for withdrawal in [false,true] {
 let fixture=aspis_prover::r0_fixture::prepare(withdrawal);
 let public=aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap().to_vec();
 let dir=out.join(format!("ledger-{i}-{withdrawal}"));let mut ledger=DurableStateOnlyMaskNonceStore::open(&dir).unwrap();
 let _=speed_prof::take();
 let start=Instant::now();
 let result=prover::prove_masked_retrying_with(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger,|_|{
 let mut nonce=[0u8;32];getrandom::fill(&mut nonce).unwrap();StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce).map_err(|_|verifier::Error::Entropy)
 }).expect("successful retry loop");
 let seconds=start.elapsed().as_secs_f64();let phases=speed_prof::take();
 let checkpoint=verifier::tx1(fixture.public(),&public,&result.proof,verifier::SPLIT,LegacyHashFn(HOST_HASH),None).unwrap();
 verifier::tx2(&public,&result.proof,&checkpoint,LegacyHashFn(HOST_HASH),None).unwrap();dense::verify(fixture.public(),&result.proof,HOST_HASH).unwrap();
 let row=json!({"fixture":if withdrawal {"withdrawal"}else{"transfer"},"run":i,"wall_seconds":seconds,"attempts":result.attempts,"proof_bytes":result.proof.len(),"verified_strict_dense":true,"phases_inclusive_exclusive_calls":phases});
 println!("SPEED_ROW {}",row);rows.push(row);std::fs::write(out.join("rows.json"),serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
 }}
}
