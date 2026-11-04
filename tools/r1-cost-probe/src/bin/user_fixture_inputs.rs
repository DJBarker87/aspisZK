//! Audit-only export of the unchanged harness's public fixture notes.
use aspis_core::field::{M31,P};
use aspis_statement::{pool_v1::*,derive_owner_key,encode_digest_canonical,poseidon2::Digest};
use serde_json::json;
fn digest(seed:u32)->Digest{core::array::from_fn(|i|M31((seed+17*i as u32+1)%P))}
fn note(n:u32)->(Digest,Digest,Digest){let mut found=0;for j in 0..10000{let k=digest(10+j);let salt=digest(100+j);let cm=pool_v1_note_commitment(&derive_owner_key(&k),1000,M31(77),&salt);let nf=pool_v1_nullifier(&k,&salt);if pool_v1_pair_forest_deposit_lane_v1(&cm).unwrap()==pool_v1_pair_forest_output_lane_v1(&nf).unwrap(){if found==n{return(k,salt,cm)}found+=1;}}panic!("fixture note search exhausted")}
fn hex(b:&[u8])->String{b.iter().map(|b|format!("{b:02x}")).collect()}
fn main(){
 let mut lanes:Vec<Vec<serde_json::Value>>=vec![vec![];8];let mut records=vec![];
 for n in 0..2{let(k,salt,cm)=note(n);let lane=pool_v1_pair_forest_deposit_lane_v1(&cm).unwrap();lanes[lane as usize].push(json!([hex(&encode_digest_canonical(&cm)),"00".repeat(32)]));
 let mut r=vec![];r.extend(encode_digest_canonical(&k));r.extend(encode_digest_canonical(&salt));r.extend(1000u64.to_le_bytes());r.extend(77u32.to_le_bytes());r.extend(encode_digest_canonical(&digest(500+n)));r.extend(encode_digest_canonical(&digest(600+n)));r.extend(encode_digest_canonical(&derive_owner_key(&digest(300))));r.extend(encode_digest_canonical(&digest(400)));r.extend(600u64.to_le_bytes());assert_eq!(r.len(),212);records.push(hex(&r));}
 println!("{}",json!({"lane_leaf_sets":lanes,"records":records}));
}
