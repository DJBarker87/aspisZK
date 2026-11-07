use super::*;
use aspis_core::field::M31;
#[path="PCF_LaneReference.rs"]mod scalar;
const PCF_P:u32=2147483647;
fn canonical_reply(d:&Digest)->bool {
 d[0].0<PCF_P && d[1].0<PCF_P && d[2].0<PCF_P && d[3].0<PCF_P &&
 d[4].0<PCF_P && d[5].0<PCF_P && d[6].0<PCF_P && d[7].0<PCF_P
}
fn first_reply(d:&Digest)->u8 {
 assert!(canonical_reply(d));
 d[0].0 as u8
}
pub(super) fn reference(d:&Digest)->Result<u8,PoolV1PairForestAccountErrorV1> {
 let r=scalar::lane_reference(d[0].0,d[1].0,d[2].0,d[3].0,d[4].0,d[5].0,d[6].0,d[7].0);
 if r==256 {Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest)} else {Ok(r as u8)}
}
#[cfg(kani)]
#[kani::proof_for_contract(pool_v1_pair_forest_deposit_lane_v1)]
#[kani::stub(digest_is_canonical,canonical_reply)]
#[kani::stub(first_canonical_byte,first_reply)]
fn lane_contract_proof(){
 let w:[u32;8]=kani::any();
 let d=[M31(w[0]),M31(w[1]),M31(w[2]),M31(w[3]),M31(w[4]),M31(w[5]),M31(w[6]),M31(w[7])];
 let _=pool_v1_pair_forest_deposit_lane_v1(&d);
}
