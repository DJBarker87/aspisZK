#![allow(unexpected_cfgs)]
use aspis_statement::{atomic_statement::encode_digest_canonical,pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1 as Snapshot};
pub fn frontier_step(snapshot:&Snapshot,output:&mut[u8],level:usize) {
 let start=160+32*level;
 output[start..start+32].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[level]));
}
pub fn frontier_loop(snapshot:&Snapshot,output:&mut[u8]) {
 for level in 0..20 {frontier_step(snapshot,output,level);}
}

#[cfg(kani)] mod proofs {
 use super::*;
 use aspis_statement::poseidon2::Digest;
fn reference(d:&Digest)->[u8;32] {let mut b=[0u8;32];
b[0..4].copy_from_slice(&d[0].to_le_bytes());
b[4..8].copy_from_slice(&d[1].to_le_bytes());
b[8..12].copy_from_slice(&d[2].to_le_bytes());
b[12..16].copy_from_slice(&d[3].to_le_bytes());
b[16..20].copy_from_slice(&d[4].to_le_bytes());
b[20..24].copy_from_slice(&d[5].to_le_bytes());
b[24..28].copy_from_slice(&d[6].to_le_bytes());
b[28..32].copy_from_slice(&d[7].to_le_bytes());
b}

fn original_loop(snapshot:&Snapshot,output:&mut[u8]) {for (level, node) in snapshot.frontier.iter().enumerate() {
        let start = 160 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn original_frontier_matches_helper_loop() {
  let snapshot:Snapshot=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Snapshot>()]>())};
  let before:[u8;800]=kani::any();let mut left=before;let mut right=before;
  let index:usize=kani::any();kani::assume(index<800);
  original_loop(&snapshot,&mut left);frontier_loop(&snapshot,&mut right);
  assert_eq!(left[index],right[index]);
 }
}
