#![allow(unexpected_cfgs)]
use aspis_statement::{atomic_statement::encode_digest_canonical,pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1 as Afterstate};
pub fn frontier_step(afterstate:&Afterstate,mut output:[u8;688],level:usize)->[u8;688] {
 let start=48+32*level;
 output[start..start+32].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[level]));
 output
}
pub fn frontier_owned(afterstate:&Afterstate,mut output:[u8;688])->[u8;688] {
 for level in 0..20 {output=frontier_step(afterstate,output,level);}
 output
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

fn original_loop(afterstate:&Afterstate,output:&mut[u8;688]) {for (level, node) in afterstate.next_frontier.iter().enumerate() {
        let start = 48 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn original_frontier_matches_owned_loop() {
  let afterstate:Afterstate=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Afterstate>()]>())};
  let before:[u8;688]=kani::any();let mut left=before;
  let index:usize=kani::any();kani::assume(index<688);
  original_loop(&afterstate,&mut left);let right=frontier_owned(&afterstate,before);
  assert_eq!(left[index],right[index]);
 }
}
