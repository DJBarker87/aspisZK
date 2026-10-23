#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::{poseidon2::Digest,atomic_statement::encode_digest_canonical,pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1 as Afterstate};
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
 fn unrolled_loop(afterstate:&Afterstate,output:&mut[u8;688]) {output[48..80].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[0]));
output[80..112].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[1]));
output[112..144].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[2]));
output[144..176].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[3]));
output[176..208].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[4]));
output[208..240].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[5]));
output[240..272].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[6]));
output[272..304].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[7]));
output[304..336].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[8]));
output[336..368].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[9]));
output[368..400].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[10]));
output[400..432].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[11]));
output[432..464].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[12]));
output[464..496].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[13]));
output[496..528].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[14]));
output[528..560].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[15]));
output[560..592].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[16]));
output[592..624].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[17]));
output[624..656].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[18]));
output[656..688].copy_from_slice(&encode_digest_canonical(&afterstate.next_frontier[19]));}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn afterstate_loop_matches_unrolled_on_exact_frame() {
  // Complete original native afterstate, no fabricated enum/pointer/reference.
  let afterstate:Afterstate=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Afterstate>()]>())};
  let before:[u8;688]=kani::any();let mut left=before;let mut right=before;
  let index:usize=kani::any();kani::assume(index<688);
  original_loop(&afterstate,&mut left);unrolled_loop(&afterstate,&mut right);
  assert_eq!(left[index],right[index]);
 }
}
