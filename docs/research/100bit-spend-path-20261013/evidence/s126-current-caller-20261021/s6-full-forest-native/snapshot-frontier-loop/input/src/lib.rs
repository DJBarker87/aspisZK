#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::{poseidon2::Digest,atomic_statement::encode_digest_canonical,pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1 as Snapshot};
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
 fn unrolled_loop(snapshot:&Snapshot,output:&mut[u8]) {output[160..192].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[0]));
output[192..224].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[1]));
output[224..256].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[2]));
output[256..288].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[3]));
output[288..320].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[4]));
output[320..352].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[5]));
output[352..384].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[6]));
output[384..416].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[7]));
output[416..448].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[8]));
output[448..480].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[9]));
output[480..512].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[10]));
output[512..544].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[11]));
output[544..576].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[12]));
output[576..608].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[13]));
output[608..640].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[14]));
output[640..672].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[15]));
output[672..704].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[16]));
output[704..736].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[17]));
output[736..768].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[18]));
output[768..800].copy_from_slice(&encode_digest_canonical(&snapshot.frontier[19]));}
 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(128)]
 fn frontier_loop_matches_unrolled_on_exact_frame() {
  // Complete original native snapshot, no fabricated enum/pointer/reference.
  let snapshot:Snapshot=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<Snapshot>()]>())};
  let before:[u8;800]=kani::any();let mut left=before;let mut right=before;
  let index:usize=kani::any();kani::assume(index<800);
  original_loop(&snapshot,&mut left);unrolled_loop(&snapshot,&mut right);
  assert_eq!(left[index],right[index]);
 }
}
