#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::poseidon2::Digest;
 use aspis_statement::atomic_statement::{encode_digest_canonical as encode,decode_digest_canonical as decode};
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

 #[kani::proof]
 #[kani::unwind(64)]
 fn encoder_matches_unrolled() {
  // Digest is the complete native eight-u32-limb carrier; all bit patterns valid.
  let digest:Digest=unsafe{core::mem::transmute(kani::any::<[u32;8]>())};
  assert_eq!(encode(&digest),reference(&digest));
 }
 #[kani::proof]
 #[kani::unwind(64)]
 fn accepted_digest_roundtrip() {
  let original:[u8;32]=kani::any();
  let result=decode(&original);
  kani::cover!(result.is_ok());
  kani::cover!(result.is_err());
  if let Ok(digest)=result {assert_eq!(encode(&digest),original);}
 }
}
