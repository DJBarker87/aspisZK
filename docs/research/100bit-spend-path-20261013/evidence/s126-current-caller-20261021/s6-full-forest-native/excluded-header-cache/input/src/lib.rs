#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
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

 #[kani::proof]
 #[kani::stub(aspis_statement::atomic_statement::encode_digest_canonical, reference)]
 #[kani::unwind(2048)]
 fn forest_header_with_checked_reference() {
  use aspis_statement::pool_v1::pair_forest_terminal::{decode_pool_v1_pair_forest_terminal_statement_v1 as decode,encode_pool_v1_pair_forest_terminal_statement_v1 as encode,PoolV1PairForestTerminalStatementV1};
  let original:[u8;1880]=kani::any();let index:usize=kani::any();kani::assume(index<144);
  if let Ok(statement)=decode(&original) {
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}));
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}));
   if let Ok(encoded)=encode(&statement){assert_eq!(encoded[index],original[index]);}
  }
 }
}
