#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::{poseidon2::Digest,atomic_statement::encode_digest_canonical as encode};
 #[kani::proof_for_contract(aspis_statement::atomic_statement::encode_digest_canonical)]
 #[kani::unwind(64)]
 fn digest_encoder_contract() {
  let digest:Digest=unsafe{core::mem::transmute(kani::any::<[u32;8]>())};
  let _=encode(&digest);
 }
 #[kani::proof]
 #[kani::stub_verified(aspis_statement::atomic_statement::encode_digest_canonical)]
 #[kani::unwind(2048)]
 fn forest_header_with_digest_contract() {
  use aspis_statement::pool_v1::pair_forest_terminal::{decode_pool_v1_pair_forest_terminal_statement_v1 as decode_forest,encode_pool_v1_pair_forest_terminal_statement_v1 as encode_forest,PoolV1PairForestTerminalStatementV1};
  let original:[u8;1880]=kani::any();let index:usize=kani::any();kani::assume(index<144);
  if let Ok(statement)=decode_forest(&original) {
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}));
   kani::cover!(matches!(statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}));
   if let Ok(encoded)=encode_forest(&statement){assert_eq!(encoded[index],original[index]);}
  }
 }
}
