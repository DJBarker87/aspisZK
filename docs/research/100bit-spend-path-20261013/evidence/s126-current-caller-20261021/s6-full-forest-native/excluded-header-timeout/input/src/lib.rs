#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::pool_v1::pair_forest_terminal::{
  decode_pool_v1_pair_forest_terminal_statement_v1 as decode,
  encode_pool_v1_pair_forest_terminal_statement_v1 as encode};
 #[kani::proof]
 #[kani::unwind(2048)]
 fn accepted_common_header_roundtrip() {
  let original:[u8;1880]=kani::any();
  let index:usize=kani::any();
  kani::assume(index<144);
  if let Ok(statement)=decode(&original) {
   kani::cover!(matches!(statement,aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1::PrivateTransfer{..}));
   kani::cover!(matches!(statement,aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalStatementV1::Withdrawal{..}));
   if let Ok(encoded)=encode(&statement) {
    assert_eq!(encoded[index],original[index]);
   }
  }
 }
}
