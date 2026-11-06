use super::*;
pub(super) fn reference()->() {()}
fn clear_empty(bytes:&[u8]) {assert!(bytes.is_empty());kani::cover!(bytes.is_empty(),"exact empty request reached");}
fn clear_wrong(bytes:&[u8]) {assert!(!bytes.is_empty());}
#[kani::proof_for_contract(<SolanaPairForestVerifierRuntimeV1 as PairForestVerifierRuntimeV1>::clear_return_data)]
#[kani::stub(solana_program::program::set_return_data,clear_empty)]
fn clear_contract(){let mut rt=SolanaPairForestVerifierRuntimeV1;rt.clear_return_data();}
#[kani::proof_for_contract(<SolanaPairForestVerifierRuntimeV1 as PairForestVerifierRuntimeV1>::clear_return_data)]
#[kani::stub(solana_program::program::set_return_data,clear_wrong)]
fn clear_wrong_argument(){let mut rt=SolanaPairForestVerifierRuntimeV1;rt.clear_return_data();}
