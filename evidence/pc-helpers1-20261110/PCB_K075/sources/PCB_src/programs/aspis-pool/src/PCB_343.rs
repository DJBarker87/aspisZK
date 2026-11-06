use super::*;
fn fixture()->PoolV1PairForestTerminalResultV1 {PoolV1PairForestTerminalResultV1 {
 transition_kind:aspis_statement::pool_v1::PoolV1TransitionKind::PrivateTransfer,master_account:[0;32],selected_lane_account:[0;32],output_lane:0,nullifier:[aspis_core::field::M31::ZERO;8],verified_afterstate:aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1 {next_pair_index:kani::any(),next_root:[aspis_core::field::M31::ZERO;8],next_frontier:[[aspis_core::field::M31::ZERO;8];aspis_statement::pool_v1::POOL_V1_PAIR_TREE_DEPTH]}}}
fn correct(x:&AuthenticatedPairForestResultV1)->&PoolV1PairForestTerminalResultV1 {&x.value}
fn wrong(_:&AuthenticatedPairForestResultV1)->&PoolV1PairForestTerminalResultV1 {Box::leak(Box::new(fixture()))}
#[kani::proof] #[kani::stub(AuthenticatedPairForestResultV1::value,correct)]
fn value_correct(){let x=AuthenticatedPairForestResultV1 {value:Box::new(fixture()),exact_bytes:alloc::vec::Vec::<u8>::new().into_boxed_slice()};assert!(core::ptr::eq(x.value(),&*x.value));}
#[kani::proof] #[kani::stub(AuthenticatedPairForestResultV1::value,wrong)]
fn value_wrong(){let x=AuthenticatedPairForestResultV1 {value:Box::new(fixture()),exact_bytes:alloc::vec::Vec::<u8>::new().into_boxed_slice()};assert!(core::ptr::eq(x.value(),&*x.value));}
