use super::*;
fn fixture()->PairPoolStateV1 {PairPoolStateV1 {
 identity:aspis_statement::pool_v1::PoolIdentityV1 {pool:[0;32],asset_mint:[0;32],token_program:[0;32],asset_id:aspis_core::field::M31::ZERO,deployment_domain:[0;32]},verifier_policy:aspis_statement::pool_v1::VerifierPolicyV1 {flags:0,registry_program:[0;32],registry_authority:[0;32],policy_binding:[0;32]},tree:aspis_statement::pool_v1::IncrementalMerkleTreeV1 {next_leaf_index:kani::any(),root:[aspis_core::field::M31::ZERO;8],frontier:[[aspis_core::field::M31::ZERO;8];aspis_statement::pool_v1::POOL_V1_TREE_DEPTH]}}}
fn correct(x:&CanonicalPairPoolStateV1)->&PairPoolStateV1 {&x.state}
fn wrong(_:&CanonicalPairPoolStateV1)->&PairPoolStateV1 {Box::leak(Box::new(fixture()))}
#[kani::proof] #[kani::stub(<CanonicalPairPoolStateV1 as core::ops::Deref>::deref,correct)]
fn state_correct(){let x=CanonicalPairPoolStateV1 {program_id:Pubkey::new_from_array([0;32]),pool:Pubkey::new_from_array([0;32]),state:Box::new(fixture())};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&*x.state));}
#[kani::proof] #[kani::stub(<CanonicalPairPoolStateV1 as core::ops::Deref>::deref,wrong)]
fn state_wrong(){let x=CanonicalPairPoolStateV1 {program_id:Pubkey::new_from_array([0;32]),pool:Pubkey::new_from_array([0;32]),state:Box::new(fixture())};assert!(core::ptr::eq(core::ops::Deref::deref(&x),&*x.state));}
