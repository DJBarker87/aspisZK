//! Shared pair-forest initialization/request data.

use aspis_core::field::M31;
use aspis_statement::pool_v1::VerifierPolicyV1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolInitializationV1 {
    pub asset_mint: [u8; 32],
    pub token_program: [u8; 32],
    pub asset_id: M31,
    pub deployment_domain: [u8; 32],
    pub verifier_policy: VerifierPolicyV1,
}
