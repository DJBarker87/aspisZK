//! Research hook AFTER the unchanged ASQ8 account/registry/ASF8 validation.
//! Only the proof grammar, research profile and cryptographic callback change.
#[path="relation_callback.rs"] mod callback;
#[path="complete_binding.rs"] mod binding;
use aspis_statement::pool_v1::*;
use solana_program::{entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
pub fn verify(id:&Pubkey,proof_key:&Pubkey,proof:&[u8],statement:&PoolV1PairForestTerminalStatementV1,digest:[u8;32])->ProgramResult{
    let attempt=binding::bind_attempt(crate::verify::sbf_hashv,&digest,&id.to_bytes(),&proof_key.to_bytes());
    let public=match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer{public,..}=>PoolV1PairForestTerminalPaymentV1::PrivateTransfer(*public),
        PoolV1PairForestTerminalStatementV1::Withdrawal{public,..}=>PoolV1PairForestTerminalPaymentV1::Withdrawal(*public),
    };
    callback::performance_verifier::verify_payment(proof,&attempt,&public,&statement.common().lane_transition).map_err(ProgramError::Custom)
}
