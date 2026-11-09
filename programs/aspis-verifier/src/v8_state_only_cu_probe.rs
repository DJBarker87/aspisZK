//! Never-production, unmined diagnostic path (PoW rejection disabled).
//! Calls the reference atomic-v3 verifier without changing its implementation.
//! Account 0 is the verifier-owned, sealed ASPU proof account, read-only.
//! Wire: diagnostic tag 240 followed by the canonical 216-byte public statement.

use aspis_statement::{
    decode_asset_id_canonical, decode_digest_canonical, encode_atomic_payment_statement_v4,
    state_only_verify::{
        verify_atomic_state_only_candidate_unmined_for_diagnostics_v3, StateOnlyVerifyPhase,
    },
    AtomicPaymentStatementV4, SpendPublic,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, hash::hashv, log::sol_log_compute_units,
    msg, program_error::ProgramError, pubkey::Pubkey,
};

pub const V8_STATE_ONLY_CU_PROBE_TAG: u8 = 240;
pub const V8_STATE_ONLY_CU_PROBE_WIRE_BYTES: usize = 217;

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_v8_state_only_cu_probe_instruction);

#[inline(never)]
fn trace(phase: StateOnlyVerifyPhase) {
    use StateOnlyVerifyPhase::*;
    let name = match phase {
        Parsed => "v8-state-only:parsed",
        Transcript => "v8-state-only:transcript-sumcheck",
        Terminal => "v8-state-only:terminal",
        Relation => "v8-state-only:relation-final-polynomial",
        OpeningsParsed => "v8-state-only:merkle-openings",
        QueriesDone => "v8-state-only:fri-queries",
        TerminalPrepared => "v8-state-only:terminal-prepared",
        TerminalPoseidon => "v8-state-only:terminal-poseidon",
        TerminalSemanticInitial => "v8-state-only:terminal-semantic-initial",
        TerminalSemanticAbsorption => "v8-state-only:terminal-semantic-absorption",
        TerminalSemanticMerkle => "v8-state-only:terminal-semantic-merkle",
        TerminalSemanticRange => "v8-state-only:terminal-semantic-range",
        TerminalSemanticPublic => "v8-state-only:terminal-semantic-public",
        TerminalCopyPatterns => "v8-state-only:terminal-copy-patterns",
        TerminalCopyRouting => "v8-state-only:terminal-copy-routing",
        TerminalCopy => "v8-state-only:terminal-copy",
        TerminalCompositionEquality => "v8-state-only:terminal-composition-equality",
        TerminalMask => "v8-state-only:terminal-mask",
        TerminalFinal => "v8-state-only:terminal-final",
    };
    msg!(name);
    sol_log_compute_units();
}

fn decode_statement(bytes: &[u8]) -> Result<AtomicPaymentStatementV4, ProgramError> {
    let invalid = |_| ProgramError::InvalidInstructionData;
    let statement = AtomicPaymentStatementV4 {
        pool: bytes[8..40].try_into().unwrap(),
        sequence: u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
        spend: SpendPublic {
            anchor: decode_digest_canonical(bytes[48..80].try_into().unwrap()).map_err(invalid)?,
            nullifier: decode_digest_canonical(bytes[80..112].try_into().unwrap())
                .map_err(invalid)?,
            output_commitment: decode_digest_canonical(bytes[112..144].try_into().unwrap())
                .map_err(invalid)?,
            asset_id: decode_asset_id_canonical(u32::from_le_bytes(
                bytes[176..180].try_into().unwrap(),
            ))
            .map_err(invalid)?,
            fee: u32::from_le_bytes(bytes[180..184].try_into().unwrap()),
        },
        output_anchor: decode_digest_canonical(bytes[144..176].try_into().unwrap())
            .map_err(invalid)?,
        deployment_domain: bytes[184..216].try_into().unwrap(),
    };
    if encode_atomic_payment_statement_v4(&statement)
        .map_err(invalid)?
        .as_slice()
        != bytes
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(statement)
}

pub fn process_v8_state_only_cu_probe_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    data: &[u8],
) -> ProgramResult {
    if data.len() != V8_STATE_ONLY_CU_PROBE_WIRE_BYTES || data[0] != V8_STATE_ONLY_CU_PROBE_TAG {
        return Err(ProgramError::InvalidInstructionData);
    }
    let statement = decode_statement(&data[1..])?;
    if accounts.len() != 1 {
        return Err(ProgramError::NotEnoughAccountKeys);
    }
    let account = &accounts[0];
    if account.owner != program_id || account.is_writable || account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    let bytes = account.try_borrow_data()?;
    if !crate::lifecycle::proof_account_finalized(&bytes) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (start, end) = crate::lifecycle::uploaded_proof_bounds(&bytes)?;
    if end != bytes.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    msg!("v8-state-only:begin");
    sol_log_compute_units();
    let verified = verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
        &bytes[start..end],
        &statement,
        |parts| hashv(parts).to_bytes(),
        Some(trace),
    )
    .map_err(|_| ProgramError::InvalidInstructionData)?;
    drop(verified);
    msg!("v8-state-only:done");
    sol_log_compute_units();
    Ok(())
}
