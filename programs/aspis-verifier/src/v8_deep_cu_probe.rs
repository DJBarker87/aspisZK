//! Local-only SBF reachability and CU probe for V8's two-point DEEP kernel.
//!
//! This deliberately has no production dispatch, lifecycle write, Pool CPI,
//! or state transition. The sole account is a read-only V8 research body.
//! Instruction byte zero selects one of two equivalent implementations:
//! heap-backed batch inversion or pointwise streaming inversion.

use aspis_core::field::{CM31, M31, QM31};
use aspis_core::transcript::{label, Transcript};
use aspis_core::v8_a100::{
    V8A100Wire, V8_A100_FRONTIER_MAX_PER_TREE, V8_A100_MAX_FRONTIER_FIXTURE,
    V8_A100_PROFILE_BINDING,
};
use aspis_core::v8_deep::{
    derive_v8_a100_ood_prefix, v8_deep_quotients_heap_batched_in_place,
    v8_deep_quotients_pointwise_in_place, V8A100TwoPointChallenges, V8_A100_FIBRE_SLOTS,
};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    log::{sol_log_compute_units, sol_log_data},
    msg,
    program_error::ProgramError,
    pubkey::Pubkey,
};

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_v8_deep_cu_probe_instruction);

pub const V8_DEEP_HEAP_BATCHED_MODE: u8 = 0;
pub const V8_DEEP_POINTWISE_MODE: u8 = 1;
pub const V8_DEEP_CANONICAL_PARSE_MODE: u8 = 2;

fn q(values: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(values[0]), M31(values[1])),
        c1: CM31::new(M31(values[2]), M31(values[3])),
    }
}

#[inline(never)]
fn derive_probe_challenges(
    wire: &V8A100Wire<'_>,
) -> Result<V8A100TwoPointChallenges, ProgramError> {
    let component_evaluations = wire
        .component_ood_vectors()
        .ok_or(ProgramError::InvalidAccountData)?;
    let mut transcript = Transcript::new(crate::verify::sbf_hashv);
    transcript.absorb(label::PROFILE, &V8_A100_PROFILE_BINDING);
    transcript.absorb(label::STATEMENT, &[0x5a; 32]);
    let prefix = derive_v8_a100_ood_prefix(&transcript, &component_evaluations)
        .map_err(|_| ProgramError::InvalidArgument)?;
    Ok(prefix.challenges(q([101, 307, 509, 701])))
}

#[inline(never)]
fn run_canonical_parse_probe(proof: &[u8]) -> ProgramResult {
    msg!("aspis-v8-deep:canonical-parse-start");
    sol_log_compute_units();
    V8A100Wire::parse_for_schedule(
        proof,
        V8_A100_MAX_FRONTIER_FIXTURE,
        V8_A100_FRONTIER_MAX_PER_TREE,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    sol_log_compute_units();
    sol_log_data(&[&[0u8; 16]]);
    Ok(())
}

#[inline(never)]
fn run_deep_probe(proof: &[u8], mode: u8) -> ProgramResult {
    let wire = V8A100Wire::parse_deferred_canonicality(proof, V8_A100_FRONTIER_MAX_PER_TREE)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let challenges = derive_probe_challenges(&wire)?;
    let mut output: Vec<[QM31; V8_A100_FIBRE_SLOTS]> = vec![[QM31::ZERO; V8_A100_FIBRE_SLOTS]; 22];

    msg!("aspis-v8-deep:kernel-start");
    sol_log_compute_units();
    match mode {
        V8_DEEP_HEAP_BATCHED_MODE => v8_deep_quotients_heap_batched_in_place(
            &wire,
            V8_A100_MAX_FRONTIER_FIXTURE,
            &challenges,
            &mut output,
        ),
        V8_DEEP_POINTWISE_MODE => v8_deep_quotients_pointwise_in_place(
            &wire,
            V8_A100_MAX_FRONTIER_FIXTURE,
            &challenges,
            &mut output,
        ),
        _ => return Err(ProgramError::InvalidInstructionData),
    }
    .map_err(|_| ProgramError::InvalidAccountData)?;
    sol_log_compute_units();

    // Consume every output so link-time optimization cannot discard either
    // implementation while the SBF analyzer measures its reachable frame.
    let checksum = output
        .iter()
        .flat_map(|row| row.iter())
        .copied()
        .fold(QM31::ZERO, QM31::add);
    let mut checksum_bytes = [0u8; 16];
    checksum.write_le_bytes(&mut checksum_bytes);
    sol_log_data(&[&checksum_bytes]);
    Ok(())
}

#[inline(never)]
fn run_probe(proof: &[u8], mode: u8) -> ProgramResult {
    match mode {
        V8_DEEP_HEAP_BATCHED_MODE | V8_DEEP_POINTWISE_MODE => run_deep_probe(proof, mode),
        V8_DEEP_CANONICAL_PARSE_MODE => run_canonical_parse_probe(proof),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

pub fn process_v8_deep_cu_probe_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let mode = *instruction_data
        .first()
        .ok_or(ProgramError::InvalidInstructionData)?;
    if instruction_data.len() != 1 || accounts.len() != 1 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof = accounts[0].try_borrow_data()?;
    run_probe(&proof, mode)
}
