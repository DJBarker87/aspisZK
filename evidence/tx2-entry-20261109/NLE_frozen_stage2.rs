pub(super) fn stage2(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if accounts.len() != 7 || data.get(..4) != Some(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[..]) {
        return Err(ProgramError::InvalidInstructionData);
    }
    program::set_return_data(&[]);
    #[cfg(feature="cu-profiling")]
    { msg!("r1:pool-adapter-stage2-begin"); solana_program::log::sol_log_compute_units(); }
    let owned = [
        snapshot(&accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES),
        snapshot(&accounts[1], POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES),
        snapshot(&accounts[2], POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
        snapshot(&accounts[3], POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES),
        snapshot(&accounts[4], POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_V2_BYTES),
        snapshot(&accounts[5], POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_V2_BYTES),
        snapshot(&accounts[6], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES),
    ];
    let current_slot = match Clock::get() { Ok(clock) => Ok(clock.slot), Err(error) => Err(error) };
    stage2_owned(program_id, &owned, data, current_slot)
}
