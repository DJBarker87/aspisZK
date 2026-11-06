fn stage2_owned(program_id: &Pubkey, accounts: &[OwnedAccount], data: &[u8], current_slot: Result<u64, ProgramError>) -> ProgramResult {
    if accounts.len() != 7 || data.get(..4) != Some(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[..])
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let validated = validate_asq8(program_id, accounts, data, current_slot)?;
    let proof_data = accounts[0].data()?;
    let checkpoint_data = accounts[6].data()?;
    let proof_start = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start.checked_add(validated.proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_data.len() != proof_end {
        return Err(ProgramError::InvalidAccountData);
    }
    let public_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&validated.statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if public_bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    verifier::tx2_authenticated(
        &public_bytes,
        &proof_data[proof_start..proof_end],
        &checkpoint_data,
        super::super::SolanaDigest,
        super::super::observer(),
    )
    .map_err(super::super::error)?;
    emit_result(&validated.statement)
}
