fn authenticate_invariant_release_registry(
    verifier_program: &Pubkey,
    pool_program: &Pubkey,
    master_account: &OwnedAccount,
    master: &PoolV1PairForestMasterV1,
    registry_account: &OwnedAccount,
    entry_account: &OwnedAccount,
    current_slot: u64,
) -> ProgramResult {
    // Versioned, owner-authenticated registry images carry the canonical bumps
    // saved by their initializers. Address checks below perform one derivation;
    // they neither search for a bump nor establish canonicality independently.
    if pool_program.to_bytes() != pool_program_id()
        || master.verifier_policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY == 0
        || master.verifier_policy.registry_program != registry_program_id()
        || master.verifier_policy.registry_authority != [0u8; 32]
        || master.verifier_policy.policy_binding != AUDIT_POLICY_BINDING
    {
        return Err(ProgramError::InvalidAccountData);
    }
    validate_verifier_policy_v1(&master.verifier_policy)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let registry_program = Pubkey::new_from_array(registry_program_id());
    require_readonly_account(registry_account, &registry_program)?;
    let immutable_deployment =
        master.verifier_policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0;
    if immutable_deployment {
        let loader = bpf_loader_upgradeable::id();
        let registry = decode_verifier_registry_v2(registry_account.data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let expected_registry = Pubkey::create_program_address(
            &[
                VERIFIER_REGISTRY_V2_SEED,
                master_account.key().as_ref(),
                &[registry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry_account.key() != &expected_registry {
            return Err(ProgramError::InvalidAccountData);
        }
        let registry_programdata = Pubkey::create_program_address(
            &[registry_program.as_ref(), &[registry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry.pool != master_account.key().to_bytes()
            || registry.authority != master.verifier_policy.registry_authority
            || registry.policy_binding != master.verifier_policy.policy_binding
            || registry.registry_program != registry_program.to_bytes()
            || registry.loader_program != loader.to_bytes()
            || registry.programdata_address != registry_programdata.to_bytes()
            || !registry.is_immutable()
            || registry.is_paused()
        {
            return Err(ProgramError::InvalidAccountData);
        }
        require_readonly_account(entry_account, &registry_program)?;
        let entry = decode_verifier_registry_entry_v2(entry_account.data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let expected_entry = Pubkey::create_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master_account.key().as_ref(),
                &PROFILE_BINDING,
                &RELEASE_BINDING,
                &[entry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry_account.key() != &expected_entry {
            return Err(ProgramError::InvalidAccountData);
        }
        let verifier_programdata = Pubkey::create_program_address(
            &[verifier_program.as_ref(), &[entry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry.pool != master_account.key().to_bytes()
            || entry.policy_binding != AUDIT_POLICY_BINDING
            || entry.verifier_program != verifier_program.to_bytes()
            || entry.profile_binding != PROFILE_BINDING
            || entry.release_binding != RELEASE_BINDING
            || entry.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
            || entry.loader_program != loader.to_bytes()
            || entry.programdata_address != verifier_programdata.to_bytes()
            || entry.expected_upgrade_authority != [0u8; 32]
            || !entry.is_active_at(current_slot)
        {
            return Err(ProgramError::InvalidAccountData);
        }
        return Ok(());
    }

    let registry = decode_verifier_registry_v1(registry_account.data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let expected_registry = Pubkey::create_program_address(
        &[
            VERIFIER_REGISTRY_SEED,
            master_account.key().as_ref(),
            &[registry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if registry_account.key() != &expected_registry {
        return Err(ProgramError::InvalidAccountData);
    }
    if registry.pool != master_account.key().to_bytes()
        || registry.authority != master.verifier_policy.registry_authority
        || registry.policy_binding != master.verifier_policy.policy_binding
        || !registry.is_immutable()
        || registry.is_paused()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    require_readonly_account(entry_account, &registry_program)?;
    let entry = decode_verifier_registry_entry_v1(entry_account.data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let expected_entry = Pubkey::create_program_address(
        &[
            VERIFIER_ENTRY_SEED,
            master_account.key().as_ref(),
            &PROFILE_BINDING,
            &RELEASE_BINDING,
            &[entry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if entry_account.key() != &expected_entry {
        return Err(ProgramError::InvalidAccountData);
    }
    if entry.pool != master_account.key().to_bytes()
        || entry.policy_binding != AUDIT_POLICY_BINDING
        || entry.verifier_program != verifier_program.to_bytes()
        || entry.profile_binding != PROFILE_BINDING
        || entry.release_binding != RELEASE_BINDING
        || entry.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
        || !entry.is_active_at(current_slot)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
