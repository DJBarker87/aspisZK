fn authenticate_asq8_accounts(
    verifier_program: &Pubkey,
    accounts: &[OwnedAccount],
    pool_program: &Pubkey,
    output_lane: u8,
    current_slot: u64,
) -> Result<AuthenticatedAsq8Accounts, ProgramError> {
    let [proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account, verifier_checkpoint] =
        accounts
    else {
        return Err(if accounts.len() < 7 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_readonly_buffer(proof_account)?;
    require_verifier_checkpoint(verifier_checkpoint, verifier_program, false)?;
    require_readonly_account(master_account, pool_program)?;
    require_readonly_account(checkpoint_account, pool_program)?;
    require_readonly_account(lane_account, pool_program)?;
    require_distinct_accounts(&[
        proof_account,
        master_account,
        checkpoint_account,
        lane_account,
        registry_account,
        entry_account,
        verifier_checkpoint,
    ])?;

    let master = decode_master_box(master_account.data()?)?;
    if master.identity.pool != master_account.key().to_bytes()
        || master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
                &[master.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *master_account.key()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    authenticate_invariant_release_registry(
        verifier_program,
        pool_program,
        master_account,
        &master,
        registry_account,
        entry_account,
        current_slot,
    )?;

    let checkpoint = decode_checkpoint_box(checkpoint_account.data()?)?;
    if checkpoint.master != master_account.key().to_bytes()
        || checkpoint.deployment_domain != master.identity.deployment_domain
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key().as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
                &[checkpoint.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *checkpoint_account.key()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let selected_lane = decode_lane_from_pool_release(lane_account.data()?)?;
    if selected_lane.master != master_account.key().to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key().as_ref(),
                &[output_lane],
                &[selected_lane.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *lane_account.key()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let live_snapshot = Box::new(PoolV1PairLiveSnapshotV1 {
        pool: master_account.key().to_bytes(),
        deployment_domain: master.identity.deployment_domain,
        sequence: selected_lane.tree.next_leaf_index,
        next_pair_index: selected_lane.tree.next_leaf_index,
        current_root: selected_lane.tree.root,
        frontier: selected_lane.tree.frontier,
    });
    Ok(AuthenticatedAsq8Accounts {
        master_account: master_account.key().to_bytes(),
        checkpoint_account: checkpoint_account.key().to_bytes(),
        selected_lane_account: lane_account.key().to_bytes(),
        master,
        checkpoint,
        selected_lane,
        live_snapshot,
    })
}
