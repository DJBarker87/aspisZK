//! Owned caller boundary. SDK guards exist only in snapshot/write wrappers.
use super::*;
use aspis_statement::pool_v1::{
    POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_V2_BYTES,
    POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_V2_BYTES,
};

struct OwnedAccount {
    key: Pubkey,
    owner: Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
    length: Result<usize, ProgramError>,
    bytes: Result<Vec<u8>, ProgramError>,
}
impl OwnedAccount {
    #[cfg_attr(kani, kani::ensures(|r| (*r == &self.key) && core::ptr::eq(*r,&self.key) != true)) ]
    fn key(&self) -> &Pubkey { &self.key }
    #[cfg_attr(kani, kani::ensures(|r| (*r == &self.owner) && core::ptr::eq(*r,&self.owner) != cfg!(NDG_invert_owner))) ]
    fn owner(&self) -> &Pubkey { &self.owner }
    fn data(&self) -> Result<&[u8], ProgramError> {
        match &self.bytes { Ok(bytes) => Ok(bytes), Err(error) => Err(error.clone()) }
    }
    fn data_len(&self) -> Result<usize, ProgramError> { self.length.clone() }
}

// Copy only decoder-admitted lengths; malformed lengths retain their original
// length and a deferred error. No adversarial account length drives allocation.
fn snapshot(account: &AccountInfo<'_>, length1: usize, length2: usize) -> OwnedAccount {
    let (length, bytes) = match account.try_borrow_data() {
        Ok(data) => {
            let length = data.len();
            let bytes = if length == length1 || length == length2 {
                Ok(data.to_vec())
            } else { Err(ProgramError::InvalidAccountData) };
            (Ok(length), bytes)
        }
        Err(error) => (Err(error.clone()), Err(error)),
    };
    OwnedAccount { key: *account.key, owner: *account.owner,
        is_signer: account.is_signer, is_writable: account.is_writable,
        executable: account.executable, length, bytes }
}

fn require_readonly_buffer(account: &OwnedAccount) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}
fn require_readonly_account(account: &OwnedAccount, owner: &Pubkey) -> ProgramResult {
    readonly_meta_ok(account.owner(), owner, account.is_signer, account.is_writable, account.executable)
}
fn require_verifier_checkpoint(account: &OwnedAccount, program_id: &Pubkey, writable: bool) -> ProgramResult {
    if account.owner() != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.data_len()? != verifier::checkpoint_size(Variant::S2) {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_distinct_accounts<const N: usize>(accounts: &[&OwnedAccount; N]) -> ProgramResult {
    let mut index = 0;
    while index < N {
        let mut previous = 0;
        while previous < index {
            if accounts[previous].key() == accounts[index].key() {
                return Err(ProgramError::InvalidArgument);
            }
            previous += 1;
        }
        index += 1;
    }
    Ok(())
}
fn require_zero(mut remaining: &[u8]) -> ProgramResult {
    while !remaining.is_empty() {
        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        remaining = &remaining[1..];
    }
    Ok(())
}
#[inline(never)]
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

#[inline(never)]
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

#[inline(never)]
fn validate_asq8(
    verifier_program: &Pubkey,
    accounts: &[OwnedAccount],
    instruction_data: &[u8],
    current_slot: Result<u64, ProgramError>,
) -> Result<ValidatedAsqa, ProgramError> {
    if instruction_data.len() != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    let request = decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if request.verifier_profile != PROFILE_BINDING
        || request.verifier_release != RELEASE_BINDING
        || request.pool_program != pool_program_id()
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let pool_program = Pubkey::new_from_array(request.pool_program);
    let output_lane = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let authenticated = authenticate_asq8_accounts(
        verifier_program,
        accounts,
        &pool_program,
        output_lane,
        current_slot?,
    )?;
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let scanned = scan_proof_buffer(proof_account.data()?)?;
    let statement =
        reconstruct_asq8_statement(&request, &authenticated, &scanned.candidate_afterstate)?;
    Ok(ValidatedAsqa {
        statement,
        proof_length: scanned.proof_length,
    })
}

#[inline(never)]
fn stage1_owned(program_id: &Pubkey, accounts: &[OwnedAccount], data: &[u8]) -> Result<Vec<u8>, ProgramError> {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    let checkpoint_account = &accounts[2];
    require_distinct_accounts(&[proof_account, public_account, checkpoint_account])?;
    require_readonly_buffer(proof_account)?;
    require_readonly_buffer(public_account)?;
    require_verifier_checkpoint(checkpoint_account, program_id, true)?;
    let checkpoint_data = checkpoint_account.data()?;
    require_zero(checkpoint_data)?;
    let public_data = public_account.data()?;
    let statement = decode_public_statement_box(&public_data)?;
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let candidate = encode_pool_v1_pair_verified_afterstate_v1(
        &statement.common().lane_transition.candidate_afterstate,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;

    let proof_data = proof_account.data()?;
    let proof_length = verifier::PROOF_BYTES;
    let proof_start = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start.checked_add(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_data.len() != proof_end
        || proof_data[..proof_start] != candidate
        || proof_data[proof_start + 8] != Variant::S2.tag()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let checkpoint = super::super::first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)?;
    if checkpoint.len() != checkpoint_data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(checkpoint)
}

#[inline(never)]
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

pub(super) fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let owned = [
        snapshot(&accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES),
        snapshot(&accounts[1], POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES),
        snapshot(&accounts[2], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES),
    ];
    let checkpoint = stage1_owned(program_id, &owned, data)?;
    accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);
    #[cfg(feature="cu-profiling")]
    { msg!("r1:pool-adapter-stage1-checkpoint-written"); solana_program::log::sol_log_compute_units(); }
    Ok(())
}

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

#[cfg(kani)]
#[path="NDG_owned.rs"]
mod NDG_owned;
