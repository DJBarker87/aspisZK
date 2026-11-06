# Proposed RuntimeProgramDerivedAddress row

PROPOSED ONLY under (as)(2). Not accepted, not used by any theorem or stub.
No change to the trust inventory is asserted. FixturePdaRuntime is seven fixture invocations and does not establish this universal law.

Exact proposed text:

For every reached `sol_create_program_address` invocation made by frozen Solana Pubkey 2.4.0 `Pubkey::create_program_address` on the deployed verifier program path, let S be the SAME ordered sequence of seed byte slices, P the SAME 32 program-id bytes, and O the fresh writable 32-byte reply region actually passed to that invocation. Seed descriptors designate live initialized immutable slices, count is at most 16, each length at most 32, and O is disjoint from all inputs and every other live allocation. The runtime reads exactly S in order and P without modifying them; its only writable memory is O. It computes D = SHA256(S[0] || ... || S[n-1] || P || ASCII("ProgramDerivedAddress")), with SHA256 interpreted by the retained SHA runtime row. If D decompresses as an Edwards25519 curve point under Solana's deployed `bytes_are_curve_point` test, the syscall returns the deployed InvalidSeeds status; otherwise it returns SUCCESS (0) and writes exactly D to O. The full nonzero status is passed to the deployed PubkeyError conversion unchanged. No account, borrow counter, guard, allocator ownership, seed, program-id, or other live memory is modified. Seed-limit failures are SDK pre-syscall branches returning MaxSeedLengthExceeded and are not runtime successes. Runtime traps/divergence and malformed-pointer behaviour outside this live/disjoint domain receive no success guarantee.

This row would license the VALUE law only. The native bridge must separately establish the SAME seed order, lengths, bytes, program-id, return code, output region and frame; no address-implies-payload premise. Error conversion (including its actual supported status domain) remains an SDK source obligation. This proposal does not assert arbitrary statuses are PubkeyError values. Approval must pin the deployed runtime version and curve-decompression semantics; neither is invented here.

Frozen call-site seed requests (source snippets, no proof credit):

```rust
        let expected_registry = Pubkey::create_program_address(
            &[
                VERIFIER_REGISTRY_V2_SEED,
                master_account.key.as_ref(),
                &[registry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry_account.key != &expected_registry {
            return Err(ProgramError::InvalidAccountData);
        }
        let registry_programdata = Pubkey::create_program_address(
            &[registry_program.as_ref(), &[registry.programdata_bump]],
```

```rust
        let registry_programdata = Pubkey::create_program_address(
            &[registry_program.as_ref(), &[registry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry.pool != master_account.key.to_bytes()
            || registry.authority != master.verifier_policy.registry_authority
            || registry.policy_binding != master.verifier_policy.policy_binding
            || registry.registry_program != registry_program.to_bytes()
            || registry.loader_program != loader.to_bytes()
            || registry.programdata_address != registry_programdata.to_bytes()
            || !registry.is_immutable()
            || registry.is_paused()
        {
```

```rust
        let expected_entry = Pubkey::create_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master_account.key.as_ref(),
                &PROFILE_BINDING,
                &RELEASE_BINDING,
                &[entry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry_account.key != &expected_entry {
            return Err(ProgramError::InvalidAccountData);
        }
```

```rust
        let verifier_programdata = Pubkey::create_program_address(
            &[verifier_program.as_ref(), &[entry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry.pool != master_account.key.to_bytes()
            || entry.policy_binding != AUDIT_POLICY_BINDING
            || entry.verifier_program != verifier_program.to_bytes()
            || entry.profile_binding != PROFILE_BINDING
            || entry.release_binding != RELEASE_BINDING
            || entry.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
            || entry.loader_program != loader.to_bytes()
            || entry.programdata_address != verifier_programdata.to_bytes()
            || entry.expected_upgrade_authority != [0u8; 32]
```

```rust
    let expected_registry = Pubkey::create_program_address(
        &[
            VERIFIER_REGISTRY_SEED,
            master_account.key.as_ref(),
            &[registry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if registry_account.key != &expected_registry {
        return Err(ProgramError::InvalidAccountData);
    }
    if registry.pool != master_account.key.to_bytes()
        || registry.authority != master.verifier_policy.registry_authority
```

```rust
    let expected_entry = Pubkey::create_program_address(
        &[
            VERIFIER_ENTRY_SEED,
            master_account.key.as_ref(),
            &PROFILE_BINDING,
            &RELEASE_BINDING,
            &[entry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if entry_account.key != &expected_entry {
        return Err(ProgramError::InvalidAccountData);
    }
```

```rust
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
                &[master.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *master_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    authenticate_invariant_release_registry(
        verifier_program,
```

```rust
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
                &[checkpoint.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let selected_lane = decode_lane_from_pool_release(&lane_account.try_borrow_data()?)?;
```

```rust
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
                &[selected_lane.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *lane_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let live_snapshot = Box::new(PoolV1PairLiveSnapshotV1 {
```

Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:programs/r1-cost-probe/src/r1_pool_adapter.rs` sha256 `09ce3b480cf772c843315b9bcdabd9bf266f4065e5a524ae2a4d5560ea4feaf3`.
