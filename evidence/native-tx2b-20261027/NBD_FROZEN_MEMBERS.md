# Exact frozen member bodies (source evidence only)

Revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Not a native/cohort proof. Signatures/line ranges and whole-file hashes are in NBD_MEMBERS.json.

## U04 crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1

```rust
{
    if bytes.len() != POOL_V1_IDENTITY_BYTES {
        return Err(PoolV1FormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_IDENTITY_MAGIC {
        return Err(PoolV1FormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_IDENTITY_VERSION {
        return Err(PoolV1FormatError::WrongVersion);
    }
    if bytes[5..8] != [0u8; 3] || bytes[108..112] != [0u8; 4] {
        return Err(PoolV1FormatError::NonZeroReserved);
    }
    let raw_asset_id = u32::from_le_bytes(bytes[104..108].try_into().unwrap());
    if raw_asset_id >= P {
        return Err(PoolV1FormatError::NonCanonicalAssetId);
    }
    Ok(PoolIdentityV1 {
        pool: bytes[8..40].try_into().unwrap(),
        asset_mint: bytes[40..72].try_into().unwrap(),
        token_program: bytes[72..104].try_into().unwrap(),
        asset_id: M31(raw_asset_id),
        deployment_domain: bytes[112..144].try_into().unwrap(),
    })
}
```

## U04 crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1

```rust
{
    if bytes.len() != POOL_V1_VERIFIER_POLICY_BYTES {
        return Err(PoolV1FormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_POLICY_MAGIC {
        return Err(PoolV1FormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_POLICY_VERSION {
        return Err(PoolV1FormatError::WrongVersion);
    }
    if bytes[6..8] != [0u8; 2] {
        return Err(PoolV1FormatError::NonZeroReserved);
    }
    let policy = VerifierPolicyV1 {
        flags: bytes[5],
        registry_program: bytes[8..40].try_into().unwrap(),
        registry_authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
    };
    validate_verifier_policy_v1(&policy)?;
    Ok(policy)
}
```

## U04 crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1

```rust
{
    if policy.flags & !POOL_V1_VERIFIER_POLICY_FLAGS_MASK != 0 {
        return Err(PoolV1FormatError::UnsupportedFlags);
    }
    if policy.registry_program == [0u8; 32] || policy.policy_binding == [0u8; 32] {
        return Err(PoolV1FormatError::ZeroRequiredBinding);
    }
    let immutable = policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY != 0;
    let immutable_deployment =
        policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0;
    if immutable_deployment && !immutable {
        return Err(PoolV1FormatError::InvalidAuthorityMode);
    }
    if immutable != (policy.registry_authority == [0u8; 32]) {
        return Err(PoolV1FormatError::InvalidAuthorityMode);
    }
    Ok(())
}
```

## U04 crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1

```rust
{
    if bytes.len() != POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES {
        return Err(PoolV1PairForestAccountErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_CHECKPOINT_MAGIC {
        return Err(PoolV1PairForestAccountErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8 {
        return Err(PoolV1PairForestAccountErrorV1::WrongLaneCount);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongDigestEncoding);
    }
    if bytes[176..].iter().any(|byte| *byte != 0) {
        return Err(PoolV1PairForestAccountErrorV1::NonZeroReserved);
    }
    let master: [u8; 32] = bytes[CHECKPOINT_MASTER_OFFSET..CHECKPOINT_DOMAIN_OFFSET]
        .try_into()
        .unwrap();
    let deployment_domain: [u8; 32] = bytes[CHECKPOINT_DOMAIN_OFFSET..CHECKPOINT_SEQUENCE_OFFSET]
        .try_into()
        .unwrap();
    if master == [0u8; 32] || deployment_domain == [0u8; 32] {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    let global_root = decode_digest_canonical(
        bytes[CHECKPOINT_GLOBAL_ROOT_OFFSET..CHECKPOINT_LANE_SEQUENCES_OFFSET]
            .try_into()
            .unwrap(),
    )
    .map_err(|_| PoolV1PairForestAccountErrorV1::NonCanonicalDigest)?;
    let mut lane_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for (lane, sequence) in lane_sequences.iter_mut().enumerate() {
        let start = CHECKPOINT_LANE_SEQUENCES_OFFSET + 8 * lane;
        *sequence = u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap());
        if *sequence > POOL_V1_PAIR_CAPACITY {
            return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
        }
    }
    Ok(PoolV1PairForestCheckpointV1 {
        bump: bytes[7],
        master,
        deployment_domain,
        checkpoint_sequence: u64::from_le_bytes(
            bytes[CHECKPOINT_SEQUENCE_OFFSET..CHECKPOINT_GLOBAL_ROOT_OFFSET]
                .try_into()
                .unwrap(),
        ),
        global_root,
        lane_sequences,
    })
}
```

## U04 crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1

```rust
{
    if bytes.len() != POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES {
        return Err(PoolV1PairForestAccountErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_MASTER_MAGIC {
        return Err(PoolV1PairForestAccountErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_MASTER_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8 {
        return Err(PoolV1PairForestAccountErrorV1::WrongLaneCount);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestAccountErrorV1::WrongDigestEncoding);
    }
    if bytes[50..64].iter().any(|byte| *byte != 0) || bytes[312..320] != [0u8; 8] {
        return Err(PoolV1PairForestAccountErrorV1::NonZeroReserved);
    }
    if bytes[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING {
        return Err(PoolV1PairForestAccountErrorV1::WrongFormatBinding);
    }
    let has_checkpoint = match bytes[MASTER_HAS_CHECKPOINT_OFFSET] {
        0 => false,
        1 => true,
        _ => return Err(PoolV1PairForestAccountErrorV1::InvalidBoolean),
    };
    let identity = decode_pool_identity_v1(&bytes[MASTER_IDENTITY_OFFSET..MASTER_POLICY_OFFSET])
        .map_err(|_| PoolV1PairForestAccountErrorV1::Identity)?;
    let verifier_policy = decode_verifier_policy_v1(&bytes[MASTER_POLICY_OFFSET..312])
        .map_err(|_| PoolV1PairForestAccountErrorV1::Policy)?;
    let mut last_checkpoint_lane_sequences = [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for (lane, sequence) in last_checkpoint_lane_sequences.iter_mut().enumerate() {
        let start = MASTER_LAST_SEQUENCES_OFFSET + 8 * lane;
        *sequence = u64::from_le_bytes(bytes[start..start + 8].try_into().unwrap());
    }
    let master = PoolV1PairForestMasterV1 {
        bump: bytes[7],
        identity,
        verifier_policy,
        initialized_lane_mask: bytes[MASTER_INITIALIZED_MASK_OFFSET],
        has_checkpoint,
        next_checkpoint_sequence: u64::from_le_bytes(
            bytes[MASTER_NEXT_CHECKPOINT_OFFSET..MASTER_INITIALIZED_MASK_OFFSET]
                .try_into()
                .unwrap(),
        ),
        last_checkpoint_lane_sequences,
    };
    validate_master(&master)?;
    Ok(master)
}
```

## U04 crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical

```rust
{
    let mut i = 0;
    while i < digest.len() {
        if digest[i].0 >= P {
            return false;
        }
        i += 1;
    }
    true
}
```

## U04 crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte

```rust
{
    encode_digest_canonical(digest)[0]
}
```

## U04 crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1

```rust
{
    if !digest_is_canonical(nullifier) {
        return Err(PoolV1PairForestAccountErrorV1::NonCanonicalDigest);
    }
    Ok(first_canonical_byte(nullifier) & 7)
}
```

## U04 crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master

```rust
{
    if master.identity.pool == [0u8; 32]
        || master.identity.asset_mint == [0u8; 32]
        || master.identity.token_program == [0u8; 32]
        || master.identity.deployment_domain == [0u8; 32]
    {
        return Err(PoolV1PairForestAccountErrorV1::ZeroRequiredBinding);
    }
    validate_verifier_policy_v1(&master.verifier_policy)
        .map_err(|_| PoolV1PairForestAccountErrorV1::Policy)?;
    if master
        .last_checkpoint_lane_sequences
        .iter()
        .any(|sequence| *sequence > POOL_V1_PAIR_CAPACITY)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    if (!master.has_checkpoint
        && (master.next_checkpoint_sequence != 0
            || master.last_checkpoint_lane_sequences != [0u64; 8]))
        || (master.has_checkpoint && master.next_checkpoint_sequence == 0)
    {
        return Err(PoolV1PairForestAccountErrorV1::InvalidMasterState);
    }
    Ok(())
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier

```rust
{
        match self {
            Self::PrivateTransfer(public) => &public.nullifier,
            Self::Withdrawal(public) => &public.nullifier,
        }
    }
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind

```rust
{
        match self {
            Self::PrivateTransfer(_) => PoolV1TransitionKind::PrivateTransfer,
            Self::Withdrawal(_) => PoolV1TransitionKind::Withdrawal,
        }
    }
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common

```rust
{
        match self {
            Self::PrivateTransfer { common, .. } | Self::Withdrawal { common, .. } => common,
        }
    }
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier

```rust
{
        match self {
            Self::PrivateTransfer { public, .. } => &public.nullifier,
            Self::Withdrawal { public, .. } => &public.nullifier,
        }
    }
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind

```rust
{
        match self {
            Self::PrivateTransfer { .. } => PoolV1TransitionKind::PrivateTransfer,
            Self::Withdrawal { .. } => PoolV1TransitionKind::Withdrawal,
        }
    }
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1

```rust
{
    if bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_FOREST_TERMINAL_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongVersion);
    }
    let kind = transition_kind(bytes[5])?;
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairForestTerminalFormatErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 0 {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let public = match kind {
        PoolV1TransitionKind::PrivateTransfer => {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                decode_pool_v1_private_transfer_public_v1(&bytes[REQUEST_PAYMENT_OFFSET..])
                    .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?,
            )
        }
        PoolV1TransitionKind::Withdrawal => PoolV1PairForestTerminalPaymentV1::Withdrawal(
            decode_pool_v1_withdrawal_public_v1(&bytes[REQUEST_PAYMENT_OFFSET..])
                .map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?,
        ),
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: bytes[REQUEST_PROFILE_OFFSET..REQUEST_RELEASE_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        verifier_release: bytes[REQUEST_RELEASE_OFFSET..REQUEST_POOL_PROGRAM_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        pool_program: bytes[REQUEST_POOL_PROGRAM_OFFSET..REQUEST_PAYMENT_OFFSET]
            .try_into()
            .map_err(|_| PoolV1PairForestTerminalFormatErrorV1::WrongLength)?,
        public,
    };
    if request.verifier_profile == [0u8; 32]
        || request.verifier_release == [0u8; 32]
        || request.pool_program == [0u8; 32]
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    Ok(request)
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1

```rust
{
    validate_result(result)?;
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = result.transition_kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = result.output_lane;
    output[RESULT_MASTER_OFFSET..RESULT_SELECTED_LANE_OFFSET]
        .copy_from_slice(&result.master_account);
    output[RESULT_SELECTED_LANE_OFFSET..RESULT_NULLIFIER_OFFSET]
        .copy_from_slice(&result.selected_lane_account);
    output[RESULT_NULLIFIER_OFFSET..RESULT_AFTERSTATE_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&result.nullifier));
    output[RESULT_AFTERSTATE_OFFSET..].copy_from_slice(
        &encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)
            .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Afterstate(error))?,
    );
    Ok(output)
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1

```rust
{
    validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;
    let common = statement.common();
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = statement.transition_kind() as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = common.output_lane;
    output[MASTER_OFFSET..CHECKPOINT_ACCOUNT_OFFSET].copy_from_slice(&common.master_account);
    output[CHECKPOINT_ACCOUNT_OFFSET..SELECTED_LANE_ACCOUNT_OFFSET]
        .copy_from_slice(&common.checkpoint_account);
    output[SELECTED_LANE_ACCOUNT_OFFSET..CHECKPOINT_SEQUENCE_OFFSET]
        .copy_from_slice(&common.selected_lane_account);
    output[CHECKPOINT_SEQUENCE_OFFSET..HISTORICAL_ANCHOR_OFFSET]
        .copy_from_slice(&common.checkpoint_sequence.to_le_bytes());
    output[HISTORICAL_ANCHOR_OFFSET..LATE_STATEMENT_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.historical_global_anchor));
    encode_pool_v1_pair_late_public_statement_v1(
        &common.lane_transition,
        &mut output[LATE_STATEMENT_OFFSET..PAYMENT_STATEMENT_OFFSET],
    )
    .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::LaneTransition(error))?;
    let payment = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            encode_pool_v1_private_transfer_public_v1(public)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            encode_pool_v1_withdrawal_public_v1(public)
        }
    }
    .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Payment(error))?;
    output[PAYMENT_STATEMENT_OFFSET..].copy_from_slice(&payment);
    Ok(output)
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common

```rust
{
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.anchor_root,
            public.nullifier,
            public.asset_id,
        ),
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => (
            public.pool,
            public.deployment_domain,
            public.anchor_sequence,
            public.anchor_root,
            public.nullifier,
            public.asset_id,
        ),
    }
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind

```rust
{
    match byte {
        value if value == PoolV1TransitionKind::PrivateTransfer as u8 => {
            Ok(PoolV1TransitionKind::PrivateTransfer)
        }
        value if value == PoolV1TransitionKind::Withdrawal as u8 => {
            Ok(PoolV1TransitionKind::Withdrawal)
        }
        _ => Err(PoolV1PairForestTerminalFormatErrorV1::InvalidTransitionKind),
    }
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1

```rust
{
    validate_pool_v1_pair_forest_terminal_statement_v1(statement)?;
    validate_result(result)?;
    let common = statement.common();
    if result.transition_kind != statement.transition_kind()
        || result.master_account != common.master_account
        || result.selected_lane_account != common.selected_lane_account
        || result.output_lane != common.output_lane
        || result.nullifier != *statement.nullifier()
        || result.verified_afterstate != common.lane_transition.candidate_afterstate
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::ResultBindingMismatch);
    }
    Ok(())
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1

```rust
{
    let common = statement.common();
    if common.master_account == [0u8; 32]
        || common.checkpoint_account == [0u8; 32]
        || common.selected_lane_account == [0u8; 32]
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    if usize::from(common.output_lane) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane);
    }
    match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            encode_pool_v1_private_transfer_public_v1(public)
                .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Payment(error))?;
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            encode_pool_v1_withdrawal_public_v1(public)
                .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Payment(error))?;
        }
    }
    let (pool, deployment, anchor_sequence, anchor, nullifier, _) =
        statement_public_common(statement);
    if pool != common.master_account {
        return Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch);
    }
    if deployment != common.lane_transition.live_snapshot.deployment_domain {
        return Err(PoolV1PairForestTerminalFormatErrorV1::DeploymentBindingMismatch);
    }
    if common.lane_transition.live_snapshot.pool != common.master_account {
        return Err(PoolV1PairForestTerminalFormatErrorV1::MasterBindingMismatch);
    }
    if anchor_sequence != common.checkpoint_sequence {
        return Err(PoolV1PairForestTerminalFormatErrorV1::CheckpointBindingMismatch);
    }
    if anchor != common.historical_global_anchor {
        return Err(PoolV1PairForestTerminalFormatErrorV1::HistoricalAnchorMismatch);
    }
    let expected_lane = pool_v1_pair_forest_output_lane_v1(&nullifier)
        .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Account(error))?;
    if expected_lane != common.output_lane {
        return Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch);
    }
    let mut late_bytes = [0u8; POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
    encode_pool_v1_pair_late_public_statement_v1(&common.lane_transition, &mut late_bytes)
        .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::LaneTransition(error))?;
    Ok(())
}
```

## U05 crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result

```rust
{
    if result.master_account == [0u8; 32] || result.selected_lane_account == [0u8; 32] {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let expected = pool_v1_pair_forest_output_lane_v1(&result.nullifier)
        .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Account(error))?;
    if result.output_lane != expected {
        return Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch);
    }
    encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)
        .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Afterstate(error))?;
    Ok(())
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1

```rust
{
    if bytes.len() != POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC[0..4] {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongVersion);
    }
    if bytes[5] != super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongPairFormat);
    }
    if bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongDigestEncoding);
    }
    if bytes[7] != 1 {
        return Err(PoolV1PairVerifierTransportErrorV1::WrongSuccessCode);
    }
    let next_root = decode_digest_canonical(&exact(&bytes[16..48])?)
        .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?;
    let next_frontier = [
        decode_digest_canonical(&exact(&bytes[48..80])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[80..112])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[112..144])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[144..176])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[176..208])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[208..240])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[240..272])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[272..304])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[304..336])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[336..368])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[368..400])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[400..432])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[432..464])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[464..496])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[496..528])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[528..560])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[560..592])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[592..624])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[624..656])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
        decode_digest_canonical(&exact(&bytes[656..688])?)
            .map_err(|_| PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)?,
    ];
    let afterstate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: u64::from_le_bytes(exact(&bytes[8..16])?),
        next_root,
        next_frontier,
    };
    validate_verified_afterstate(&afterstate)?;
    Ok(afterstate)
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1

```rust
{
    validate_verified_afterstate(afterstate)?;
    let mut output = [0u8; POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC);
    output[4] = POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION;
    output[5] = super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = 1;
    output[8..16].copy_from_slice(&afterstate.next_pair_index.to_le_bytes());
    output[16..48].copy_from_slice(&encode_digest_canonical(&afterstate.next_root));
    for (level, node) in afterstate.next_frontier.iter().enumerate() {
        let start = 48 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }
    Ok(output)
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact

```rust
{
    bytes
        .try_into()
        .map_err(|_| PoolV1PairVerifierTransportErrorV1::WrongLength)
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate

```rust
{
    if afterstate.next_pair_index == 0 || afterstate.next_pair_index > super::POOL_V1_PAIR_CAPACITY
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex);
    }
    if !super::pair_tree_profile::digest_is_canonical(&afterstate.next_root) {
        return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);
    }
    let mut level = 0;
    while level < afterstate.next_frontier.len() {
        if !super::pair_tree_profile::digest_is_canonical(&afterstate.next_frontier[level]) {
            return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);
        }
        level += 1;
    }
    Ok(())
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical

```rust
{
    let mut i = 0;
    while i < value.len() {
        if value[i].0 >= P {
            return false;
        }
        i += 1;
    }
    true
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1

```rust
{
    if output.len() != POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES {
        return Err(PoolV1PairLatePublicStatementErrorV1::WrongLength);
    }
    if statement.live_snapshot.next_pair_index.checked_add(1)
        != Some(statement.candidate_afterstate.next_pair_index)
    {
        return Err(PoolV1PairLatePublicStatementErrorV1::AfterstateIndexMismatch);
    }
    output.fill(0);
    output[..8].copy_from_slice(&POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC);
    output[8] = POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION;
    output[9] = POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT;
    output[10..12]
        .copy_from_slice(&(POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES as u16).to_le_bytes());
    output[12..16].copy_from_slice(&(POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES as u32).to_le_bytes());
    output[16..20].copy_from_slice(&(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES as u32).to_le_bytes());
    output[20..24]
        .copy_from_slice(&(POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES as u32).to_le_bytes());
    encode_pool_v1_pair_live_snapshot_v1(
        &statement.live_snapshot,
        &mut output[32..32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES],
    )
    .map_err(|error| PoolV1PairLatePublicStatementErrorV1::Snapshot(error))?;
    let encoded_afterstate =
        encode_pool_v1_pair_verified_afterstate_v1(&statement.candidate_afterstate)
            .map_err(|error| PoolV1PairLatePublicStatementErrorV1::Afterstate(error))?;
    output[32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES..].copy_from_slice(&encoded_afterstate);
    Ok(())
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1

```rust
{
    if output.len() != POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES {
        return Err(PoolV1PairLiveSnapshotErrorV1::WrongLength);
    }
    validate_pool_v1_pair_live_snapshot_v1(snapshot)?;

    output.fill(0);
    output[..8].copy_from_slice(&POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC);
    output[8] = POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION;
    output[16..48].copy_from_slice(&POOL_V1_PAIR_TREE_FORMAT_BINDING);
    output[48..80].copy_from_slice(&snapshot.pool);
    output[80..112].copy_from_slice(&snapshot.deployment_domain);
    output[112..120].copy_from_slice(&snapshot.sequence.to_le_bytes());
    output[120..128].copy_from_slice(&snapshot.next_pair_index.to_le_bytes());
    output[128..160].copy_from_slice(&encode_digest_canonical(&snapshot.current_root));
    for (level, node) in snapshot.frontier.iter().enumerate() {
        let start = 160 + 32 * level;
        output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }
    Ok(())
}
```

## U03 crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1

```rust
{
    if snapshot.pool == [0u8; 32] || snapshot.deployment_domain == [0u8; 32] {
        return Err(PoolV1PairLiveSnapshotErrorV1::ZeroRequiredBinding);
    }
    if snapshot.sequence != snapshot.next_pair_index {
        return Err(PoolV1PairLiveSnapshotErrorV1::SequenceIndexMismatch);
    }
    if snapshot.next_pair_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1PairLiveSnapshotErrorV1::TreeFull);
    }
    if !digest_is_canonical(&snapshot.current_root) {
        return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);
    }
    let mut level = 0;
    while level < snapshot.frontier.len() {
        if !digest_is_canonical(&snapshot.frontier[level]) {
            return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);
        }
        level += 1;
    }
    Ok(())
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from

```rust
{
        match value {
            0 => Ok(Self::Pending),
            1 => Ok(Self::Active),
            2 => Ok(Self::Paused),
            3 => Ok(Self::Retired),
            _ => Err(PoolV1VerifierRegistryFormatError::InvalidStatus),
        }
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot

```rust
{
        self.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at

```rust
{
        self.status == VerifierEntryStatusV1::Active
            && self.activation_slot <= slot
            && (self.has_no_retirement_slot() || slot < self.retirement_slot)
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot

```rust
{
        self.retirement_slot == POOL_V1_VERIFIER_ENTRY_NO_RETIREMENT_SLOT
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at

```rust
{
        self.status == VerifierEntryStatusV1::Active
            && self.activation_slot <= slot
            && (self.has_no_retirement_slot() || slot < self.retirement_slot)
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable

```rust
{
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE != 0
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused

```rust
{
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED != 0
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable

```rust
{
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_IMMUTABLE != 0
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused

```rust
{
        self.flags & POOL_V1_VERIFIER_REGISTRY_FLAG_PAUSED != 0
    }
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1

```rust
{
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[184..192] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let entry = VerifierRegistryEntryV1 {
        status: VerifierEntryStatusV1::try_from(bytes[5])?,
        statement_version: bytes[6],
        bump: bytes[7],
        pool: bytes[8..40].try_into().unwrap(),
        verifier_program: bytes[40..72].try_into().unwrap(),
        profile_binding: bytes[72..104].try_into().unwrap(),
        release_binding: bytes[104..136].try_into().unwrap(),
        activation_slot: u64::from_le_bytes(bytes[136..144].try_into().unwrap()),
        retirement_slot: u64::from_le_bytes(bytes[144..152].try_into().unwrap()),
        policy_binding: bytes[152..184].try_into().unwrap(),
    };
    validate_verifier_registry_entry_v1(&entry)?;
    Ok(entry)
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2

```rust
{
    if bytes.len() != POOL_V1_VERIFIER_ENTRY_V2_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_ENTRY_V2_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_ENTRY_V2_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[7] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode);
    }
    if bytes[314..320] != [0u8; 6] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let entry = VerifierRegistryEntryV2 {
        status: VerifierEntryStatusV1::try_from(bytes[5])?,
        statement_version: bytes[6],
        bump: bytes[312],
        pool: bytes[8..40].try_into().unwrap(),
        verifier_program: bytes[40..72].try_into().unwrap(),
        profile_binding: bytes[72..104].try_into().unwrap(),
        release_binding: bytes[104..136].try_into().unwrap(),
        loader_program: bytes[136..168].try_into().unwrap(),
        programdata_address: bytes[168..200].try_into().unwrap(),
        programdata_bump: bytes[313],
        executable_hash: bytes[200..232].try_into().unwrap(),
        expected_upgrade_authority: bytes[232..264].try_into().unwrap(),
        activation_slot: u64::from_le_bytes(bytes[264..272].try_into().unwrap()),
        retirement_slot: u64::from_le_bytes(bytes[272..280].try_into().unwrap()),
        policy_binding: bytes[280..312].try_into().unwrap(),
    };
    validate_verifier_registry_entry_v2(&entry)?;
    Ok(entry)
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1

```rust
{
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[7] != 0 || bytes[120..128] != [0u8; 8] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let registry = VerifierRegistryV1 {
        flags: bytes[5],
        bump: bytes[6],
        pool: bytes[8..40].try_into().unwrap(),
        authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
        generation: u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
        minimum_activation_delay_slots: u64::from_le_bytes(bytes[112..120].try_into().unwrap()),
    };
    validate_verifier_registry_v1(&registry)?;
    Ok(registry)
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2

```rust
{
    if bytes.len() != POOL_V1_VERIFIER_REGISTRY_V2_BYTES {
        return Err(PoolV1VerifierRegistryFormatError::WrongLength);
    }
    if bytes[..4] != POOL_V1_VERIFIER_REGISTRY_V2_MAGIC {
        return Err(PoolV1VerifierRegistryFormatError::WrongMagic);
    }
    if bytes[4] != POOL_V1_VERIFIER_REGISTRY_V2_VERSION {
        return Err(PoolV1VerifierRegistryFormatError::WrongVersion);
    }
    if bytes[6] != POOL_V1_VERIFIER_DEPLOYMENT_MODE_IMMUTABLE_LOADER_V3 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidDeploymentMode);
    }
    if bytes[249..256] != [0u8; 7] {
        return Err(PoolV1VerifierRegistryFormatError::NonZeroReserved);
    }
    let registry = VerifierRegistryV2 {
        flags: bytes[5],
        bump: bytes[7],
        pool: bytes[8..40].try_into().unwrap(),
        authority: bytes[40..72].try_into().unwrap(),
        policy_binding: bytes[72..104].try_into().unwrap(),
        generation: u64::from_le_bytes(bytes[104..112].try_into().unwrap()),
        minimum_activation_delay_slots: u64::from_le_bytes(bytes[112..120].try_into().unwrap()),
        registry_program: bytes[120..152].try_into().unwrap(),
        loader_program: bytes[152..184].try_into().unwrap(),
        programdata_address: bytes[184..216].try_into().unwrap(),
        programdata_bump: bytes[248],
        executable_hash: bytes[216..248].try_into().unwrap(),
    };
    validate_verifier_registry_v2(&registry)?;
    Ok(registry)
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero

```rust
{
    *value == [0u8; 32]
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1

```rust
{
    if entry.statement_version == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidStatementVersion);
    }
    if required_binding_is_zero(&entry.pool)
        || required_binding_is_zero(&entry.verifier_program)
        || required_binding_is_zero(&entry.profile_binding)
        || required_binding_is_zero(&entry.release_binding)
        || required_binding_is_zero(&entry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if !entry.has_no_retirement_slot() && entry.retirement_slot <= entry.activation_slot {
        return Err(PoolV1VerifierRegistryFormatError::InvalidRetirementSlot);
    }
    Ok(())
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2

```rust
{
    if entry.statement_version == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidStatementVersion);
    }
    if required_binding_is_zero(&entry.pool)
        || required_binding_is_zero(&entry.verifier_program)
        || required_binding_is_zero(&entry.profile_binding)
        || required_binding_is_zero(&entry.release_binding)
        || required_binding_is_zero(&entry.loader_program)
        || required_binding_is_zero(&entry.programdata_address)
        || required_binding_is_zero(&entry.executable_hash)
        || required_binding_is_zero(&entry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if entry.expected_upgrade_authority != [0u8; 32] {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if !entry.has_no_retirement_slot() && entry.retirement_slot <= entry.activation_slot {
        return Err(PoolV1VerifierRegistryFormatError::InvalidRetirementSlot);
    }
    Ok(())
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1

```rust
{
    if registry.flags & !POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK != 0 {
        return Err(PoolV1VerifierRegistryFormatError::UnsupportedFlags);
    }
    if required_binding_is_zero(&registry.pool)
        || required_binding_is_zero(&registry.policy_binding)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if registry.is_immutable() != required_binding_is_zero(&registry.authority) {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if registry.minimum_activation_delay_slots == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidActivationDelay);
    }
    Ok(())
}
```

## U04 crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2

```rust
{
    if registry.flags & !POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK != 0 {
        return Err(PoolV1VerifierRegistryFormatError::UnsupportedFlags);
    }
    if required_binding_is_zero(&registry.pool)
        || required_binding_is_zero(&registry.policy_binding)
        || required_binding_is_zero(&registry.registry_program)
        || required_binding_is_zero(&registry.loader_program)
        || required_binding_is_zero(&registry.programdata_address)
        || required_binding_is_zero(&registry.executable_hash)
    {
        return Err(PoolV1VerifierRegistryFormatError::ZeroRequiredBinding);
    }
    if registry.is_immutable() != required_binding_is_zero(&registry.authority) {
        return Err(PoolV1VerifierRegistryFormatError::InvalidAuthorityMode);
    }
    if registry.minimum_activation_delay_slots == 0 {
        return Err(PoolV1VerifierRegistryFormatError::InvalidActivationDelay);
    }
    Ok(())
}
```
