fn binding_tail(statement:&PoolV1PairForestTerminalStatementV1,result:&PoolV1PairForestTerminalResultV1) -> Result<(),PoolV1PairForestTerminalFormatErrorV1> {
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
fn binding_prefix(statement:&PoolV1PairForestTerminalStatementV1) -> Result<(),PoolV1PairForestTerminalFormatErrorV1> {
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
    Ok(())
}
fn statement_public_common(
    statement: &PoolV1PairForestTerminalStatementV1,
) -> ([u8; 32], [u8; 32], u64, Digest, Digest, M31) {
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

fn lane_binding(statement:&PoolV1PairForestTerminalStatementV1) -> Result<(),PoolV1PairForestTerminalFormatErrorV1> {
    let common=statement.common();
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
    Ok(())
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_binding_tail() {
    let statement=statement::statement();let result=construct(&statement);
    assert_eq!(binding_tail(&statement,&result),Ok(()));
    kani::cover!(statement.transition_kind()==PoolV1TransitionKind::PrivateTransfer);
    kani::cover!(statement.transition_kind()==PoolV1TransitionKind::Withdrawal);
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_binding_prefix() {
    let statement=statement::statement();let c=statement.common();
    let expected=if c.master_account==[0;32] || c.checkpoint_account==[0;32] || c.selected_lane_account==[0;32] {
        Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)
    } else if c.output_lane>=8 {Err(PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane)} else {Ok(())};
    assert_eq!(binding_prefix(&statement),expected);
    kani::cover!(expected.is_ok());kani::cover!(expected.is_err());
}
#[kani::proof]
#[kani::unwind(34)]
fn S2K_lane_binding() {
    let statement=statement::statement();let result=construct(&statement);
    if lane_binding(&statement).is_ok() {
        assert_eq!(pool_v1_pair_forest_output_lane_v1(&result.nullifier),Ok(result.output_lane));
    }
    kani::cover!(lane_binding(&statement).is_ok());
}
