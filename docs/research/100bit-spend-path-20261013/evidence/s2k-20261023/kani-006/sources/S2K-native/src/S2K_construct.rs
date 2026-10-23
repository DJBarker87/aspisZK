fn construct(statement: &PoolV1PairForestTerminalStatementV1) -> PoolV1PairForestTerminalResultV1 {
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: statement.common().master_account,
        selected_lane_account: statement.common().selected_lane_account,
        output_lane: statement.common().output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: statement.common().lane_transition.candidate_afterstate,
    };
    result
}
