#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalCommonV1 {
    pub master_account: [u8; 32],
    pub checkpoint_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub output_lane: u8,
    pub checkpoint_sequence: u64,
    /// Historical global membership anchor reconstructed at trace block 56.
    pub historical_global_anchor: Digest,
    /// Exact selected-output-lane beforestate and candidate afterstate.
    pub lane_transition: PoolV1PairLatePublicStatementV1,
}