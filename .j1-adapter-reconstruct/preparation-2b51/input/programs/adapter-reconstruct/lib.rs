// Generated exact declaration cut; see source-pins.json.
extern crate alloc;

#[cfg(feature = "pool-adapter")]
mod r1_pool_adapter {
use alloc::boxed::Box;
use solana_program_error::ProgramError;
use aspis_statement::pool_v1::{
    PoolV1PairForestMasterV1, PoolV1PairForestCheckpointV1,
    PoolV1PairForestLaneStateV1, PoolV1PairLiveSnapshotV1,
    PoolV1PairForestTerminalCommonV1, PoolV1PairLatePublicStatementV1,
    PoolV1PairForestTerminalStatementV1, PoolV1PairForestTerminalPaymentV1,
    PoolV1PairForestTerminalRequestV1,
    validate_pool_v1_pair_forest_terminal_statement_v1,
};

struct AuthenticatedAsq8Accounts {
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    master: Box<PoolV1PairForestMasterV1>,
    checkpoint: Box<PoolV1PairForestCheckpointV1>,
    selected_lane: Box<PoolV1PairForestLaneStateV1>,
    live_snapshot: Box<PoolV1PairLiveSnapshotV1>,
}

#[inline(never)]
fn asq8_common(
    authenticated: &AuthenticatedAsq8Accounts,
    candidate_afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
) -> Box<PoolV1PairForestTerminalCommonV1> {
    Box::new(PoolV1PairForestTerminalCommonV1 {
        master_account: authenticated.master_account,
        checkpoint_account: authenticated.checkpoint_account,
        selected_lane_account: authenticated.selected_lane_account,
        output_lane: authenticated.selected_lane.lane_id,
        checkpoint_sequence: authenticated.checkpoint.checkpoint_sequence,
        historical_global_anchor: authenticated.checkpoint.global_root,
        lane_transition: PoolV1PairLatePublicStatementV1 {
            live_snapshot: *authenticated.live_snapshot,
            candidate_afterstate: *candidate_afterstate,
        },
    })
}

#[inline(never)]
fn transfer_statement_box(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    let statement = Box::new(PoolV1PairForestTerminalStatementV1::PrivateTransfer {
        common: *common,
        public,
    });
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(statement)
}

#[inline(never)]
fn withdrawal_statement_box(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1WithdrawalPublicV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    let statement = Box::new(PoolV1PairForestTerminalStatementV1::Withdrawal {
        common: *common,
        public,
    });
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(statement)
}

#[inline(never)]
fn reconstruct_asq8_statement(
    request: &PoolV1PairForestTerminalRequestV1,
    authenticated: &AuthenticatedAsq8Accounts,
    candidate_afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    if authenticated.live_snapshot.next_pair_index.checked_add(1)
        != Some(candidate_afterstate.next_pair_index)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let requested_asset_id = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => public.asset_id,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => public.asset_id,
    };
    if authenticated.master.identity.asset_id != requested_asset_id {
        return Err(ProgramError::InvalidInstructionData);
    }
    let common = asq8_common(authenticated, candidate_afterstate);
    match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            transfer_statement_box(common, public)
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            withdrawal_statement_box(common, public)
        }
    }
}

}
