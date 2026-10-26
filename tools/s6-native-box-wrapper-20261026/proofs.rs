#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
    use aspis_statement::pool_v1::pair_forest_terminal::{
        PoolV1PairForestTerminalStatementV1 as Statement,
        PoolV1PairForestTerminalStatementV1,
        PoolV1PairForestTerminalFormatErrorV1 as FormatError,
        decode_pool_v1_pair_forest_terminal_statement_v1,
    };
    use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
    // The frozen solana_program::program_error module re-exports this exact
    // SDK type. Its release version/checksum and re-export are separately pinned.
    use solana_program_error::ProgramError;

fn decode_public_statement_box(
    bytes: &[u8],
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_statement_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

    // BEGIN GENERATED CONSTRUCTORS
    // Every scalar is independent. Literal arrays cover all native array
    // coordinates; no canonicality or successful decoder premise is imposed.
    fn make_PoolV1PairForestTerminalCommonV1()->aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalCommonV1 {
        aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalCommonV1 {
            master_account: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            checkpoint_account: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            selected_lane_account: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            output_lane: kani::any::<u8>(),
            checkpoint_sequence: kani::any::<u64>(),
            historical_global_anchor: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            lane_transition: make_PoolV1PairLatePublicStatementV1(),
        }
    }
    fn make_PoolV1PrivateTransferPublicV1()->aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1 {
        aspis_statement::pool_v1::payment_relation::PoolV1PrivateTransferPublicV1 {
            pool: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            deployment_domain: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            anchor_sequence: kani::any::<u64>(),
            anchor_root: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            nullifier: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            asset_id: aspis_core::field::M31(kani::any::<u32>()),
            recipient_commitment: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            change_commitment: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
        }
    }
    fn make_PoolV1WithdrawalPublicV1()->aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1 {
        aspis_statement::pool_v1::payment_relation::PoolV1WithdrawalPublicV1 {
            pool: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            deployment_domain: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            anchor_sequence: kani::any::<u64>(),
            anchor_root: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            nullifier: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            asset_id: aspis_core::field::M31(kani::any::<u32>()),
            amount: kani::any::<u32>(),
            destination_token_account: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            change_commitment: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
        }
    }
    fn make_PoolV1PairLatePublicStatementV1()->aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1 {
        aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1 {
            live_snapshot: make_PoolV1PairLiveSnapshotV1(),
            candidate_afterstate: make_PoolV1PairVerifiedAfterstateV1(),
        }
    }
    fn make_PoolV1PairLiveSnapshotV1()->aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1 {
        aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1 {
            pool: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            deployment_domain: [kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()],
            sequence: kani::any::<u64>(),
            next_pair_index: kani::any::<u64>(),
            current_root: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            frontier: [[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())]],
        }
    }
    fn make_PoolV1PairVerifiedAfterstateV1()->aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1 {
        aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: kani::any::<u64>(),
            next_root: [aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],
            next_frontier: [[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())],[aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>()),aspis_core::field::M31(kani::any::<u32>())]],
        }
    }

    fn arbitrary_statement()->Statement {
        if kani::any::<bool>() {
            Statement::PrivateTransfer { common: make_PoolV1PairForestTerminalCommonV1(), public: make_PoolV1PrivateTransferPublicV1() }
        } else {
            Statement::Withdrawal { common: make_PoolV1PairForestTerminalCommonV1(), public: make_PoolV1WithdrawalPublicV1() }
        }
    }
    // END GENERATED CONSTRUCTORS


    fn observe(s:&Statement,family:u8,i:usize,j:usize)->u64 {
        match s {
            Statement::PrivateTransfer {common,public} => match family {
                0=>1u64,
                1=>common.master_account[i%32] as u64,
                2=>common.checkpoint_account[i%32] as u64,
                3=>common.selected_lane_account[i%32] as u64,
                4=>common.output_lane as u64,
                5=>common.checkpoint_sequence as u64,
                6=>common.historical_global_anchor[i%8].0 as u64,
                7=>common.lane_transition.live_snapshot.pool[i%32] as u64,
                8=>common.lane_transition.live_snapshot.deployment_domain[i%32] as u64,
                9=>common.lane_transition.live_snapshot.sequence as u64,
                10=>common.lane_transition.live_snapshot.next_pair_index as u64,
                11=>common.lane_transition.live_snapshot.current_root[i%8].0 as u64,
                12=>common.lane_transition.live_snapshot.frontier[i%20][j%8].0 as u64,
                13=>common.lane_transition.candidate_afterstate.next_pair_index as u64,
                14=>common.lane_transition.candidate_afterstate.next_root[i%8].0 as u64,
                15=>common.lane_transition.candidate_afterstate.next_frontier[i%20][j%8].0 as u64,
                16=>public.pool[i%32] as u64,
                17=>public.deployment_domain[i%32] as u64,
                18=>public.anchor_sequence as u64,
                19=>public.anchor_root[i%8].0 as u64,
                20=>public.nullifier[i%8].0 as u64,
                21=>public.asset_id.0 as u64,
                22=>public.recipient_commitment[i%8].0 as u64,
                23=>public.change_commitment[i%8].0 as u64,
                _=>0,
            },
            Statement::Withdrawal {common,public} => match family {
                0=>2u64,
                1=>common.master_account[i%32] as u64,
                2=>common.checkpoint_account[i%32] as u64,
                3=>common.selected_lane_account[i%32] as u64,
                4=>common.output_lane as u64,
                5=>common.checkpoint_sequence as u64,
                6=>common.historical_global_anchor[i%8].0 as u64,
                7=>common.lane_transition.live_snapshot.pool[i%32] as u64,
                8=>common.lane_transition.live_snapshot.deployment_domain[i%32] as u64,
                9=>common.lane_transition.live_snapshot.sequence as u64,
                10=>common.lane_transition.live_snapshot.next_pair_index as u64,
                11=>common.lane_transition.live_snapshot.current_root[i%8].0 as u64,
                12=>common.lane_transition.live_snapshot.frontier[i%20][j%8].0 as u64,
                13=>common.lane_transition.candidate_afterstate.next_pair_index as u64,
                14=>common.lane_transition.candidate_afterstate.next_root[i%8].0 as u64,
                15=>common.lane_transition.candidate_afterstate.next_frontier[i%20][j%8].0 as u64,
                16=>public.pool[i%32] as u64,
                17=>public.deployment_domain[i%32] as u64,
                18=>public.anchor_sequence as u64,
                19=>public.anchor_root[i%8].0 as u64,
                20=>public.nullifier[i%8].0 as u64,
                21=>public.asset_id.0 as u64,
                22=>public.amount as u64,
                23=>public.destination_token_account[i%32] as u64,
                24=>public.change_commitment[i%8].0 as u64,
                _=>0,
            },
        }
    }

    fn byte32()->[u8;32] {[kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()]}
    fn byte24()->[u8;24] {[kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>(),kani::any::<u8>()]}
    fn bytes1880()->[u8;1880] {
        let mut bytes=[0u8;1880];
        bytes[0..32].copy_from_slice(&byte32());
        bytes[32..64].copy_from_slice(&byte32());
        bytes[64..96].copy_from_slice(&byte32());
        bytes[96..128].copy_from_slice(&byte32());
        bytes[128..160].copy_from_slice(&byte32());
        bytes[160..192].copy_from_slice(&byte32());
        bytes[192..224].copy_from_slice(&byte32());
        bytes[224..256].copy_from_slice(&byte32());
        bytes[256..288].copy_from_slice(&byte32());
        bytes[288..320].copy_from_slice(&byte32());
        bytes[320..352].copy_from_slice(&byte32());
        bytes[352..384].copy_from_slice(&byte32());
        bytes[384..416].copy_from_slice(&byte32());
        bytes[416..448].copy_from_slice(&byte32());
        bytes[448..480].copy_from_slice(&byte32());
        bytes[480..512].copy_from_slice(&byte32());
        bytes[512..544].copy_from_slice(&byte32());
        bytes[544..576].copy_from_slice(&byte32());
        bytes[576..608].copy_from_slice(&byte32());
        bytes[608..640].copy_from_slice(&byte32());
        bytes[640..672].copy_from_slice(&byte32());
        bytes[672..704].copy_from_slice(&byte32());
        bytes[704..736].copy_from_slice(&byte32());
        bytes[736..768].copy_from_slice(&byte32());
        bytes[768..800].copy_from_slice(&byte32());
        bytes[800..832].copy_from_slice(&byte32());
        bytes[832..864].copy_from_slice(&byte32());
        bytes[864..896].copy_from_slice(&byte32());
        bytes[896..928].copy_from_slice(&byte32());
        bytes[928..960].copy_from_slice(&byte32());
        bytes[960..992].copy_from_slice(&byte32());
        bytes[992..1024].copy_from_slice(&byte32());
        bytes[1024..1056].copy_from_slice(&byte32());
        bytes[1056..1088].copy_from_slice(&byte32());
        bytes[1088..1120].copy_from_slice(&byte32());
        bytes[1120..1152].copy_from_slice(&byte32());
        bytes[1152..1184].copy_from_slice(&byte32());
        bytes[1184..1216].copy_from_slice(&byte32());
        bytes[1216..1248].copy_from_slice(&byte32());
        bytes[1248..1280].copy_from_slice(&byte32());
        bytes[1280..1312].copy_from_slice(&byte32());
        bytes[1312..1344].copy_from_slice(&byte32());
        bytes[1344..1376].copy_from_slice(&byte32());
        bytes[1376..1408].copy_from_slice(&byte32());
        bytes[1408..1440].copy_from_slice(&byte32());
        bytes[1440..1472].copy_from_slice(&byte32());
        bytes[1472..1504].copy_from_slice(&byte32());
        bytes[1504..1536].copy_from_slice(&byte32());
        bytes[1536..1568].copy_from_slice(&byte32());
        bytes[1568..1600].copy_from_slice(&byte32());
        bytes[1600..1632].copy_from_slice(&byte32());
        bytes[1632..1664].copy_from_slice(&byte32());
        bytes[1664..1696].copy_from_slice(&byte32());
        bytes[1696..1728].copy_from_slice(&byte32());
        bytes[1728..1760].copy_from_slice(&byte32());
        bytes[1760..1792].copy_from_slice(&byte32());
        bytes[1792..1824].copy_from_slice(&byte32());
        bytes[1824..1856].copy_from_slice(&byte32());
        bytes[1856..1880].copy_from_slice(&byte24());
        bytes
    }


    static mut ANSWER:*const Result<Statement,FormatError>=core::ptr::null();
    static mut CALLS:u8=0;
    static mut SEEN:*const u8=core::ptr::null();
    static mut LENGTH:usize=0;
    fn decoder_return(bytes:&[u8])->Result<Statement,FormatError> {
        unsafe {
            CALLS+=1;
            assert!(CALLS==1);
            SEEN=bytes.as_ptr();LENGTH=bytes.len();
            *ANSWER
        }
    }

    fn aliases(statement:&Statement, selected:Public<'_>)->bool {
        match (statement,selected) {
            (Statement::PrivateTransfer{common,public},Public::Transfer(p,lane))=>
                core::ptr::eq(p,public)&&core::ptr::eq(lane,&common.lane_transition),
            (Statement::Withdrawal{common,public},Public::Withdrawal(p,lane))=>
                core::ptr::eq(p,public)&&core::ptr::eq(lane,&common.lane_transition),
            _=>false,
        }
    }

    fn run(negative:bool,family:u8) {
        let bytes=bytes1880();
        let i:usize=kani::any();let j:usize=kani::any();
        let answer=if kani::any::<bool>() {Ok(arbitrary_statement())} else {Err(kani::any::<FormatError>())};
        unsafe {ANSWER=&answer;CALLS=0;SEEN=core::ptr::null();LENGTH=0;}
        let returned=decode_public_statement_box(&bytes);
        unsafe {
            assert!(CALLS==1);
            assert!(SEEN==bytes.as_ptr());
            assert!(LENGTH==bytes.len());
        }
        match (answer,returned) {
            (Ok(mut before),Ok(after))=> {
                if negative {
                    // Only the final common frontier coordinate is changed.
                    match &mut before {
                        Statement::PrivateTransfer{common,..}|Statement::Withdrawal{common,..}=>
                            common.lane_transition.candidate_afterstate.next_frontier[19][7].0^=1,
                    }
                }
                assert!(observe(&before,family,i,j)==observe(&after,family,i,j));
                assert!(aliases(&after,after.semantic_public()));
                match &*after {
                    Statement::PrivateTransfer{..}=>kani::cover!(true,"transfer boxed return"),
                    Statement::Withdrawal{..}=>kani::cover!(true,"withdrawal boxed return"),
                }
                // Actual native Box destructor is executed after its last use.
                drop(after);
            },
            (Err(_),Err(error))=> {
                assert!(matches!(error,ProgramError::InvalidAccountData));
                kani::cover!(true,"native decoder error mapped");
            },
            _=>assert!(false,"native wrapper result classification differs"),
        }
    }

    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_projection() {run(false,kani::any());}

    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn last_frontier_negative_control() {run(true,kani::any());}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_0() {run(false,0);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_1() {run(false,1);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_2() {run(false,2);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_3() {run(false,3);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_4() {run(false,4);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_5() {run(false,5);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_6() {run(false,6);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_7() {run(false,7);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_8() {run(false,8);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_9() {run(false,9);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_10() {run(false,10);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_11() {run(false,11);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_12() {run(false,12);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_13() {run(false,13);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_14() {run(false,14);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_15() {run(false,15);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_16() {run(false,16);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_17() {run(false,17);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_18() {run(false,18);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_19() {run(false,19);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_20() {run(false,20);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_21() {run(false,21);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_22() {run(false,22);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_23() {run(false,23);}
    #[kani::proof]
    #[kani::unwind(8)]
    #[kani::stub(aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_statement_v1,decoder_return)]
    fn native_boxed_decoder_family_24() {run(false,24);}

}
