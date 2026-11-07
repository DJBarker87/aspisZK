use aspis_statement::pool_v1::*;
use aspis_statement::poseidon2::Digest;
use aspis_core::field::M31;
fn NMN_any_PoolV1PairLiveSnapshotV1()->PoolV1PairLiveSnapshotV1{PoolV1PairLiveSnapshotV1{pool:kani::any(),
deployment_domain:kani::any(),
sequence:kani::any(),
next_pair_index:kani::any(),
current_root:core::array::from_fn(|_|M31(kani::any())),
frontier:core::array::from_fn(|_|core::array::from_fn(|_|M31(kani::any())))}}
fn NMN_any_PoolV1PairVerifiedAfterstateV1()->PoolV1PairVerifiedAfterstateV1{PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),
next_root:core::array::from_fn(|_|M31(kani::any())),
next_frontier:core::array::from_fn(|_|core::array::from_fn(|_|M31(kani::any())))}}
fn NMN_any_PoolV1PairLatePublicStatementV1()->PoolV1PairLatePublicStatementV1{PoolV1PairLatePublicStatementV1{live_snapshot:NMN_any_PoolV1PairLiveSnapshotV1(),
candidate_afterstate:NMN_any_PoolV1PairVerifiedAfterstateV1()}}
fn NMN_any_PoolV1PairForestTerminalCommonV1()->PoolV1PairForestTerminalCommonV1{PoolV1PairForestTerminalCommonV1{master_account:kani::any(),
checkpoint_account:kani::any(),
selected_lane_account:kani::any(),
output_lane:kani::any(),
checkpoint_sequence:kani::any(),
historical_global_anchor:core::array::from_fn(|_|M31(kani::any())),
lane_transition:NMN_any_PoolV1PairLatePublicStatementV1()}}
fn NMN_any_PoolV1PrivateTransferPublicV1()->PoolV1PrivateTransferPublicV1{PoolV1PrivateTransferPublicV1{pool:kani::any(),
deployment_domain:kani::any(),
anchor_sequence:kani::any(),
anchor_root:core::array::from_fn(|_|M31(kani::any())),
nullifier:core::array::from_fn(|_|M31(kani::any())),
asset_id:M31(kani::any()),
recipient_commitment:core::array::from_fn(|_|M31(kani::any())),
change_commitment:core::array::from_fn(|_|M31(kani::any()))}}
fn NMN_any_PoolV1WithdrawalPublicV1()->PoolV1WithdrawalPublicV1{PoolV1WithdrawalPublicV1{pool:kani::any(),
deployment_domain:kani::any(),
anchor_sequence:kani::any(),
anchor_root:core::array::from_fn(|_|M31(kani::any())),
nullifier:core::array::from_fn(|_|M31(kani::any())),
asset_id:M31(kani::any()),
amount:kani::any(),
destination_token_account:kani::any(),
change_commitment:core::array::from_fn(|_|M31(kani::any()))}}
fn NMN_any_statement()->PoolV1PairForestTerminalStatementV1{if kani::any(){PoolV1PairForestTerminalStatementV1::PrivateTransfer{common:NMN_any_PoolV1PairForestTerminalCommonV1(),public:NMN_any_PoolV1PrivateTransferPublicV1()}}else{PoolV1PairForestTerminalStatementV1::Withdrawal{common:NMN_any_PoolV1PairForestTerminalCommonV1(),public:NMN_any_PoolV1WithdrawalPublicV1()}}}

// Bit-valid payloads: the pinned six-struct field tree consists ONLY of
// u8/u32/u64 and M31(pub u32) arrays/records. It contains no bool, enum,
// pointer, reference, NonZero, guard or Drop field. Every payload bit pattern
// is valid; the outer statement enum is still constructed by a Rust variant.
fn NMN_pod_common()->PoolV1PairForestTerminalCommonV1 {
 let raw:[u8;core::mem::size_of::<PoolV1PairForestTerminalCommonV1>()]=kani::any();
 unsafe{core::mem::transmute(raw)}
}
fn NMN_statement_variant(withdraw:bool)->PoolV1PairForestTerminalStatementV1 {
 if withdraw {
  let raw:[u8;core::mem::size_of::<PoolV1WithdrawalPublicV1>()]=kani::any();
  let public=unsafe{core::mem::transmute(raw)};
  PoolV1PairForestTerminalStatementV1::Withdrawal{common:NMN_pod_common(),public}
 }else{
  let raw:[u8;core::mem::size_of::<PoolV1PrivateTransferPublicV1>()]=kani::any();
  let public=unsafe{core::mem::transmute(raw)};
  PoolV1PairForestTerminalStatementV1::PrivateTransfer{common:NMN_pod_common(),public}
 }
}
