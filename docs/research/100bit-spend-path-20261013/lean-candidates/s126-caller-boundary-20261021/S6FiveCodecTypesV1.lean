import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error





namespace AspisS6FiveUnrolledCodec



@[reducible]
def aspis_core.field.M31 := Std.U32



inductive aspis_statement.atomic_statement.AtomicStatementError where
| NonCanonicalDigest : aspis_statement.atomic_statement.AtomicStatementError
| NonCanonicalAssetId : aspis_statement.atomic_statement.AtomicStatementError
| FeeOutOfRange : aspis_statement.atomic_statement.AtomicStatementError
| PathDepthMismatch : aspis_statement.atomic_statement.AtomicStatementError
| InsertionIndexOutOfRange :
  aspis_statement.atomic_statement.AtomicStatementError
| CurrentAnchorMismatch : aspis_statement.atomic_statement.AtomicStatementError
| OutputAnchorMismatch : aspis_statement.atomic_statement.AtomicStatementError


@[discriminant u8 [1,2]]
inductive aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind where
| PrivateTransfer :
  aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind
| Withdrawal : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind



inductive aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError where
| TreeFull : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| InsufficientCapacity :
  aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| IndexOutOfRange : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| RootMismatch : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| NonCanonicalFrontier :
  aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| WrongLength : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| WrongMagic : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| WrongVersion : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| WrongDepth : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| WrongTreeHash : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| WrongDigestEncoding :
  aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| NonCanonicalDigest :
  aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
| NonZeroReserved : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError



inductive aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  where
| WrongLength :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongMagic :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongVersion :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongLaneCount :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongDigestEncoding :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongDepth :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| WrongFormatBinding :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| NonZeroReserved :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| ZeroRequiredBinding :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| InvalidBoolean :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| InvalidMasterState :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| InvalidLane :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| LaneMasterMismatch :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| LaneOrderMismatch :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| LaneSequenceDecreased :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| DuplicateCheckpoint :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| CheckpointSequenceOverflow :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| NonCanonicalDigest :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| Identity :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| Policy :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
| Tree :
  aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError →
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1



structure aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  sequence : Std.U64
  next_pair_index : Std.U64
  current_root : Array aspis_core.field.M31 8#usize
  frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize



structure aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
  where
  next_pair_index : Std.U64
  next_root : Array aspis_core.field.M31 8#usize
  next_frontier : Array (Array aspis_core.field.M31 8#usize) 20#usize



structure aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
  where
  live_snapshot :
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  candidate_afterstate :
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1



structure aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
  where
  master_account : Array Std.U8 32#usize
  checkpoint_account : Array Std.U8 32#usize
  selected_lane_account : Array Std.U8 32#usize
  output_lane : Std.U8
  checkpoint_sequence : Std.U64
  historical_global_anchor : Array aspis_core.field.M31 8#usize
  lane_transition :
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1



structure aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
  where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  amount : Std.U32
  destination_token_account : Array Std.U8 32#usize
  change_commitment : Array aspis_core.field.M31 8#usize



structure aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
  where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient_commitment : Array aspis_core.field.M31 8#usize
  change_commitment : Array aspis_core.field.M31 8#usize



inductive aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
  where
| PrivateTransfer :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
    →
  aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
| Withdrawal :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
    →
  aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1



inductive aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  where
| WrongLength :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongMagic :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongVersion :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongTransitionKind :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| WrongDigestEncoding :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| NonZeroReserved :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| ZeroRequiredBinding :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidAnchorSequence :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| NonCanonicalDigest :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| NonCanonicalAssetId :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidWithdrawalAmount :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidDestination :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| InvalidEnvelope :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
| EnvelopeMismatch :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError



inductive aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
  where
| WrongLength :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| WrongMagic :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| WrongVersion :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| WrongFormatBinding :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| NonZeroReserved :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| ZeroRequiredBinding :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| SequenceIndexMismatch :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| TreeFull :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
| NonCanonicalDigest :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1



inductive aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  where
| WrongLength :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongMagic :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongVersion :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongStatementVersion :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongDigestEncoding :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidTransitionKind :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongSuccessCode :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| WrongPairFormat :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| ZeroRequiredBinding :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidProofBodyLength :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidStatementPayloadLength :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidLiveSnapshotPayloadLength :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| NonCanonicalOutputPair :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| InvalidAfterstateIndex :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
| NonCanonicalAfterstate :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1



inductive aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
  where
| WrongLength :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongMagic :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongVersion :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongItemCount :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongHeaderLength :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongSnapshotLength :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongAfterstateLength :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| WrongTotalLength :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| NonZeroReserved :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| Snapshot :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 →
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| Afterstate :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 →
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
| AfterstateIndexMismatch :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1



inductive aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  where
| WrongLength :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WrongMagic :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WrongVersion :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WrongDigestEncoding :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| InvalidTransitionKind :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| InvalidOutputLane :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| NonZeroBinding :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| NonCanonicalDigest :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| OutputLaneMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| MasterBindingMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| DeploymentBindingMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| HistoricalAnchorMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| CheckpointBindingMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| SelectedLaneBindingMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| LiveSnapshotMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| CandidateAfterstateMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| ResultBindingMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| WithdrawalDestinationMismatch :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| Payment :
  aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
    →
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| LaneTransition :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
    →
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| Afterstate :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 →
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
| Account :
  aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
    →
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1



structure aspis_statement.pool_v1.payment_relation.CommonPublicV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_3
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_2
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1.closure
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1.closure
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.exact.closure (N : Std.Usize) := Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_20
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_19
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_18
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_17
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_16
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_15
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_14
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_13
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_12
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_11
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_10
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_9
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_8
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_7
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_6
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_5
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_4
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_3
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_2
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1.closure
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_5
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_4
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_3
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_2
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.pair_forest_terminal.decode_terminal_common_boxed_v1.closure
  :=
Unit



def aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_2
  :=
Unit



def aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1.closure
  :=
Unit



def aspis_statement.pool_v1.payment_relation.decode_common.closure_1 := Unit



def aspis_statement.pool_v1.payment_relation.decode_common.closure := Unit



def aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure_1
  :=
Unit



def aspis_statement.pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1.closure
  :=
Unit

end AspisS6FiveUnrolledCodec

#print axioms AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
