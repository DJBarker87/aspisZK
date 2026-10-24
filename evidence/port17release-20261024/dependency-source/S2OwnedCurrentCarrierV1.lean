import S2OwnedStage1ReachabilityV1
import CurrentCompactFirstCompositionV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.CurrentCarrier

def fromDecoderAfterstate (x : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}

def fromDecoderSnapshot (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}

def fromDecoderTransfer (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}

def fromDecoderWithdrawal (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}

def fromDecoderTransition (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=fromDecoderSnapshot x.live_snapshot,candidate_afterstate:=fromDecoderAfterstate x.candidate_afterstate}

def fromDecoderCommon (x : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  {master_account:=x.master_account, checkpoint_account:=x.checkpoint_account, selected_lane_account:=x.selected_lane_account, output_lane:=x.output_lane, checkpoint_sequence:=x.checkpoint_sequence, historical_global_anchor:=x.historical_global_anchor,lane_transition:=fromDecoderTransition x.lane_transition}

def fromDecoderStatement : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
  | .PrivateTransfer c p => .PrivateTransfer (fromDecoderCommon c) (fromDecoderTransfer p)
  | .Withdrawal c p => .Withdrawal (fromDecoderCommon c) (fromDecoderWithdrawal p)

def toDecoderAfterstate (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}

def toDecoderSnapshot (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}

def toDecoderTransfer (x : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}

def toDecoderWithdrawal (x : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}

def toDecoderTransition (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toDecoderSnapshot x.live_snapshot,candidate_afterstate:=toDecoderAfterstate x.candidate_afterstate}

def toDecoderCommon (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  {master_account:=x.master_account, checkpoint_account:=x.checkpoint_account, selected_lane_account:=x.selected_lane_account, output_lane:=x.output_lane, checkpoint_sequence:=x.checkpoint_sequence, historical_global_anchor:=x.historical_global_anchor,lane_transition:=toDecoderTransition x.lane_transition}

def toDecoderStatement : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 → AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
  | .PrivateTransfer c p => .PrivateTransfer (toDecoderCommon c) (toDecoderTransfer p)
  | .Withdrawal c p => .Withdrawal (toDecoderCommon c) (toDecoderWithdrawal p)

def toCurrentAfterstate (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}

def toCurrentSnapshot (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}

def toCurrentTransfer (x : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}

def toCurrentWithdrawal (x : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}

def toCurrentTransition (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toCurrentSnapshot x.live_snapshot,candidate_afterstate:=toCurrentAfterstate x.candidate_afterstate}

def toCurrentPublic : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  | .Transfer p t => .Transfer (toCurrentTransfer p) (toCurrentTransition t)
  | .Withdrawal p t => .Withdrawal (toCurrentWithdrawal p) (toCurrentTransition t)

def fromCurrentAfterstate (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}

def fromCurrentSnapshot (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}

def fromCurrentTransfer (x : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}

def fromCurrentWithdrawal (x : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}

def fromCurrentTransition (x : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=fromCurrentSnapshot x.live_snapshot,candidate_afterstate:=fromCurrentAfterstate x.candidate_afterstate}

def fromCurrentPublic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  | .Transfer p t => .Transfer (fromCurrentTransfer p) (fromCurrentTransition t)
  | .Withdrawal p t => .Withdrawal (fromCurrentWithdrawal p) (fromCurrentTransition t)

def fromDecoderTreeError : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError → AspisS2OwnedStage1.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
  | .TreeFull => .TreeFull
  | .InsufficientCapacity => .InsufficientCapacity
  | .IndexOutOfRange => .IndexOutOfRange
  | .RootMismatch => .RootMismatch
  | .NonCanonicalFrontier => .NonCanonicalFrontier
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongDepth => .WrongDepth
  | .WrongTreeHash => .WrongTreeHash
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .NonZeroReserved => .NonZeroReserved

def toDecoderTreeError : AspisS2OwnedStage1.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError → AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError
  | .TreeFull => .TreeFull
  | .InsufficientCapacity => .InsufficientCapacity
  | .IndexOutOfRange => .IndexOutOfRange
  | .RootMismatch => .RootMismatch
  | .NonCanonicalFrontier => .NonCanonicalFrontier
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongDepth => .WrongDepth
  | .WrongTreeHash => .WrongTreeHash
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .NonZeroReserved => .NonZeroReserved

theorem fromDecoderTreeError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) : toDecoderTreeError (fromDecoderTreeError x)=x := by
  cases x <;> simp only [fromDecoderTreeError, toDecoderTreeError]

theorem toDecoderTreeError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) : fromDecoderTreeError (toDecoderTreeError x)=x := by
  cases x <;> simp only [toDecoderTreeError, fromDecoderTreeError]

def fromDecoderAccountError : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongLaneCount => .WrongLaneCount
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .WrongDepth => .WrongDepth
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidBoolean => .InvalidBoolean
  | .InvalidMasterState => .InvalidMasterState
  | .InvalidLane => .InvalidLane
  | .LaneMasterMismatch => .LaneMasterMismatch
  | .LaneOrderMismatch => .LaneOrderMismatch
  | .LaneSequenceDecreased => .LaneSequenceDecreased
  | .DuplicateCheckpoint => .DuplicateCheckpoint
  | .CheckpointSequenceOverflow => .CheckpointSequenceOverflow
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .Identity => .Identity
  | .Policy => .Policy
  | .Tree x0 => .Tree (fromDecoderTreeError x0)

def toDecoderAccountError : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongLaneCount => .WrongLaneCount
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .WrongDepth => .WrongDepth
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidBoolean => .InvalidBoolean
  | .InvalidMasterState => .InvalidMasterState
  | .InvalidLane => .InvalidLane
  | .LaneMasterMismatch => .LaneMasterMismatch
  | .LaneOrderMismatch => .LaneOrderMismatch
  | .LaneSequenceDecreased => .LaneSequenceDecreased
  | .DuplicateCheckpoint => .DuplicateCheckpoint
  | .CheckpointSequenceOverflow => .CheckpointSequenceOverflow
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .Identity => .Identity
  | .Policy => .Policy
  | .Tree x0 => .Tree (toDecoderTreeError x0)

theorem fromDecoderAccountError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : toDecoderAccountError (fromDecoderAccountError x)=x := by
  cases x <;> simp only [fromDecoderAccountError, toDecoderAccountError, fromDecoderTreeError_roundtrip]

theorem toDecoderAccountError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : fromDecoderAccountError (toDecoderAccountError x)=x := by
  cases x <;> simp only [toDecoderAccountError, fromDecoderAccountError, toDecoderTreeError_roundtrip]

def fromDecoderPaymentError : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongTransitionKind => .WrongTransitionKind
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidAnchorSequence => .InvalidAnchorSequence
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .NonCanonicalAssetId => .NonCanonicalAssetId
  | .InvalidWithdrawalAmount => .InvalidWithdrawalAmount
  | .InvalidDestination => .InvalidDestination
  | .InvalidEnvelope => .InvalidEnvelope
  | .EnvelopeMismatch => .EnvelopeMismatch

def toDecoderPaymentError : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongTransitionKind => .WrongTransitionKind
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidAnchorSequence => .InvalidAnchorSequence
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .NonCanonicalAssetId => .NonCanonicalAssetId
  | .InvalidWithdrawalAmount => .InvalidWithdrawalAmount
  | .InvalidDestination => .InvalidDestination
  | .InvalidEnvelope => .InvalidEnvelope
  | .EnvelopeMismatch => .EnvelopeMismatch

theorem fromDecoderPaymentError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : toDecoderPaymentError (fromDecoderPaymentError x)=x := by
  cases x <;> simp only [fromDecoderPaymentError, toDecoderPaymentError, fromDecoderTreeError_roundtrip, fromDecoderAccountError_roundtrip]

theorem toDecoderPaymentError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : fromDecoderPaymentError (toDecoderPaymentError x)=x := by
  cases x <;> simp only [toDecoderPaymentError, fromDecoderPaymentError, toDecoderTreeError_roundtrip, toDecoderAccountError_roundtrip]

def fromDecoderSnapshotError : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .SequenceIndexMismatch => .SequenceIndexMismatch
  | .TreeFull => .TreeFull
  | .NonCanonicalDigest => .NonCanonicalDigest

def toDecoderSnapshotError : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .SequenceIndexMismatch => .SequenceIndexMismatch
  | .TreeFull => .TreeFull
  | .NonCanonicalDigest => .NonCanonicalDigest

theorem fromDecoderSnapshotError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : toDecoderSnapshotError (fromDecoderSnapshotError x)=x := by
  cases x <;> simp only [fromDecoderSnapshotError, toDecoderSnapshotError, fromDecoderTreeError_roundtrip, fromDecoderAccountError_roundtrip, fromDecoderPaymentError_roundtrip]

theorem toDecoderSnapshotError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : fromDecoderSnapshotError (toDecoderSnapshotError x)=x := by
  cases x <;> simp only [toDecoderSnapshotError, fromDecoderSnapshotError, toDecoderTreeError_roundtrip, toDecoderAccountError_roundtrip, toDecoderPaymentError_roundtrip]

def fromDecoderAfterstateError : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongStatementVersion => .WrongStatementVersion
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .InvalidTransitionKind => .InvalidTransitionKind
  | .WrongSuccessCode => .WrongSuccessCode
  | .WrongPairFormat => .WrongPairFormat
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidProofBodyLength => .InvalidProofBodyLength
  | .InvalidStatementPayloadLength => .InvalidStatementPayloadLength
  | .InvalidLiveSnapshotPayloadLength => .InvalidLiveSnapshotPayloadLength
  | .NonCanonicalOutputPair => .NonCanonicalOutputPair
  | .InvalidAfterstateIndex => .InvalidAfterstateIndex
  | .NonCanonicalAfterstate => .NonCanonicalAfterstate

def toDecoderAfterstateError : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongStatementVersion => .WrongStatementVersion
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .InvalidTransitionKind => .InvalidTransitionKind
  | .WrongSuccessCode => .WrongSuccessCode
  | .WrongPairFormat => .WrongPairFormat
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .InvalidProofBodyLength => .InvalidProofBodyLength
  | .InvalidStatementPayloadLength => .InvalidStatementPayloadLength
  | .InvalidLiveSnapshotPayloadLength => .InvalidLiveSnapshotPayloadLength
  | .NonCanonicalOutputPair => .NonCanonicalOutputPair
  | .InvalidAfterstateIndex => .InvalidAfterstateIndex
  | .NonCanonicalAfterstate => .NonCanonicalAfterstate

theorem fromDecoderAfterstateError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : toDecoderAfterstateError (fromDecoderAfterstateError x)=x := by
  cases x <;> simp only [fromDecoderAfterstateError, toDecoderAfterstateError, fromDecoderTreeError_roundtrip, fromDecoderAccountError_roundtrip, fromDecoderPaymentError_roundtrip, fromDecoderSnapshotError_roundtrip]

theorem toDecoderAfterstateError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : fromDecoderAfterstateError (toDecoderAfterstateError x)=x := by
  cases x <;> simp only [toDecoderAfterstateError, fromDecoderAfterstateError, toDecoderTreeError_roundtrip, toDecoderAccountError_roundtrip, toDecoderPaymentError_roundtrip, toDecoderSnapshotError_roundtrip]

def fromDecoderTransitionError : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongItemCount => .WrongItemCount
  | .WrongHeaderLength => .WrongHeaderLength
  | .WrongSnapshotLength => .WrongSnapshotLength
  | .WrongAfterstateLength => .WrongAfterstateLength
  | .WrongTotalLength => .WrongTotalLength
  | .NonZeroReserved => .NonZeroReserved
  | .Snapshot x0 => .Snapshot (fromDecoderSnapshotError x0)
  | .Afterstate x0 => .Afterstate (fromDecoderAfterstateError x0)
  | .AfterstateIndexMismatch => .AfterstateIndexMismatch

def toDecoderTransitionError : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongItemCount => .WrongItemCount
  | .WrongHeaderLength => .WrongHeaderLength
  | .WrongSnapshotLength => .WrongSnapshotLength
  | .WrongAfterstateLength => .WrongAfterstateLength
  | .WrongTotalLength => .WrongTotalLength
  | .NonZeroReserved => .NonZeroReserved
  | .Snapshot x0 => .Snapshot (toDecoderSnapshotError x0)
  | .Afterstate x0 => .Afterstate (toDecoderAfterstateError x0)
  | .AfterstateIndexMismatch => .AfterstateIndexMismatch

theorem fromDecoderTransitionError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : toDecoderTransitionError (fromDecoderTransitionError x)=x := by
  cases x <;> simp only [fromDecoderTransitionError, toDecoderTransitionError, fromDecoderTreeError_roundtrip, fromDecoderAccountError_roundtrip, fromDecoderPaymentError_roundtrip, fromDecoderSnapshotError_roundtrip, fromDecoderAfterstateError_roundtrip]

theorem toDecoderTransitionError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : fromDecoderTransitionError (toDecoderTransitionError x)=x := by
  cases x <;> simp only [toDecoderTransitionError, fromDecoderTransitionError, toDecoderTreeError_roundtrip, toDecoderAccountError_roundtrip, toDecoderPaymentError_roundtrip, toDecoderSnapshotError_roundtrip, toDecoderAfterstateError_roundtrip]

def fromDecoderDecodeError : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 → AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .InvalidTransitionKind => .InvalidTransitionKind
  | .InvalidOutputLane => .InvalidOutputLane
  | .NonZeroBinding => .NonZeroBinding
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .OutputLaneMismatch => .OutputLaneMismatch
  | .MasterBindingMismatch => .MasterBindingMismatch
  | .DeploymentBindingMismatch => .DeploymentBindingMismatch
  | .HistoricalAnchorMismatch => .HistoricalAnchorMismatch
  | .CheckpointBindingMismatch => .CheckpointBindingMismatch
  | .SelectedLaneBindingMismatch => .SelectedLaneBindingMismatch
  | .LiveSnapshotMismatch => .LiveSnapshotMismatch
  | .CandidateAfterstateMismatch => .CandidateAfterstateMismatch
  | .ResultBindingMismatch => .ResultBindingMismatch
  | .WithdrawalDestinationMismatch => .WithdrawalDestinationMismatch
  | .Payment x0 => .Payment (fromDecoderPaymentError x0)
  | .LaneTransition x0 => .LaneTransition (fromDecoderTransitionError x0)
  | .Afterstate x0 => .Afterstate (fromDecoderAfterstateError x0)
  | .Account x0 => .Account (fromDecoderAccountError x0)

def toDecoderDecodeError : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongDigestEncoding => .WrongDigestEncoding
  | .InvalidTransitionKind => .InvalidTransitionKind
  | .InvalidOutputLane => .InvalidOutputLane
  | .NonZeroBinding => .NonZeroBinding
  | .NonCanonicalDigest => .NonCanonicalDigest
  | .OutputLaneMismatch => .OutputLaneMismatch
  | .MasterBindingMismatch => .MasterBindingMismatch
  | .DeploymentBindingMismatch => .DeploymentBindingMismatch
  | .HistoricalAnchorMismatch => .HistoricalAnchorMismatch
  | .CheckpointBindingMismatch => .CheckpointBindingMismatch
  | .SelectedLaneBindingMismatch => .SelectedLaneBindingMismatch
  | .LiveSnapshotMismatch => .LiveSnapshotMismatch
  | .CandidateAfterstateMismatch => .CandidateAfterstateMismatch
  | .ResultBindingMismatch => .ResultBindingMismatch
  | .WithdrawalDestinationMismatch => .WithdrawalDestinationMismatch
  | .Payment x0 => .Payment (toDecoderPaymentError x0)
  | .LaneTransition x0 => .LaneTransition (toDecoderTransitionError x0)
  | .Afterstate x0 => .Afterstate (toDecoderAfterstateError x0)
  | .Account x0 => .Account (toDecoderAccountError x0)

theorem fromDecoderDecodeError_roundtrip (x : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : toDecoderDecodeError (fromDecoderDecodeError x)=x := by
  cases x <;> simp only [fromDecoderDecodeError, toDecoderDecodeError, fromDecoderTreeError_roundtrip, fromDecoderAccountError_roundtrip, fromDecoderPaymentError_roundtrip, fromDecoderSnapshotError_roundtrip, fromDecoderAfterstateError_roundtrip, fromDecoderTransitionError_roundtrip]

theorem toDecoderDecodeError_roundtrip (x : AspisS2OwnedStage1.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : fromDecoderDecodeError (toDecoderDecodeError x)=x := by
  cases x <;> simp only [toDecoderDecodeError, fromDecoderDecodeError, toDecoderTreeError_roundtrip, toDecoderAccountError_roundtrip, toDecoderPaymentError_roundtrip, toDecoderSnapshotError_roundtrip, toDecoderAfterstateError_roundtrip, toDecoderTransitionError_roundtrip]

theorem decoder_statement_roundtrip (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    toDecoderStatement (fromDecoderStatement s)=s := by cases s <;> rfl
theorem fresh_statement_roundtrip (s : Reachability.Statement) :
    fromDecoderStatement (toDecoderStatement s)=s := by cases s <;> rfl
theorem current_public_roundtrip (p : AspisR1CurrentCaller.FirstComposition.Public) :
    toCurrentPublic (fromCurrentPublic p)=p := by cases p <;> rfl
theorem fresh_public_roundtrip (p : Reachability.Public) :
    fromCurrentPublic (toCurrentPublic p)=p := by cases p <;> rfl
theorem selected_public (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    (do
      let p ← aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public (fromDecoderStatement s)
      ok (toCurrentPublic p)) =
    ok (AspisR1CurrentCaller.FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) := by
  cases s <;> rfl

#print axioms decoder_statement_roundtrip
#print axioms fresh_statement_roundtrip
#print axioms current_public_roundtrip
#print axioms selected_public
#print axioms fromDecoderDecodeError_roundtrip
end AspisS2OwnedStage1.CurrentCarrier
