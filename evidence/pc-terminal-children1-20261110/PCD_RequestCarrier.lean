import NFY_Part059
import PCD_FrozenRequest.Types
set_option autoImplicit false
noncomputable section
namespace PCD_FrozenRequest
open Aeneas Aeneas.Std
-- Concrete structural carrier maps. Every child error constructor is retained;
-- no axiom, free Ops, unknown result or accepted-only premise is installed.
def mapPoolV1TreeError (x : AdapterRw.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) : aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError :=
  match x with
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

def mapPoolV1PairForestAccountErrorV1 (x : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match x with
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
  | .Tree x0 => .Tree (mapPoolV1TreeError x0)

def mapPoolV1PaymentStatementFormatError (x : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match x with
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

def mapPoolV1PairLiveSnapshotErrorV1 (x : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match x with
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .SequenceIndexMismatch => .SequenceIndexMismatch
  | .TreeFull => .TreeFull
  | .NonCanonicalDigest => .NonCanonicalDigest

def mapPoolV1PairVerifierTransportErrorV1 (x : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match x with
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

def mapPoolV1PairLatePublicStatementErrorV1 (x : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match x with
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongItemCount => .WrongItemCount
  | .WrongHeaderLength => .WrongHeaderLength
  | .WrongSnapshotLength => .WrongSnapshotLength
  | .WrongAfterstateLength => .WrongAfterstateLength
  | .WrongTotalLength => .WrongTotalLength
  | .NonZeroReserved => .NonZeroReserved
  | .Snapshot x0 => .Snapshot (mapPoolV1PairLiveSnapshotErrorV1 x0)
  | .Afterstate x0 => .Afterstate (mapPoolV1PairVerifierTransportErrorV1 x0)
  | .AfterstateIndexMismatch => .AfterstateIndexMismatch

def mapPoolV1PairForestTerminalFormatErrorV1 (x : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match x with
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
  | .Payment x0 => .Payment (mapPoolV1PaymentStatementFormatError x0)
  | .LaneTransition x0 => .LaneTransition (mapPoolV1PairLatePublicStatementErrorV1 x0)
  | .Afterstate x0 => .Afterstate (mapPoolV1PairVerifierTransportErrorV1 x0)
  | .Account x0 => .Account (mapPoolV1PairForestAccountErrorV1 x0)

def mapPoolV1WithdrawalPublicV1 (x : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  amount := x.amount
  destination_token_account := x.destination_token_account
  change_commitment := x.change_commitment
}

def unmapPoolV1WithdrawalPublicV1 (x : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  amount := x.amount
  destination_token_account := x.destination_token_account
  change_commitment := x.change_commitment
}

def mapPoolV1PrivateTransferPublicV1 (x : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment
}

def unmapPoolV1PrivateTransferPublicV1 (x : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment
}

abbrev SharedRequest := AspisR1.NFY_JHd_RequestNative.Request
abbrev LocalRequest := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1

def mapRequest (x : SharedRequest) : LocalRequest := {
  verifier_profile := x.verifier_profile, verifier_release := x.verifier_release,
  pool_program := x.pool_program, «public» := match x.«public» with
    | .PrivateTransfer p => .PrivateTransfer (mapPoolV1PrivateTransferPublicV1 p)
    | .Withdrawal p => .Withdrawal (mapPoolV1WithdrawalPublicV1 p)
}
def unmapRequest (x : LocalRequest) : SharedRequest := {
  verifier_profile := x.verifier_profile, verifier_release := x.verifier_release,
  pool_program := x.pool_program, «public» := match x.«public» with
    | .PrivateTransfer p => .PrivateTransfer (unmapPoolV1PrivateTransferPublicV1 p)
    | .Withdrawal p => .Withdrawal (unmapPoolV1WithdrawalPublicV1 p)
}
theorem request_roundtrip (x : SharedRequest) : unmapRequest (mapRequest x) = x := by
  cases x with
  | mk profile release program payment =>
    cases payment with
    | PrivateTransfer p => cases p; rfl
    | Withdrawal p => cases p; rfl
#print axioms request_roundtrip
end PCD_FrozenRequest
