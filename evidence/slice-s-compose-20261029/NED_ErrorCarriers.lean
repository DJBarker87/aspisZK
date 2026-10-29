import NBN_U05
import JHf_ReconstructionSlot
set_option autoImplicit false
namespace NED_ErrorCarriers
open Aeneas Aeneas.Std Result
def fromRawPoolV1PaymentStatementFormatError (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match value with
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
def toRawPoolV1PaymentStatementFormatError (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match value with
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
theorem from_to_PoolV1PaymentStatementFormatError (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    fromRawPoolV1PaymentStatementFormatError (toRawPoolV1PaymentStatementFormatError value) = value := by
  cases value <;> simp only [toRawPoolV1PaymentStatementFormatError,fromRawPoolV1PaymentStatementFormatError]
#print axioms from_to_PoolV1PaymentStatementFormatError
theorem to_from_PoolV1PaymentStatementFormatError (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    toRawPoolV1PaymentStatementFormatError (fromRawPoolV1PaymentStatementFormatError value) = value := by
  cases value <;> simp only [fromRawPoolV1PaymentStatementFormatError,toRawPoolV1PaymentStatementFormatError]
#print axioms to_from_PoolV1PaymentStatementFormatError
def fromRawPoolV1PairLiveSnapshotErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match value with
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .SequenceIndexMismatch => .SequenceIndexMismatch
  | .TreeFull => .TreeFull
  | .NonCanonicalDigest => .NonCanonicalDigest
def toRawPoolV1PairLiveSnapshotErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match value with
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongFormatBinding => .WrongFormatBinding
  | .NonZeroReserved => .NonZeroReserved
  | .ZeroRequiredBinding => .ZeroRequiredBinding
  | .SequenceIndexMismatch => .SequenceIndexMismatch
  | .TreeFull => .TreeFull
  | .NonCanonicalDigest => .NonCanonicalDigest
theorem from_to_PoolV1PairLiveSnapshotErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) :
    fromRawPoolV1PairLiveSnapshotErrorV1 (toRawPoolV1PairLiveSnapshotErrorV1 value) = value := by
  cases value <;> simp only [toRawPoolV1PairLiveSnapshotErrorV1,fromRawPoolV1PairLiveSnapshotErrorV1]
#print axioms from_to_PoolV1PairLiveSnapshotErrorV1
theorem to_from_PoolV1PairLiveSnapshotErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) :
    toRawPoolV1PairLiveSnapshotErrorV1 (fromRawPoolV1PairLiveSnapshotErrorV1 value) = value := by
  cases value <;> simp only [fromRawPoolV1PairLiveSnapshotErrorV1,toRawPoolV1PairLiveSnapshotErrorV1]
#print axioms to_from_PoolV1PairLiveSnapshotErrorV1
def fromRawPoolV1PairVerifierTransportErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match value with
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
def toRawPoolV1PairVerifierTransportErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match value with
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
theorem from_to_PoolV1PairVerifierTransportErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    fromRawPoolV1PairVerifierTransportErrorV1 (toRawPoolV1PairVerifierTransportErrorV1 value) = value := by
  cases value <;> simp only [toRawPoolV1PairVerifierTransportErrorV1,fromRawPoolV1PairVerifierTransportErrorV1]
#print axioms from_to_PoolV1PairVerifierTransportErrorV1
theorem to_from_PoolV1PairVerifierTransportErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
    toRawPoolV1PairVerifierTransportErrorV1 (fromRawPoolV1PairVerifierTransportErrorV1 value) = value := by
  cases value <;> simp only [fromRawPoolV1PairVerifierTransportErrorV1,toRawPoolV1PairVerifierTransportErrorV1]
#print axioms to_from_PoolV1PairVerifierTransportErrorV1
def fromRawPoolV1PairLatePublicStatementErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match value with
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongItemCount => .WrongItemCount
  | .WrongHeaderLength => .WrongHeaderLength
  | .WrongSnapshotLength => .WrongSnapshotLength
  | .WrongAfterstateLength => .WrongAfterstateLength
  | .WrongTotalLength => .WrongTotalLength
  | .NonZeroReserved => .NonZeroReserved
  | .Snapshot x => .Snapshot (fromRawPoolV1PairLiveSnapshotErrorV1 x)
  | .Afterstate x => .Afterstate (fromRawPoolV1PairVerifierTransportErrorV1 x)
  | .AfterstateIndexMismatch => .AfterstateIndexMismatch
def toRawPoolV1PairLatePublicStatementErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match value with
  | .WrongLength => .WrongLength
  | .WrongMagic => .WrongMagic
  | .WrongVersion => .WrongVersion
  | .WrongItemCount => .WrongItemCount
  | .WrongHeaderLength => .WrongHeaderLength
  | .WrongSnapshotLength => .WrongSnapshotLength
  | .WrongAfterstateLength => .WrongAfterstateLength
  | .WrongTotalLength => .WrongTotalLength
  | .NonZeroReserved => .NonZeroReserved
  | .Snapshot x => .Snapshot (toRawPoolV1PairLiveSnapshotErrorV1 x)
  | .Afterstate x => .Afterstate (toRawPoolV1PairVerifierTransportErrorV1 x)
  | .AfterstateIndexMismatch => .AfterstateIndexMismatch
theorem from_to_PoolV1PairLatePublicStatementErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) :
    fromRawPoolV1PairLatePublicStatementErrorV1 (toRawPoolV1PairLatePublicStatementErrorV1 value) = value := by
  cases value <;> simp only [toRawPoolV1PairLatePublicStatementErrorV1,fromRawPoolV1PairLatePublicStatementErrorV1 ,from_to_PoolV1PairLiveSnapshotErrorV1,from_to_PoolV1PairVerifierTransportErrorV1]
#print axioms from_to_PoolV1PairLatePublicStatementErrorV1
theorem to_from_PoolV1PairLatePublicStatementErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) :
    toRawPoolV1PairLatePublicStatementErrorV1 (fromRawPoolV1PairLatePublicStatementErrorV1 value) = value := by
  cases value <;> simp only [fromRawPoolV1PairLatePublicStatementErrorV1,toRawPoolV1PairLatePublicStatementErrorV1 ,to_from_PoolV1PairLiveSnapshotErrorV1,to_from_PoolV1PairVerifierTransportErrorV1]
#print axioms to_from_PoolV1PairLatePublicStatementErrorV1
def fromRawPoolV1TreeError (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError :=
  match value with
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
def toRawPoolV1TreeError (value : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError :=
  match value with
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
theorem from_to_PoolV1TreeError (value : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) :
    fromRawPoolV1TreeError (toRawPoolV1TreeError value) = value := by
  cases value <;> simp only [toRawPoolV1TreeError,fromRawPoolV1TreeError]
#print axioms from_to_PoolV1TreeError
theorem to_from_PoolV1TreeError (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) :
    toRawPoolV1TreeError (fromRawPoolV1TreeError value) = value := by
  cases value <;> simp only [fromRawPoolV1TreeError,toRawPoolV1TreeError]
#print axioms to_from_PoolV1TreeError
def fromRawPoolV1PairForestAccountErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match value with
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
  | .Tree x => .Tree (fromRawPoolV1TreeError x)
def toRawPoolV1PairForestAccountErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match value with
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
  | .Tree x => .Tree (toRawPoolV1TreeError x)
theorem from_to_PoolV1PairForestAccountErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :
    fromRawPoolV1PairForestAccountErrorV1 (toRawPoolV1PairForestAccountErrorV1 value) = value := by
  cases value <;> simp only [toRawPoolV1PairForestAccountErrorV1,fromRawPoolV1PairForestAccountErrorV1 ,from_to_PoolV1TreeError]
#print axioms from_to_PoolV1PairForestAccountErrorV1
theorem to_from_PoolV1PairForestAccountErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) :
    toRawPoolV1PairForestAccountErrorV1 (fromRawPoolV1PairForestAccountErrorV1 value) = value := by
  cases value <;> simp only [fromRawPoolV1PairForestAccountErrorV1,toRawPoolV1PairForestAccountErrorV1 ,to_from_PoolV1TreeError]
#print axioms to_from_PoolV1PairForestAccountErrorV1
def fromRawPoolV1PairForestTerminalFormatErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match value with
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
  | .Payment x => .Payment (fromRawPoolV1PaymentStatementFormatError x)
  | .LaneTransition x => .LaneTransition (fromRawPoolV1PairLatePublicStatementErrorV1 x)
  | .Afterstate x => .Afterstate (fromRawPoolV1PairVerifierTransportErrorV1 x)
  | .Account x => .Account (fromRawPoolV1PairForestAccountErrorV1 x)
def toRawPoolV1PairForestTerminalFormatErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match value with
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
  | .Payment x => .Payment (toRawPoolV1PaymentStatementFormatError x)
  | .LaneTransition x => .LaneTransition (toRawPoolV1PairLatePublicStatementErrorV1 x)
  | .Afterstate x => .Afterstate (toRawPoolV1PairVerifierTransportErrorV1 x)
  | .Account x => .Account (toRawPoolV1PairForestAccountErrorV1 x)
theorem from_to_PoolV1PairForestTerminalFormatErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) :
    fromRawPoolV1PairForestTerminalFormatErrorV1 (toRawPoolV1PairForestTerminalFormatErrorV1 value) = value := by
  cases value <;> simp only [toRawPoolV1PairForestTerminalFormatErrorV1,fromRawPoolV1PairForestTerminalFormatErrorV1 ,from_to_PoolV1PairForestAccountErrorV1,from_to_PoolV1PairLatePublicStatementErrorV1,from_to_PoolV1PairVerifierTransportErrorV1,from_to_PoolV1PaymentStatementFormatError]
#print axioms from_to_PoolV1PairForestTerminalFormatErrorV1
theorem to_from_PoolV1PairForestTerminalFormatErrorV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) :
    toRawPoolV1PairForestTerminalFormatErrorV1 (fromRawPoolV1PairForestTerminalFormatErrorV1 value) = value := by
  cases value <;> simp only [fromRawPoolV1PairForestTerminalFormatErrorV1,toRawPoolV1PairForestTerminalFormatErrorV1 ,to_from_PoolV1PairForestAccountErrorV1,to_from_PoolV1PairLatePublicStatementErrorV1,to_from_PoolV1PairVerifierTransportErrorV1,to_from_PoolV1PaymentStatementFormatError]
#print axioms to_from_PoolV1PairForestTerminalFormatErrorV1
end NED_ErrorCarriers
