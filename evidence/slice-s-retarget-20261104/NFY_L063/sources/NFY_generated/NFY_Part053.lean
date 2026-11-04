import Lean
import NFY_Part029
import NFY_Part052
import NFY_Part030
import NFY_Part049
import RPz7_S6CurrentAdapterCarrierV1
import NFY_Part032

-- BEGIN copied NED_ErrorCarriers: evidence/slice-s-compose-20261029/NED_ErrorCarriers.lean
set_option autoImplicit false
namespace NFY_NED_ErrorCarriers
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
end NFY_NED_ErrorCarriers
-- END copied NED_ErrorCarriers
-- BEGIN copied NED_DigestCohorts: evidence/slice-s-compose-20261029/NED_DigestCohorts.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_DigestCohorts
open Aeneas Aeneas.Std Result

theorem m31_encode (v : U32) :
    AspisR1AdapterReconstruct.aspis_core.field.M31.to_le_bytes v =
    AspisR1TerminalDecoder.aspis_core.field.M31.to_le_bytes v := by rfl

/-- Symbolic loop-body correspondence on arbitrary words, without evaluating
any concrete numeral recurrence or unfolding a buffer-length search. -/
theorem digest_encode (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.atomic_statement.encode_digest_canonical d =
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical d := by rfl

theorem first_byte (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.first_canonical_byte d =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.first_canonical_byte d := by rfl

#print axioms m31_encode
#print axioms digest_encode
#print axioms first_byte
end NFY_NED_DigestCohorts
-- END copied NED_DigestCohorts
-- BEGIN copied NED_ReconstructCarriers: evidence/slice-s-compose-20261029/NED_ReconstructCarriers.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_ReconstructCarriers
open Aeneas Aeneas.Std Result
abbrev Terminal := NFY_NBN_StatementResult.Statement
abbrev Raw := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev RawCommon := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1

def toRaw (s : Terminal) : Raw := AspisR1.JHf_Carrier.toPoolV1PairForestTerminalStatementV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 s)
def fromRaw (s : Raw) : Terminal := AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1
  (AspisR1.JHf_Carrier.fromPoolV1PairForestTerminalStatementV1 s)
def toRawCommon (c : Common) : RawCommon := AspisR1.JHf_Carrier.toPoolV1PairForestTerminalCommonV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalCommonV1 c)
def fromRawCommon (c : RawCommon) : Common := AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalCommonV1
  (AspisR1.JHf_Carrier.fromPoolV1PairForestTerminalCommonV1 c)

theorem common_roundtrip (c : Common) : fromRawCommon (toRawCommon c) = c := by
  unfold fromRawCommon toRawCommon
  rw [AspisR1.JHf_Carrier.from_toPoolV1PairForestTerminalCommonV1]
  exact AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalCommonV1 c

theorem statement_roundtrip (s : Terminal) : fromRaw (toRaw s) = s := by
  unfold fromRaw toRaw
  rw [AspisR1.JHf_Carrier.from_toPoolV1PairForestTerminalStatementV1]
  exact AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1 s

theorem common_argument (s : Terminal) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common (toRaw s) =
    ok (toRawCommon (NFY_NBN_StatementResult.common s)) := by
  cases s <;> rfl

theorem parts_argument (s : Terminal) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.statement_public_common (toRaw s) =
    ok (NFY_NBN_StatementResult.parts s) := by
  cases s <;> rfl

#print axioms common_roundtrip
#print axioms statement_roundtrip
#print axioms common_argument
#print axioms parts_argument
end NFY_NED_ReconstructCarriers
-- END copied NED_ReconstructCarriers
-- BEGIN copied NED_PaymentCohorts: evidence/slice-s-compose-20261029/NED_PaymentCohorts.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_PaymentCohorts
open Aeneas Aeneas.Std Result
abbrev T := NFY_NBN_ValidatorSummary.Transfer
abbrev W := NFY_NBN_ValidatorSummary.Withdrawal
abbrev C := NFY_NBG_PaymentChecks.C
abbrev RT := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev RW := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev RC := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.CommonPublicV1

def toRawTransfer (p : T) : RT := AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PrivateTransferPublicV1 p)
def toRawWithdrawal (p : W) : RW := AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1WithdrawalPublicV1 p)
def toRawCommon (c : C) : RC :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id⟩

theorem transfer_common (p : T) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.transfer_common (toRawTransfer p) =
    ok (toRawCommon (NFY_NBG_PaymentValidators.tc p)) := by rfl

theorem withdrawal_common (p : W) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.withdrawal_common (toRawWithdrawal p) =
    ok (toRawCommon (NFY_NBG_PaymentValidators.wc p)) := by rfl

theorem digest_canonical (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical d =
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical d := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem canonical_result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical d =
    ok (NFY_NBG_PaymentChecks.canonical d) := by
  rw [digest_canonical,NFY_NBG_PaymentChecks.canonical_result]

#print axioms transfer_common
#print axioms withdrawal_common
#print axioms digest_canonical
#print axioms canonical_result
end NFY_NED_PaymentCohorts
-- END copied NED_PaymentCohorts
-- BEGIN copied NED_CommonValidation: evidence/slice-s-compose-20261029/NED_CommonValidation.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_CommonValidation
open Aeneas Aeneas.Std Result NFY_NED_PaymentCohorts
abbrev TE := AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev RE := AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError

def mapPayment {T : Type} : core.result.Result T TE → core.result.Result T RE
  | .Ok v => .Ok v
  | .Err e => .Err (NFY_NED_ErrorCarriers.toRawPoolV1PaymentStatementFormatError e)

theorem capacity :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = ok 1048576#u64 := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH
  rfl

theorem common_result (c : C) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.validate_common (toRawCommon c) =
    ok (mapPayment (NFY_NBG_PaymentChecks.common c)) := by
  simp [AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.validate_common,
    toRawCommon,NFY_NBG_PaymentChecks.zero_result,capacity,NFY_NED_PaymentCohorts.canonical_result,
    NFY_NBG_PaymentChecks.common,AspisR1AdapterReconstruct.aspis_core.field.P,mapPayment,
    NFY_NED_ErrorCarriers.toRawPoolV1PaymentStatementFormatError]
  repeat' split
  all_goals simp_all

#print axioms capacity
#print axioms common_result
end NFY_NED_CommonValidation
-- END copied NED_CommonValidation
-- BEGIN copied NED_PaymentResultTransport: evidence/slice-s-compose-20261029/NED_PaymentResultTransport.lean
set_option autoImplicit false
namespace NFY_NED_PaymentResultTransport
open Aeneas Aeneas.Std Result NFY_NED_CommonValidation

theorem map_ite {T : Type} (p : Prop) [Decidable p]
    (a b : core.result.Result T TE) :
    mapPayment (if p then a else b) = if p then mapPayment a else mapPayment b := by
  split <;> rfl

theorem outer_ok {T : Type} (r : core.result.Result T TE) :
    (do let x ← (ok r : Result (core.result.Result T TE)); ok (mapPayment x)) = ok (mapPayment r) := rfl

#print axioms map_ite
#print axioms outer_ok
end NFY_NED_PaymentResultTransport
-- END copied NED_PaymentResultTransport
-- BEGIN copied NED_PaymentValidation: evidence/slice-s-compose-20261029/NED_PaymentValidation.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_PaymentValidation
open Aeneas Aeneas.Std Result NFY_NED_PaymentCohorts NFY_NED_CommonValidation
open AspisR1AdapterReconstruct

theorem transfer_result (p : T) :
    aspis_statement.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 (toRawTransfer p) =
    ok (mapPayment (NFY_NBG_PaymentValidators.transfer p)) := by
  unfold aspis_statement.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
  rw [NFY_NED_PaymentCohorts.transfer_common,bind_tc_ok,NFY_NED_CommonValidation.common_result,bind_tc_ok]
  cases h : NFY_NBG_PaymentChecks.common (NFY_NBG_PaymentValidators.tc p) with
  | Err e => simp [NFY_NBG_PaymentValidators.transfer,h,mapPayment,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp [NFY_NBG_PaymentValidators.transfer,h,mapPayment,NFY_NED_PaymentResultTransport.map_ite,canonical_result,
      toRawTransfer,AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1PrivateTransferPublicV1,
      core.result.Result.Insts.CoreOpsTry.branch,NFY_NED_ErrorCarriers.toRawPoolV1PaymentStatementFormatError]
    repeat' split
    all_goals simp_all

theorem value_limit : aspis_statement.spend.VALUE_LIMIT = ok 1073741824#u32 := by
  unfold aspis_statement.spend.VALUE_LIMIT
  rfl

theorem withdrawal_result (p : W) :
    aspis_statement.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 (toRawWithdrawal p) =
    ok (mapPayment (NFY_NBG_PaymentValidators.withdrawal p)) := by
  unfold aspis_statement.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
  rw [NFY_NED_PaymentCohorts.withdrawal_common,bind_tc_ok,NFY_NED_CommonValidation.common_result,bind_tc_ok]
  cases h : NFY_NBG_PaymentChecks.common (NFY_NBG_PaymentValidators.wc p) with
  | Err e => simp [NFY_NBG_PaymentValidators.withdrawal,h,mapPayment,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    by_cases large : 1073741824 ≤ p.amount.val <;>
      simp [NFY_NBG_PaymentValidators.withdrawal,h,large,mapPayment,NFY_NED_PaymentResultTransport.map_ite,canonical_result,
      toRawWithdrawal,AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1WithdrawalPublicV1,
      NFY_NBG_PaymentChecks.zero_result,value_limit,
      core.result.Result.Insts.CoreOpsTry.branch,NFY_NED_ErrorCarriers.toRawPoolV1PaymentStatementFormatError]
    all_goals repeat' split
    all_goals simp_all +arith <;> scalar_tac

#print axioms transfer_result
#print axioms value_limit
#print axioms withdrawal_result
end NFY_NED_PaymentValidation
-- END copied NED_PaymentValidation
-- BEGIN copied NED_ScannerCohorts: evidence/slice-s-compose-20261029/NED_ScannerCohorts.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_ScannerCohorts
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem account_body (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body d i =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem account_loop (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop d i =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop
  rw [funext (account_body d)]

theorem account (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical d =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical d := account_loop d 0#usize

theorem profile_body (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem profile_loop (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop d i =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop
  rw [funext (profile_body d)]

theorem profile (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical d =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical d := profile_loop d 0#usize

theorem profile_result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical d =
    ok (decide (NBD_DigestInduction.Canonical d)) := by
  rw [profile,NBD_DigestInduction.source]

theorem account_result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical d =
    ok (decide (NBD_DigestInduction.Canonical d)) := by
  rw [account,NBD_DigestInduction.same_scanner,NBD_DigestInduction.source]

#print axioms account_body
#print axioms account_loop
#print axioms account
#print axioms profile_body
#print axioms profile_loop
#print axioms profile
#print axioms profile_result
#print axioms account_result
end NFY_NED_ScannerCohorts
-- END copied NED_ScannerCohorts
-- BEGIN copied NEQ_EncoderOracle: evidence/slice-s-compose6-20261102/NEQ_EncoderOracle.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEQ_EncoderOracle
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NFY_NBN_StatementResult
open NFY_NED_EncoderTrace (Call R)
abbrev Validate := Statement → Result (core.result.Result Unit NFY_NBN_StatementResult.Error)
abbrev Pay := Statement → Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Late := NFY_NEE_ValidatorMutation.Late
abbrev Digest := Array U32 8#usize → Result (Array U8 32#usize)
def payStep (pay : Pay) (s : Statement) (anchor : Array U8 32#usize) (late : Slice U8) : R × List Call :=
  let r : R := do
    let pay ← pay s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok a => ok (.Ok ((NFY_NBN_StatementEncoderSummary.prefixBytes s anchor ++ late.val) ++ a.val))
  (r,[.payment s])

def lateStep (pay : Pay) (late : Late) (s : Statement) (anchor : Array U8 32#usize) : R × List Call :=
  let arg := (common s).lane_transition
  let out := NFY_NBN_LateResult.zero
  match late arg out with
  | .fail e => (.fail e,[.late arg out])
  | .div => (.div,[.late arg out])
  | .ok (.Err e,_) => (ok (.Err (.LaneTransition e)),[.late arg out])
  | .ok (.Ok _,late) => ((payStep pay s anchor late).1,.late arg out :: (payStep pay s anchor late).2)

def anchorStep (pay : Pay) (late : Late) (digest : Digest) (s : Statement) : R × List Call :=
  let d := (common s).historical_global_anchor
  match digest d with
  | .fail e => (.fail e,[.digest d])
  | .div => (.div,[.digest d])
  | .ok anchor => ((lateStep pay late s anchor).1,.digest d :: (lateStep pay late s anchor).2)

def run (validate : Validate) (pay : Pay) (late : Late) (digest : Digest) (s : Statement) : R × List Call :=
  let validation := validate s
  match validation with
  | .fail e => (.fail e,[.validate s])
  | .div => (.div,[.validate s])
  | .ok (.Err e) => (ok (.Err e),[.validate s])
  | .ok (.Ok _) => ((anchorStep pay late digest s).1,.validate s :: (anchorStep pay late digest s).2)

theorem pay_substitution (s : Statement) (anchor : Array U8 32#usize) (out : Slice U8) :
    payStep NFY_NEM_PaymentReached.pay s anchor out = NFY_NED_EncoderTrace.payStep s anchor out := by
  unfold payStep NFY_NED_EncoderTrace.payStep
  rw [NFY_NEM_PaymentReached.payment_instance]
  rfl

theorem late_substitution (s : Statement) (anchor : Array U8 32#usize) :
    lateStep NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late s anchor = NFY_NED_EncoderTrace.lateStep s anchor := by
  unfold lateStep NFY_NED_EncoderTrace.lateStep
  dsimp only
  have same : NFY_NEM_LateOracle.late (common s).lane_transition NFY_NBN_LateResult.zero =
      NFY_NBN_LateSummary.run NFY_NED_EncoderTrace.enc (common s).lane_transition NFY_NBN_LateResult.zero :=
    (NFY_NED_SubtreeComposition.late_encode _ _).symm
  rw [same]
  cases h : NFY_NBN_LateSummary.run NFY_NED_EncoderTrace.enc (common s).lane_transition NFY_NBN_LateResult.zero with
  | fail e => rfl
  | div => rfl
  | ok pair => cases pair with
    | mk status out => cases status with
      | Err e => rfl
      | Ok u =>
        simp only []
        rw [pay_substitution]

theorem anchor_substitution (s : Statement) :
    anchorStep NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late atomic_statement.encode_digest_canonical s =
      NFY_NED_EncoderTrace.anchorStep s := by
  unfold anchorStep NFY_NED_EncoderTrace.anchorStep NFY_NED_EncoderTrace.enc
  dsimp only
  cases h : atomic_statement.encode_digest_canonical (common s).historical_global_anchor with
  | fail e => rfl
  | div => rfl
  | ok anchor =>
    simp only []
    rw [late_substitution]

theorem substitution (s : Statement) :
    run pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late atomic_statement.encode_digest_canonical s =
      NFY_NED_EncoderTrace.run s := by
  unfold run NFY_NED_EncoderTrace.run
  rw [← NFY_NED_CodecComposition.validator s]
  change (match NFY_NED_ExecutionComposition.validatorReference s with
    | .fail e => _ | .div => _ | .ok (.Err e) => _ | .ok (.Ok u) => _) = _
  cases h : NFY_NED_ExecutionComposition.validatorReference s with
  | fail e => rfl
  | div => rfl
  | ok status => cases status with
    | Err e => rfl
    | Ok u =>
      simp only []
      rw [anchor_substitution]

theorem result_state_effects {State : Type} (s : Statement) (state : State) :
    let observed := run pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      NFY_NEM_PaymentReached.pay NFY_NEM_LateOracle.late atomic_statement.encode_digest_canonical s
    (observed.1,state,observed.2) =
      (NFY_NBN_StatementEncoderSummary.observe (AspisS6OuterNativeInstalled.encode s),
       state,(NFY_NED_EncoderTrace.run s).2) := by
  dsimp only
  rw [substitution,NFY_NED_EncoderTrace.erases]

#print axioms pay_substitution
#print axioms late_substitution
#print axioms anchor_substitution
#print axioms substitution
#print axioms result_state_effects
end NFY_NEQ_EncoderOracle
-- END copied NEQ_EncoderOracle
-- BEGIN copied NEU_BoxDecodeModel: evidence/slice-s-compose7-20261103/NEU_BoxDecodeModel.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NEU_BoxDecodeModel
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Common := PoolV1PairForestTerminalCommonV1

def transferRun (c : Common) (b : Array U8 216#usize) := do
  let decoded ← NFY_NEQ_PaymentDecode.transferFull b.to_slice
  match decoded with
  | .Err e => ok (.Err (.Payment e) : core.result.Result PoolV1PairForestTerminalStatementV1 PoolV1PairForestTerminalFormatErrorV1)
  | .Ok p => ok (.Ok (.PrivateTransfer c p))

def withdrawalRun (c : Common) (b : Array U8 216#usize) := do
  let decoded ← NFY_NEQ_PaymentDecode.withdrawalFull b.to_slice
  match decoded with
  | .Err e => ok (.Err (.Payment e) : core.result.Result PoolV1PairForestTerminalStatementV1 PoolV1PairForestTerminalFormatErrorV1)
  | .Ok p => ok (.Ok (.Withdrawal c p))

theorem transfer_result_state_effects {State : Type} (c : Common) (b : Array U8 216#usize) (state : State) :
    (transferRun c b,state,([] : List Unit)) =
    (decode_transfer_statement_boxed_v1 c b.to_slice,state,[]) := by
  have same := congrArg (fun x => x.1) (NFY_NEQ_PaymentDecode.transfer_result_state_effects b.to_slice state)
  dsimp only at same
  unfold transferRun decode_transfer_statement_boxed_v1
  rw [same,NFY_NBP_TransferDecode.fixed]
  cases NFY_NBP_PaymentModel.transfer_decoded b <;> rfl

theorem withdrawal_result_state_effects {State : Type} (c : Common) (b : Array U8 216#usize) (state : State) :
    (withdrawalRun c b,state,([] : List Unit)) =
    (decode_withdrawal_statement_boxed_v1 c b.to_slice,state,[]) := by
  have same := congrArg (fun x => x.1) (NFY_NEQ_PaymentDecode.withdrawal_result_state_effects b.to_slice state)
  dsimp only at same
  unfold withdrawalRun decode_withdrawal_statement_boxed_v1
  rw [same,NFY_NBP_WithdrawalDecode.fixed]
  cases NFY_NBP_PaymentModel.withdrawal_decoded b <;> rfl

#print axioms transfer_result_state_effects
#print axioms withdrawal_result_state_effects
end NFY_NEU_BoxDecodeModel
-- END copied NEU_BoxDecodeModel

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
