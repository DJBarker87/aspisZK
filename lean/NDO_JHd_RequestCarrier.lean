import NDO_JHd_RequestValue
import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.JHd_RequestCarrier
open Aeneas Aeneas.Std Result

def mapPoolV1PaymentStatementFormatError (e : AspisR20Request.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongTransitionKind=>.WrongTransitionKind
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .NonZeroReserved=>.NonZeroReserved
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .InvalidAnchorSequence=>.InvalidAnchorSequence
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .NonCanonicalAssetId=>.NonCanonicalAssetId
  | .InvalidWithdrawalAmount=>.InvalidWithdrawalAmount
  | .InvalidDestination=>.InvalidDestination
  | .InvalidEnvelope=>.InvalidEnvelope
  | .EnvelopeMismatch=>.EnvelopeMismatch
#print axioms mapPoolV1PaymentStatementFormatError

def mapPoolV1TreeError (e : AspisR20Request.pool_v1.incremental_merkle.PoolV1TreeError) : AdapterRw.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError :=
  match e with
  | .TreeFull=>.TreeFull
  | .InsufficientCapacity=>.InsufficientCapacity
  | .IndexOutOfRange=>.IndexOutOfRange
  | .RootMismatch=>.RootMismatch
  | .NonCanonicalFrontier=>.NonCanonicalFrontier
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongDepth=>.WrongDepth
  | .WrongTreeHash=>.WrongTreeHash
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .NonZeroReserved=>.NonZeroReserved
#print axioms mapPoolV1TreeError

def mapPoolV1PairForestAccountErrorV1 (e : AspisR20Request.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongLaneCount=>.WrongLaneCount
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .WrongDepth=>.WrongDepth
  | .WrongFormatBinding=>.WrongFormatBinding
  | .NonZeroReserved=>.NonZeroReserved
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .InvalidBoolean=>.InvalidBoolean
  | .InvalidMasterState=>.InvalidMasterState
  | .InvalidLane=>.InvalidLane
  | .LaneMasterMismatch=>.LaneMasterMismatch
  | .LaneOrderMismatch=>.LaneOrderMismatch
  | .LaneSequenceDecreased=>.LaneSequenceDecreased
  | .DuplicateCheckpoint=>.DuplicateCheckpoint
  | .CheckpointSequenceOverflow=>.CheckpointSequenceOverflow
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .Identity=>.Identity
  | .Policy=>.Policy
  | .Tree x=>.Tree (mapPoolV1TreeError x)
#print axioms mapPoolV1PairForestAccountErrorV1

def mapPoolV1PairLiveSnapshotErrorV1 (e : AspisR20Request.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongFormatBinding=>.WrongFormatBinding
  | .NonZeroReserved=>.NonZeroReserved
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .SequenceIndexMismatch=>.SequenceIndexMismatch
  | .TreeFull=>.TreeFull
  | .NonCanonicalDigest=>.NonCanonicalDigest
#print axioms mapPoolV1PairLiveSnapshotErrorV1

def mapPoolV1PairVerifierTransportErrorV1 (e : AspisR20Request.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongStatementVersion=>.WrongStatementVersion
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .InvalidTransitionKind=>.InvalidTransitionKind
  | .WrongSuccessCode=>.WrongSuccessCode
  | .WrongPairFormat=>.WrongPairFormat
  | .ZeroRequiredBinding=>.ZeroRequiredBinding
  | .InvalidProofBodyLength=>.InvalidProofBodyLength
  | .InvalidStatementPayloadLength=>.InvalidStatementPayloadLength
  | .InvalidLiveSnapshotPayloadLength=>.InvalidLiveSnapshotPayloadLength
  | .NonCanonicalOutputPair=>.NonCanonicalOutputPair
  | .InvalidAfterstateIndex=>.InvalidAfterstateIndex
  | .NonCanonicalAfterstate=>.NonCanonicalAfterstate
#print axioms mapPoolV1PairVerifierTransportErrorV1

def mapPoolV1PairLatePublicStatementErrorV1 (e : AspisR20Request.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongItemCount=>.WrongItemCount
  | .WrongHeaderLength=>.WrongHeaderLength
  | .WrongSnapshotLength=>.WrongSnapshotLength
  | .WrongAfterstateLength=>.WrongAfterstateLength
  | .WrongTotalLength=>.WrongTotalLength
  | .NonZeroReserved=>.NonZeroReserved
  | .Snapshot x=>.Snapshot (mapPoolV1PairLiveSnapshotErrorV1 x)
  | .Afterstate x=>.Afterstate (mapPoolV1PairVerifierTransportErrorV1 x)
  | .AfterstateIndexMismatch=>.AfterstateIndexMismatch
#print axioms mapPoolV1PairLatePublicStatementErrorV1

def mapPoolV1PairForestTerminalFormatErrorV1 (e : AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match e with
  | .WrongLength=>.WrongLength
  | .WrongMagic=>.WrongMagic
  | .WrongVersion=>.WrongVersion
  | .WrongDigestEncoding=>.WrongDigestEncoding
  | .InvalidTransitionKind=>.InvalidTransitionKind
  | .InvalidOutputLane=>.InvalidOutputLane
  | .NonZeroBinding=>.NonZeroBinding
  | .NonCanonicalDigest=>.NonCanonicalDigest
  | .OutputLaneMismatch=>.OutputLaneMismatch
  | .MasterBindingMismatch=>.MasterBindingMismatch
  | .DeploymentBindingMismatch=>.DeploymentBindingMismatch
  | .HistoricalAnchorMismatch=>.HistoricalAnchorMismatch
  | .CheckpointBindingMismatch=>.CheckpointBindingMismatch
  | .SelectedLaneBindingMismatch=>.SelectedLaneBindingMismatch
  | .LiveSnapshotMismatch=>.LiveSnapshotMismatch
  | .CandidateAfterstateMismatch=>.CandidateAfterstateMismatch
  | .ResultBindingMismatch=>.ResultBindingMismatch
  | .WithdrawalDestinationMismatch=>.WithdrawalDestinationMismatch
  | .Payment x=>.Payment (mapPoolV1PaymentStatementFormatError x)
  | .LaneTransition x=>.LaneTransition (mapPoolV1PairLatePublicStatementErrorV1 x)
  | .Afterstate x=>.Afterstate (mapPoolV1PairVerifierTransportErrorV1 x)
  | .Account x=>.Account (mapPoolV1PairForestAccountErrorV1 x)
#print axioms mapPoolV1PairForestTerminalFormatErrorV1

def privateTransfer (p : AspisR20Request.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩

def withdrawal (p : AspisR20Request.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩

def payment (p : AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1) :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1 :=
  match p with
  | .PrivateTransfer p=>.PrivateTransfer (privateTransfer p)
  | .Withdrawal p=>.Withdrawal (withdrawal p)

def request (p : AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1) :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1 :=
  ⟨p.verifier_profile,p.verifier_release,p.pool_program,payment p.«public»⟩

def actual := request JHd_RequestValue.value

theorem profile : actual.verifier_profile=AdapterRw.r1_pool_adapter.PROFILE_BINDING := rfl
theorem release : actual.verifier_release=AdapterRw.r1_pool_adapter.RELEASE_BINDING := rfl
theorem pool : actual.pool_program=JHb_Programs.pool := rfl
#print axioms profile
#print axioms release
#print axioms pool
end AspisR1.JHd_RequestCarrier
