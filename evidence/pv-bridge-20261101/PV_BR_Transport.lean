import PV_BR_BuilderAdmission
import PV_BR_ProverTypes
import AspisR1WithdrawalValidation.Types
import AspisR1TerminalDecoder.Types
import AspisR1FinishRelationCurrent.Types

/-! D540 privacy-only transport. No omission of retry or entropy outcomes. -/
set_option autoImplicit false
namespace PV_BR_Transport

abbrev paymentShared := AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
def paymentToShared : AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope
  | AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch => AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch
def paymentFromShared : AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope
  | AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch => AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch
theorem payment_left_inverse (e : AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : paymentFromShared (paymentToShared e) = e := by
  cases e <;> rfl
theorem payment_right_inverse (e : AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : paymentToShared (paymentFromShared e) = e := by
  cases e <;> rfl
theorem payment_discriminant (e : AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    AspisR1WithdrawalValidation.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.read_discriminant (paymentToShared e) = AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.read_discriminant e := by
  cases e <;> rfl
theorem payment_injective : Function.Injective paymentToShared := by
  intro a b h
  have h' := congrArg paymentFromShared h
  exact (payment_left_inverse a).symm.trans (h'.trans (payment_left_inverse b))

abbrev treeShared := AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError
def treeToShared : AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError → AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.TreeFull => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.TreeFull
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.InsufficientCapacity => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.InsufficientCapacity
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongLength => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongLength
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongMagic => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongMagic
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongVersion => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongVersion
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongDepth => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongDepth
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongTreeHash => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongTreeHash
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongDigestEncoding => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongDigestEncoding
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalDigest => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalDigest
  | AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.NonZeroReserved => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonZeroReserved
def treeFromShared : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError → AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.TreeFull => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.TreeFull
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.InsufficientCapacity => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.InsufficientCapacity
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongLength => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongLength
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongMagic => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongMagic
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongVersion => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongVersion
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongDepth => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongDepth
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongTreeHash => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongTreeHash
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongDigestEncoding => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.WrongDigestEncoding
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalDigest => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalDigest
  | AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonZeroReserved => AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.NonZeroReserved
theorem tree_left_inverse (e : AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError) : treeFromShared (treeToShared e) = e := by
  cases e <;> rfl
theorem tree_right_inverse (e : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) : treeToShared (treeFromShared e) = e := by
  cases e <;> rfl
theorem tree_discriminant (e : AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError) :
    AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.read_discriminant (treeToShared e) = AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError.read_discriminant e := by
  cases e <;> rfl
theorem tree_injective : Function.Injective treeToShared := by
  intro a b h
  have h' := congrArg treeFromShared h
  exact (tree_left_inverse a).symm.trans (h'.trans (tree_left_inverse b))

inductive ProverOnly where
  | rejected | attemptsExhausted | entropy
abbrev VerifierShared := AspisR1FinishRelationCurrent.verifier.Error
def verifierEmbed : AspisR1FinishRelationCurrent.verifier.Error → AspisR1ProverCommit.verifier.Error
  | AspisR1FinishRelationCurrent.verifier.Error.Parse => AspisR1ProverCommit.verifier.Error.Parse
  | AspisR1FinishRelationCurrent.verifier.Error.Semantic => AspisR1ProverCommit.verifier.Error.Semantic
  | AspisR1FinishRelationCurrent.verifier.Error.Transcript => AspisR1ProverCommit.verifier.Error.Transcript
  | AspisR1FinishRelationCurrent.verifier.Error.Relation => AspisR1ProverCommit.verifier.Error.Relation
  | AspisR1FinishRelationCurrent.verifier.Error.Merkle => AspisR1ProverCommit.verifier.Error.Merkle
  | AspisR1FinishRelationCurrent.verifier.Error.Query => AspisR1ProverCommit.verifier.Error.Query
  | AspisR1FinishRelationCurrent.verifier.Error.Checkpoint => AspisR1ProverCommit.verifier.Error.Checkpoint
  | AspisR1FinishRelationCurrent.verifier.Error.Allocation => AspisR1ProverCommit.verifier.Error.Allocation
def verifierSplit : AspisR1ProverCommit.verifier.Error → Sum AspisR1FinishRelationCurrent.verifier.Error ProverOnly
  | AspisR1ProverCommit.verifier.Error.Parse => .inl AspisR1FinishRelationCurrent.verifier.Error.Parse
  | AspisR1ProverCommit.verifier.Error.Semantic => .inl AspisR1FinishRelationCurrent.verifier.Error.Semantic
  | AspisR1ProverCommit.verifier.Error.Transcript => .inl AspisR1FinishRelationCurrent.verifier.Error.Transcript
  | AspisR1ProverCommit.verifier.Error.Relation => .inl AspisR1FinishRelationCurrent.verifier.Error.Relation
  | AspisR1ProverCommit.verifier.Error.Merkle => .inl AspisR1FinishRelationCurrent.verifier.Error.Merkle
  | AspisR1ProverCommit.verifier.Error.Query => .inl AspisR1FinishRelationCurrent.verifier.Error.Query
  | AspisR1ProverCommit.verifier.Error.Checkpoint => .inl AspisR1FinishRelationCurrent.verifier.Error.Checkpoint
  | AspisR1ProverCommit.verifier.Error.Allocation => .inl AspisR1FinishRelationCurrent.verifier.Error.Allocation
  | AspisR1ProverCommit.verifier.Error.Rejected => .inr .rejected
  | AspisR1ProverCommit.verifier.Error.AttemptsExhausted => .inr .attemptsExhausted
  | AspisR1ProverCommit.verifier.Error.Entropy => .inr .entropy
def verifierJoin : Sum AspisR1FinishRelationCurrent.verifier.Error ProverOnly → AspisR1ProverCommit.verifier.Error
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Parse => AspisR1ProverCommit.verifier.Error.Parse
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Semantic => AspisR1ProverCommit.verifier.Error.Semantic
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Transcript => AspisR1ProverCommit.verifier.Error.Transcript
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Relation => AspisR1ProverCommit.verifier.Error.Relation
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Merkle => AspisR1ProverCommit.verifier.Error.Merkle
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Query => AspisR1ProverCommit.verifier.Error.Query
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Checkpoint => AspisR1ProverCommit.verifier.Error.Checkpoint
  | .inl AspisR1FinishRelationCurrent.verifier.Error.Allocation => AspisR1ProverCommit.verifier.Error.Allocation
  | .inr .rejected => AspisR1ProverCommit.verifier.Error.Rejected
  | .inr .attemptsExhausted => AspisR1ProverCommit.verifier.Error.AttemptsExhausted
  | .inr .entropy => AspisR1ProverCommit.verifier.Error.Entropy
theorem verifier_retraction (e : AspisR1FinishRelationCurrent.verifier.Error) : verifierSplit (verifierEmbed e) = .inl e := by
  cases e <;> rfl
theorem verifier_join_split (e : AspisR1ProverCommit.verifier.Error) : verifierJoin (verifierSplit e) = e := by
  cases e <;> rfl
theorem verifier_split_join (e : Sum AspisR1FinishRelationCurrent.verifier.Error ProverOnly) : verifierSplit (verifierJoin e) = e := by
  cases e with
  | inl e => cases e <;> rfl
  | inr e => cases e <;> rfl
theorem verifier_embedding_injective : Function.Injective verifierEmbed := by
  intro a b h
  have h' := congrArg verifierSplit h
  rw [verifier_retraction, verifier_retraction] at h'
  exact Sum.inl.inj h'
theorem verifier_discriminant (e : AspisR1FinishRelationCurrent.verifier.Error) :
    AspisR1ProverCommit.verifier.Error.read_discriminant (verifierEmbed e) = AspisR1FinishRelationCurrent.verifier.Error.read_discriminant e := by
  cases e <;> rfl

/-- Complete Rust Result error transport, including every error constructor. -/
def mapCoreError {T E F : Type} (f : E → F) :
    Aeneas.Std.core.result.Result T E → Aeneas.Std.core.result.Result T F
  | .Ok x => .Ok x
  | .Err e => .Err (f e)
theorem mapCoreError_inverse {T E F : Type} (f : E → F) (g : F → E)
    (inverse : ∀ e, g (f e) = e) (r : Aeneas.Std.core.result.Result T E) :
    mapCoreError g (mapCoreError f r) = r := by
  cases r with
  | Ok x => rfl
  | Err e => exact congrArg Aeneas.Std.core.result.Result.Err (inverse e)
theorem payment_result_transport {T : Type} (r : Aeneas.Std.core.result.Result T AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) :
    mapCoreError paymentFromShared (mapCoreError paymentToShared r) = r :=
  mapCoreError_inverse paymentToShared paymentFromShared payment_left_inverse r
theorem tree_result_transport {T : Type} (r : Aeneas.Std.core.result.Result T AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError) :
    mapCoreError treeFromShared (mapCoreError treeToShared r) = r :=
  mapCoreError_inverse treeToShared treeFromShared tree_left_inverse r

#print axioms payment_left_inverse
#print axioms payment_right_inverse
#print axioms payment_discriminant
#print axioms payment_injective
#print axioms tree_left_inverse
#print axioms tree_right_inverse
#print axioms tree_discriminant
#print axioms tree_injective
#print axioms verifier_retraction
#print axioms verifier_join_split
#print axioms verifier_split_join
#print axioms verifier_embedding_injective
#print axioms verifier_discriminant
#print axioms mapCoreError_inverse
#print axioms payment_result_transport
#print axioms tree_result_transport
end PV_BR_Transport
