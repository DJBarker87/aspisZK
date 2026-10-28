import R1Z.PV_RunJoin_OuterTypes30
import R1Z.BuilderAdmissionCommon
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OuterABI30
open Aeneas Aeneas.Std Result
open PV_RunJoin_Outer30

def membershipToForest (x : PV_RunJoin_Outer30.pool_v1.payment_relation.PoolV1MembershipWitnessV1) : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1MembershipWitnessV1 where
  siblings := x.siblings
  index := x.index

def membershipFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1MembershipWitnessV1) : PV_RunJoin_Outer30.pool_v1.payment_relation.PoolV1MembershipWitnessV1 where
  siblings := x.siblings
  index := x.index

def membershipToAdmission (x : PV_RunJoin_Outer30.pool_v1.payment_relation.PoolV1MembershipWitnessV1) : AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1MembershipWitnessV1 where
  siblings := x.siblings
  index := x.index

theorem membership_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1MembershipWitnessV1) : membershipToForest (membershipFromForest x) = x := by cases x; rfl
#print axioms membership_roundtrip

def leafToForest (x : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 where
  first_commitment := x.first_commitment
  second_occupied := x.second_occupied
  second_commitment := x.second_commitment
  second_occupancy_inverse := x.second_occupancy_inverse

def leafFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 where
  first_commitment := x.first_commitment
  second_occupied := x.second_occupied
  second_commitment := x.second_commitment
  second_occupancy_inverse := x.second_occupancy_inverse

def leafToAdmission (x : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) : AspisBuilderAdmissionSource.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 where
  first_commitment := x.first_commitment
  second_occupied := x.second_occupied
  second_commitment := x.second_commitment
  second_occupancy_inverse := x.second_occupancy_inverse

theorem leaf_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) : leafToForest (leafFromForest x) = x := by cases x; rfl
#print axioms leaf_roundtrip

def pairToForest (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : R1Z.BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 where
  nullifier_key := x.nullifier_key
  salt := x.salt
  value := x.value
  pair_leaf := leafToForest x.pair_leaf
  selected_second := x.selected_second
  membership := membershipToForest x.membership

def pairFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 where
  nullifier_key := x.nullifier_key
  salt := x.salt
  value := x.value
  pair_leaf := leafFromForest x.pair_leaf
  selected_second := x.selected_second
  membership := membershipFromForest x.membership

def pairToAdmission (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : AspisBuilderAdmissionSource.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 where
  nullifier_key := x.nullifier_key
  salt := x.salt
  value := x.value
  pair_leaf := leafToAdmission x.pair_leaf
  selected_second := x.selected_second
  membership := membershipToAdmission x.membership

theorem pair_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : pairToForest (pairFromForest x) = x := by cases x; rfl
#print axioms pair_roundtrip

def inputToForest (x : PV_RunJoin_Outer30.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1 where
  pair := pairToForest x.pair
  super_root_siblings := x.super_root_siblings
  super_root_directions := x.super_root_directions

def inputFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) : PV_RunJoin_Outer30.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1 where
  pair := pairFromForest x.pair
  super_root_siblings := x.super_root_siblings
  super_root_directions := x.super_root_directions

theorem input_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1) : inputToForest (inputFromForest x) = x := by cases x; rfl
#print axioms input_roundtrip

def noteToForest (x : PV_RunJoin_Outer30.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1) : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1 where
  owner_key := x.owner_key
  salt := x.salt
  value := x.value

def noteFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1) : PV_RunJoin_Outer30.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1 where
  owner_key := x.owner_key
  salt := x.salt
  value := x.value

theorem note_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1) : noteToForest (noteFromForest x) = x := by cases x; rfl
#print axioms note_roundtrip

def snapshotToForest (x : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  sequence := x.sequence
  next_pair_index := x.next_pair_index
  current_root := x.current_root
  frontier := x.frontier

def snapshotFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  sequence := x.sequence
  next_pair_index := x.next_pair_index
  current_root := x.current_root
  frontier := x.frontier

theorem snapshot_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : snapshotToForest (snapshotFromForest x) = x := by cases x; rfl
#print axioms snapshot_roundtrip

def publicToForest (x : PV_RunJoin_Outer30.pool_v1.pair_forest_trace.ForestPublic) : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.ForestPublic where
  anchor := x.anchor
  nullifier := x.nullifier
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment
  asset := x.asset

def publicFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.ForestPublic) : PV_RunJoin_Outer30.pool_v1.pair_forest_trace.ForestPublic where
  anchor := x.anchor
  nullifier := x.nullifier
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment
  asset := x.asset

theorem public_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.ForestPublic) : publicToForest (publicFromForest x) = x := by cases x; rfl
#print axioms public_roundtrip

def compilationToForest (x : PV_RunJoin_Outer30.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 where
  trace := x.trace
  semantic_c1 := x.semantic_c1
  public_statement := x.public_statement

def compilationFromForest (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : PV_RunJoin_Outer30.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 where
  trace := x.trace
  semantic_c1 := x.semantic_c1
  public_statement := x.public_statement

theorem compilation_roundtrip (x : R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : compilationToForest (compilationFromForest x) = x := by cases x; rfl
#print axioms compilation_roundtrip

def contextToAdmission (x : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentRelationContextV1 where
  runtime_binding := ⟨x.runtime_binding.pool,x.runtime_binding.deployment_domain,
    x.runtime_binding.anchor_sequence,x.runtime_binding.anchor_root,x.runtime_binding.asset_id⟩
  spent_nullifiers := x.spent_nullifiers

def formatFromForest : R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → PV_RunJoin_Outer30.pool_v1.payment_relation.PV30_PoolV1PaymentStatementFormatError
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

def leafErrorFromForest : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 → PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PV30_PoolV1PairLeafErrorV1
  | .NonCanonicalCommitment => .NonCanonicalCommitment
  | .NonCanonicalOccupancy => .NonCanonicalOccupancy
  | .NonCanonicalInverse => .NonCanonicalInverse
  | .OccupancyNotBoolean => .OccupancyNotBoolean
  | .SentinelInverseMismatch => .SentinelInverseMismatch
  | .EmptyInverseNonZero => .EmptyInverseNonZero
  | .EmptyCommitmentNonZero => .EmptyCommitmentNonZero
  | .OccupiedSentinelZero => .OccupiedSentinelZero
  | .SelectedSlotEmpty => .SelectedSlotEmpty

def treeErrorFromForest : R1Z.BuilderForestAdmissionPort.pool_v1.incremental_merkle.PoolV1TreeError → R1Z.BuilderForestAdmissionPort.pool_v1.incremental_merkle.PoolV1TreeError
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

def errorFromForest : R1Z.BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTraceErrorV1 → PV_RunJoin_Outer30.pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1
  | .Statement v0 => .Statement (formatFromForest v0)
  | .PairLeaf v0 => .PairLeaf (leafErrorFromForest v0)
  | .Tree v0 => .Tree (treeErrorFromForest v0)
  | .Shape => .Shape
  | .WrongVariant => .WrongVariant
  | .RuntimeBinding => .RuntimeBinding
  | .NullifierAlreadySpent => .NullifierAlreadySpent
  | .WitnessDigest => .WitnessDigest
  | .ValueOutOfRange => .ValueOutOfRange
  | .Conservation => .Conservation
  | .HashSchedule => .HashSchedule
  | .SelectedCommitmentMismatch => .SelectedCommitmentMismatch
  | .AnchorMismatch => .AnchorMismatch
  | .NullifierMismatch => .NullifierMismatch
  | .RecipientCommitmentMismatch => .RecipientCommitmentMismatch
  | .ChangeCommitmentMismatch => .ChangeCommitmentMismatch
  | .SnapshotBindingMismatch => .SnapshotBindingMismatch
  | .BlockMismatch v0 v1 v2 => .BlockMismatch (v0) (v1) (v2)
  | .AuxiliaryMismatch v0 v1 => .AuxiliaryMismatch (v0) (v1)
  | .MetadataMismatch => .MetadataMismatch
  | .CopyLayout => .CopyLayout
  | .CopyImbalance => .CopyImbalance

def formatFromAdmission : AspisBuilderAdmissionSource.pool_v1.payment_relation.PoolV1PaymentStatementFormatError → PV_RunJoin_Outer30.pool_v1.payment_relation.PV30_PoolV1PaymentStatementFormatError
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

def leafErrorFromAdmission : AspisBuilderAdmissionSource.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 → PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PV30_PoolV1PairLeafErrorV1
  | .NonCanonicalCommitment => .NonCanonicalCommitment
  | .NonCanonicalOccupancy => .NonCanonicalOccupancy
  | .NonCanonicalInverse => .NonCanonicalInverse
  | .OccupancyNotBoolean => .OccupancyNotBoolean
  | .SentinelInverseMismatch => .SentinelInverseMismatch
  | .EmptyInverseNonZero => .EmptyInverseNonZero
  | .EmptyCommitmentNonZero => .EmptyCommitmentNonZero
  | .OccupiedSentinelZero => .OccupiedSentinelZero
  | .SelectedSlotEmpty => .SelectedSlotEmpty

def treeErrorFromAdmission : AspisBuilderAdmissionSource.pool_v1.incremental_merkle.PoolV1TreeError → R1Z.BuilderForestAdmissionPort.pool_v1.incremental_merkle.PoolV1TreeError
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

def errorFromAdmission : AspisBuilderAdmissionSource.pool_v1.pair_trace.PoolV1PairTraceErrorV1 → PV_RunJoin_Outer30.pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1
  | .Statement v0 => .Statement (formatFromAdmission v0)
  | .PairLeaf v0 => .PairLeaf (leafErrorFromAdmission v0)
  | .Tree v0 => .Tree (treeErrorFromAdmission v0)
  | .Shape => .Shape
  | .WrongVariant => .WrongVariant
  | .RuntimeBinding => .RuntimeBinding
  | .NullifierAlreadySpent => .NullifierAlreadySpent
  | .WitnessDigest => .WitnessDigest
  | .ValueOutOfRange => .ValueOutOfRange
  | .Conservation => .Conservation
  | .HashSchedule => .HashSchedule
  | .SelectedCommitmentMismatch => .SelectedCommitmentMismatch
  | .AnchorMismatch => .AnchorMismatch
  | .NullifierMismatch => .NullifierMismatch
  | .RecipientCommitmentMismatch => .RecipientCommitmentMismatch
  | .ChangeCommitmentMismatch => .ChangeCommitmentMismatch
  | .SnapshotBindingMismatch => .SnapshotBindingMismatch
  | .BlockMismatch v0 v1 v2 => .BlockMismatch (v0) (v1) (v2)
  | .AuxiliaryMismatch v0 v1 => .AuxiliaryMismatch (v0) (v1)
  | .MetadataMismatch => .MetadataMismatch
  | .CopyLayout => .CopyLayout
  | .CopyImbalance => .CopyImbalance

def formatToForest : PV_RunJoin_Outer30.pool_v1.payment_relation.PV30_PoolV1PaymentStatementFormatError → R1Z.BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1PaymentStatementFormatError
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

def leafErrorToForest : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PV30_PoolV1PairLeafErrorV1 → R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1
  | .NonCanonicalCommitment => .NonCanonicalCommitment
  | .NonCanonicalOccupancy => .NonCanonicalOccupancy
  | .NonCanonicalInverse => .NonCanonicalInverse
  | .OccupancyNotBoolean => .OccupancyNotBoolean
  | .SentinelInverseMismatch => .SentinelInverseMismatch
  | .EmptyInverseNonZero => .EmptyInverseNonZero
  | .EmptyCommitmentNonZero => .EmptyCommitmentNonZero
  | .OccupiedSentinelZero => .OccupiedSentinelZero
  | .SelectedSlotEmpty => .SelectedSlotEmpty

def errorToForest : PV_RunJoin_Outer30.pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1 → R1Z.BuilderForestAdmissionPort.pool_v1.pair_trace.PoolV1PairTraceErrorV1
  | .Statement v0 => .Statement (formatToForest v0)
  | .PairLeaf v0 => .PairLeaf (leafErrorToForest v0)
  | .Tree v0 => .Tree (v0)
  | .Shape => .Shape
  | .WrongVariant => .WrongVariant
  | .RuntimeBinding => .RuntimeBinding
  | .NullifierAlreadySpent => .NullifierAlreadySpent
  | .WitnessDigest => .WitnessDigest
  | .ValueOutOfRange => .ValueOutOfRange
  | .Conservation => .Conservation
  | .HashSchedule => .HashSchedule
  | .SelectedCommitmentMismatch => .SelectedCommitmentMismatch
  | .AnchorMismatch => .AnchorMismatch
  | .NullifierMismatch => .NullifierMismatch
  | .RecipientCommitmentMismatch => .RecipientCommitmentMismatch
  | .ChangeCommitmentMismatch => .ChangeCommitmentMismatch
  | .SnapshotBindingMismatch => .SnapshotBindingMismatch
  | .BlockMismatch v0 v1 v2 => .BlockMismatch (v0) (v1) (v2)
  | .AuxiliaryMismatch v0 v1 => .AuxiliaryMismatch (v0) (v1)
  | .MetadataMismatch => .MetadataMismatch
  | .CopyLayout => .CopyLayout
  | .CopyImbalance => .CopyImbalance

end R1Z.PV_RunJoin_OuterABI30
