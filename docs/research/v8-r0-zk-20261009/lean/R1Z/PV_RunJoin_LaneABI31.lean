import R1Z.PV_RunJoin_LaneFuns31
import R1Z.PV_RunJoin_OuterExternal30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneABI31
open Aeneas Aeneas.Std Result
def fromOuter (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 :=
  ⟨x.nullifier_key,x.salt,x.value,
    ⟨x.pair_leaf.first_commitment,x.pair_leaf.second_occupied,
      x.pair_leaf.second_commitment,x.pair_leaf.second_occupancy_inverse⟩,
    x.selected_second,⟨x.membership.siblings,x.membership.index⟩⟩

def toOuter (x : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1 :=
  ⟨x.nullifier_key,x.salt,x.value,
    ⟨x.pair_leaf.first_commitment,x.pair_leaf.second_occupied,
      x.pair_leaf.second_commitment,x.pair_leaf.second_occupancy_inverse⟩,
    x.selected_second,⟨x.membership.siblings,x.membership.index⟩⟩

theorem roundtrip_outer (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : toOuter (fromOuter x) = x := by cases x; rfl
#print axioms roundtrip_outer

theorem roundtrip_lane (x : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) : fromOuter (toOuter x) = x := by cases x; rfl
#print axioms roundtrip_lane

def leafErrorToOuter : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PV31_PoolV1PairLeafErrorV1 → PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PV30_PoolV1PairLeafErrorV1
  | .NonCanonicalCommitment => .NonCanonicalCommitment
  | .NonCanonicalOccupancy => .NonCanonicalOccupancy
  | .NonCanonicalInverse => .NonCanonicalInverse
  | .OccupancyNotBoolean => .OccupancyNotBoolean
  | .SentinelInverseMismatch => .SentinelInverseMismatch
  | .EmptyInverseNonZero => .EmptyInverseNonZero
  | .EmptyCommitmentNonZero => .EmptyCommitmentNonZero
  | .OccupiedSentinelZero => .OccupiedSentinelZero
  | .SelectedSlotEmpty => .SelectedSlotEmpty

def leafErrorFromOuter : PV_RunJoin_Outer30.pool_v1.pair_tree_profile.PV30_PoolV1PairLeafErrorV1 → PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PV31_PoolV1PairLeafErrorV1
  | .NonCanonicalCommitment => .NonCanonicalCommitment
  | .NonCanonicalOccupancy => .NonCanonicalOccupancy
  | .NonCanonicalInverse => .NonCanonicalInverse
  | .OccupancyNotBoolean => .OccupancyNotBoolean
  | .SentinelInverseMismatch => .SentinelInverseMismatch
  | .EmptyInverseNonZero => .EmptyInverseNonZero
  | .EmptyCommitmentNonZero => .EmptyCommitmentNonZero
  | .OccupiedSentinelZero => .OccupiedSentinelZero
  | .SelectedSlotEmpty => .SelectedSlotEmpty

theorem error_roundtrip (e : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PV31_PoolV1PairLeafErrorV1) : leafErrorFromOuter (leafErrorToOuter e) = e := by cases e <;> rfl
#print axioms error_roundtrip

def errorToOuter : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PV31_PoolV1PairTraceErrorV1 → PV_RunJoin_Outer30.pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1
  | .Statement a => .Statement a
  | .PairLeaf a => .PairLeaf (leafErrorToOuter a)
  | .Tree a => .Tree a
  | .Shape  => .Shape 
  | .WrongVariant  => .WrongVariant 
  | .RuntimeBinding  => .RuntimeBinding 
  | .NullifierAlreadySpent  => .NullifierAlreadySpent 
  | .WitnessDigest  => .WitnessDigest 
  | .ValueOutOfRange  => .ValueOutOfRange 
  | .Conservation  => .Conservation 
  | .HashSchedule  => .HashSchedule 
  | .SelectedCommitmentMismatch  => .SelectedCommitmentMismatch 
  | .AnchorMismatch  => .AnchorMismatch 
  | .NullifierMismatch  => .NullifierMismatch 
  | .RecipientCommitmentMismatch  => .RecipientCommitmentMismatch 
  | .ChangeCommitmentMismatch  => .ChangeCommitmentMismatch 
  | .SnapshotBindingMismatch  => .SnapshotBindingMismatch 
  | .BlockMismatch a b c => .BlockMismatch a b c
  | .AuxiliaryMismatch a b => .AuxiliaryMismatch a b
  | .MetadataMismatch  => .MetadataMismatch 
  | .CopyLayout  => .CopyLayout 
  | .CopyImbalance  => .CopyImbalance 

variable [BuilderForestAdmissionPort.ExternalLinear]
def call (x : PV_RunJoin_Outer30.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1) :
    Result (core.result.Result (Array U32 8#usize)
      PV_RunJoin_Outer30.pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) := do
  let r ← PV_RunJoin_Lane31.lane_root (fromOuter x)
  ok (match r with | .Ok d => .Ok d | .Err e => .Err (errorToOuter e))

def native : PV_RunJoin_Outer30.LaneRoot := ⟨call⟩
end R1Z.PV_RunJoin_LaneABI31
