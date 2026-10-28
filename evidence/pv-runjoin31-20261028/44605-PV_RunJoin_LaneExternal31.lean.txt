import R1Z.PV_RunJoin_LaneTypes31
import R1Z.BuilderAdmissionStd
set_option autoImplicit false
noncomputable section
namespace PV_RunJoin_Lane31
open Aeneas Aeneas.Std Result
abbrev core.result.Result.map_err := @R1Z.BuilderAdmissionStd.mapErr
def leafToForest (x : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) :
    R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1 :=
  ⟨x.first_commitment,x.second_occupied,x.second_commitment,x.second_occupancy_inverse⟩

def leafErrorFromForest : R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 → aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1
  | .NonCanonicalCommitment => .NonCanonicalCommitment
  | .NonCanonicalOccupancy => .NonCanonicalOccupancy
  | .NonCanonicalInverse => .NonCanonicalInverse
  | .OccupancyNotBoolean => .OccupancyNotBoolean
  | .SentinelInverseMismatch => .SentinelInverseMismatch
  | .EmptyInverseNonZero => .EmptyInverseNonZero
  | .EmptyCommitmentNonZero => .EmptyCommitmentNonZero
  | .OccupiedSentinelZero => .OccupiedSentinelZero
  | .SelectedSlotEmpty => .SelectedSlotEmpty

variable [R1Z.BuilderForestAdmissionPort.ExternalLinear]
def aspis_statement.pool_v1.format.pool_v1_tree_parent :=
  R1Z.BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent
def aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest (x : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1) :
    Result (core.result.Result (Array U32 8#usize) aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1) := do
  let r ← R1Z.BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest (leafToForest x)
  ok (match r with | .Ok d => .Ok d | .Err e => .Err (leafErrorFromForest e))
end PV_RunJoin_Lane31
