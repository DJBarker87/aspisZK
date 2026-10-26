import PoolS2_LaneFacts
import PoolV_ChronologyAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PlannerModel
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation PoolS2_Lanes
abbrev Root := Array U32 8#usize
abbrev Checkpoint := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
structure Plan where
  next_master : Master
  checkpoint : Checkpoint

def nextMaster (m : Master) (lanes : Lanes) (next : U64) : Master :=
  {m with
    has_checkpoint := true
    next_checkpoint_sequence := next
    last_checkpoint_lane_sequences := sequences lanes}

def assembled (m : Master) (lanes : Lanes) (root : Root) (bump : U8) (next : U64) : Plan :=
  {next_master := nextMaster m lanes next
   checkpoint := {
     bump := bump
     master := m.identity.pool
     deployment_domain := m.identity.deployment_domain
     checkpoint_sequence := m.next_checkpoint_sequence
     global_root := root
     lane_sequences := sequences lanes}}

/-- Full VALUE/ERROR normal-form reference of the original pure planner.
Native iterator/struct decomposition is STILL OPEN. No independent successful
master, lane, chronology or post-validation call is an argument. -/
def run (m : Master) (lanes : Lanes) (root : Root) (bump : U8) :
    Result (core.result.Result Plan ForestError) := by
  classical
  exact do
    let validated ← PoolS2_MasterValidation.run m
    match validated with
    | .Err e => ok (.Err e)
    | .Ok _ =>
      if m.initialized_lane_mask ≠ 255#u8 then ok (.Err .InvalidMasterState)
      else if root.val.any (fun limb => limb.val ≥ 2147483647) then ok (.Err .NonCanonicalDigest)
      else match check m.identity.pool 0 lanes.val with
      | .Err e => ok (.Err e)
      | .Ok _ =>
        let pair ← PoolV_Chronology.chronology (Array.to_slice (sequences lanes))
          (Array.to_slice m.last_checkpoint_lane_sequences) m.has_checkpoint m.next_checkpoint_sequence
        if pair.1 = 1#u8 then ok (.Err .LaneSequenceDecreased)
        else if pair.1 = 2#u8 then ok (.Err .DuplicateCheckpoint)
        else if pair.1 = 3#u8 then ok (.Err .CheckpointSequenceOverflow)
        else
          let plan := assembled m lanes root bump pair.2
          let post ← PoolS2_MasterValidation.run plan.next_master
          match post with
          | .Err e => ok (.Err e)
          | .Ok _ => ok (.Ok plan)

#print axioms run
end AspisR1.PoolS2_PlannerModel
end
