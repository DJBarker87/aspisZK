import PoolS2_MasterValidExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_Lanes
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterValidation
abbrev Lane := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev Lanes := Array Lane 8#usize
abbrev Sequences := Array U64 8#usize
/-- Pure interpretation of the original planner's fixed-order enumerate loop;
not a native iterator/source refinement certificate. All lane fields retained. -/
def check (master : Key) (expected : Nat) : List Lane → core.result.Result Unit ForestError
  | [] => .Ok ()
  | lane::rest => by
    classical
    exact if lane.master ≠ master then .Err .LaneMasterMismatch
    else if lane.lane_id.val ≠ expected then .Err .LaneOrderMismatch
    else if lane.tree.next_leaf_index > capacity then .Err .InvalidMasterState
    else check master (expected+1) rest

def sequences (lanes : Lanes) : Sequences :=
  ⟨lanes.val.map (fun lane => lane.tree.next_leaf_index),by simpa using lanes.property⟩

theorem sequence_list (lanes : Lanes) :
    (sequences lanes).val = lanes.val.map (fun lane => lane.tree.next_leaf_index) := rfl

theorem sequence_length (lanes : Lanes) : (sequences lanes).val.length = 8 := by
  exact (sequences lanes).property

#print axioms sequence_list
#print axioms sequence_length
end AspisR1.PoolS2_Lanes
end
