import PCD_LaneRef.Funs
set_option autoImplicit false
namespace PCD_LaneValue
open Aeneas Aeneas.Std PCD_LaneRef

def candidate (lane : Lane) (after : After) : Lane :=
  { lane with
      tree := {
        next_leaf_index := after.next_pair_index
        root := after.next_root
        frontier := after.next_frontier } }

theorem finish_exact (lane : Lane) (after : After) :
    finish_lane lane after = .ok (candidate lane after) := rfl

theorem metadata_frame (lane : Lane) (after : After) :
    (candidate lane after).master = lane.master ∧
    (candidate lane after).bump = lane.bump ∧
    (candidate lane after).lane_id = lane.lane_id := ⟨rfl, rfl, rfl⟩

theorem tree_exact (lane : Lane) (after : After) :
    (candidate lane after).tree.next_leaf_index = after.next_pair_index ∧
    (candidate lane after).tree.root = after.next_root ∧
    (candidate lane after).tree.frontier = after.next_frontier := ⟨rfl, rfl, rfl⟩

#print axioms finish_exact
#print axioms metadata_frame
#print axioms tree_exact
end PCD_LaneValue
