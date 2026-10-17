import AspisR1PairForestLaneWriteSourceCut.LaneWriteCheckedAddSuccess

open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace AspisR1PairForestLaneWriteSourceCut.OutputProjection

theorem next_pair_forest_lane_success_checked_add_val
    (lane : PoolV1PairForestLaneStateV1)
    (emptyRoots : Array (Array M31 8#usize) 21#usize)
    (result : PoolV1PairForestTerminalResultV1)
    (out : PoolV1PairForestLaneStateV1)
    (hsuccess : next_pair_forest_lane_v1 lane emptyRoots result =
      .ok (core.result.Result.Ok out)) :
    result.verified_afterstate.next_pair_index.val =
      lane.tree.next_leaf_index.val + 1 := by
  have hchecked := next_pair_forest_lane_success_checked_add lane emptyRoots result out hsuccess
  have hspec := Aeneas.Std.U64.checked_add_bv_spec
    lane.tree.next_leaf_index (1#u64)
  rw [hchecked] at hspec
  simpa using hspec.2.1

#print axioms next_pair_forest_lane_success_checked_add_val
end AspisR1PairForestLaneWriteSourceCut.OutputProjection
