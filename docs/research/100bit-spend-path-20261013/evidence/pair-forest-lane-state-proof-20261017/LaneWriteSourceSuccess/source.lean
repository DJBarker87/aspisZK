import LaneWriteOutputProjection

open Aeneas Aeneas.Std Result

set_option autoImplicit false
namespace AspisR1PairForestLaneWriteSourceCut.OutputProjection

private theorem bind_ok {α β : Type} {x : Result α} {f : α → Result β}
    {y : β} (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/-- A successful production source helper call preserves the lane identity
    fields and writes the verifier result's next cursor/root/frontier into the
    returned lane value. The cursor-successor check and inactive-frontier
    checks remain part of the exact extracted source function. -/
theorem next_pair_forest_lane_success_fields
    (lane : PoolV1PairForestLaneStateV1)
    (emptyRoots : Array (Array M31 8#usize) 21#usize)
    (result : PoolV1PairForestTerminalResultV1)
    (out : PoolV1PairForestLaneStateV1)
    (hsuccess : next_pair_forest_lane_v1 lane emptyRoots result =
      .ok (core.result.Result.Ok out)) :
    out.bump = lane.bump ∧ out.master = lane.master ∧
    out.lane_id = lane.lane_id ∧
    out.tree.next_leaf_index = result.verified_afterstate.next_pair_index ∧
    out.tree.root = result.verified_afterstate.next_root ∧
    out.tree.frontier = result.verified_afterstate.next_frontier := by
  rw [next_pair_forest_lane_v1.eq_def] at hsuccess
  obtain ⟨checked, hchecked, hrest⟩ := bind_ok hsuccess
  obtain ⟨mismatch, hmismatch, hrest⟩ := bind_ok hrest
  by_cases hm : mismatch = true
  · simp [hmismatch, hm] at hrest
  · simp only [hmismatch, hm, if_false] at hrest
    obtain ⟨slice, hslice, hrest⟩ := bind_ok hrest
    obtain ⟨iter, hiter, hrest⟩ := bind_ok hrest
    obtain ⟨enumerated, henumerated, hloop⟩ := bind_ok hrest
    have hfields := loop_success_copies_lane_and_afterstate
      result enumerated lane.bump lane.master lane.lane_id emptyRoots out hloop
    exact hfields

#print axioms next_pair_forest_lane_success_fields

end AspisR1PairForestLaneWriteSourceCut.OutputProjection
