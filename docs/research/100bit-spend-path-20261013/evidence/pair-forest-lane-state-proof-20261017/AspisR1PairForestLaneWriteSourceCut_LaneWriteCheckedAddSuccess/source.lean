import LaneWriteSourceSuccess

open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace AspisR1PairForestLaneWriteSourceCut.OutputProjection

private theorem bind_ok {α β : Type} {x : Result α} {f : α → Result β}
    {y : β} (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

theorem next_pair_forest_lane_success_checked_add
    (lane : PoolV1PairForestLaneStateV1)
    (emptyRoots : Array (Array M31 8#usize) 21#usize)
    (result : PoolV1PairForestTerminalResultV1)
    (out : PoolV1PairForestLaneStateV1)
    (hsuccess : next_pair_forest_lane_v1 lane emptyRoots result =
      .ok (core.result.Result.Ok out)) :
    U64.checked_add lane.tree.next_leaf_index 1#u64 =
      some result.verified_afterstate.next_pair_index := by
  rw [next_pair_forest_lane_v1.eq_def] at hsuccess
  obtain ⟨checked, hchecked, hrest⟩ := bind_ok hsuccess
  obtain ⟨mismatch, hmismatch, hrest⟩ := bind_ok hrest
  have hm : mismatch = false := by
    by_cases ht : mismatch = true
    · simp [ht] at hrest
    · cases mismatch <;> simp_all
  have hchecked' : U64.checked_add lane.tree.next_leaf_index 1#u64 = checked := by
    simpa [Aeneas.Std.lift] using hchecked
  have hopt : checked = some result.verified_afterstate.next_pair_index := by
    cases checked with
    | none =>
      simp [core.cmp.PartialEq.ne.trait_default,
        core.cmp.PartialEq.ne.default,
        core.option.Option.Insts.CoreCmpPartialEqOption.eq] at hmismatch
      simp_all
    | some got =>
      simp [core.cmp.PartialEq.ne.trait_default,
        core.cmp.PartialEq.ne.default,
        core.option.Option.Insts.CoreCmpPartialEqOption.eq] at hmismatch
      simpa [hm] using hmismatch
  rw [hchecked', hopt]

#print axioms next_pair_forest_lane_success_checked_add
end AspisR1PairForestLaneWriteSourceCut.OutputProjection
