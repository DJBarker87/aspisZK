import RPv_FJh_InternalLaneStep

/-! Symbolic execution of the final fifteen-lane update loop. Earlier lanes
are framed, and no concrete fifteen-iteration source term is normalized. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalLaneLoop
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalLaneStep
open AspisV8R17.RawReducer (P)

theorem loop_success_fuel (state : State) (full : Raw4) (iter : Range) (fuel : Nat)
    (hstart : 1 ≤ iter.start.val) (hend : iter.end.val ≤ 16)
    (hspan : iter.start.val + fuel = iter.end.val)
    (hstate : CanonicalState state) (hfull : RawBound full (16*AspisV8R17.RawReducer.P)) :
    ∃ out : State, state_only_poseidon.internal_linear_lazy_loop1 iter state full = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        if iter.start.val ≤ j.val ∧ j.val < iter.end.val then laneModel full state j
        else Decode (cell state j) := by
  induction fuel generalizing state iter with
  | zero =>
    have hstop : iter.start.val ≥ iter.end.val := by omega
    have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
    refine ⟨state,?_,hstate,?_⟩
    · rw [source_loop_eq,hnext]
      rfl
    · intro j
      have hnot : ¬ (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
      rw [if_neg hnot]
  | succ fuel ih =>
    have hlt : iter.start.val < iter.end.val := by omega
    have hidx : iter.start.val < 16 := by omega
    obtain ⟨iter1,hnext,hinc,hend1,_⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hlt
    have hstart1 : 1 ≤ iter1.start.val := by omega
    have hend' : iter1.end.val ≤ 16 := by rw [hend1]; exact hend
    have hspan' : iter1.start.val + fuel = iter1.end.val := by rw [hend1]; omega
    obtain ⟨value,hstep,hvalueCan,hstate1Can,hstepModel,hstepCells⟩ :=
      step_success state full iter.start hstart hidx hstate hfull
    let state1 := state.set iter.start value
    obtain ⟨out,hrec,houtCan,houtModel⟩ := ih state1 iter1 hstart1 hend' hspan' hstate1Can
    refine ⟨out,?_,houtCan,?_⟩
    · rw [source_loop_eq,hnext]
      change (do
        let nextState ← runStep state full iter.start
        state_only_poseidon.internal_linear_lazy_loop1 iter1 nextState full) = .ok out
      rw [hstep]
      change state_only_poseidon.internal_linear_lazy_loop1 iter1 state1 full = .ok out
      exact hrec
    · intro j
      have hv := houtModel j
      rw [hinc,hend1] at hv
      rw [hv]
      by_cases hj : j.val = iter.start.val
      · have hafter : ¬ (iter.start.val + 1 ≤ j.val ∧ j.val < iter.end.val) := by omega
        have hinside : iter.start.val ≤ j.val ∧ j.val < iter.end.val := by omega
        rw [if_neg hafter,if_pos hinside]
        have hcell := hstepCells j
        rw [if_pos hj] at hcell
        have hindex : (⟨iter.start.val,hidx⟩ : Fin 16) = j := Fin.ext hj.symm
        change Decode (cell state1 j) = laneModel full state ⟨iter.start.val,hidx⟩ at hcell
        exact hcell.trans (congrArg (laneModel full state) hindex)
      · have hcell : Decode (cell state1 j) = Decode (cell state j) := by
          have h := hstepCells j
          rw [if_neg hj] at h
          exact h
        unfold laneModel
        rw [hcell]
        have hrange : (iter.start.val + 1 ≤ j.val ∧ j.val < iter.end.val) ↔
            (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
        by_cases hin : iter.start.val ≤ j.val ∧ j.val < iter.end.val
        · rw [if_pos (hrange.mpr hin),if_pos hin]
        · have hn : ¬ (iter.start.val + 1 ≤ j.val ∧ j.val < iter.end.val) :=
            fun h => hin (hrange.mp h)
          rw [if_neg hn,if_neg hin]

theorem source_success (state : State) (full : Raw4)
    (hstate : CanonicalState state) (hfull : RawBound full (16*AspisV8R17.RawReducer.P)) :
    ∃ out : State,
      state_only_poseidon.internal_linear_lazy_loop1
        { start := 1#usize, «end» := poseidon2.POSEIDON2_WIDTH } state full = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        if j.val = 0 then Decode (cell state j) else laneModel full state j := by
  have hwidth : poseidon2.POSEIDON2_WIDTH = 16#usize := by unfold poseidon2.POSEIDON2_WIDTH; rfl
  obtain ⟨out,hrun,hcan,hmodel⟩ := loop_success_fuel state full
    { start := 1#usize, «end» := 16#usize } 15 (by decide) (by decide) (by decide) hstate hfull
  refine ⟨out,?_,hcan,?_⟩
  · rw [hwidth]
    exact hrun
  · intro j
    have h := hmodel j
    by_cases hz : j.val = 0
    · have hnot : ¬ ((1#usize).val ≤ j.val ∧ j.val < (16#usize).val) := by rw [hz]; decide
      rw [if_neg hnot] at h
      rw [if_pos hz]
      exact h
    · have hin : (1#usize).val ≤ j.val ∧ j.val < (16#usize).val := by
        have hj := j.isLt
        scalar_tac
      rw [if_pos hin] at h
      rw [if_neg hz]
      exact h

#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.FJh_InternalLaneLoop
