import PoseidonQMFullRoundLoopSource

/-! Symbolic traversal of both actual nonlinear full-round loops. Fuel is a
proof measure for the source range, not an evaluated 16-cell recurrence. -/
set_option autoImplicit false
namespace AspisR1.PoseidonQMFullRoundLoopModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (State CanonicalState QM Exact Decode cell)
open AspisR1.PoseidonQMFullRoundCellStep
open AspisR1.PoseidonQMFullRoundLoopSource

def laneModel (state : State) (constants1 : State) (i : Fin 16) : Exact :=
  R0P.poseidonPow5 (Decode (cell state i) + Decode (cell constants1 i))

theorem loop_success_fuel (packed : Bool) (state : State) (constants1 : State)
    (iter : Range) (fuel : Nat)
    (hend : iter.end.val ≤ 16) (hspan : iter.start.val + fuel = iter.end.val)
    (hstate : CanonicalState state) (hconstants : CanonicalState constants1) :
    ∃ out : State, loop packed iter state constants1 = .ok out ∧ CanonicalState out ∧
      ∀ j : Fin 16, Decode (cell out j) =
        if iter.start.val ≤ j.val ∧ j.val < iter.end.val then laneModel state constants1 j
        else Decode (cell state j) := by
  induction fuel generalizing state iter with
  | zero =>
    have hstop : iter.start.val ≥ iter.end.val := by omega
    have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
    refine ⟨state,?_,hstate,?_⟩
    · rw [generated_loop_step]
      rw [hnext]
      change Result.ok state = Result.ok state
      rfl
    · intro j
      have hnot : ¬ (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
      rw [if_neg hnot]
  | succ fuel ih =>
    have hlt : iter.start.val < iter.end.val := by omega
    have hidx : iter.start.val < 16 := by omega
    obtain ⟨iter1,hnext,hinc,hend1,_⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hlt
    have hend' : iter1.end.val ≤ 16 := by rw [hend1]; exact hend
    have hspan' : iter1.start.val + fuel = iter1.end.val := by rw [hend1]; omega
    obtain ⟨value,hstep,hvalueCan,hstate1Can,hstepModel,hstepCells⟩ :=
      runStep_success state constants1 iter.start hidx hstate hconstants
    let state1 := state.set iter.start value
    obtain ⟨out,hrec,houtCan,houtModel⟩ := ih state1 iter1 hend' hspan' hstate1Can
    refine ⟨out,?_,houtCan,?_⟩
    · rw [generated_loop_step]
      rw [hnext]
      change (do
        let nextState ← runStep state constants1 iter.start
        loop packed iter1 nextState constants1) = .ok out
      rw [hstep]
      change loop packed iter1 state1 constants1 = .ok out
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
        change Decode (cell state1 j) = laneModel state constants1 ⟨iter.start.val,hidx⟩ at hcell
        exact hcell.trans (congrArg (laneModel state constants1) hindex)
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

/-- The exact width-16 source range computes every nonlinear round cell and
preserves canonicality, for either generated full-round variant. -/
theorem all_cells_success (packed : Bool) (state : State) (constants1 : State)
    (hstate : CanonicalState state) (hconstants : CanonicalState constants1) :
    ∃ out : State,
      loop packed { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state constants1 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) = laneModel state constants1 j := by
  have hwidth : poseidon2.POSEIDON2_WIDTH = 16#usize := by
    unfold poseidon2.POSEIDON2_WIDTH
    rfl
  obtain ⟨out,hrun,hcan,hmodel⟩ := loop_success_fuel packed state constants1
    { start := 0#usize, «end» := 16#usize } 16 (by decide) (by decide) hstate hconstants
  refine ⟨out,?_,hcan,?_⟩
  · rw [hwidth]
    exact hrun
  · intro j
    have h := hmodel j
    have hj : (0#usize).val ≤ j.val ∧ j.val < (16#usize).val := by
      have := j.isLt
      scalar_tac
    rw [if_pos hj] at h
    exact h

#print axioms loop_success_fuel
#print axioms all_cells_success
end AspisR1.PoseidonQMFullRoundLoopModel
