import RPv_FJh_InternalLaneReassembly
import OccupancyRangeTraversal

/-! Exact body equation and checked update for the remaining internal-linear
lane loop. Source limb conversion is total and is reduced only once here. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalLaneStep
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalLaneReassembly (rawDecode shiftRun)
open AspisV8R17.RawReducer (P)
abbrev Range := core.ops.range.Range Usize

def diagonal (j : Fin 16) : Exact :=
  ((1 <<< R0P.poseidonInternalShifts (⟨j.val-1,by omega⟩ : Fin 15) : Nat) : Exact)
def laneModel (full : Raw4) (state : State) (j : Fin 16) : Exact :=
  rawDecode full + Decode (cell state j) * diagonal j

def runStep (state : State) (full : Raw4) (lane : Usize) : Result State := do
  let q ← Array.index_usize state lane
  let value ← shiftRun full q lane
  Array.update state lane value

theorem source_loop_eq (iter : Range) (state : State) (full : Raw4) :
    state_only_poseidon.internal_linear_lazy_loop1 iter state full = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok state
      | some lane =>
        let state1 ← runStep state full lane
        state_only_poseidon.internal_linear_lazy_loop1 iter1 state1 full) := by
  rw [state_only_poseidon.internal_linear_lazy_loop1.eq_def]
  simp only [runStep,shiftRun,AspisR1.FJh_InternalStateWords.wordVec_source,bind_assoc_eq,bind_tc_ok]
  all_goals rfl

theorem step_success (state : State) (full : Raw4) (lane : Usize)
    (hlane : 1 ≤ lane.val) (hend : lane.val < 16)
    (hs : CanonicalState state) (hf : RawBound full (16*AspisV8R17.RawReducer.P)) :
    ∃ value : QM, runStep state full lane = .ok (state.set lane value) ∧
      Canonical value ∧ CanonicalState (state.set lane value) ∧
      Decode value = laneModel full state ⟨lane.val,hend⟩ ∧
      ∀ j : Fin 16, Decode (cell (state.set lane value) j) =
        if j.val = lane.val then laneModel full state ⟨lane.val,hend⟩ else Decode (cell state j) := by
  let index : Fin 16 := ⟨lane.val,hend⟩
  let q := cell state index
  have hread : Array.index_usize state lane = .ok q :=
    AspisR1.FJh_InternalStateWords.state_source_read state lane hend
  obtain ⟨value,hshift,hcan,hmodel⟩ :=
    AspisR1.FJh_InternalLaneReassembly.shift_source full q lane hlane hend hf (hs index)
  have hupdate : Array.update state lane value = .ok (state.set lane value) := by
    obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists (Array.update_spec state lane value
      (by simpa [state.property] using hend))
    simpa only [hset] using hrun
  have hmodel' : Decode value = laneModel full state index := hmodel
  refine ⟨value,?_,hcan,set_canonical state lane value hs hcan,hmodel',?_⟩
  · simp only [runStep,hread,hshift,hupdate,bind_tc_ok]
  · intro j
    rw [cell_set]
    split
    · exact hmodel'
    · rfl

#print axioms source_loop_eq
#print axioms step_success
end AspisR1.FJh_InternalLaneStep
