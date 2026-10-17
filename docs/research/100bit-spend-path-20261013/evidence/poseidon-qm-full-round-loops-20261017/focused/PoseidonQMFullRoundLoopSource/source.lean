import PoseidonQMFullRoundCellStep
import OccupancyRangeTraversal

set_option autoImplicit false
namespace AspisR1.PoseidonQMFullRoundLoopSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (State CanonicalState QM Exact Decode cell)
open AspisR1.PoseidonQMFullRoundCellStep
abbrev Range := core.ops.range.Range Usize

def loop (packed : Bool) (iter : Range) (state constants1 : State) : Result State :=
  if packed then state_only_poseidon.full_round_packed_loop iter state constants1
  else state_only_poseidon.full_round_loop iter state constants1

theorem generated_loop_step (packed : Bool) (iter : Range) (state constants1 : State) :
    loop packed iter state constants1 = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok state
      | some lane =>
        let state1 ← runStep state constants1 lane
        loop packed iter1 state1 constants1) := by
  cases packed
  · simp only [loop,Bool.false_eq_true,ite_false]
    rw [state_only_poseidon.full_round_loop.eq_def]
    simp only [runStep,bind_assoc_eq]
    rfl
  · simp only [loop,ite_true]
    rw [state_only_poseidon.full_round_packed_loop.eq_def]
    simp only [runStep,bind_assoc_eq]
    rfl

#print axioms generated_loop_step
end AspisR1.PoseidonQMFullRoundLoopSource
