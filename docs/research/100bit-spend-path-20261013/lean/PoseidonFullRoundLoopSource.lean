import AspisR1.PoseidonFullRoundCellStep
import OccupancyRangeTraversal

/-! One exact body equation shared by the two generated nonlinear loops.
Only their recursive names differ; no iterations are unfolded here. -/
set_option autoImplicit false
namespace AspisR1.PoseidonFullRoundLoopSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
abbrev Range := core.ops.range.Range Usize

def loop (packed : Bool) (iter : Range) (state : State) (constants1 : Constants) : Result State :=
  if packed then state_only_poseidon.full_round_m31_constants_packed_loop iter state constants1
  else state_only_poseidon.full_round_m31_constants_loop iter state constants1


/-- Moving the final continuation inside the checked mutable-index tuple
match is symbolic bind congruence; the source arithmetic is kept opaque. -/
theorem runStep_bind {α : Type} (state : State) (constants1 : Constants) (lane : Usize)
    (next : State → Result α) :
    (do let state1 ← runStep state constants1 lane; next state1) = (do
      let q ← Array.index_usize state lane
      let c ← Array.index_usize constants1 lane
      let m ← field.M31.add q.c0.a c
      let (q1,back) ← Array.index_mut_usize state lane
      let state1 := back (AspisR1.PoseidonM31ConstantPow5.updated q1 m)
      let q2 ← Array.index_usize state1 lane
      let q3 ← state_only_poseidon.pow5 q2
      let state2 ← Array.update state1 lane q3
      next state2) := by
  simp only [runStep,bind_assoc_eq]
  congr 1
  funext q
  congr 1
  funext c
  congr 1
  funext m
  congr 1
  funext pair
  rcases pair with ⟨q1,back⟩
  change (do
    let state1 ← (do
      let q2 ← Array.index_usize (back (AspisR1.PoseidonM31ConstantPow5.updated q1 m)) lane
      let q3 ← state_only_poseidon.pow5 q2
      Array.update (back (AspisR1.PoseidonM31ConstantPow5.updated q1 m)) lane q3)
    next state1) = (do
      let q2 ← Array.index_usize (back (AspisR1.PoseidonM31ConstantPow5.updated q1 m)) lane
      let q3 ← state_only_poseidon.pow5 q2
      let state2 ← Array.update (back (AspisR1.PoseidonM31ConstantPow5.updated q1 m)) lane q3
      next state2)
  simp only [bind_assoc_eq]


theorem generated_loop_step (packed : Bool) (iter : Range) (state : State) (constants1 : Constants) :
    loop packed iter state constants1 = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok state
      | some lane =>
        let state1 ← runStep state constants1 lane
        loop packed iter1 state1 constants1) := by
  cases packed
  · simp only [loop,Bool.false_eq_true,ite_false]
    rw [state_only_poseidon.full_round_m31_constants_loop.eq_def]
    simp only [runStep_bind,AspisR1.PoseidonM31ConstantPow5.updated]
    rfl
  · simp only [loop,ite_true]
    rw [state_only_poseidon.full_round_m31_constants_packed_loop.eq_def]
    simp only [runStep_bind,AspisR1.PoseidonM31ConstantPow5.updated]
    rfl

#print axioms runStep_bind

#print axioms generated_loop_step
end AspisR1.PoseidonFullRoundLoopSource
