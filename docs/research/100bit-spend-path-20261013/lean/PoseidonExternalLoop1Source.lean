import PoseidonExternalLazySourceCut
import Aeneas.Std.WP

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.PoseidonExternalLoop1Source
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev State := Array field.QM31 16#usize
abbrev Sums := Array (Array Std.U64 4#usize) 4#usize
abbrev Closure1 := state_only_poseidon.external_linear_lazy.closure_1

/-- The exact one-index body of external loop 1, including the actual source
    `array_from_fn_copy` and `extension_from_raw_limbs` calls. -/
def runStep (state : State) (sums : Sums) (index : Usize) : Result (State × Usize) := do
  let q ← Array.index_usize state index
  let limbs ← state_only_poseidon.extension_limbs q
  let raw ← array_from_fn_copy 4#usize core.marker.CopyU64
    state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
    0#u64 (limbs,sums,index)
  let q1 ← state_only_poseidon.extension_from_raw_limbs raw
  let state1 ← Array.update state index q1
  let index1 ← index + 1#usize
  ok (state1,index1)

/-- Exact source equation for the generated partial-fixpoint traversal. -/
theorem generated_loop1_step (state : State) (sums : Sums) (index : Usize) :
    state_only_poseidon.external_linear_lazy_loop1 state sums index = (do
      if index < poseidon2.POSEIDON2_WIDTH then
        let (state1,index1) ← runStep state sums index
        state_only_poseidon.external_linear_lazy_loop1 state1 sums index1
      else ok state) := by
  rw [state_only_poseidon.external_linear_lazy_loop1.eq_def]
  simp only [runStep, bind_assoc_eq]
  rfl

#print axioms generated_loop1_step
end AspisR1.PoseidonExternalLoop1Source
