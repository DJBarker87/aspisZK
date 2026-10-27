import RPu_FIx_PathStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathLoopStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev loop := pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop

theorem value (r : core.ops.range.Range Usize) (selector : NQ) (a a1 : Array NQ 16#usize)
    (bit : NQ) (path : Array NQ 17#usize) :
    loop r selector a a1 bit path=(do
      let (o,r') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      match o with
      | none => ok path
      | some lane => do
        let next ← FIx_PathStep.run lane selector a a1 bit path
        loop r' selector a a1 bit next) := by
  rw [loop,pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop]
  simp only [FIx_PathStep.run,bind_assoc_eq]
  rfl
#print axioms value
end AspisR1.FIx_PathLoopStep
end
