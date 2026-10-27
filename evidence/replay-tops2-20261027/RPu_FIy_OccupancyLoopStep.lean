import RPu_FIy_OccupancyStep
set_option autoImplicit false
namespace AspisR1.FIy_OccupancyLoopStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev loop := pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop

theorem value (r : core.ops.range.Range Usize) (a : Array NQ 16#usize)
    (m b : NQ) (o : Array NQ 12#usize) :
    loop r a m o b=(do
      let (opt,r') ← core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      match opt with
      | none=>ok o
      | some lane=>do
        let next ← FIy_OccupancyStep.run lane a m b o
        loop r' a m next b) := by
  rw [loop,pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop]
  simp only [FIy_OccupancyStep.run,bind_assoc_eq]
  rfl
#print axioms value
end AspisR1.FIy_OccupancyLoopStep
