import RPv_FIx_PreweightedGroup
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedLoopStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
abbrev loop := @pool_v1.pair_forest_semantic_terminal.add_preweighted_loop

theorem value {N : Usize} (r : core.ops.range.RangeInclusive Usize)
    (packed : Array NQ 24#usize) (start : Usize) (values : Array NQ N) :
    loop r packed start values=(do
      let (o,r') ← core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next core.iter.range.StepUsize r
      match o with
      | none => ok packed
      | some group => do
        let next ← FIx_PreweightedGroup.run packed group start values
        loop r' next start values) := by
  rw [loop,pool_v1.pair_forest_semantic_terminal.add_preweighted_loop]
  simp only [FIx_PreweightedGroup.run,bind_assoc_eq]
  rfl
#print axioms value
end AspisR1.FIx_PreweightedLoopStep
end
