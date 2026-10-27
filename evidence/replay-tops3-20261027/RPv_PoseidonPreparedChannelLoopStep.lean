import RPv_PoseidonPreparedSum3Source
import RPv_PoseidonPreparedChannelGeneratedStep
import OccupancyRangeTraversal

set_option autoImplicit false
namespace AspisR1PoseidonPreparedChannelLoopStep
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev Sums := Array (Array Std.U64 3#usize) 3#usize

/-- One `some channel` body of the exact 04fc innermost qmsum3 loop. -/
def runStep
    (left : Array field.PreparedQm31Multiplier 3#usize)
    (sums : Sums) (index : Std.Usize)
    (right_components : Array (Array field.M31 3#usize) 3#usize)
    (component channel : Std.Usize) : Result Sums := do
  let pqm ← Array.index_usize left index
  let a ← Array.index_usize pqm.components component
  let m ← Array.index_usize a channel
  let i ← lift (UScalar.cast .U64 m)
  let a1 ← Array.index_usize right_components component
  let m1 ← Array.index_usize a1 channel
  let i1 ← lift (UScalar.cast .U64 m1)
  let i2 ← i * i1
  let a2 ← Array.index_usize sums component
  let i3 ← Array.index_usize a2 channel
  let i4 ← i3 + i2
  let (a3, index_mut_back) ← Array.index_mut_usize sums component
  let a4 ← Array.update a3 channel i4
  let a5 := index_mut_back a4
  .ok a5

theorem generated_loop_step
    (iter : core.ops.range.Range Std.Usize)
    (left : Array field.PreparedQm31Multiplier 3#usize)
    (sums : Sums) (index : Std.Usize)
    (right_components : Array (Array field.M31 3#usize) 3#usize)
    (component : Std.Usize) :
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
      iter left sums index right_components component = (do
        let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
        match o with
        | none => .ok sums
        | some channel => do
            let sums1 ← runStep left sums index right_components component channel
            AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
              iter1 left sums1 index right_components component) := by
  rw [AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def]
  simp only [runStep, bind_assoc_eq]
  rfl

#print axioms generated_loop_step
end AspisR1PoseidonPreparedChannelLoopStep
