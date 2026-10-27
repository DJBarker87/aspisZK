import RPu_AspisR1_PoseidonPreparedComponentLoopExact

set_option autoImplicit false
namespace AspisR1PoseidonPreparedIndexLoopStep
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev RightArray := Array field.QM31 3#usize
abbrev Sums := Array (Array Std.U64 3#usize) 3#usize
abbrev Components := Array (Array field.M31 3#usize) 3#usize
abbrev Range := core.ops.range.Range Std.Usize
abbrev Loop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0
abbrev ComponentLoop := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0

theorem generated_index_loop_step
    (iter : Range) (left : PreparedArray) (right : RightArray) (sums : Sums) :
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0
      iter left right sums = (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok sums
      | some index => do
          let q ← Array.index_usize right index
          let rightSum ← field.CM31.add q.c0 q.c1
          let m ← field.M31.add q.c0.a q.c0.b
          let m1 ← field.M31.add q.c1.a q.c1.b
          let m2 ← field.M31.add rightSum.a rightSum.b
          let components : Components := Array.make 3#usize [
            Array.make 3#usize [q.c0.a, q.c0.b, m],
            Array.make 3#usize [q.c1.a, q.c1.b, m1],
            Array.make 3#usize [rightSum.a, rightSum.b, m2]]
          let sums1 ← ComponentLoop { start := 0#usize, «end» := 3#usize }
            left sums index components
          Loop iter1 left right sums1) := by
  rw [AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0.eq_def]
  rfl

#print axioms generated_index_loop_step
end AspisR1PoseidonPreparedIndexLoopStep
