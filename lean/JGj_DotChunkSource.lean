import JGj_DotInput
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.JGj_DotChunkSource
open Aeneas Aeneas.Std Result
open FIq_Native
abbrev QM := FIv_NativeArithmetic.NQ
abbrev Raw4 := JGj_RawBounds.Raw
abbrev Range := core.ops.range.Range Usize

theorem source_loop_eq (iter : Range) (weights : Slice QM) (values : Slice U32) (raw : Raw4) :
    field.qm31_m31_dot_loop1_loop0 iter weights values raw = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok raw
      | some index =>
        let value ← Slice.index_usize values index
        let weight ← Slice.index_usize weights index
        let nextRaw ← AspisR1.JGj_DotInput.run raw weight value
        field.qm31_m31_dot_loop1_loop0 iter1 weights values nextRaw) := by
  rw [field.qm31_m31_dot_loop1_loop0.eq_def]
  simp only [AspisR1.JGj_DotInput.run,AspisR1.JGj_DotWordStep.step,
    bind_assoc_eq,lift,bind_tc_ok]
  all_goals rfl

#print axioms source_loop_eq
end AspisR1.JGj_DotChunkSource
