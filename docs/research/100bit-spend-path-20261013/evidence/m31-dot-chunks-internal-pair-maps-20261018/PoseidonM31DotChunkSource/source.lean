import PoseidonM31DotInput
import OccupancyRangeTraversal

/-! One exact source equation for a scalar-weight dot chunk. The total U32
cast is normalized once, so the helper preserves all fallible read order. -/
set_option autoImplicit false
namespace AspisR1.PoseidonM31DotChunkSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (QM)
open AspisR1.PoseidonInternalClosureSums (Raw4)
abbrev Range := core.ops.range.Range Usize

theorem source_loop_eq (iter : Range) (weights : Slice QM) (values : Slice U32) (raw : Raw4) :
    field.qm31_m31_dot_loop1_loop0 iter weights values raw = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok raw
      | some index =>
        let value ← Slice.index_usize values index
        let weight ← Slice.index_usize weights index
        let nextRaw ← AspisR1.PoseidonM31DotInput.run raw weight value
        field.qm31_m31_dot_loop1_loop0 iter1 weights values nextRaw) := by
  rw [field.qm31_m31_dot_loop1_loop0.eq_def]
  simp only [AspisR1.PoseidonM31DotInput.run,AspisR1.PoseidonM31DotWordStep.step,
    bind_assoc_eq,lift,bind_tc_ok]
  all_goals rfl

#print axioms source_loop_eq
end AspisR1.PoseidonM31DotChunkSource
