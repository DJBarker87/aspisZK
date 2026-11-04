import NEV_ActualDotStep
import NEV_DotCell
set_option autoImplicit false
noncomputable section
namespace NEV_DotEight
open Aeneas Aeneas.Std Result AspisR1
/-- Eight fixed cells, in the literal order of the actual source. -/
def eight (coefficient : Array U32 8#usize) (scalar : U32) (sums : Array U64 8#usize) : Result (Array U64 8#usize) := do
 let s1 ← NEV_DotCell.cell coefficient scalar sums 0#usize
 let s2 ← NEV_DotCell.cell coefficient scalar s1 1#usize
 let s3 ← NEV_DotCell.cell coefficient scalar s2 2#usize
 let s4 ← NEV_DotCell.cell coefficient scalar s3 3#usize
 let s5 ← NEV_DotCell.cell coefficient scalar s4 4#usize
 let s6 ← NEV_DotCell.cell coefficient scalar s5 5#usize
 let s7 ← NEV_DotCell.cell coefficient scalar s6 6#usize
 let s8 ← NEV_DotCell.cell coefficient scalar s7 7#usize
 ok s8
/-- The SAME actual selected coefficient feeds every widened operand. This
factors monadic association only; it does not assume a successful read/cell. -/
theorem suffix (g : Array FIo_Native.aspis_core.field.wide_exact.WideExact 29#usize)
    (term : Usize) (scalar : U32) (sums : Array U64 8#usize) :
    NEV_ActualDotStep.update g term scalar sums=
      (do let value ← Array.index_usize g term
          let coefficient ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value
          eight coefficient scalar sums) := by
  simp only [NEV_ActualDotStep.update,eight,NEV_DotCell.cell,bind_assoc_eq,bind_tc_ok,lift]
#print axioms suffix
end NEV_DotEight
end
