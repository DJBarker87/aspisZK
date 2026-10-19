import BatchedWeightsPushOuterFlushV15
import AspisR1BatchedWeightsSetCellFactsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsPushOuterVecFrameV1
open BatchedWeightsPushOuterFlushV15
abbrev BW := AspisR1BatchedWeightsPushLoopAllPrefixV11.BW
abbrev Usize := UScalar UScalarTy.Usize

/-- The outer write in generated `push` is exactly a vector `set`; its
length and every nonselected row are preserved. The actual flush theorem
supplies `back_eq_set` after executing the generated `index_mut` branch. -/
theorem vec_set_preserves_length_and_other_rows
    (rows : alloc.vec.Vec (Array Std.U64 4#usize)) (index k : Usize)
    (hindex : index.val < rows.length) (hk : k.val < rows.length)
    (hne : k.val ≠ index.val) (row : Array Std.U64 4#usize) :
    (alloc.vec.Vec.set rows index row).length = rows.length ∧
    (alloc.vec.Vec.set rows index row).val[k.val]'(by simpa [List.length_set] using hk) =
      rows.val[k.val]'(by simpa using hk) := by
  constructor
  · simp [alloc.vec.Vec.set, List.length_set]
  · exact AspisR1BatchedWeightsSetCellFactsV1.vec_set_frame
      rows index k hindex hk (Ne.symm hne) row

#print axioms vec_set_preserves_length_and_other_rows
end BatchedWeightsPushOuterVecFrameV1
