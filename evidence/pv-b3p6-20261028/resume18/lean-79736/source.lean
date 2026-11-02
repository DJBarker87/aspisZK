import PV_B3P_CopyPrefix559227
namespace PV_B3P_PackCopyGuard559227
open Aeneas Aeneas.Std core.ops.range PV_B3P_ArrayHelpers559227 PV_B3P_CopyPrefix559227
set_option autoImplicit false
/-- qm31_pack_base4 borrows precisely values.len cells from a four-cell array.
The source assertion supplies the existing <=4 domain. This derives the nested
copy's panic exclusion, rather than assuming the copy returned successfully. -/
theorem pack4_copy_guard {α : Type} (dest : Array α 4#usize) (values : Slice α)
    (shape : values.val.length ≤ 4) :
    ∃ segment back,
      core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
        (RangeTo.mk values.len) dest.to_slice = .ok (segment,back) ∧
      copy_source segment values = .ok values := by
  apply copy_prefix_no_panic dest.to_slice values values.len
  · simpa only [Slice.len_val,Array.to_slice,Array.length_val] using shape
  · rfl

#print axioms pack4_copy_guard
end PV_B3P_PackCopyGuard559227
