import PV_B3P_ArrayHelpers559227
namespace PV_B3P_CopyPrefix559227
open Aeneas Aeneas.Std core.ops.range PV_B3P_ArrayHelpers559227
set_option autoImplicit false
/-- The copy's source length is used to construct the destination prefix; this
is the control path in core::field::qm31_pack_base4, unlike host_terminal_field's
explicit index loop. No formatter semantics is used. -/
theorem prefix_copy_guard {α : Type} (dest : Slice α) (end_ : Usize)
    (guard : end_.val ≤ dest.val.length) :
    ∃ prefix back,
      core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
        (RangeTo.mk end_) dest = .ok (prefix,back) ∧ prefix.val.length = end_.val := by
  unfold core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
  have h : end_ ≤ dest.length := guard
  rw [if_pos h]
  refine ⟨_,_,rfl,?_⟩
  simp only [List.slice_length]
  omega

/-- A successful prefix borrow and the existing equal-length guard exclude the
copy mismatch branch, including its panic formatting. Complete source/caller
association and raw pointer copy semantics remain separate obligations. -/
theorem copy_prefix_no_panic {α : Type} (dest src : Slice α) (end_ : Usize)
    (guard : end_.val ≤ dest.val.length) (source_length : src.val.length = end_.val) :
    ∃ prefix back,
      core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
        (RangeTo.mk end_) dest = .ok (prefix,back) ∧
      copy_source prefix src = .ok src := by
  obtain ⟨prefix,back,borrow,length⟩ := prefix_copy_guard dest end_ guard
  refine ⟨prefix,back,borrow,copy_no_panic prefix src ?_⟩
  change prefix.val.length = src.val.length
  exact length.trans source_length.symm

#print axioms prefix_copy_guard
#print axioms copy_prefix_no_panic
end PV_B3P_CopyPrefix559227
