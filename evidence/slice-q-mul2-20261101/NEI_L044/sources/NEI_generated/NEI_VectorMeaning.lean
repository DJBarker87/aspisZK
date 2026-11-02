import NEG_PushAssociation
set_option autoImplicit false
namespace NEI_VectorMeaning
open Aeneas Aeneas.Std Result
abbrev Row := Array U64 4#usize
/-- Standard-library read and backward Vec restoration on the SAME full carrier.
Native physical interpretation is the separate vector_row_context check. -/
theorem borrow (v : alloc.vec.Vec Row) (index : Usize)
 (bound : index.val < v.val.length) :
 ∃ row back,
 alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Row) v index= ok (row,back) ∧
 row=v.val[index.val] ∧ ∀ replacement,back replacement=v.set index replacement := by
 obtain ⟨⟨row,back⟩,run,value,(fun replacement => congrFun restore replacement)⟩ :=
  WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec v index bound)
 refine ⟨row,back,?_,value,(fun replacement => congrFun restore replacement)⟩
 rw [alloc.vec.Vec.index_mut_slice_index]
 exact run
#print axioms borrow
end NEI_VectorMeaning
