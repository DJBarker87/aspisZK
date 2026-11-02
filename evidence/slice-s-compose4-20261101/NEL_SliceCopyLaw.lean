import NEL_CopyArrayLaw
set_option autoImplicit false
noncomputable section
namespace NEL_SliceCopyLaw
open Aeneas Aeneas.Std Result

/-- Dynamic borrowed slices use the same value law, preserving their complete
original allocation outside the copied window. No independent poststate occurs. -/
theorem loop_binding (dst src : Slice U8) (start k : Nat)
    (fits : start + src.length ≤ dst.length) :
    KMX_CopyMeaning.loop (fun j => src.val[j-start]?) (fun j => dst.val[j]?)
      start src.length k = (dst.setSlice! start src.val).val[k]? := by
  rw [KMX_CopyMeaning.loop_spec]
  change (if start ≤ k ∧ k < start + src.val.length then src.val[k-start]? else dst.val[k]?) =
    (dst.val.setSlice! start src.val)[k]?
  by_cases hi : start ≤ k ∧ k < start + src.val.length
  · rw [if_pos hi]
    exact (NEL_CopyArrayLaw.list_inside dst.val src.val start k fits hi).symm
  · rw [if_neg hi]
    exact (NEJ_ArrayFrame.list_frame dst.val src.val start k fits (by omega)).symm

#print axioms loop_binding
end NEL_SliceCopyLaw
