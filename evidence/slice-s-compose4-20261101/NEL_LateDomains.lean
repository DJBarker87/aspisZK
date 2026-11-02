import NEL_SliceCopyLaw
set_option autoImplicit false
noncomputable section
namespace NEL_LateDomains
open Aeneas Aeneas.Std Result

theorem child_window_lengths (out : Slice U8) (size : out.length = 1520) :
    ((out.val.drop 32).take 800).length = 800 ∧
    (out.val.drop 832).length = 688 := by
  change out.val.length = 1520 at size
  simp only [List.length_take,List.length_drop,size]
  decide

/-- Snapshot and afterstate windows partition the suffix; header bytes belong
neither to child, including when a child rejects. -/
theorem child_windows (k : Nat) :
    ((32 ≤ k ∧ k < 832) ∨ (832 ≤ k ∧ k < 1520)) ↔ 32 ≤ k ∧ k < 1520 := by omega

theorem header_frame (out src : Slice U8) (size : out.length = 1520)
    (source_size : src.length = 800) (k : Nat) (header : k < 32) :
    (out.setSlice! 32 src.val).val[k]? = out.val[k]? := by
  apply NEJ_ArrayFrame.list_frame
  · change 32 + src.length ≤ out.length
    omega
  · exact Or.inl header

#print axioms child_window_lengths
#print axioms child_windows
#print axioms header_frame
end NEL_LateDomains
