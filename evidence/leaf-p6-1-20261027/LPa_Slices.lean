import XRk_DecodeModels
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace LPa.Slices

def segment (bs : Slice U8) (lo hi : Nat) : Slice U8 :=
  ⟨(bs.val.drop lo).take (hi-lo),by
    exact Nat.le_trans (List.length_take_le' _ _) (Nat.le_trans (by simp) bs.property)⟩

theorem range_success (bs : Slice U8) (lo hi : Nat) (valid : lo ≤ hi ∧ hi ≤ bs.val.length) :
    XRk_sliceRange bs lo hi = ok (segment bs lo hi) := by
  simp only [XRk_sliceRange, if_pos valid]
  rfl

theorem segment_length (bs : Slice U8) (lo hi : Nat) (valid : lo ≤ hi ∧ hi ≤ bs.val.length) :
    (segment bs lo hi).val.length = hi-lo := by
  simp only [segment, List.length_take, List.length_drop]
  omega
#print axioms range_success
#print axioms segment_length
end LPa.Slices
