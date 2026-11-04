import NEV_DotCarrier
set_option autoImplicit false
namespace AspisR1.NFC_ArrayFour
open Aeneas Aeneas.Std
/-- Carrier decomposition with only headline-selected imports. -/
theorem shape {α : Type} (array : Array α 4#usize) :
    ∃ a b c d, array=Array.make 4#usize [a,b,c,d] := by
  rcases array with ⟨xs,h⟩
  change xs.length=4 at h
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        cases xs with
        | nil => simp at h
        | cons d xs =>
          cases xs with
          | nil => exact ⟨a,b,c,d,rfl⟩
          | cons _ _ => simp at h
#print axioms shape
end AspisR1.NFC_ArrayFour
