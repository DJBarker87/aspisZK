import KMY_WindowComposition
set_option autoImplicit false
namespace KMY_WindowTranslation
open KMY_WindowComposition
theorem translate_window {α : Type} (src before : Nat → α)
    (origin pos size j : Nat) :
    window src before (origin+pos) size (origin+j) =
      window src (fun k => before (origin+k)) pos size j := by
  rw [window_spec, window_spec]
  have h : (origin+pos ≤ origin+j ∧ origin+j < origin+pos+size) ↔
      (pos ≤ j ∧ j < pos+size) := by omega
  have sub : origin+j-(origin+pos) = j-pos := by omega
  simp only [h, sub]

#print axioms translate_window
end KMY_WindowTranslation
