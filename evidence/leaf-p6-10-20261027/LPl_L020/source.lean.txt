import Aeneas
set_option autoImplicit false
namespace LPl_C
/-- Appending a tail cannot change an already contained read window. -/
theorem window_append {A : Type} (xs tail : List A) (offset width : Nat)
    (contained : offset+width ≤ xs.length) :
    ((xs++tail).drop offset).take width = (xs.drop offset).take width := by
  rw [List.drop_append_of_le_length (by omega : offset ≤ xs.length)]
  exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)
#print axioms window_append
end LPl_C
