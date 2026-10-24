import Aeneas
set_option autoImplicit false
namespace AspisS6SliceFrame
/-- Replacing an in-place slice never changes its enclosing list length,
including clipped and out-of-range replacements. Proved from the definition. -/
theorem setSlice_length {T : Type} (xs : List T) (index : Nat) (ys : List T) :
    (xs.setSlice! index ys).length=xs.length := by
  simp only [List.setSlice!,List.length_append,List.length_take,List.length_drop]
  omega
#print axioms setSlice_length
end AspisS6SliceFrame
