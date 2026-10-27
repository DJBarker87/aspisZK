import R1Z.PDict_OwnedTarget262
set_option autoImplicit false
namespace R1Z.PDict_CoordinatesEq262
open Aeneas Aeneas.Std PDict_OwnedPrefix262

/-- Coordinate equality yields complete array equality without evaluating a
finite enumeration or a concrete array construction. -/
theorem eq_of_coordinates {T : Type} (out target : Array T 1024#usize)
    (same : PDict_OwnedLoop262.Coordinates out target) : out = target := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [Array.length_eq, Array.length_eq]
  · intro n outBound targetBound
    have small : n < 1024 := by scalar_tac
    let position : Fin 1024 := ⟨n,small⟩
    have bound : (PDict_OwnedTarget262.index position).val < 1024 := by
      rw [PDict_OwnedTarget262.index_value]
      exact position.isLt
    have equality := same (PDict_OwnedTarget262.index position) bound
    simp only [coordinate, Array.getElem_Usize_eq, PDict_OwnedTarget262.index_value] at equality
    exact equality

#print axioms eq_of_coordinates
end R1Z.PDict_CoordinatesEq262
