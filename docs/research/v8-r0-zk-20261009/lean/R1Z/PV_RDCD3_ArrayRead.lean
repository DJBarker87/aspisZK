import Aeneas
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_ArrayRead
open Aeneas Aeneas.Std Result
-- Symbolic read theorem: no reduction of byte encodings is needed.
theorem read {α : Type} {n : Usize} (v : Array α n) (i : Usize)
    (bound : i.val < n.val) : ∃ x, Array.index_usize v i = ok x := by
  have h : i.val < v.val.length := by rw [v.property]; exact bound
  simp only [Array.index_usize, Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem h]
  exact ⟨_, rfl⟩
#print axioms read
end R1Z.PV_RDCD3_ArrayRead
