import R1Z.PV_CBM_ValueClassification
namespace R1Z.PV_CBM_ValueFree
open PV_CBM_InventoryShape PV_CBM_ValueClassification
set_option autoImplicit false

theorem valueFree_iff (offset column : Nat) (ho : offset < 16) :
    free (1008+offset) column ↔ usedColumns offset ≤ column := by
  constructor
  · intro hf
    have hn : ¬ auxUsed (1008+offset) column := by
      rcases hf with h | h
      · exact False.elim (by have hp := h.1; unfold poseidon at hp; omega)
      · exact h.2
    by_contra hc
    have hlt : column < usedColumns offset := by omega
    exact hn ((valueAux_iff offset column ho).mpr hlt)
  · intro hc
    apply free_aux _ _ (by omega)
    intro haux
    have h := (valueAux_iff offset column ho).mp haux
    omega

#print axioms valueFree_iff
end R1Z.PV_CBM_ValueFree
