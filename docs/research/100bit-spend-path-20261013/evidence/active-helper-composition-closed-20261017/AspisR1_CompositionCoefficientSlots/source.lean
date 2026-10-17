import SemanticCompositionCoefficients

/-! Symbolic coefficient slots, reused by source callers without reducing
any retained registry or field arithmetic. -/
set_option autoImplicit false
namespace AspisR1.CompositionCoefficientSlots
open AspisR1.SemanticCompositionCoefficients

theorem poseidon_slot (p : Fin 4 → ExactQM) (s : Fin 24 → ExactQM) (c : ExactQM)
    (i : Fin 4) : lanesFromModels p s c (Fin.castAdd 25 i) = p i := by
  simp only [lanesFromModels, Fin.val_castAdd, i.isLt, ↓reduceDIte]

theorem semantic_slot (p : Fin 4 → ExactQM) (s : Fin 24 → ExactQM) (c : ExactQM)
    (i : Fin 24) : lanesFromModels p s c (Fin.natAdd 4 (Fin.castAdd 1 i)) = s i := by
  have h0 : ¬ (4 + i.val < 4) := by omega
  have h28 : 4 + i.val < 28 := by omega
  simp only [lanesFromModels, Fin.val_natAdd, Fin.val_castAdd, dif_neg h0, dif_pos h28]
  have hidx : (⟨4 + i.val - 4, by omega⟩ : Fin 24) = i := by
    apply Fin.ext
    exact Nat.add_sub_cancel_left 4 i.val
  exact congrArg s hidx

theorem copy_slot (p : Fin 4 → ExactQM) (s : Fin 24 → ExactQM) (c : ExactQM) :
    lanesFromModels p s c 28 = c := by
  simp [lanesFromModels]

#print axioms poseidon_slot
#print axioms semantic_slot
#print axioms copy_slot
end AspisR1.CompositionCoefficientSlots
