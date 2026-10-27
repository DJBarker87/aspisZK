import R1Z.PV_CBM_PathGeometry
namespace R1Z.PV_CBM_PathClassification
open PV_CBM_InventoryShape PV_CBM_PathGeometry
set_option autoImplicit false

theorem pathUsed_mod (row column : Nat) (hr : 912 ≤ row ∧ row < 1008) :
    pathUsed row column ↔
      ((row - 912) % 4 = 1 ∧ column ≤ 8) ∨ (row - 912) % 4 = 2 := by
  rw [pathUsed_iff]
  constructor
  · rintro (⟨level, hlevel, heq, hc⟩ | ⟨level, hlevel, heq⟩)
    · exact Or.inl ⟨by omega, hc⟩
    · exact Or.inr (by omega)
  · rintro (⟨hmod, hc⟩ | hmod)
    · exact Or.inl ⟨(row - 912) / 4, by omega, by omega, hc⟩
    · exact Or.inr ⟨(row - 912) / 4, by omega, by omega⟩

theorem pathFree_iff (row column : Nat) (hr : 912 ≤ row ∧ row < 1008) :
    free row column ↔ ¬ pathUsed row column := by
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim ((Nat.not_lt.mpr hr.1) h.1)
    · intro hp
      exact h.2 ⟨hr.1, Or.inl ⟨hr.2, hp⟩⟩
  · intro h
    apply free_aux row column hr.1
    rintro ⟨_, haux | haux⟩
    · exact h haux.2
    · omega

theorem pathFree_mod (row column : Nat) (hr : 912 ≤ row ∧ row < 1008) :
    free row column ↔
      (row - 912) % 4 = 0 ∨ (row - 912) % 4 = 3 ∨
      ((row - 912) % 4 = 1 ∧ 9 ≤ column) := by
  rw [pathFree_iff row column hr, pathUsed_mod row column hr]
  omega

theorem paddingFree_iff (row column : Nat) (hr : row < 912) :
    free row column ↔ 13 ≤ row % 16 := by
  constructor
  · rintro (h | h)
    · exact h.2
    · exact False.elim (h.1 hr)
  · exact free_padding row column hr

#print axioms pathUsed_mod
#print axioms pathFree_iff
#print axioms pathFree_mod
#print axioms paddingFree_iff
end R1Z.PV_CBM_PathClassification
