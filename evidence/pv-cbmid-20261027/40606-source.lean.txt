import R1Z.PV_CBM_InventoryShape
namespace R1Z.PV_CBM_PathGeometry
open PV_CBM_InventoryShape
set_option autoImplicit false

theorem pathBase_closed (level : Nat) : pathBase level = 913 + 4 * level := by
  unfold pathBase
  omega

theorem pathBase_range (level : Nat) (h : level < 24) :
    913 ≤ pathBase level ∧ pathBase level + 1 < 1008 := by
  rw [pathBase_closed]
  omega

theorem pathBase_injective (a b : Nat) (h : pathBase a = pathBase b) : a = b := by
  rw [pathBase_closed, pathBase_closed] at h
  omega

theorem distinct_next (a b : Nat) : pathBase a ≠ pathBase b + 1 := by
  rw [pathBase_closed, pathBase_closed]
  omega

theorem pathUsed_iff (row column : Nat) : pathUsed row column ↔
    (∃ level : Nat, level < 24 ∧ row = 913 + 4 * level ∧ column ≤ 8) ∨
    (∃ level : Nat, level < 24 ∧ row = 914 + 4 * level) := by
  constructor
  · rintro ⟨level, hlevel, h | h⟩
    · exact Or.inl ⟨level, hlevel, by simpa only [pathBase_closed] using h.1, h.2⟩
    · apply Or.inr
      refine ⟨level, hlevel, ?_⟩
      rw [pathBase_closed] at h
      omega
  · rintro (⟨level, hlevel, hrow, hcolumn⟩ | ⟨level, hlevel, hrow⟩)
    · exact ⟨level, hlevel, Or.inl ⟨hrow.trans (pathBase_closed level).symm, hcolumn⟩⟩
    · refine ⟨level, hlevel, Or.inr ?_⟩
      rw [pathBase_closed]
      omega

theorem pathUsed_range (row column : Nat) (h : pathUsed row column) :
    912 ≤ row ∧ row < 1008 := by
  rcases h with ⟨level, hlevel, h | h⟩
  · have hp := pathBase_range level hlevel
    omega
  · have hp := pathBase_range level hlevel
    omega

#print axioms pathBase_closed
#print axioms pathBase_range
#print axioms pathBase_injective
#print axioms distinct_next
#print axioms pathUsed_iff
#print axioms pathUsed_range
end R1Z.PV_CBM_PathGeometry
