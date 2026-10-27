import R1Z.PV_CBM_InventoryShape
namespace R1Z.PV_CBM_ValueClassification
open PV_CBM_InventoryShape
set_option autoImplicit false

theorem exists_three (P : Nat → Prop) :
    (∃ v : Nat, v < 3 ∧ P v) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨v, hv, hp⟩
    have h : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases h with h | h | h
    · exact Or.inl (h ▸ hp)
    · exact Or.inr (Or.inl (h ▸ hp))
    · exact Or.inr (Or.inr (h ▸ hp))
  · rintro (h | h | h)
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩

def usedColumns (offset : Nat) : Nat :=
  if offset < 6 then 11
  else if offset = 6 then 3
  else if offset = 7 then 2
  else if offset = 8 ∨ offset = 9 ∨ offset = 12 ∨ offset = 14 then 11
  else if offset = 10 then 10 else 0

theorem valueUsed_expanded (row column : Nat) :
    valueUsed row column ↔
      ((row = 1008 ∨ row = 1009 ∨ row = 1010 ∨ row = 1011 ∨
        row = 1012 ∨ row = 1013 ∨ row = 1016 ∨ row = 1020 ∨ row = 1022) ∧ column ≤ 10) ∨
      (row = 1014 ∧ column < 3) ∨ (row = 1015 ∧ column < 2) := by
  have h0 : Nat.xor 1008 12 = 1020 := rfl
  have h1 : Nat.xor 1010 12 = 1022 := rfl
  have h2 : Nat.xor 1012 12 = 1016 := rfl
  unfold valueUsed
  rw [exists_three]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, h0, h1, h2]
  omega

theorem valueAux_iff (offset column : Nat) (ho : offset < 16) :
    auxUsed (1008 + offset) column ↔ column < usedColumns offset := by
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 ∨ offset = 8 ∨
    offset = 9 ∨ offset = 10 ∨ offset = 11 ∨ offset = 12 ∨ offset = 13 ∨
    offset = 14 ∨ offset = 15 := by omega
  unfold auxUsed
  rw [valueUsed_expanded]
  unfold occupancyUsed usedColumns
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst offset <;> norm_num <;> omega

#print axioms exists_three
#print axioms valueUsed_expanded
#print axioms valueAux_iff
end R1Z.PV_CBM_ValueClassification
