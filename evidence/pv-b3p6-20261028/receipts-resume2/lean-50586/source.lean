import Aeneas.Std
namespace PV_B3P_MaskShape132
set_option autoImplicit false

def base (level : Nat) : Nat := 912 + 16*(level/4) + 1 + 4*(level%4)
def pathUsed (row column : Nat) : Prop :=
  ∃ level, level < 24 ∧ ((row = base level ∧ column ≤ 8) ∨ row = base level + 1)
def localUsed (row column : Nat) : Prop :=
  ((row%16 = 1 ∨ row%16 = 5 ∨ row%16 = 9 ∨ row%16 = 13) ∧ column ≤ 8) ∨
    row%16 = 2 ∨ row%16 = 6 ∨ row%16 = 10 ∨ row%16 = 14

theorem base_bounds (level : Nat) (hl : level < 24) :
    912 ≤ base level ∧ base level + 1 < 1008 := by
  unfold base
  omega

theorem base_local (level : Nat) (hl : level < 24) :
    (base level)%16 = 1 ∨ (base level)%16 = 5 ∨
      (base level)%16 = 9 ∨ (base level)%16 = 13 := by
  unfold base
  omega

theorem path_to_local (row column : Nat) (h : pathUsed row column) : localUsed row column := by
  obtain ⟨level,hl,h⟩ := h
  have hm := base_local level hl
  rcases h with ⟨rfl,hc⟩ | rfl
  · unfold localUsed
    exact Or.inl ⟨hm,hc⟩
  · unfold localUsed
    omega

#print axioms base_bounds
#print axioms base_local
#print axioms path_to_local
end PV_B3P_MaskShape132
