import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBM_InventoryShape
set_option autoImplicit false

/-- Owned row classification used by the P6 inventory candidate. -/
def pathBase (level : Nat) : Nat := 912 + 16 * (level / 4) + 1 + 4 * (level % 4)
def pathUsed (row column : Nat) : Prop :=
  ∃ level : Nat, level < 24 ∧ ((row = pathBase level ∧ column ≤ 8) ∨ row = pathBase level + 1)
def poseidon (row : Nat) : Prop := row < 912
def valueUsed (row column : Nat) : Prop :=
  (∃ value : Nat, value < 3 ∧
    ((row = 1008 + 2 * value ∧ column ≤ 10) ∨
     (row = 1009 + 2 * value ∧ column ≤ 10) ∨
     (row = Nat.xor (1008 + 2 * value) 12 ∧ column ≤ 10))) ∨
  (row = 1014 ∧ column < 3) ∨ (row = 1015 ∧ column < 2)
def occupancyUsed (row column : Nat) : Prop :=
  (row = 1017 ∧ column ≤ 10) ∨ (row = 1018 ∧ column < 10)
def auxUsed (row column : Nat) : Prop :=
  912 ≤ row ∧ ((row < 1008 ∧ pathUsed row column) ∨
    (1008 ≤ row ∧ (valueUsed row column ∨ occupancyUsed row column)))
def free (row column : Nat) : Prop :=
  (poseidon row ∧ 13 ≤ row % 16) ∨ (¬ poseidon row ∧ ¬ auxUsed row column)

theorem free_padding (row column : Nat) (hrow : row < 912)
    (hpad : 13 ≤ row % 16) : free row column := Or.inl ⟨hrow, hpad⟩

theorem free_aux (row column : Nat) (hrow : 912 ≤ row)
    (hused : ¬ auxUsed row column) : free row column :=
  Or.inr ⟨Nat.not_lt.mpr hrow, hused⟩

theorem used_path_not_free (row column level : Nat) (hlevel : level < 24)
    (hrow : row = pathBase level) (hcolumn : column ≤ 8)
    (hrange : 912 ≤ row ∧ row < 1008) : ¬ free row column := by
  intro h
  rcases h with h | h
  · exact (Nat.not_lt.mpr hrange.1) h.1
  · exact h.2 ⟨hrange.1, Or.inl ⟨hrange.2, level, hlevel, Or.inl ⟨hrow, hcolumn⟩⟩⟩

#print axioms free_padding
#print axioms free_aux
#print axioms used_path_not_free
end R1Z.PV_CBM_InventoryShape
