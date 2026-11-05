import NIK_Footprint
set_option autoImplicit false
namespace NIO_Cpi

/-- Explicit physical interpretation obligation, not inferred from key inequality. -/
def CellKeyCompatible (key cell : Nat → Nat) : Prop :=
  ∀ a b, cell a = cell b → key a = key b

theorem distinct_key_cells (key cell : Nat → Nat)
    (compatible : CellKeyCompatible key cell) (a b : Nat)
    (distinct : key a ≠ key b) : cell a ≠ cell b := by
  intro same
  exact distinct (compatible a b same)
#print axioms distinct_key_cells

/-- One uniqueness-loop step extends the checked prefix; no bounded-buffer replay. -/
theorem uniqueness_step (key : Nat → Nat) (n : Nat)
    (prior : ∀ i j, i < n → j < n → i ≠ j → key i ≠ key j)
    (new : ∀ i, i < n → key i ≠ key n) :
    ∀ i j, i < n+1 → j < n+1 → i ≠ j → key i ≠ key j := by
  intro i j hi hj ne
  by_cases hin : i < n
  · by_cases hjn : j < n
    · exact prior i j hin hjn ne
    · have he : j = n := by omega
      subst j
      exact new i hin
  · have he : i = n := by omega
    subst i
    have hjn : j < n := by omega
    exact Ne.symm (new j hjn)
#print axioms uniqueness_step

theorem deposit_index_separation (start guarded offset : Nat)
    (s : start = 3 ∨ start = 4)
    (g : guarded = 1 ∨ guarded = 2 ∨ (start = 4 ∧ guarded = 3)) :
    guarded ≠ start + offset := by
  rcases s with s | s <;> rcases g with g | g | g <;> omega
#print axioms deposit_index_separation

theorem forest_index_separation (cursor guarded offset : Nat)
    (g : guarded = 2 ∨ guarded = 3 ∨ guarded = 4 ∨ guarded = cursor)
    (c : 4 ≤ cursor) : guarded ≠ cursor + 7 + offset := by
  rcases g with g | g | g | g <;> omega
#print axioms forest_index_separation

theorem pair_index_separation (cursor guarded offset : Nat)
    (g : guarded ≤ cursor) : guarded ≠ cursor + 5 + offset := by omega
#print axioms pair_index_separation

/-- Counter preservation outside a physical footprint is the actual child premise. -/
theorem held_counter_frame {F : Type} (s u : AspisR1.S2Trust.Heap F)
    (touch : Nat → Prop) (frame : NIK_Footprint.CounterFrame s u touch)
    (guarded : Nat) (outside : ¬ touch guarded) :
    u.counter guarded = s.counter guarded := frame.2 guarded outside
#print axioms held_counter_frame
end NIO_Cpi
