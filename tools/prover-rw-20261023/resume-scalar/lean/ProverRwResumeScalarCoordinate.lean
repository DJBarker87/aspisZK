import Lean.Elab.Tactic.Omega

/- Coordinate arithmetic only; not a native Rust semantics theorem. -/
namespace ProverRwResumeScalar

theorem coordinate_range (raw : Nat) : raw % 32 < 32 :=
  Nat.mod_lt raw (by omega)

theorem observer_indices (j : Nat) (h : j < 32) :
    j < 32 ∧ j < 64 ∧ j + 32 < 64 ∧ j + 32 < 2^64 := by
  omega

/-- Every64 position is covered by exactly one of the selected halves. -/
theorem coordinate_cover (k : Nat) (h : k < 64) :
    ∃ j, j < 32 ∧ (k = j ∨ k = j + 32) := by
  by_cases hk : k < 32
  · exact ⟨k, hk, Or.inl rfl⟩
  · exact ⟨k - 32, by omega, Or.inr (by omega)⟩

/-- Extensional observation recovery; inputs remain unrestricted complete arrays. -/
theorem all_coordinates_equal {α : Type} (a b : Fin 64 → α)
    (h : ∀ j : Fin 32,
      a ⟨j.val, by omega⟩ = b ⟨j.val, by omega⟩ ∧
      a ⟨j.val + 32, by omega⟩ = b ⟨j.val + 32, by omega⟩) : a = b := by
  funext k
  obtain ⟨j, hj, hk | hk⟩ := coordinate_cover k.val k.isLt
  · have he : k = (⟨j, by omega⟩ : Fin 64) := Fin.ext hk
    rw [he]
    exact (h ⟨j, hj⟩).1
  · have he : k = (⟨j + 32, by omega⟩ : Fin 64) := Fin.ext hk
    rw [he]
    exact (h ⟨j, hj⟩).2

#print axioms coordinate_range
#print axioms observer_indices
#print axioms coordinate_cover
#print axioms all_coordinates_equal
end ProverRwResumeScalar
