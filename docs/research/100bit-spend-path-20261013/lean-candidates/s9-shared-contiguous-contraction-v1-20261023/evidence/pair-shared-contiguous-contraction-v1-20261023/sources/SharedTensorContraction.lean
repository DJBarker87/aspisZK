import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AspisR1.SharedTensorContraction

/-- A common factor on each of four outer slots can be moved outside the
inner sixteen-term contraction. -/
theorem contract
    {E : Type*} [CommSemiring E]
    (f : Fin 4 → Fin 16 → E) (lo : Fin 16 → E) (hi : Fin 4 → E) :
    (∑ s : Fin 4, ∑ j : Fin 16, f s j * (lo j * hi s)) =
      ∑ s : Fin 4, (∑ j : Fin 16, f s j * lo j) * hi s := by
  apply Finset.sum_congr rfl
  intro s _hs
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (mul_assoc (f s j) (lo j) (hi s)).symm

/-- The same contraction can be applied to two outer factor vectors while
sharing the inner partial vector. -/
theorem contract_pair
    {E : Type*} [CommSemiring E]
    (f : Fin 4 → Fin 16 → E) (lo : Fin 16 → E)
    (hi₀ hi₁ : Fin 4 → E) :
    ((∑ s : Fin 4, ∑ j : Fin 16, f s j * (lo j * hi₀ s)) =
        ∑ s : Fin 4, (∑ j : Fin 16, f s j * lo j) * hi₀ s) ∧
      ((∑ s : Fin 4, ∑ j : Fin 16, f s j * (lo j * hi₁ s)) =
        ∑ s : Fin 4, (∑ j : Fin 16, f s j * lo j) * hi₁ s) := by
  exact ⟨contract f lo hi₀, contract f lo hi₁⟩

#print axioms contract
#print axioms contract_pair

end AspisR1.SharedTensorContraction
