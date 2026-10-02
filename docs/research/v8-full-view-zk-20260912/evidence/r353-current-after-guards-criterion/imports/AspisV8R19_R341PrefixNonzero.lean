import AspisV8R19.R332PrefixInitializationSelectors

/-! Algebraic nonzero criterion for the source-indexed prefix products.
The criterion does not prove the batch's iterator guard or its execution. -/
set_option autoImplicit false
namespace AspisV8R19.R341PrefixNonzero
open AspisV8R15.ExactTowerBase
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R326PrefixProductSelectors
noncomputable section

theorem sourcePrefixValue_succ (f : Nat → M31Exact) (j : Nat) :
    sourcePrefixValue f (j + 1) = sourcePrefixValue f j * f (j + 1) := by
  simp only [sourcePrefixValue, prefixAccum, Nat.zero_add]

theorem sourcePrefixValue_ne_zero_iff (f : Nat → M31Exact) (j : Nat) :
    sourcePrefixValue f j ≠ 0 ↔ ∀ k, k ≤ j → f k ≠ 0 := by
  induction j with
  | zero =>
      change f 0 ≠ 0 ↔ ∀ k, k ≤ 0 → f k ≠ 0
      constructor
      · intro h k hk
        have hk0 : k = 0 := by omega
        simpa only [hk0] using h
      · intro h
        exact h 0 (by omega)
  | succ j ih =>
      rw [sourcePrefixValue_succ, mul_ne_zero_iff, ih]
      constructor
      · rintro ⟨h, hn⟩ k hk
        by_cases hj : k ≤ j
        · exact h k hj
        · have hk1 : k = j + 1 := by omega
          simpa only [hk1] using hn
      · intro h
        exact ⟨fun k hk => h k (by omega), h (j + 1) (by omega)⟩

theorem initialized_pair_total_ne_zero_iff
    (f g : Nat → M31Exact) (L K : Nat) (hL : 0 < L) (hK : 0 < K) :
    sourcePrefixValue f (L - 1) * sourcePrefixValue g (K - 1) ≠ 0 ↔
      (∀ j, j < L → f j ≠ 0) ∧ (∀ j, j < K → g j ≠ 0) := by
  rw [mul_ne_zero_iff, sourcePrefixValue_ne_zero_iff, sourcePrefixValue_ne_zero_iff]
  constructor
  · rintro ⟨hf, hg⟩
    exact ⟨fun j hj => hf j (by omega), fun j hj => hg j (by omega)⟩
  · rintro ⟨hf, hg⟩
    exact ⟨fun j hj => hf j (by omega), fun j hj => hg j (by omega)⟩

#print axioms sourcePrefixValue_succ
#print axioms sourcePrefixValue_ne_zero_iff
#print axioms initialized_pair_total_ne_zero_iff
end
end AspisV8R19.R341PrefixNonzero
