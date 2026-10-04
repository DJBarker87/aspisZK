import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R652ResidualCoefficientCompletion
open scoped BigOperators
variable {F : Type*} [Field F]

def evalSeven (d : Fin 7 → F) (alpha : F) : F := ∑ i, d i * alpha^i.val

/-- A first-fold-compatible seven-coefficient difference is determined by
its first six coefficients when alpha is nonzero. Zero alpha is excluded
explicitly and remains a separate failure/degeneracy obligation. -/
theorem ordinary_completion (d : Fin 7 → F) (alpha : F) (ha : alpha ≠ 0)
    (he : evalSeven d alpha = 0) (hs : ∀ i : Fin 7, i ≠ 6 → d i = 0) :
    ∀ i, d i = 0 := by
  have h6 : d 6 = 0 := by
    have hv : evalSeven d alpha = d 6 * alpha^6 := by
      unfold evalSeven
      rw [Finset.sum_eq_single (6 : Fin 7)]
      · rfl
      · intro i _ hi
        rw [hs i hi, zero_mul]
      · simp
    rw [hv] at he
    exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero 6 ha)
  intro i
  by_cases hi : i = 6
  · simpa only [hi] using h6
  · exact hs i hi

/-- The five selected structured coefficient differences, the retained
boundary and first-fold evaluation recover both omitted coefficients. -/
theorem structured_completion (d : Fin 7 → F) (alpha : F) (ha : alpha ≠ 0)
    (he : evalSeven d alpha = 0) (hb : d 0 + d 4 = 0)
    (hs : ∀ i : Fin 7, i ≠ 4 → i ≠ 6 → d i = 0) : ∀ i, d i = 0 := by
  have h0 : d 0 = 0 := hs 0 (by decide) (by decide)
  have h4 : d 4 = 0 := by simpa only [h0, zero_add] using hb
  apply ordinary_completion d alpha ha he
  intro i hi
  by_cases h : i = 4
  · simpa only [h] using h4
  · exact hs i h hi

#print axioms ordinary_completion
#print axioms structured_completion
end AspisV8R19.R652ResidualCoefficientCompletion
