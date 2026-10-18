import Mathlib.Algebra.Polynomial.Taylor

open Polynomial
noncomputable section

namespace RRChildSliceTaylor

variable {K : Type*} [Field K]

/-- The coefficient of `X^n` in the child polynomial after substituting
`Y ↦ a + X*Y` into `Σ_i X^i g_i(Y)`. -/
def childCoeff (g : Nat → K[X]) (a : K) (n : Nat) : K[X] :=
  ∑ i ∈ Finset.range (n + 1),
    C ((Polynomial.taylor a (g i)).coeff (n - i)) * X ^ (n - i)

theorem childCoeff_natDegree_le (g : Nat → K[X]) (a : K) (n : Nat) :
    (childCoeff g a n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  unfold childCoeff
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Polynomial.coeff_C_mul_X_pow]
  split
  · rename_i heq
    omega
  · rfl

theorem childCoeff_top_coeff (g : Nat → K[X]) (a : K) (n : Nat) :
    (childCoeff g a n).coeff n = (Polynomial.taylor a (g 0)).coeff n := by
  unfold childCoeff
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp [Polynomial.coeff_C_mul_X_pow]
  · intro i hi hne
    simp only [Polynomial.coeff_C_mul_X_pow]
    split
    · rename_i heq
      have hiNat : i ≤ n := by
        have hi' := Finset.mem_range.mp hi
        omega
      have : i = 0 := by omega
      exact (hne this).elim
    · rfl
  · simp

end RRChildSliceTaylor
