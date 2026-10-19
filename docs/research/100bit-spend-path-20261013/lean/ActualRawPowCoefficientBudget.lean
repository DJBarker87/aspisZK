import CompPoly.Univariate.Raw.Proofs
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace ActualRawPowCoefficientBudget
open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- One naive Raw.mul coefficient-operation budget: the first term covers
coefficient products, the second coefficient additions during the convolution
fold, and the last final output inspection. -/
def rawMulCoefficientBudget (p q : CPolynomial.Raw F) : Nat :=
  p.size * q.size + p.size * (p.size + q.size) + (p.size + q.size)

/-- Mirror the actual linear `Raw.pow` iterator, annotating every actual
multiplication with its naive-convolution coefficient budget. -/
def rawPowWithCoefficientBudget (p : CPolynomial.Raw F) : Nat → CPolynomial.Raw F × Nat
  | 0 => (1, 0)
  | n + 1 =>
      let prev := rawPowWithCoefficientBudget p n
      (p * prev.1, prev.2 + rawMulCoefficientBudget p prev.1)

theorem rawPowWithCoefficientBudget_value (p : CPolynomial.Raw F) (n : Nat) :
    (rawPowWithCoefficientBudget p n).1 = p ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rawPowWithCoefficientBudget]
      rw [ih, CPolynomial.Raw.pow_succ]

theorem rawXpow_size (n : Nat) [Nontrivial F] :
    ((CPolynomial.Raw.X : CPolynomial.Raw F) ^ n).size = n + 1 := by
  rw [CPolynomial.Raw.X_pow_eq_monomial_one]
  simp [CPolynomial.Raw.monomial, one_ne_zero]

theorem rawXpow_coefficient_budget_le (n : Nat) [Nontrivial F] :
    (rawPowWithCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F) n).2 ≤
      12 * n * (n + 1) := by
  induction n with
  | zero => simp [rawPowWithCoefficientBudget]
  | succ n ih =>
      have hsize :
          (rawPowWithCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F) n).1.size = n + 1 := by
        rw [rawPowWithCoefficientBudget_value, rawXpow_size]
      have hXsize : (CPolynomial.Raw.X : CPolynomial.Raw F).size = 2 := by rfl
      have hstep : rawMulCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F)
          (rawPowWithCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F) n).1 =
          5 * n + 11 := by
        simp [rawMulCoefficientBudget, hsize, hXsize]
        omega
      change (rawPowWithCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F) n).2 +
          rawMulCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F)
            (rawPowWithCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F) n).1 ≤
        12 * (n + 1) * (n + 2)
      rw [hstep]
      have hlinear : 5 * n + 11 ≤ 24 * (n + 1) := by omega
      calc
        (rawPowWithCoefficientBudget (CPolynomial.Raw.X : CPolynomial.Raw F) n).2 +
            (5 * n + 11) ≤ 12 * n * (n + 1) + (5 * n + 11) :=
          Nat.add_le_add_right ih _
        _ ≤ 12 * n * (n + 1) + 24 * (n + 1) :=
          Nat.add_le_add_left hlinear _
        _ = 12 * (n + 1) * (n + 2) := by
          ring

#print axioms rawPowWithCoefficientBudget_value
#print axioms rawXpow_size
#print axioms rawXpow_coefficient_budget_le
end ActualRawPowCoefficientBudget
