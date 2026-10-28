import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_E1Product

/-- Pointwise conditional uniformity implies a uniform completed finite tape.
This is algebra on an already associated successful-return kernel. It assumes
no OS availability, error-tag law, or native execution equality. -/
theorem product_uniform {C R : Type} [Fintype R] (law : C → R → ℚ)
    (uniform : ∀ c r, law c r = 1 / (Fintype.card R : ℚ))
    (n : Nat) (context : Fin n → (Fin n → R) → C) (t : Fin n → R) :
    (∏ i, law (context i t) (t i)) = 1 / (Fintype.card (Fin n → R) : ℚ) := by
  simp only [uniform,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Fintype.card_fun,Nat.cast_pow,one_div_pow]


theorem weight_total {C R : Type} [Fintype R] [Nonempty R] (law : C → R → ℚ)
    (uniform : ∀ c r, law c r = 1 / (Fintype.card R : ℚ))
    (n : Nat) (context : Fin n → (Fin n → R) → C) :
    (∑ t : Fin n → R, ∏ i, law (context i t) (t i)) = 1 := by
  simp_rw [product_uniform law uniform]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem weighted_test {C R : Type} [Fintype R] (law : C → R → ℚ)
    (uniform : ∀ c r, law c r = 1 / (Fintype.card R : ℚ))
    (n : Nat) (context : Fin n → (Fin n → R) → C) (f : (Fin n → R) → ℚ) :
    (∑ t : Fin n → R, (∏ i, law (context i t) (t i)) * f t) =
      (∑ t, f t) / Fintype.card (Fin n → R) := by
  simp_rw [product_uniform law uniform]
  simp only [one_div_mul_eq_div,Finset.sum_div]

#print axioms weight_total
#print axioms weighted_test

#print axioms product_uniform
end R1Z.PV_RunJoin_E1Product
