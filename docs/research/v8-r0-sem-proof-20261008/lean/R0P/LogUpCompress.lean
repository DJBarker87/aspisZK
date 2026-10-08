import Mathlib.Algebra.Polynomial.BigOperators
import R0P.Copy

/-! # G7: tagged-tuple compression as a polynomial

Source: `crates/aspis-statement/src/logup.rs:73–83` and
`pool_v1/pair_forest_copy_terminal.rs:232–263`, inspection pin
e4d68a70d3f6beb215c9f6dd418f4a2a3740c809. The tag has constant coefficient;
the first tuple limb uses lambda, and each subsequent limb advances the
power once. `copyPowers` preserves that source loop; `copy_powers_eq` is its
proved power identity. The polynomial below has exactly those coefficients.

This file proves deterministic polynomial identities only. It does not
assert injectivity after evaluation at a fixed lambda, a probability bound,
or copy balance. All coefficient and degree arguments are symbolic in the
limb index, without evaluating a concrete finite universe or source table.
-/

set_option autoImplicit false
open Polynomial
open scoped BigOperators

namespace R0P
variable {K : Type} [Field K]

/-- Literal tagged compression polynomial: tag at degree zero, followed by
the sixteen tuple limbs at degrees one through sixteen. -/
noncomputable def compressPoly (p : K × (Fin 16 → K)) : K[X] :=
  C p.1 + ∑ j : Fin 16, C (p.2 j) * X ^ (j.val + 1)

private theorem compressPoly_coeff_zero (p : K × (Fin 16 → K)) :
    (compressPoly p).coeff 0 = p.1 := by
  classical
  have h : ∀ j : Fin 16, ¬ (0 : Nat) = j.val + 1 := by intro j; omega
  simp only [compressPoly, coeff_add, coeff_C_zero, finsetSum_coeff,
    coeff_C_mul_X_pow, h, if_false, Finset.sum_const_zero, add_zero]

private theorem compressPoly_coeff_limb (p : K × (Fin 16 → K)) (j : Fin 16) :
    (compressPoly p).coeff (j.val + 1) = p.2 j := by
  classical
  simp only [compressPoly, coeff_add, coeff_C_succ, finsetSum_coeff,
    coeff_C_mul_X_pow, zero_add]
  rw [Finset.sum_eq_single j]
  · exact if_pos rfl
  · intro i _ hij
    apply if_neg
    intro h
    apply hij
    apply Fin.ext
    omega
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Equality before evaluation preserves the complete tagged tuple. -/
theorem compressPoly_eq_iff (p q : K × (Fin 16 → K)) :
    compressPoly p = compressPoly q ↔ p = q := by
  constructor
  · intro h
    apply Prod.ext
    · have hc := congrArg (fun f : K[X] => f.coeff 0) h
      simpa only [compressPoly_coeff_zero] using hc
    · funext j
      have hc := congrArg (fun f : K[X] => f.coeff (j.val + 1)) h
      simpa only [compressPoly_coeff_limb] using hc
  · intro h
    exact congrArg compressPoly h

/-- The collision difference is the zero polynomial exactly for equal
tagged tuples. This is a polynomial statement, not a claim about a root. -/
theorem compressPoly_sub_eq_zero_iff (p q : K × (Fin 16 → K)) :
    compressPoly p - compressPoly q = 0 ↔ p = q := by
  rw [sub_eq_zero, compressPoly_eq_iff]

private theorem compressPoly_natDegree_le (p : K × (Fin 16 → K)) :
    (compressPoly p).natDegree ≤ 16 := by
  classical
  unfold compressPoly
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simpa only [natDegree_C] using (Nat.zero_le 16)
  · apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_X_pow_le (p.2 j) (j.val + 1)).trans (by omega)

/-- Subtracting two tagged compressions preserves the degree-sixteen bound,
including when the difference is zero. -/
theorem compressPoly_sub_natDegree_le (p q : K × (Fin 16 → K)) :
    (compressPoly p - compressPoly q).natDegree ≤ 16 := by
  exact (natDegree_sub_le _ _).trans
    (max_le (compressPoly_natDegree_le p) (compressPoly_natDegree_le q))

/-- Evaluation agrees with the literal Copy powers: the tag contributes at
degree zero, and tuple limb j uses the source's iterative power j+1. -/
theorem compressPoly_eval (p : K × (Fin 16 → K)) (lam : K) :
    (compressPoly p).eval lam = p.1 + ∑ j : Fin 16, copyPowers lam j * p.2 j := by
  classical
  simp only [compressPoly, eval_add, eval_C, eval_finsetSum, eval_mul, eval_pow, eval_X]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [copy_powers_eq]
  exact mul_comm _ _

#print axioms compressPoly_coeff_zero
#print axioms compressPoly_coeff_limb
#print axioms compressPoly_eq_iff
#print axioms compressPoly_sub_eq_zero_iff
#print axioms compressPoly_natDegree_le
#print axioms compressPoly_sub_natDegree_le
#print axioms compressPoly_eval

end R0P
