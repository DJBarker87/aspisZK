import Mathlib

set_option autoImplicit false
namespace AspisV8R19.R708ClearedCircleSubstitution
open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F]

def cleared (P : Polynomial F) : Polynomial F :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    C (P.coeff n) * (-(X^2 + 1))^n * X^(P.natDegree - n)

lemma coeff_base_pow_top (n D : Nat) (hn : n < D) :
    ((-(X^2 + 1 : Polynomial F))^n * X^(D-n)).coeff (2*D) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  apply lt_of_le_of_lt (natDegree_mul_le _ _)
  rw [natDegree_pow, natDegree_X_pow]
  have hbase : (-(X^2 + 1 : Polynomial F)).natDegree ≤ 2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    simp only [coeff_neg, coeff_add, coeff_X_pow, coeff_one, add_eq_zero_iff_eq_neg]
    split_ifs <;> omega
  have : n * 2 + (D-n) < 2*D := by omega
  exact lt_of_le_of_lt (Nat.add_le_add (Nat.mul_le_mul_right n hbase) (le_refl _)) this

lemma coeff_base_top (D : Nat) :
    ((-(X^2 + 1 : Polynomial F))^D * X^(D-D)).coeff (2*D) = (-1:F)^D := by
  simp [sub_self]

lemma cleared_coeff_top (P : Polynomial F) (hP : P ≠ 0) :
    (cleared P).coeff (2 * P.natDegree) = P.leadingCoeff * (-1 : F)^P.natDegree := by
  unfold cleared
  rw [Finset.sum_congr rfl]
  sorry

lemma cleared_ne_zero (P : Polynomial F) (hP : P ≠ 0) : cleared P ≠ 0 := by
  intro hz
  have hc := cleared_coeff_top P hP
  rw [hz, coeff_zero] at hc
  have hlead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  exact (mul_ne_zero hlead (pow_ne_zero _ neg_one_ne_zero)) hc.symm

#print axioms cleared_coeff_top
#print axioms cleared_ne_zero
end AspisV8R19.R708ClearedCircleSubstitution
