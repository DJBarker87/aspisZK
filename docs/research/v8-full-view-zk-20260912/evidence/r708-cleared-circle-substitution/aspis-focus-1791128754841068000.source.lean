import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R708ClearedCircleSubstitution
open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F]

noncomputable def base : Polynomial F := -(X^2 + C (1:F))

noncomputable def cleared (P : Polynomial F) : Polynomial F :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    C (P.coeff n) * ((base (F:=F))^n * X^(P.natDegree - n))

lemma base_natDegree : (base (F:=F)).natDegree = 2 := by
  unfold base
  rw [natDegree_neg, natDegree_X_pow_add_C]

lemma base_leadingCoeff : (base (F:=F)).leadingCoeff = -1 := by
  unfold base
  rw [leadingCoeff_neg, leadingCoeff_X_pow_add_C (by omega)]

lemma coeff_base_pow_top (D : Nat) :
    ((base (F:=F))^D).coeff (2*D) = (-1:F)^D := by
  have hd : ((base (F:=F))^D).natDegree = 2*D := by
    rw [natDegree_pow, base_natDegree]
    omega
  rw [← hd, coeff_natDegree, leadingCoeff_pow, base_leadingCoeff]

lemma coeff_base_pow_top_mul (D : Nat) :
    ((base (F:=F))^D * X^(D-D)).coeff (2*D) = (-1:F)^D := by
  simpa [base] using coeff_base_pow_top (F:=F) D

lemma coeff_base_pow_top_zero (n D : Nat) (hn : n < D) :
    ((base (F:=F))^n * X^(D-n)).coeff (2*D) = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  calc
    ((base (F:=F))^n * X^(D-n)).natDegree ≤
        ((base (F:=F))^n).natDegree + (X^(D-n) : Polynomial F).natDegree := natDegree_mul_le
    _ ≤ n * (base (F:=F)).natDegree + (D-n) := by
      gcongr
      · exact natDegree_pow_le (p:=base (F:=F)) (n:=n)
      · simp
    _ ≤ n * 2 + (D-n) := by rw [base_natDegree]
    _ < 2*D := by omega

lemma cleared_coeff_top (P : Polynomial F) (hP : P ≠ 0) :
    (cleared P).coeff (2 * P.natDegree) = P.leadingCoeff * (-1 : F)^P.natDegree := by
  unfold cleared
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single P.natDegree]
  · rw [coeff_C_mul, coeff_base_pow_top_mul, coeff_natDegree]
  · intro n hn hne
    have hnlt : n < P.natDegree := by
      have hnmem := Finset.mem_range.mp hn
      omega
    rw [coeff_C_mul, coeff_base_pow_top_zero n P.natDegree hnlt, mul_zero]
  · intro hnot
    exfalso
    apply hnot
    exact Finset.mem_range.mpr (by omega)

lemma cleared_ne_zero (P : Polynomial F) (hP : P ≠ 0) : cleared P ≠ 0 := by
  intro hz
  have hc := cleared_coeff_top P hP
  rw [hz, coeff_zero] at hc
  have hlead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hone : (-1 : F) ≠ 0 := by
    intro h
    have : (1:F) = 0 := by simpa using congrArg Neg.neg h
    exact one_ne_zero this
  exact (mul_ne_zero hlead (pow_ne_zero _ hone)) hc.symm

#print axioms coeff_base_pow_top
#print axioms cleared_coeff_top
#print axioms cleared_ne_zero

end AspisV8R19.R708ClearedCircleSubstitution
