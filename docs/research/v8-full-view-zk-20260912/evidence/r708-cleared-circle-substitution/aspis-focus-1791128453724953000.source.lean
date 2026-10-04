import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R708ClearedCircleSubstitution
open scoped BigOperators
open Polynomial

variable {F : Type*} [Field F]

noncomputable def cleared (P : Polynomial F) : Polynomial F :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    C (P.coeff n) * (-(X^2 + C (1:F)))^n * X^(P.natDegree - n)

noncomputable def base : Polynomial F := -(X^2 + C (1:F))

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
    _ ≤ n * 2 + (D-n) := by
      gcongr
      · exact natDegree_pow_le (p:=base (F:=F)) (n:=n)
      · simp
    _ < 2*D := by omega

#print axioms coeff_base_pow_top
#print axioms coeff_base_pow_top_zero

#print axioms cleared_coeff_top
#print axioms cleared_ne_zero
end AspisV8R19.R708ClearedCircleSubstitution
