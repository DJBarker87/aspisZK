import R1SubfieldBatchStage2
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.BigOperators

/-! Symbolic residual-polynomial facts for a 22-coordinate batch. These are
algebraic statements only; they make no probability, Fiat--Shamir, protocol,
or source-correspondence claim. -/

set_option autoImplicit false

namespace AspisR1.ResidualBatch

open Polynomial
open scoped BigOperators

noncomputable section

variable {K E : Type} [Field K] [Field E] [Fintype K]

/-- Encode the 22 residual coordinates as coefficients of a sparse polynomial. -/
def residualPolynomial (r : Fin 22 → E) : E[X] :=
  ∑ i : Fin 22, Polynomial.monomial i.val (r i)

theorem residualPolynomial_coeff (r : Fin 22 → E) (i : Fin 22) :
    (residualPolynomial r).coeff i.val = r i := by
  classical
  rw [residualPolynomial]
  change (∑ j : Fin 22, Polynomial.monomial j.val (r j)).coeff i.val = r i
  rw [show (∑ j : Fin 22, Polynomial.monomial j.val (r j)).coeff i.val =
      ∑ j : Fin 22, (Polynomial.monomial j.val (r j)).coeff i.val by
        exact map_sum (Polynomial.lcoeff E i.val)
          (fun j : Fin 22 => Polynomial.monomial j.val (r j)) Finset.univ]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    have hne : j.val ≠ i.val := by
      intro hv
      exact hji (Fin.ext hv)
    simp [Polynomial.coeff_monomial, hne]
  · simp

theorem residualPolynomial_eq_zero_iff (r : Fin 22 → E) :
    residualPolynomial r = 0 ↔ ∀ i, r i = 0 := by
  constructor
  · intro h i
    have hcoeff := congrArg (fun p : E[X] => p.coeff i.val) h
    simpa only [residualPolynomial_coeff, Polynomial.coeff_zero] using hcoeff
  · intro hr
    classical
    simp [residualPolynomial, hr]

theorem residualPolynomial_natDegree_le (r : Fin 22 → E) :
    (residualPolynomial r).natDegree ≤ 21 := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [residualPolynomial]
  change (∑ i : Fin 22, Polynomial.monomial i.val (r i)).coeff m = 0
  rw [show (∑ i : Fin 22, Polynomial.monomial i.val (r i)).coeff m =
      ∑ i : Fin 22, (Polynomial.monomial i.val (r i)).coeff m by
        exact map_sum (Polynomial.lcoeff E m)
          (fun i : Fin 22 => Polynomial.monomial i.val (r i)) Finset.univ]
  apply Finset.sum_eq_zero
  intro i _hi
  have hne : m ≠ i.val := by omega
  simp [Polynomial.coeff_monomial, Ne.symm hne]

theorem eval_residualPolynomial (iota : K →+* E) (rho : K)
    (r : Fin 22 → E) :
    (residualPolynomial r).eval (iota rho) =
      ∑ i : Fin 22, (iota rho) ^ i.val * r i := by
  classical
  simp [residualPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, mul_comm]

/-- Challenges are bad exactly when the nonzero residual polynomial vanishes. -/
noncomputable def bad (iota : K →+* E) (r : Fin 22 → E) : Finset K := by
  classical
  exact if residualPolynomial r = 0 then ∅ else
    Finset.univ.filter fun rho : K =>
      (residualPolynomial r).eval (iota rho) = 0

theorem bad_card_le_21 (iota : K →+* E) (r : Fin 22 → E) :
    (bad iota r).card ≤ 21 := by
  classical
  by_cases hp : residualPolynomial r = 0
  · simp [bad, hp]
  · simp only [bad, if_neg hp]
    exact AspisR1.subfield_bad_card_le_21 iota (residualPolynomial r) hp
      (residualPolynomial_natDegree_le r)

theorem all_zero_of_eval_zero_outside_bad (iota : K →+* E) (rho : K)
    (r : Fin 22 → E)
    (hrho : rho ∉ bad iota r)
    (heval : ∑ i : Fin 22, (iota rho) ^ i.val * r i = 0) :
    ∀ i, r i = 0 := by
  classical
  by_cases hp : residualPolynomial r = 0
  · exact residualPolynomial_eq_zero_iff r |>.mp hp
  · have hroot : (residualPolynomial r).eval (iota rho) ≠ 0 := by
      intro hzero
      apply hrho
      simp [bad, hp, hzero]
    have heval_zero : (residualPolynomial r).eval (iota rho) = 0 := by
      rw [eval_residualPolynomial]
      exact heval
    exact False.elim (hroot heval_zero)

/-- Residuals against a 64-symbol message expand as the value batch minus the
message coefficients paired with their 22-coordinate basis columns. -/
def residual {K E : Type} [Field K] [Field E]
    (iota : K →+* E) (values : Fin 22 → E) (message : Fin 64 → E)
    (basis : Fin 22 → Fin 64 → K) : Fin 22 → E :=
  fun i => values i - ∑ j : Fin 64, message j * iota (basis i j)

theorem weighted_residual_identity (iota : K →+* E) (rho : K)
    (values : Fin 22 → E) (message : Fin 64 → E)
    (basis : Fin 22 → Fin 64 → K) :
    ∑ i : Fin 22, (iota rho) ^ i.val * residual iota values message basis i =
      (∑ i : Fin 22, (iota rho) ^ i.val * values i) -
        ∑ j : Fin 64, message j *
          iota (∑ i : Fin 22, rho ^ i.val * basis i j) := by
  classical
  have hcolumns :
      (∑ i : Fin 22, (iota rho) ^ i.val *
        (∑ j : Fin 64, message j * iota (basis i j))) =
      ∑ j : Fin 64, message j *
        iota (∑ i : Fin 22, rho ^ i.val * basis i j) := by
    calc
      _ = ∑ i : Fin 22, ∑ j : Fin 64,
            message j * ((iota rho) ^ i.val * iota (basis i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j : Fin 64, ∑ i : Fin 22,
            message j * ((iota rho) ^ i.val * iota (basis i j)) :=
        Finset.sum_comm
      _ = ∑ j : Fin 64, message j *
            (∑ i : Fin 22, (iota rho) ^ i.val * iota (basis i j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
      _ = ∑ j : Fin 64, message j *
            iota (∑ i : Fin 22, rho ^ i.val * basis i j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul, map_pow]
  calc
    _ = ∑ i : Fin 22,
          ((iota rho) ^ i.val * values i - (iota rho) ^ i.val *
            (∑ j : Fin 64, message j * iota (basis i j))) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [residual]
      ring
    _ = (∑ i : Fin 22, (iota rho) ^ i.val * values i) -
          ∑ i : Fin 22, (iota rho) ^ i.val *
            (∑ j : Fin 64, message j * iota (basis i j)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i : Fin 22, (iota rho) ^ i.val * values i) -
          ∑ j : Fin 64, message j *
            iota (∑ i : Fin 22, rho ^ i.val * basis i j) := by
      rw [hcolumns]

#print axioms residualPolynomial_coeff
#print axioms residualPolynomial_eq_zero_iff
#print axioms residualPolynomial_natDegree_le
#print axioms eval_residualPolynomial
#print axioms bad_card_le_21
#print axioms all_zero_of_eval_zero_outside_bad
#print axioms weighted_residual_identity

end
end AspisR1.ResidualBatch
