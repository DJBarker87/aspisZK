import R1OpeningRecordCodec
import R1TwoRoundComparison

/-! Symbolic polynomial views of the two seven-coefficient opening rows.

This module connects the typed opening payloads to the polynomial operations
used by the comparison model. It does not claim a Rust Horner-evaluation
refinement or an acceptance result.
-/
set_option autoImplicit false
noncomputable section

namespace AspisR1.OpeningPolynomialView

open Polynomial
open AspisWideTower
open scoped BigOperators

abbrev E := AspisWideTower.WideExact

/-- Coefficients are placed in ascending monomial order. -/
def polynomial {n : Nat} (coefficients : Fin n → E) : Polynomial E :=
  ∑ i : Fin n, C (coefficients i) * X ^ i.val

theorem coeff_at {n : Nat} (coefficients : Fin n → E) (i : Fin n) :
    (polynomial coefficients).coeff i.val = coefficients i := by
  classical
  unfold polynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hval : j.val ≠ i.val := by
      intro h
      exact hji (Fin.ext h)
    simp [hval]
  · simp

theorem polynomial_natDegree_le {n : Nat} (coefficients : Fin n → E)
    (hn : 0 < n) :
    (polynomial coefficients).natDegree ≤ n - 1 := by
  unfold polynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem polynomial_eval {n : Nat} (coefficients : Fin n → E) (x : E) :
    (polynomial coefficients).eval x =
      ∑ i : Fin n, coefficients i * x ^ i.val := by
  simp [polynomial]

/-- Polynomial view of the first opening-row coefficient payload. -/
def firstPolynomial
    (payload : AspisR1.OpeningRecordCodec.Payload .first) : Polynomial E :=
  polynomial payload

/-- Polynomial view of the second opening-row coefficient payload. -/
def secondPolynomial
    (payload : AspisR1.OpeningRecordCodec.Payload .second) : Polynomial E :=
  polynomial payload.2

theorem firstPolynomial_natDegree_le
    (payload : AspisR1.OpeningRecordCodec.Payload .first) :
    (firstPolynomial payload).natDegree ≤ 6 := by
  exact polynomial_natDegree_le payload (by decide)

theorem secondPolynomial_natDegree_le
    (payload : AspisR1.OpeningRecordCodec.Payload .second) :
    (secondPolynomial payload).natDegree ≤ 6 := by
  exact polynomial_natDegree_le payload.2 (by decide)

theorem firstPolynomial_boundary
    (payload : AspisR1.OpeningRecordCodec.Payload .first) :
    AspisR1.TwoRoundComparison.boundary (firstPolynomial payload) =
      payload 0 + payload 4 := by
  rw [AspisR1.TwoRoundComparison.boundary, firstPolynomial,
    coeff_at payload (0 : Fin 7), coeff_at payload (4 : Fin 7)]

theorem secondPolynomial_boundary
    (payload : AspisR1.OpeningRecordCodec.Payload .second) :
    AspisR1.TwoRoundComparison.boundary (secondPolynomial payload) =
      payload.2 0 + payload.2 4 := by
  rw [AspisR1.TwoRoundComparison.boundary, secondPolynomial,
    coeff_at payload.2 (0 : Fin 7), coeff_at payload.2 (4 : Fin 7)]

#print axioms coeff_at
#print axioms polynomial_natDegree_le
#print axioms polynomial_eval
#print axioms firstPolynomial_natDegree_le
#print axioms secondPolynomial_natDegree_le
#print axioms firstPolynomial_boundary
#print axioms secondPolynomial_boundary

end AspisR1.OpeningPolynomialView
end
