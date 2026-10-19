import R1NaturalProjection
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Generic algebra for one radix-four round pairing. The formulas mirror the
specified source permutation `[0, 3, 2, 1]` and Horner orders. This file proves
only polynomial degree, evaluation, coefficient-boundary, and Horner
identities; it is not a source-semantics or multi-round soundness result. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1.RoundPairing

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def quarter : K := (4 : K)⁻¹

def dot {n : Nat} (q w : Fin n → K) : K :=
  ∑ i : Fin n, q i * w i

def primalFold {n : Nat} (alpha : K) (q : Fin (4 * n) → K)
    (d : Fin n) : K :=
  ∑ s : Fin 4, q (AspisR1.childIndex d s) * alpha ^ s.val

/-- Rust's source permutation, written as the four entries `[0,3,2,1]`. -/
def sourcePerm : Fin 4 → Fin 4 := ![0, 3, 2, 1]

theorem sourcePerm_val (t : Fin 4) :
    (sourcePerm t).val = (4 - t.val) % 4 := by
  fin_cases t <;> rfl

def dualFold {n : Nat} (alpha : K) (w : Fin (4 * n) → K)
    (d : Fin n) : K :=
  quarter * ∑ t : Fin 4,
    w (AspisR1.childIndex d t) * alpha ^ ((4 - t.val) % 4)

def roundPolynomial {n : Nat} (q w : Fin (4 * n) → K) : K[X] :=
  ∑ d : Fin n, ∑ s : Fin 4, ∑ t : Fin 4,
    monomial (s.val + (4 - t.val) % 4)
      (quarter * q (AspisR1.childIndex d s) * w (AspisR1.childIndex d t))

def primalHorner {n : Nat} (alpha : K) (q : Fin (4 * n) → K)
    (d : Fin n) : K :=
  q (AspisR1.childIndex d 0) + alpha *
    (q (AspisR1.childIndex d 1) + alpha *
      (q (AspisR1.childIndex d 2) + alpha *
        q (AspisR1.childIndex d 3)))

def dualHorner {n : Nat} (alpha : K) (w : Fin (4 * n) → K)
    (d : Fin n) : K :=
  quarter * (w (AspisR1.childIndex d 0) + alpha *
    (w (AspisR1.childIndex d 3) + alpha *
      (w (AspisR1.childIndex d 2) + alpha *
        w (AspisR1.childIndex d 1))))

theorem primalFold_horner {n : Nat} (alpha : K)
    (q : Fin (4 * n) → K) (d : Fin n) :
    primalFold alpha q d = primalHorner alpha q d := by
  rw [primalFold, Fin.sum_univ_four]
  simp [primalHorner]
  ring

theorem dualFold_horner {n : Nat} (alpha : K)
    (w : Fin (4 * n) → K) (d : Fin n) :
    dualFold alpha w d = dualHorner alpha w d := by
  unfold dualFold dualHorner
  apply congrArg (fun z : K => quarter * z)
  rw [Fin.sum_univ_four]
  simp [AspisR1.childIndex]
  ring

theorem round_degree {n : Nat} (q w : Fin (4 * n) → K) :
    (roundPolynomial q w).natDegree ≤ 6 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d _hd
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s _hs
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _ht
  apply (Polynomial.natDegree_monomial_le _).trans
  have hs := s.isLt
  have ht := Nat.mod_lt (4 - t.val) (by decide : 0 < 4)
  omega

theorem round_eval {n : Nat} (alpha : K)
    (q w : Fin (4 * n) → K) :
    (roundPolynomial q w).eval alpha =
      dot (primalFold alpha q) (dualFold alpha w) := by
  simp only [roundPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, dot, primalFold, dualFold,
    Finset.mul_sum, Finset.sum_mul, pow_add]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  apply Finset.sum_congr rfl
  intro t _ht
  ring

theorem round_boundary {n : Nat} (q w : Fin (4 * n) → K) :
    (roundPolynomial q w).coeff 0 + (roundPolynomial q w).coeff 4 =
      quarter * dot q w := by
  have reindex : dot q w =
      ∑ d : Fin n, ∑ s : Fin 4,
        q (AspisR1.childIndex d s) * w (AspisR1.childIndex d s) := by
    rw [dot, ← (AspisR1.fibreIndexEquiv n).sum_comp,
      Fintype.sum_prod_type]
    rfl
  rw [reindex, roundPolynomial]
  simp only [Polynomial.finsetSum_coeff, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  simp [Fin.sum_univ_four, Polynomial.coeff_monomial]
  ring

/-- If the degree-zero/four coefficient claim is known, cancel the quarter
factor to recover the original dot product. -/
theorem round_boundary_cancellation {n : Nat}
    (h4 : (4 : K) ≠ 0) (q w : Fin (4 * n) → K) :
    dot q w = 4 *
      ((roundPolynomial q w).coeff 0 + (roundPolynomial q w).coeff 4) := by
  rw [round_boundary]
  dsimp [quarter]
  field_simp [h4]

theorem round_boundary_cancellation_of_claim {n : Nat}
    (h4 : (4 : K) ≠ 0) (q w : Fin (4 * n) → K) (claim : K)
    (hclaim : (roundPolynomial q w).coeff 0 +
      (roundPolynomial q w).coeff 4 = claim) :
    dot q w = 4 * claim := by
  rw [round_boundary_cancellation h4, hclaim]

#print axioms sourcePerm_val
#print axioms primalFold_horner
#print axioms dualFold_horner
#print axioms round_degree
#print axioms round_eval
#print axioms round_boundary
#print axioms round_boundary_cancellation
#print axioms round_boundary_cancellation_of_claim

end AspisR1.RoundPairing

end
