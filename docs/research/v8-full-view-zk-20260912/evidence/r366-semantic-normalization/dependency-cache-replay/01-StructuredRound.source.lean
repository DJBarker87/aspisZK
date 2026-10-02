import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Algebra for a proposed mask, not a theorem about the current V8 source. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
open Polynomial
variable {F : Type*} [Field F] {n : ℕ}

def roundEval (a : F) (b : Fin n → F) (x : F) : F :=
  a * (1 - 2*x) + ∑ i, b i * (x^(i.val+2) - x)

noncomputable def roundPolynomial (a : F) (b : Fin n → F) : F[X] :=
  C a * (1 - C 2 * X) + ∑ i, C (b i) * (X^(i.val+2) - X)

theorem roundPolynomial_eval (a : F) (b : Fin n → F) (x : F) :
    (roundPolynomial a b).eval x = roundEval a b x := by
  simp [roundPolynomial, roundEval, eval_finsetSum]

theorem roundEval_zero (a : F) (b : Fin n → F) : roundEval a b 0 = a := by
  simp [roundEval]

theorem roundEval_one (a : F) (b : Fin n → F) : roundEval a b 1 = -a := by
  simp [roundEval]
  ring

theorem roundEval_boundary (a : F) (b : Fin n → F) :
    roundEval a b 0 + roundEval a b 1 = 0 := by
  rw [roundEval_zero, roundEval_one, add_neg_cancel]

def semanticRound (carry a : F) (b : Fin n → F) (x : F) : F :=
  carry / 2 + roundEval a b x

theorem semanticRound_boundary [NeZero (2 : F)] (carry a : F) (b : Fin n → F) :
    semanticRound carry a b 0 + semanticRound carry a b 1 = carry := by
  simp only [semanticRound, roundEval_zero, roundEval_one]
  field_simp
  ring

/-- The constant coefficient is shifted by carry/2; the 26 coefficients
at degrees 2..27 are unchanged. No division by a challenge occurs. -/
def roundCoordinates (carry : F) : (F × (Fin n → F)) ≃ (F × (Fin n → F)) where
  toFun u := (carry / 2 + u.1, u.2)
  invFun v := (v.1 - carry / 2, v.2)
  left_inv u := by rcases u with ⟨a,b⟩; simp
  right_inv v := by rcases v with ⟨a,b⟩; simp

theorem roundPolynomial_coeff_zero (a : F) (b : Fin n → F) :
    (roundPolynomial a b).coeff 0 = a := by
  simp [roundPolynomial, coeff_X_pow]

theorem roundPolynomial_coeff_high (a : F) (b : Fin n → F) (i : Fin n) :
    (roundPolynomial a b).coeff (i.val+2) = b i := by
  have h0 : i.val+2 ≠ 0 := by omega
  have h1 : i.val+2 ≠ 1 := by omega
  simp [roundPolynomial, coeff_C_mul, coeff_X_pow, coeff_one, coeff_X, h0, h1,
    ← Fin.ext_iff, mul_ite]

theorem roundPolynomial_degree (a : F) (b : Fin n → F) :
    (roundPolynomial a b).natDegree ≤ n+1 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · apply (natDegree_C_mul_le _ _).trans
      simp
  · apply natDegree_sum_le_of_forall_le
    intro i _
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp only [natDegree_X_pow]
      have := i.isLt
      omega
    · simp

#print axioms roundPolynomial_eval
#print axioms roundEval_boundary
#print axioms semanticRound_boundary
#print axioms roundCoordinates
#print axioms roundPolynomial_coeff_zero
#print axioms roundPolynomial_coeff_high
#print axioms roundPolynomial_degree
end AspisV8R17
