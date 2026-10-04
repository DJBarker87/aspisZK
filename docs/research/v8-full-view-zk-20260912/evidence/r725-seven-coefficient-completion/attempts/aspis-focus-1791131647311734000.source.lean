import AspisV8R19.R652ResidualCoefficientCompletion
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R725SevenCoefficientCompletion
open scoped BigOperators
open AspisV8R19.R652ResidualCoefficientCompletion
variable {F : Type*} [Field F]

lemma completion_rows12356 (d : Fin 7 → F) (alpha : F)
    (he : evalSeven d alpha = 0) (hb : d 0 + d 4 = 0)
    (hs : d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 0 ∧ d 5 = 0 ∧ d 6 = 0)
    (halpha : 1-alpha^4 ≠ 0) : ∀ i, d i = 0 := by
  rcases hs with ⟨h1,h2,h3,h5,h6⟩
  have h4 : d 4 = -d 0 := by linarith
  have h0mul : d 0 * (1-alpha^4) = 0 := by
    simpa [evalSeven,Fin.sum_univ_succ,h1,h2,h3,h4,h5,h6] using he
  have h0 : d 0 = 0 := (mul_eq_zero.mp h0mul).resolve_right halpha
  have h4zero : d 4 = 0 := by rw [h4,h0,neg_zero]
  intro i
  fin_cases i <;> assumption

lemma completion_rows02356 (d : Fin 7 → F) (alpha : F)
    (he : evalSeven d alpha = 0) (hb : d 0 + d 4 = 0)
    (hs : d 0 = 0 ∧ d 2 = 0 ∧ d 3 = 0 ∧ d 5 = 0 ∧ d 6 = 0)
    (halpha : alpha ≠ 0) : ∀ i, d i = 0 := by
  rcases hs with ⟨h0,h2,h3,h5,h6⟩
  have h4 : d 4 = 0 := by linarith
  have h1mul : d 1 * alpha = 0 := by
    simpa [evalSeven,Fin.sum_univ_succ,h0,h2,h3,h4,h5,h6] using he
  have h1 : d 1 = 0 := (mul_eq_zero.mp h1mul).resolve_right halpha
  intro i
  fin_cases i <;> assumption

#print axioms completion_rows12356
#print axioms completion_rows02356
end AspisV8R19.R725SevenCoefficientCompletion
