import R1SemanticCoefficientCodec
import R1OpeningPolynomialView

/-! Algebraic bridge for the selected semantic coefficient model. These statements relate the
reverse-Horner and boundary-fold shapes to the existing coefficient polynomial
model; they do not claim Rust/source refinement or verifier acceptance. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticPolynomialChecks

open AspisWideTower
open scoped BigOperators

abbrev Coefficients := AspisR1.SemanticCoefficientCodec.Coefficients
abbrev E := AspisWideTower.WideExact

/-- Same list fold as the historical `AspisV8R17.sourceMixHorner`, stated
locally to avoid importing its larger generated-module dependency graph. -/
def sourceHorner {F : Type*} [Field F] (x : F) (cs : List F) : F :=
  cs.reverse.foldl (fun acc c => acc * x + c) 0

theorem sourceHorner_cons {F : Type*} [Field F] (x c : F) (cs : List F) :
    sourceHorner x (c :: cs) = sourceHorner x cs * x + c := by
  simp [sourceHorner, List.reverse_cons, List.foldl_append]

/-- Generic finite-list Horner identity, following the induction route of
`AspisV8R17.sourceMixHorner_eq_sum` from SourceMixing.lean
(SHA-256 a6f60c3c, see the retained source for the original generic proof). -/
theorem sourceHorner_ofFn_eq_sum {F : Type*} [Field F]
    (n : Nat) (cs : Fin n → F) (x : F) :
    sourceHorner x (List.ofFn cs) = ∑ i, cs i * x ^ i.val := by
  induction n with
  | zero => simp [sourceHorner]
  | succ n ih =>
      rw [List.ofFn_succ, sourceHorner_cons, ih]
      simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
        Fin.val_succ, pow_succ]
      simp only [← mul_assoc, ← Finset.sum_mul]
      exact add_comm _ _

/-- The 28 decoded low-wide coefficients, interpreted by the retained
ascending-monomial polynomial, have the same value as reverse Horner. -/
theorem horner_eq_semantic_polynomial_eval
    (xs : Coefficients) (x : E) :
    (List.ofFn (fun i : Fin 28 => (xs i).val)).reverse.foldl
        (fun acc c => acc * x + c) 0 =
      (AspisR1.SemanticCoefficientCodec.polynomial xs).eval x := by
  change sourceHorner x
    (List.ofFn (fun i : Fin 28 => (xs i).val)) = _
  rw [sourceHorner_ofFn_eq_sum]
  have hpoly : AspisR1.SemanticCoefficientCodec.polynomial xs =
      AspisR1.OpeningPolynomialView.polynomial
        (fun i : Fin 28 => (xs i).val) := rfl
  rw [hpoly, AspisR1.OpeningPolynomialView.polynomial_eval]

private theorem foldl_add_sum {F : Type*} [AddMonoid F] (ys : List F) (a : F) :
    ys.foldl (fun acc c => acc + c) a = a + ys.sum := by
  induction ys generalizing a with
  | nil => simp
  | cons c ys ih =>
      simp only [List.foldl_cons, List.sum_cons, ih, add_assoc]

/-- The source-shaped boundary accumulator runs forward over every coefficient,
seeded by coefficient zero. Algebraically this is `p(0)+p(1)` for the modeled
polynomial. -/
theorem boundary_add_eq_semantic_polynomial_evals
    (xs : Coefficients) :
    (List.ofFn (fun i : Fin 28 => (xs i).val)).foldl
        (fun acc c => acc + c) (xs ⟨0, by decide⟩).val =
      (AspisR1.SemanticCoefficientCodec.polynomial xs).eval 0 +
        (AspisR1.SemanticCoefficientCodec.polynomial xs).eval 1 := by
  let cs : Fin 28 → E := fun i => (xs i).val
  have hfold :
      (List.ofFn cs).foldl (fun acc c => acc + c) (cs 0) =
        cs 0 + ∑ i : Fin 28, cs i := by
    rw [foldl_add_sum, List.sum_ofFn]
  have hpoly : AspisR1.SemanticCoefficientCodec.polynomial xs =
      AspisR1.OpeningPolynomialView.polynomial cs := rfl
  have h0 :
      (AspisR1.SemanticCoefficientCodec.polynomial xs).eval 0 = cs 0 := by
    rw [hpoly, Polynomial.eval_zero]
    exact AspisR1.OpeningPolynomialView.coeff_at cs (0 : Fin 28)
  have h1 :
      (AspisR1.SemanticCoefficientCodec.polynomial xs).eval 1 =
        ∑ i : Fin 28, cs i := by
    rw [hpoly, AspisR1.OpeningPolynomialView.polynomial_eval]
    simp only [one_pow, mul_one]
  rw [h0, h1]
  simpa [cs] using hfold

#print axioms horner_eq_semantic_polynomial_eval
#print axioms boundary_add_eq_semantic_polynomial_evals

end AspisR1.LiteralSemanticPolynomialChecks
end
