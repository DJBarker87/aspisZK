import RPt_JFv_RawSemanticPolynomialOps
import Mathlib.Algebra.Polynomial.Degree.Lemmas
set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticListPolynomialDegree
open Polynomial

/-- The recursive low-order list polynomial has degree at most its list length;
this generic bound is independent of all semantic-parser assumptions. -/
theorem polynomial_natDegree_le_length {K : Type} [CommSemiring K]
    (coefficients : List K) :
    (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial coefficients).natDegree ≤
      coefficients.length := by
  induction coefficients with
  | nil => simp [AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial]
  | cons c cs ih =>
      change (Polynomial.C c + Polynomial.X *
        AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree ≤
        cs.length + 1
      have hconst : (Polynomial.C c : Polynomial K).natDegree ≤ 0 := by simp
      have hX : (Polynomial.X : Polynomial K).natDegree ≤ 1 := Polynomial.natDegree_X_le
      have hmul : (Polynomial.X *
          AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree ≤
          cs.length + 1 := by
        calc
          _ ≤ (Polynomial.X : Polynomial K).natDegree +
              (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ 1 + cs.length := Nat.add_le_add hX ih
          _ = cs.length + 1 := by omega
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (hconst.trans (by omega)) hmul)

#print axioms polynomial_natDegree_le_length
end AspisR1PublicPreparation.RawSemanticListPolynomialDegree
