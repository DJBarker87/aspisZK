import RawSemanticListPolynomialDegree
import RawSemanticCheckedStepPolynomialAdapter
import Mathlib.Algebra.Polynomial.Degree.Lemmas

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticPolynomialDegree28
open Polynomial
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawSemanticCheckedStepPolynomialAdapter

abbrev MainQM := AspisR1PublicPreparation.aspis_core.field.QM31

/-- A list with n coefficients produces a polynomial of degree strictly less
than n whenever it is nonempty. -/
theorem polynomial_natDegree_lt_length_of_ne_nil {K : Type} [CommSemiring K]
    (coefficients : List K) (hne : coefficients ≠ []) :
    (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial coefficients).natDegree <
      coefficients.length := by
  induction coefficients with
  | nil => cases hne rfl
  | cons c cs ih =>
      change (Polynomial.C c + Polynomial.X *
        AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree <
        cs.length + 1
      by_cases hcs : cs = []
      · subst cs
        simp [AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial]
      · have htail := ih hcs
        have hconst : (Polynomial.C c : Polynomial K).natDegree ≤ 0 := by simp
        have hX : (Polynomial.X : Polynomial K).natDegree ≤ 1 := Polynomial.natDegree_X_le
        have hmul : (Polynomial.X *
            AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree ≤
            cs.length := by
          calc
            _ ≤ (Polynomial.X : Polynomial K).natDegree +
                (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree :=
                  Polynomial.natDegree_mul_le
            _ ≤ 1 + (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs).natDegree :=
                  Nat.add_le_add_right hX _
            _ ≤ cs.length := by omega
        have hadd := Polynomial.natDegree_add_le
          (Polynomial.C c)
          (Polynomial.X * AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial cs)
        omega

/-- The production-shaped 28-cell coefficient vector yields degree at most 27. -/
theorem exactPolynomial_natDegree_le_27 (coefficients : Array MainQM 28#usize) :
    (exactPolynomial coefficients).natDegree ≤ 27 := by
  have hlen : ((mainArrayToProbe coefficients).v.map
      AspisR1.ExtractedMaskQM31Exact.decode).length = 28 := by
    simp only [List.length_map]
    simpa [mainArrayToProbe] using coefficients.property
  have hne : (mainArrayToProbe coefficients).v.map
      AspisR1.ExtractedMaskQM31Exact.decode ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [hlen] at this
  have hstrict := polynomial_natDegree_lt_length_of_ne_nil
    ((mainArrayToProbe coefficients).v.map AspisR1.ExtractedMaskQM31Exact.decode) hne
  change (AspisR1PublicPreparation.RawSemanticPolynomialOps.polynomial
      ((mainArrayToProbe coefficients).v.map AspisR1.ExtractedMaskQM31Exact.decode)).natDegree ≤ 27
  omega

#print axioms polynomial_natDegree_lt_length_of_ne_nil
#print axioms exactPolynomial_natDegree_le_27
end AspisR1PublicPreparation.RawSemanticPolynomialDegree28
