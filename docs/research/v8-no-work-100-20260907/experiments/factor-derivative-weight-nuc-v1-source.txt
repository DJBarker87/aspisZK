import FactorIdentityCover

/-! Differentiating the outer Y removes its complete weight c. The bound
uses natural subtraction and therefore also covers zero/constant polynomials
and derivatives killed by finite characteristic. No primeness, positive
Y-degree, nonzero derivative, actual OOD regularity, or candidate curve is
assumed. Only the actual substituted answer's degree is bounded.

Draft only: source-reviewed, not compiled.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.FactorDerivativeWeight
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisV8.FactorCoherence
noncomputable section

/-- For each surviving derivative coefficient, the corresponding original
coefficient has Y-exponent exactly one larger. Multiplication by a natural
scalar cannot increase its inner degree, including in finite characteristic. -/
theorem derivative_weight_le {R : Type*} [CommRing R] [IsDomain R]
    (c : Nat) (F : Polynomial (Polynomial R)) :
    localBivariateWeight c F.derivative ≤ localBivariateWeight c F - c := by
  apply localBivariateWeight_le_of_coeff
  intro i member
  have originalMember : i+1 ∈ F.support := Polynomial.of_mem_support_derivative member
  have originalBound := coeff_weight_le_localBivariateWeight c F (i+1) originalMember
  have coefficientDegree : (F.derivative.coeff i).natDegree ≤
      (F.coeff (i+1)).natDegree := by
    rw [Polynomial.coeff_derivative]
    have scalar : (i : Polynomial R)+1 = ((i+1 : Nat) : Polynomial R) := by
      rw [Nat.cast_add, Nat.cast_one]
    calc
      (F.coeff (i+1)*((i : Polynomial R)+1)).natDegree ≤
          (F.coeff (i+1)).natDegree+((i : Polynomial R)+1).natDegree :=
        Polynomial.natDegree_mul_le
      _ = (F.coeff (i+1)).natDegree := by
        rw [scalar, Polynomial.natDegree_natCast, Nat.add_zero]
  simp only [Nat.add_mul, Nat.one_mul] at originalBound
  omega

/-- Specializing the ignored X variable and a degree-c actual OOD answer
cannot undo the derivative's full Y-weight drop. Natural subtraction is
essential when the original polynomial has weight below c. -/
theorem derivative_curve_degree {K : Type*} [Field K]
    (c : Nat) (F : TrivariatePolynomial K) (t : K) (answer : K[X])
    (degree : answer.natDegree ≤ c) :
    (derivativeCurve F t answer).natDegree ≤ trivariateYZWeight c F - c :=
  (FactorIdentityCover.point_degree_le_weight c F.derivative t answer degree).trans
    (derivative_weight_le c F)

/-- Width29 specialization. Nonzeroness is still a separate premise for
turning this degree bound into a finite root count. -/
theorem width29_derivative_curve_degree {K : Type*} [Field K]
    (F : TrivariatePolynomial K) (t : K) (answer : K[X])
    (degree : answer.natDegree ≤ 28) :
    (derivativeCurve F t answer).natDegree ≤ trivariateYZWeight 28 F - 28 :=
  derivative_curve_degree 28 F t answer degree

#print axioms derivative_weight_le
#print axioms derivative_curve_degree
#print axioms width29_derivative_curve_degree
end
end AspisV8.FactorDerivativeWeight
