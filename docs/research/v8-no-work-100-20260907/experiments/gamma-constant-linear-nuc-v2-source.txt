import MonicFactorOOD
import Mathlib.RingTheory.Localization.FractionRing

/-! Linear-Y factors with gamma-constant, possibly nonconstant-in-X
denominators. The rational root is constructed, not assumed. If its
numerator exceeds the OOD answer degree, a fixed coefficient obstruction
applies even when the denominator vanishes at the OOD point. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.GammaConstantLinear
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV8.FactorCoherence AspisV8.FactorIdentityCover
noncomputable section
variable {K : Type*} [Field K]

theorem leading_coefficient_ne_zero (F : TrivariatePolynomial K)
    (linear : F.natDegree = 1) : F.coeff 1 ≠ 0 := by
  rw [← linear]
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro zero
  simp only [zero, Polynomial.natDegree_zero] at linear
  omega

theorem constant_coefficient_ne_zero (A : Polynomial K[X])
    (constant : A.natDegree = 0) (nonzero : A ≠ 0) : A.coeff 0 ≠ 0 := by
  intro zero
  apply nonzero
  rw [Polynomial.eq_C_of_natDegree_eq_zero constant, zero, Polynomial.C_0]

/-- The only inversion is in K(X), a mathematical analysis field. It is
not a new prover/verifier field or an unchecked inverse witness. -/
def rationalRoot (A B : Polynomial K[X]) : Polynomial (FractionRing K[X]) :=
  C (-(algebraMap K[X] (FractionRing K[X]) (A.coeff 0))⁻¹) *
    B.map (algebraMap K[X] (FractionRing K[X]))

theorem rationalRoot_degree (A B : Polynomial K[X]) :
    (rationalRoot A B).natDegree ≤ B.natDegree :=
  Polynomial.natDegree_C_mul_le _ _ |>.trans Polynomial.natDegree_map_le

theorem rationalRoot_equation (A B : Polynomial K[X])
    (constant : A.natDegree = 0) (nonzero : A ≠ 0) :
    A.map (algebraMap K[X] (FractionRing K[X])) * rationalRoot A B +
      B.map (algebraMap K[X] (FractionRing K[X])) = 0 := by
  have injective := IsFractionRing.injective K[X] (FractionRing K[X])
  have scalarNonzero : algebraMap K[X] (FractionRing K[X]) (A.coeff 0) ≠ 0 := by
    simpa only [map_zero] using
      injective.ne (constant_coefficient_ne_zero A constant nonzero)
  unfold rationalRoot
  conv_lhs => lhs; lhs; rw [Polynomial.eq_C_of_natDegree_eq_zero constant]
  rw [Polynomial.map_C, ← mul_assoc, ← Polynomial.C_mul]
  simp only [mul_neg, mul_inv_cancel₀ scalarNonzero, Polynomial.C_neg,
    Polynomial.C_1]
  ring

theorem linear_ood_equation (F : TrivariatePolynomial K)
    (linear : F.natDegree = 1) (x : K) (answer : K[X])
    (identity : pointSubstitution x answer F = 0) :
    (F.coeff 1).map (Polynomial.evalRingHom x) * answer +
      (F.coeff 0).map (Polynomial.evalRingHom x) = 0 := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one linear.le] at identity
  simpa only [pointSubstitution, RingHom.coe_comp, Function.comp_apply,
    specializeEvaluationPoint, Polynomial.coe_mapRingHom, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, evaluateInnerVariable] using identity

theorem coefficient_x_degree (F : TrivariatePolynomial K) (i j : Nat) :
    ((F.coeff i).coeff j).natDegree ≤ (trivariateXOuterEquiv K F).natDegree := by
  have bound := reorderFactorCoefficients_coeff_natDegree_le F i
  have inner := coeff_natDegree_le_bivariate_swap_natDegree (F.coeff i) j
  have bound' : (Polynomial.Bivariate.swap (F.coeff i)).natDegree ≤
      (trivariateXOuterEquiv K F).natDegree := by
    rw [reorderFactorCoefficients, Polynomial.coeff_map] at bound
    exact bound
  exact inner.trans bound'

/-- H is chosen from the fixed F alone. No monicity and no nonvanishing
of A at x are assumed. The actual OOD answer may depend on x. -/
theorem excess_numerator_obstruction (degree : Nat) (F : TrivariatePolynomial K)
    (constant : (F.coeff 1).natDegree = 0)
    (excess : degree < (F.coeff 0).natDegree) :
    ∃ H : K[X], H ≠ 0 ∧ H.natDegree ≤ (trivariateXOuterEquiv K F).natDegree ∧
      ∀ x (answer : K[X]), F.natDegree = 1 → answer.natDegree ≤ degree →
        pointSubstitution x answer F = 0 → H.eval x = 0 := by
  let j := (F.coeff 0).natDegree
  have nonzero : F.coeff 0 ≠ 0 := by
    intro zero
    simp only [zero, Polynomial.natDegree_zero] at excess
    omega
  refine ⟨(F.coeff 0).coeff j, Polynomial.leadingCoeff_ne_zero.mpr nonzero,
    coefficient_x_degree F 0 j, ?_⟩
  intro x answer linear answerDegree identity
  have equation := linear_ood_equation F linear x answer identity
  rw [Polynomial.eq_C_of_natDegree_eq_zero constant, Polynomial.map_C] at equation
  have coefficient := congrArg (fun p : K[X] => p.coeff j) equation
  have firstZero : (C ((Polynomial.evalRingHom x) ((F.coeff 1).coeff 0)) *
      answer).coeff j = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      ((Polynomial.natDegree_C_mul_le _ _).trans answerDegree |>.trans_lt excess)
  rw [Polynomial.coeff_add, firstZero, zero_add, Polynomial.coeff_map,
    Polynomial.coeff_zero] at coefficient
  exact coefficient

#print axioms leading_coefficient_ne_zero
#print axioms constant_coefficient_ne_zero
#print axioms rationalRoot_degree
#print axioms rationalRoot_equation
#print axioms linear_ood_equation
#print axioms coefficient_x_degree
#print axioms excess_numerator_obstruction
end
end AspisV8.GammaConstantLinear
