import MiddleSimpleInterpolationV2
import AspisFormal.K1.V7ExactCorrelatedAgreementFactorBudgets

/-! Candidate-root and degree interfaces of the new multiplicity-one
middle-only parent. Agreement is with the literal degree-28 received curves;
the candidate is arbitrary at the current gamma and is never moved before
its actual source selection. Selected encoder/support transport is separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.MiddleSimpleRoot
open Polynomial Finset
open AspisK1.V7Tag73ExactMultiplicityThreeGS
open AspisK1.V7ExactCorrelatedAgreementInterpolation
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.MiddleSimpleInterpolation
noncomputable section
variable {K : Type*} [Field K]

/-- Multiplicity one suffices: more ordinary roots than the substituted
polynomial's degree force the whole specialization to vanish. -/
theorem candidate_substitute_zero
    {n maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (positive : 0 < zBound) (lastRow : maximumDegree*ell ≤ weightedDegree)
    (points : Fin n → K) (injective : Function.Injective points)
    (lanes : Fin (curveDegree+1) → Fin n → K)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (kernel : simpleMap points lanes coefficients = 0)
    (gamma : K) (candidate : K[X]) (support : Finset (Fin n))
    (degree : candidate.natDegree ≤ maximumDegree)
    (large : weightedDegree < support.card)
    (agreement : ∀ i ∈ support,
      candidate.eval (points i) = (receivedCurvePolynomial lanes i).eval gamma) :
    interpolationSubstitute (specializeCurveCoefficients lastRow coefficients gamma)
      candidate = 0 := by
  classical
  let Q := interpolationSubstitute
    (specializeCurveCoefficients lastRow coefficients gamma) candidate
  by_contra nonzero
  have qNonzero : Q ≠ 0 := nonzero
  have roots : (support.image points).val ⊆ Q.roots := by
    intro x member
    obtain ⟨i, inSupport, rfl⟩ := Finset.mem_image.mp member
    apply (Polynomial.mem_roots qNonzero).mpr
    change Q.eval (points i) = 0
    rw [interpolationSubstitute_eval, agreement i inSupport,
      interpolationConstraint_specializeCurveCoefficients,
      constraint_zero positive points lanes coefficients kernel i,
      Polynomial.eval_zero]
  have imageCard : (support.image points).card = support.card :=
    Finset.card_image_iff.mpr injective.injOn
  have bound := Polynomial.card_le_degree_of_subset_roots roots
  rw [imageCard] at bound
  have degreeBound : Q.natDegree ≤ weightedDegree :=
    interpolationSubstitute_natDegree_le lastRow _ candidate degree
  exact Nat.not_lt_of_ge (bound.trans degreeBound) large

theorem candidate_root
    {n maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (positive : 0 < zBound) (lastRow : maximumDegree*ell ≤ weightedDegree)
    (points : Fin n → K) (injective : Function.Injective points)
    (lanes : Fin (curveDegree+1) → Fin n → K)
    (coefficients : CurveMonomialIndex maximumDegree curveDegree
      (weightedDegree+1) (ell+1) zBound → K)
    (kernel : simpleMap points lanes coefficients = 0)
    (gamma : K) (candidate : K[X]) (support : Finset (Fin n))
    (degree : candidate.natDegree ≤ maximumDegree)
    (large : weightedDegree < support.card)
    (agreement : ∀ i ∈ support,
      candidate.eval (points i) = (receivedCurvePolynomial lanes i).eval gamma) :
    challengeCandidateHom gamma candidate (curveTrivariatePolynomial coefficients) = 0 := by
  change substituteCandidate candidate
    (specializeChallenge gamma (curveTrivariatePolynomial coefficients)) = 0
  rw [specializeChallenge_curveTrivariatePolynomial lastRow coefficients gamma,
    substituteCandidate_weightedBivariatePolynomial]
  exact candidate_substitute_zero positive lastRow points injective lanes coefficients
    kernel gamma candidate support degree large agreement

abbrev Coefficients (K : Type*) := CurveMonomialIndex 1024 28 803230 2 41 → K

theorem middle_root (points : Fin 1048576 → K)
    (injective : Function.Injective points) (lanes : Fin 29 → Fin 1048576 → K)
    (coefficients : Coefficients K) (kernel : simpleMap points lanes coefficients = 0)
    (gamma : K) (candidate : K[X]) (support : Finset (Fin 1048576))
    (degree : candidate.natDegree ≤ 1024) (large : 803230 ≤ support.card)
    (agreement : ∀ i ∈ support,
      candidate.eval (points i) = (receivedCurvePolynomial lanes i).eval gamma) :
    challengeCandidateHom gamma candidate (curveTrivariatePolynomial coefficients) = 0 :=
  candidate_root (by decide : 0 < 41) (by decide : 1024*1 ≤ 803229)
    points injective lanes coefficients kernel gamma candidate support degree
    (by omega) agreement

theorem parent_nonzero (coefficients : Coefficients K) (nonzero : coefficients ≠ 0) :
    curveTrivariatePolynomial coefficients ≠ 0 :=
  curveTrivariatePolynomial_ne_zero coefficients nonzero

theorem parent_y_degree (coefficients : Coefficients K) :
    (curveTrivariatePolynomial coefficients).natDegree ≤ 1 :=
  Nat.le_of_lt_succ (curveTrivariatePolynomial_natDegree_lt (by decide : 0 < 2) coefficients)

theorem parent_x_degree (coefficients : Coefficients K) :
    (trivariateXOuterEquiv K (curveTrivariatePolynomial coefficients)).natDegree ≤ 803229 :=
  Nat.le_of_lt_succ (curveTrivariatePolynomial_xNatDegree_lt
    (by decide : 0 < 803230) coefficients)

theorem parent_yz_weight (coefficients : Coefficients K) :
    trivariateYZWeight 28 (curveTrivariatePolynomial coefficients) ≤ 40 :=
  Nat.le_of_lt_succ (trivariateYZWeight_curveTrivariatePolynomial_lt
    (by decide : 0 < 41) coefficients)

/-- Abstract the parent before comparing factor degrees, so this symbolic
argument never unfolds the large finite coefficient representation. -/
theorem positive_factor_linear_of_parent (P F : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (small : P.natDegree ≤ 1)
    (member : F ∈ curvePrimeFactors P) (positive : 0 < F.natDegree) :
    F.natDegree = 1 := by
  have upper : F.natDegree ≤ 1 :=
    (curvePrimeFactor_natDegree_le P F nonzero member).trans small
  exact Nat.le_antisymm upper (Nat.succ_le_iff.mpr positive)

/-- A positive-Y retained factor of this auxiliary parent must be linear.
This excludes higher Y degrees without a polynomiality or factor-selection
assumption on any candidate. -/
set_option maxRecDepth 512 in
theorem positive_factor_linear (coefficients : Coefficients K) (nonzero : coefficients ≠ 0)
    (F : TrivariatePolynomial K)
    (member : F ∈ curvePrimeFactors (curveTrivariatePolynomial coefficients))
    (positive : 0 < F.natDegree) : F.natDegree = 1 :=
  positive_factor_linear_of_parent (curveTrivariatePolynomial coefficients) F
    (parent_nonzero coefficients nonzero) (parent_y_degree coefficients) member positive

#print axioms candidate_substitute_zero
#print axioms candidate_root
#print axioms middle_root
#print axioms parent_nonzero
#print axioms parent_y_degree
#print axioms parent_x_degree
#print axioms parent_yz_weight
#print axioms positive_factor_linear_of_parent
#print axioms positive_factor_linear
end
end AspisV8.MiddleSimpleRoot
