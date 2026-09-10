import SingularOODResultant
import FactorDerivativeWeight

/-! A fixed prime factor supplies a canonical pre-OOD obstruction: the
leading Z-coefficient of its derived Y-resultant. Outside roots of this
fixed X-polynomial, an actual retained OOD answer has a nonzero derivative
curve. This gives the small gamma-degree bound without assuming actual-point
regularity, a candidate curve, or any constraint on post-alpha choices.

Source-review draft only; no compilation is claimed here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.SingularOODCoefficient
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.FactorCoherence
open AspisV8.FactorIdentityCover
open AspisV8.FactorDerivativeWeight
open AspisV5ComponentCQM31TowerExact
noncomputable section
variable {K : Type*} [Field K]

/-- The resultant is outer Z, inner X. Its leading coefficient is selected
from F alone, before either actual OOD point or answer is supplied. -/
def obstruction (F : TrivariatePolynomial K) : K[X] :=
  (separabilityCertificate F).leadingCoeff

theorem obstruction_nonzero (P F : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (positive : 0 < F.natDegree) (derivative : F.derivative ≠ 0) :
    obstruction F ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr
    (separabilityCertificate_ne_zero P F nonzero member positive derivative)

/-- The fixed certificate's coefficient uses the X budget, not its much
larger Z degree. Only the positive Y degree is needed for this inequality. -/
theorem obstruction_degree (F : TrivariatePolynomial K)
    (positive : 0 < F.natDegree) :
    (obstruction F).natDegree ≤
      (2 * F.natDegree - 1) * (trivariateXOuterEquiv K F).natDegree := by
  have coefficientBound := coeff_natDegree_le_bivariate_swap_natDegree
    (separabilityCertificate F) (separabilityCertificate F).natDegree
  have resultantBound := separabilityCertificate_xNatDegree_le F
  have derivativeBound := Polynomial.natDegree_derivative_le F
  have sizeBound : F.natDegree + F.derivative.natDegree ≤ 2 * F.natDegree - 1 := by
    omega
  exact (coefficientBound.trans resultantBound).trans
    (Nat.mul_le_mul_right _ sizeBound)

/-- Literal variable-order transport. No equality of finite-field functions
is substituted for an identity of polynomials. -/
theorem obstruction_vanishes (F : TrivariatePolynomial K) (t : K)
    (vanishes : (Polynomial.Bivariate.swap (separabilityCertificate F)).eval
      (C t) = 0) :
    (obstruction F).eval t = 0 := by
  have coefficient := coeff_swap_eval
    (Polynomial.Bivariate.swap (separabilityCertificate F))
    (separabilityCertificate F).natDegree t
  rw [Polynomial.Bivariate.swap_swap_apply, vanishes, Polynomial.coeff_zero]
    at coefficient
  exact coefficient

theorem singular_obstruction (F : TrivariatePolynomial K)
    (positive : 0 < F.natDegree) (t : K) (answer : K[X])
    (identity : pointSubstitution t answer F = 0)
    (singular : derivativeCurve F t answer = 0) :
    (obstruction F).eval t = 0 :=
  obstruction_vanishes F t
    (SingularOODResultant.source_singular_certificate F positive t answer
      identity singular)

theorem derivative_nonzero_of_obstruction (F : TrivariatePolynomial K)
    (positive : 0 < F.natDegree) (t : K) (answer : K[X])
    (identity : pointSubstitution t answer F = 0)
    (notRoot : (obstruction F).eval t ≠ 0) :
    derivativeCurve F t answer ≠ 0 := by
  intro singular
  exact notRoot (singular_obstruction F positive t answer identity singular)

/-- Larger than any candidate-qualified singular event: both actual
derivative evaluations vanish, without imposing a candidate or support. -/
def bothSingular (F : TrivariatePolynomial K)
    (points : Fin 2 → K) (answers : Fin 2 → K[X]) (Gamma : Finset K) : Finset K := by
  classical
  exact Gamma.filter fun gamma =>
    ∀ r, (derivativeCurve F (points r) (answers r)).eval gamma = 0

/-- Either both actual points hit the fixed pre-OOD obstruction, or one
row's nonzero polynomial bounds the simultaneous singular gamma event.
The answer degree c is the full claim degree, not the local helper degree. -/
theorem both_singular_bound_or (c : Nat) (F : TrivariatePolynomial K)
    (points : Fin 2 → K) (answers : Fin 2 → K[X]) (Gamma : Finset K)
    (retained : Retained points answers F)
    (degrees : ∀ r, (answers r).natDegree ≤ c) :
    (∀ r, (obstruction F).eval (points r) = 0) ∨
      (bothSingular F points answers Gamma).card ≤ trivariateYZWeight c F - c := by
  classical
  by_cases allRoots : ∀ r, (obstruction F).eval (points r) = 0
  · exact Or.inl allRoots
  · right
    obtain ⟨r, notRoot⟩ : ∃ r, (obstruction F).eval (points r) ≠ 0 := by
      simpa only [not_forall] using allRoots
    have nonzero := derivative_nonzero_of_obstruction F retained.1
      (points r) (answers r) (retained.2 r) notRoot
    apply (Polynomial.card_le_degree_of_subset_roots
      (p := derivativeCurve F (points r) (answers r)) ?_).trans
      (derivative_curve_degree c F (points r) (answers r) (degrees r))
    intro gamma member
    exact (Polynomial.mem_roots nonzero).mpr ((Finset.mem_filter.mp member).2 r)

/-- Reuse the deployed V7 characteristic guard. No nonzero derivative is
assumed for an actual prime factor in the selected degree range. -/
theorem exactV7_obstruction_nonzero (P F : TrivariatePolynomial QM31Exact)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (positive : 0 < F.natDegree) (parentDegree : P.natDegree < 113) :
    obstruction F ≠ 0 :=
  obstruction_nonzero P F nonzero member positive
    (exactV7_curvePrimeFactor_derivative_ne_zero P F nonzero member positive parentDegree)

/-- The nonzero obstruction and its degree are established before the
universal actual OOD arguments. No chosen smooth point, supplied resultant,
component membership, received polynomiality, or pre-alpha final occurs. -/
theorem exactV7_obstruction_control (P F : TrivariatePolynomial QM31Exact)
    (nonzero : P ≠ 0) (member : F ∈ curvePrimeFactors P)
    (positive : 0 < F.natDegree) (parentDegree : P.natDegree < 113) :
    obstruction F ≠ 0 ∧
      (obstruction F).natDegree ≤
        (2 * F.natDegree - 1) * (trivariateXOuterEquiv QM31Exact F).natDegree ∧
      ∀ (points : Fin 2 → QM31Exact) (answers : Fin 2 → QM31Exact[X])
        (Gamma : Finset QM31Exact), Retained points answers F →
        (∀ r, (answers r).natDegree ≤ 28) →
        (∀ r, (obstruction F).eval (points r) = 0) ∨
          (bothSingular F points answers Gamma).card ≤ trivariateYZWeight 28 F - 28 := by
  refine ⟨exactV7_obstruction_nonzero P F nonzero member positive parentDegree,
    obstruction_degree F positive, ?_⟩
  intro points answers Gamma retained degrees
  exact both_singular_bound_or 28 F points answers Gamma retained degrees

#print axioms obstruction_nonzero
#print axioms obstruction_degree
#print axioms obstruction_vanishes
#print axioms singular_obstruction
#print axioms derivative_nonzero_of_obstruction
#print axioms both_singular_bound_or
#print axioms exactV7_obstruction_nonzero
#print axioms exactV7_obstruction_control
end
end AspisV8.SingularOODCoefficient
