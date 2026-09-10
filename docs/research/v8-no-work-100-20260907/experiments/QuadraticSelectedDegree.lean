import QuadraticFactorSource
import SelectedMonicCover

/-!
Actual X-degree guard for the selected quadratic source discriminant.
The generic coefficient bound is the pinned V7 reorder theorem. The
selected field is used only to instantiate already-symbolic degree bounds;
no field elements or large finite universes are normalized.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticSelectedDegree
noncomputable section
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth

/-- These are exactly the K[Z][X] coefficient polynomials used by
QuadraticFactorSource, bounded by the source factor's genuine X degree. -/
theorem coefficient_x_degree_le {K : Type*} [Field K]
    (F : TrivariatePolynomial K) (i : Nat) :
    (Polynomial.Bivariate.swap (F.coeff i)).natDegree ≤
      (trivariateXOuterEquiv K F).natDegree := by
  have bound := reorderFactorCoefficients_coeff_natDegree_le F i
  simpa only [reorderFactorCoefficients, Polynomial.coeff_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv] using bound

/-- Symbolic discriminant degree, with no quadratic-degree or nonzero
coefficient assumption needed. Cancellation can only lower the degree. -/
theorem discriminant_x_degree_le {K : Type*} [Field K]
    (F : TrivariatePolynomial K) :
    (QuadraticFactorSource.discriminant F).natDegree ≤
      2 * (trivariateXOuterEquiv K F).natDegree := by
  have a := coefficient_x_degree_le F 2
  have b := coefficient_x_degree_le F 1
  have c := coefficient_x_degree_le F 0
  have square := Polynomial.natDegree_pow_le
    (p := Polynomial.Bivariate.swap (F.coeff 1)) (n := 2)
  have leftProduct := Polynomial.natDegree_mul_le
    (p := (4 : BivariatePolynomial K)) (q := Polynomial.Bivariate.swap (F.coeff 2))
  have product := Polynomial.natDegree_mul_le
    (p := 4 * Polynomial.Bivariate.swap (F.coeff 2))
    (q := Polynomial.Bivariate.swap (F.coeff 0))
  have difference := Polynomial.natDegree_sub_le
    ((Polynomial.Bivariate.swap (F.coeff 1))^2)
    (4 * Polynomial.Bivariate.swap (F.coeff 2) * Polynomial.Bivariate.swap (F.coeff 0))
  simp only [Polynomial.natDegree_ofNat] at leftProduct
  unfold QuadraticFactorSource.discriminant
  omega

private abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
attribute [local irreducible] curvePrimeFactors
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.SelectedFactorCoherence AspisV8.SelectedOODGate
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- The factor is from the actual C1/C2-only family, not an arbitrary
bounded-degree replacement. Its parent's existing X cap supplies 229374. -/
theorem selected_discriminant_x_degree_le
    (c1 : C1Received) (c2 : C2Received) (F : TrivariatePolynomial K)
    (member : F ∈ curvePrimeFactors (parent c1 c2)) :
    (QuadraticFactorSource.discriminant F).natDegree ≤ 229374 := by
  have nonzero : parent c1 c2 ≠ 0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  have factorBound := curvePrimeFactor_xNatDegree_le (K := K) (parent c1 c2) F nonzero member
  have parentBound : (trivariateXOuterEquiv K (parent c1 c2)).natDegree ≤ 114687 := by
    simpa only [K, SelectedReceivedOracle.K] using SelectedMonicCover.parent_x_degree c1 c2
  have discriminantBound := discriminant_x_degree_le F
  omega

/-- The numeric characteristic-degree premise of the source dichotomy
is derived for every member of the fixed selected family. This does not
assert verifier acceptance, Y degree two, or a sampler law. -/
theorem selected_discriminant_lt_characteristic
    (c1 : C1Received) (c2 : C2Received) (F : TrivariatePolynomial K)
    (member : F ∈ curvePrimeFactors (parent c1 c2)) :
    (QuadraticFactorSource.discriminant F).natDegree < 2147483647 := by
  have bound := selected_discriminant_x_degree_le c1 c2 F member
  omega

#print axioms coefficient_x_degree_le
#print axioms discriminant_x_degree_le
#print axioms selected_discriminant_x_degree_le
#print axioms selected_discriminant_lt_characteristic
end
end AspisV8.QuadraticSelectedDegree
