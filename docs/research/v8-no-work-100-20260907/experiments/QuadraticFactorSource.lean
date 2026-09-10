import FactorIdentityCover
import QuadraticConstructedParity

/-!
Literal variable-order bridge from the maintained trivariate factor maps
to the quadratic parity root event. The source ring is K[X][Z][Y]; each
Y coefficient is swapped to K[Z][X], then Z is specialized coefficientwise.
No verifier-acceptance or root-correspondence premise is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.QuadraticFactorSource
noncomputable section
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementRegularWeights
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets

/-- The three actual coefficient terms, over a coefficient ring rather
than an incorrectly assumed field of bivariate polynomials. -/
theorem quadratic_shape {R : Type*} [CommRing R]
    (F : R[X]) (degree : F.natDegree ≤ 2) :
    F = C (F.coeff 2)*X^2 + C (F.coeff 1)*X + C (F.coeff 0) := by
  have finite := F.as_sum_range_C_mul_X_pow' (n := 3) (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one, pow_one] at finite
  calc
    F = C (F.coeff 0) + C (F.coeff 1)*X + C (F.coeff 2)*X^2 := finite
    _ = C (F.coeff 2)*X^2 + C (F.coeff 1)*X + C (F.coeff 0) := by ac_rfl

variable {K : Type*} [Field K]

/-- In the source map Z is evaluated at C gamma. In the parity consumer
the same operation maps eval gamma over swapped X coefficients. -/
theorem coefficient_specialization (P : BivariatePolynomial K) (gamma : K) :
    P.eval (C gamma) = (Polynomial.Bivariate.swap P).map (Polynomial.evalRingHom gamma) := by
  ext i
  rw [Polynomial.coeff_map]
  exact (FactorIdentityCover.coeff_swap_eval P i gamma).symm

private theorem candidate_C (P : BivariatePolynomial K) (gamma : K) (U : K[X]) :
    challengeCandidateHom gamma U (C P) = P.eval (C gamma) := by
  simp only [challengeCandidateHom, RingHom.coe_comp, Function.comp_apply,
    specializeChallenge, Polynomial.coe_mapRingHom, Polynomial.map_C,
    substituteCandidate, Polynomial.coe_evalRingHom, Polynomial.eval_C]

private theorem candidate_X (gamma : K) (U : K[X]) :
    challengeCandidateHom gamma U (X : TrivariatePolynomial K) = U := by
  simp only [challengeCandidateHom, RingHom.coe_comp, Function.comp_apply,
    specializeChallenge, Polynomial.coe_mapRingHom, Polynomial.map_X,
    substituteCandidate, Polynomial.coe_evalRingHom, Polynomial.eval_X]

/-- The exact value identity, stronger than only transferring zero. It
uses the actual specialization and candidate homomorphisms. -/
theorem candidate_value (F : TrivariatePolynomial K) (degree : F.natDegree ≤ 2)
    (gamma : K) (U : K[X]) :
    challengeCandidateHom gamma U F =
      (Polynomial.Bivariate.swap (F.coeff 2)).map (Polynomial.evalRingHom gamma) * U^2 +
      (Polynomial.Bivariate.swap (F.coeff 1)).map (Polynomial.evalRingHom gamma) * U +
      (Polynomial.Bivariate.swap (F.coeff 0)).map (Polynomial.evalRingHom gamma) := by
  have evaluated := congrArg (challengeCandidateHom gamma U) (quadratic_shape F degree)
  simpa only [map_add, map_mul, map_pow, candidate_C, candidate_X,
    coefficient_specialization] using evaluated

/-- The same adaptive U is the existential witness of RootsAt. Degree two
is the literal outer Y degree, not an assumed quadratic template. -/
theorem candidate_root (F : TrivariatePolynomial K) (degree : F.natDegree = 2)
    (gamma : K) (U : K[X]) (root : challengeCandidateHom gamma U F = 0) :
    QuadraticConstructedParity.RootsAt
      (Polynomial.Bivariate.swap (F.coeff 2))
      (Polynomial.Bivariate.swap (F.coeff 1))
      (Polynomial.Bivariate.swap (F.coeff 0)) gamma := by
  refine ⟨U, ?_⟩
  exact (candidate_value F degree.le gamma U).symm.trans root

/-- Every actual Y coefficient has Z degree at most the maintained
weighted curve degree. Zero coefficients are handled explicitly. -/
theorem coefficient_degree_le_weight (F : TrivariatePolynomial K)
    (curveDegree i : Nat) :
    (F.coeff i).natDegree ≤ trivariateYZWeight curveDegree F := by
  by_cases zero : F.coeff i = 0
  · rw [zero, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · have weighted := coeff_weight_le_localBivariateWeight curveDegree F i
      (Polynomial.mem_support_iff.mpr zero)
    change (F.coeff i).natDegree ≤ localBivariateWeight curveDegree F
    omega

/-- Literal discriminant in the parity consumer's K[Z][X] order. -/
def discriminant (F : TrivariatePolynomial K) : Polynomial K[X] :=
  (Polynomial.Bivariate.swap (F.coeff 1))^2 -
    4 * Polynomial.Bivariate.swap (F.coeff 2) * Polynomial.Bivariate.swap (F.coeff 0)

/-- Challenge degree of the actual discriminant is at most twice the
existing factor weight. This holds for every curveDegree, in particular 28;
no degree-2 helper substitution is used for the full batching challenge. -/
theorem discriminant_degree_le_weight (F : TrivariatePolynomial K) (curveDegree : Nat) :
    (Polynomial.Bivariate.swap (discriminant F)).natDegree ≤
      2 * trivariateYZWeight curveDegree F := by
  have a := coefficient_degree_le_weight F curveDegree 2
  have b := coefficient_degree_le_weight F curveDegree 1
  have c := coefficient_degree_le_weight F curveDegree 0
  have square := Polynomial.natDegree_pow_le (p := F.coeff 1) (n := 2)
  have leftProduct := Polynomial.natDegree_mul_le
    (p := (4 : BivariatePolynomial K)) (q := F.coeff 2)
  have product := Polynomial.natDegree_mul_le (p := 4 * F.coeff 2) (q := F.coeff 0)
  have difference := Polynomial.natDegree_sub_le ((F.coeff 1)^2) (4 * F.coeff 2 * F.coeff 0)
  simp only [Polynomial.natDegree_ofNat] at leftProduct
  simp only [discriminant, map_sub, map_pow, map_mul, map_ofNat,
    Polynomial.Bivariate.swap_swap_apply]
  omega

#print axioms quadratic_shape
#print axioms coefficient_specialization
#print axioms candidate_value
#print axioms candidate_root
#print axioms coefficient_degree_le_weight
#print axioms discriminant_degree_le_weight
end
end AspisV8.QuadraticFactorSource
