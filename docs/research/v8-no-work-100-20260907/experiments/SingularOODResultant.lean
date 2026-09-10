import FactorCoherence
import Mathlib.RingTheory.Localization.FractionRing

/-! A whole actual OOD answer identity and derivative identity force the
derived V7 resultant certificate to vanish at that same point. The generic
predecessor passes through the fraction field of the coefficient domain;
it retains explicit degree bounds, including all specialization degree-drop
and zero-polynomial cases. No supplied certificate or candidate curve.

Draft only: source-reviewed, not compiled.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.SingularOODResultant
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV8.FactorCoherence
noncomputable section

/-- The borrowed common-root theorem is over a field. Embed the entire
coefficient domain injectively into its fraction field, preserving roots and
the supplied upper degree bounds, then pull its zero resultant back. The
positive first bound excludes the exceptional 0-by-0 determinant. -/
theorem common_root_resultant_zero {R : Type*} [CommRing R] [IsDomain R]
    (left right : R[X]) (leftDegree rightDegree : Nat) (root : R)
    (positive : 0 < leftDegree)
    (leftBound : left.natDegree ≤ leftDegree)
    (rightBound : right.natDegree ≤ rightDegree)
    (leftRoot : left.eval root=0) (rightRoot : right.eval root=0) :
    Polynomial.resultant left right leftDegree rightDegree=0 := by
  let phi : R →+* FractionRing R := algebraMap R (FractionRing R)
  have injective : Function.Injective phi := IsFractionRing.injective _ _
  have mapRoot : ∀ p : R[X], p.eval root=0 →
      (p.map phi).eval (phi root)=0 := by
    intro p zero
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, zero, map_zero]
  have mappedZero := resultant_eq_zero_of_common_root_of_natDegree_le
    (left.map phi) (right.map phi) leftDegree rightDegree (phi root) positive
    (Polynomial.natDegree_map_le.trans leftBound)
    (Polynomial.natDegree_map_le.trans rightBound)
    (mapRoot left leftRoot) (mapRoot right rightRoot)
  apply injective
  rw [map_zero]
  exact (Polynomial.resultant_map_map left right leftDegree rightDegree phi).symm.trans
    mappedZero

/-- Source-shaped endpoint: both equations are polynomial identities in
gamma along the literal actual answer A. The RESULT is vanishing of the
derived certificate at the actual OOD point t; no nonvanishing/full-resultant
premise and no chosen horizontal candidate occurs. -/
theorem source_singular_certificate {K : Type*} [Field K]
    (F : TrivariatePolynomial K) (positive : 0 < F.natDegree)
    (t : K) (answer : K[X])
    (identity : pointSubstitution t answer F=0)
    (singular : derivativeCurve F t answer=0) :
    (Polynomial.Bivariate.swap (separabilityCertificate F)).eval (C t)=0 := by
  rw [← specialized_resultant_eq_certificate_eval_x]
  apply common_root_resultant_zero
    (specializeEvaluationPoint t F) (specializeEvaluationPoint t F.derivative)
    F.natDegree F.derivative.natDegree answer positive
  · exact Polynomial.natDegree_map_le
  · exact Polynomial.natDegree_map_le
  · exact identity
  · exact singular

#print axioms common_root_resultant_zero
#print axioms source_singular_certificate
end
end AspisV8.SingularOODResultant
