import SimplePolynomialRootRigidity
import SelectedIdentityCover

/-! Actual selected image-valid covered quotients on the same simple
factor branch have the same reconstructed original message. The shared OOD
value is derived from the literal source reconstruction, not supplied as a
candidate correspondence. No final is frozen before alpha, and no theorem
here makes the gamma-dependent message a polynomial component curve. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedSimpleRootRigidity
namespace Generic
open Polynomial
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisV8.FactorCoherence
variable {K : Type*} [Field K]

theorem derivative_at_point (F : TrivariatePolynomial K) (t gamma : K) (U : K[X]) :
    ((specializeChallenge gamma F).derivative.eval U).eval t =
      (specializeEvaluationPointChallenge t gamma F).derivative.eval (U.eval t) := by
  have derivativeMap : specializeChallenge gamma F.derivative =
      (specializeChallenge gamma F).derivative :=
    (Polynomial.derivative_map F (Polynomial.evalRingHom (C gamma))).symm
  calc
    _ = (challengeCandidateHom gamma U F.derivative).eval t := by
      change _ = ((specializeChallenge gamma F.derivative).eval U).eval t
      rw [derivativeMap]
    _ = (specializeEvaluationPointChallenge t gamma F.derivative).eval (U.eval t) :=
      (specializeEvaluationPointChallenge_eval_candidate F.derivative t gamma U).symm
    _ = _ := by rw [specializeEvaluationPointChallenge_derivative]

theorem candidate_unique (F : TrivariatePolynomial K) (t gamma : K) (answer U V : K[X])
    (leftRoot : challengeCandidateHom gamma U F = 0)
    (rightRoot : challengeCandidateHom gamma V F = 0)
    (leftPoint : U.eval t = answer.eval gamma)
    (rightPoint : V.eval t = answer.eval gamma)
    (regular : (derivativeCurve F t answer).eval gamma ≠ 0) : U = V := by
  apply SimplePolynomialRootRigidity.polynomial_roots_equal
    (specializeChallenge gamma F) t U V leftRoot rightRoot (leftPoint.trans rightPoint.symm)
  intro singular
  apply regular
  rw [derivativeCurve, pointSubstitution_eval,
    specializeEvaluationPointChallenge_derivative, ← leftPoint]
  exact (derivative_at_point F t gamma U).symm.trans singular
end Generic

open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7Tag73ExactGRSConversion
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.SelectedQuotientOriginal AspisV8.QuotientFamilySelected
open AspisV8.ComponentOODBinding AspisV8.SelectedOODGate
noncomputable section
abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Q and Q' can be different adaptive post-alpha choices. Membership in
the same factor is the explicit retained-branch restriction; equality of
their roots/messages is the conclusion, never a premise. -/
theorem original_unique (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, pointX d r ≠ -1) (gamma : K) (F : TrivariatePolynomial K)
    (Q Q' : Fin 1024 → K)
    (member : Q ∈ literalFamily (SelectedComponentGame.received c1 c2 d gamma))
    (member' : Q' ∈ literalFamily (SelectedComponentGame.received c1 c2 d gamma))
    (image : Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0)
    (image' : Q' 1023=0 ∧ d.b*Q' 1022-d.c*Q' 1021=0)
    (root : challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) F=0)
    (root' : challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original Q')) F=0)
    (r : Fin 2)
    (regular : (FactorCoherence.derivativeCurve F (point d r)
      (CurveOODGate.answerCurve (answers d r))).eval gamma ≠ 0) :
    (atGamma d gamma).original Q = (atGamma d gamma).original Q' := by
  have leftPoint := (SelectedIdentityCover.literal_candidate c1 c2 d checked circles west
    gamma Q member image).2 r
  have rightPoint := (SelectedIdentityCover.literal_candidate c1 c2 d checked circles west
    gamma Q' member' image').2 r
  apply exactCircleGRSPolynomial_injective
  exact Generic.candidate_unique F (point d r) gamma
    (CurveOODGate.answerCurve (answers d r))
    (exactCircleGRSPolynomial ((atGamma d gamma).original Q))
    (exactCircleGRSPolynomial ((atGamma d gamma).original Q'))
    root root' leftPoint rightPoint regular

/-- Uniformity across arbitrary indices includes adaptive alpha branches.
Only original-message uniqueness is concluded: no global component tuple,
quotient uniqueness, extraction algorithm, or probability is asserted. -/
theorem adaptive_original_unique {Index : Type*}
    (c1 : C1Received) (c2 : C2Received) (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, pointX d r ≠ -1) (gamma : K) (F : TrivariatePolynomial K)
    (Q : Index → Fin 1024 → K)
    (member : ∀ a, Q a ∈ literalFamily (SelectedComponentGame.received c1 c2 d gamma))
    (image : ∀ a, Q a 1023=0 ∧ d.b*Q a 1022-d.c*Q a 1021=0)
    (root : ∀ a, challengeCandidateHom gamma
      (exactCircleGRSPolynomial ((atGamma d gamma).original (Q a))) F=0)
    (r : Fin 2) (regular : (FactorCoherence.derivativeCurve F (point d r)
      (CurveOODGate.answerCurve (answers d r))).eval gamma ≠ 0) :
    ∀ a b, (atGamma d gamma).original (Q a) = (atGamma d gamma).original (Q b) := by
  intro a b
  exact original_unique c1 c2 d checked circles west gamma F (Q a) (Q b)
    (member a) (member b) (image a) (image b) (root a) (root b) r regular

#print axioms Generic.derivative_at_point
#print axioms Generic.candidate_unique
#print axioms original_unique
#print axioms adaptive_original_unique
end
end AspisV8.SelectedSimpleRootRigidity
