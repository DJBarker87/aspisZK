import Wide.OuterSelection

/-!
# Generic final specialization root
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisWide.Terminal

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]


open Polynomial
open AspisWide.MultiplicityThreeGS
open AspisWide.Agreement
open AspisWide.Interpolation
open AspisWide.Factors
open AspisWide.LocalFactors
open AspisWide.Smooth
open AspisWide.FunctionField
open AspisWide.PowerSeriesLift
open AspisWide.RegularHensel
open AspisWide.FactorBudgets
open AspisWide.ConcreteBranch
open AspisWide.OuterSelection
open AspisWide.GRSConversion
open AspisWide.FinalEncoder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisCircleGroupOrder (P)

noncomputable section

/-- Symbolic bridge between the interpolation module's specialized
bivariate polynomial and the factor module's trivariate candidate-root map. -/
theorem final_challengeCandidateHom_curveTrivariatePolynomial_eq_zero
    {K : Type*} [Field K]
    {maximumDegree curveDegree weightedDegree ell zBound : Nat}
    (lastRow : maximumDegree * ell ≤ weightedDegree)
    (coefficients :
      CurveMonomialIndex maximumDegree curveDegree (weightedDegree + 1)
        (ell + 1) zBound → K)
    (z : K) (candidate : K[X])
    (root : interpolationSubstitute
      (specializeCurveCoefficients lastRow coefficients z) candidate = 0) :
    challengeCandidateHom z candidate
      (curveTrivariatePolynomial coefficients) = 0 := by
  change substituteCandidate candidate
      (specializeChallenge z (curveTrivariatePolynomial coefficients)) = 0
  rw [specializeChallenge_curveTrivariatePolynomial lastRow coefficients z]
  rw [substituteCandidate_weightedBivariatePolynomial]
  exact root


set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
-- Keep the concrete specialization opaque after the symbolic rewrite.
/-- Convert the exact final interpolation-specialization statement to the
branch selector's trivariate root convention.  This declaration is kept
opaque so its large dependent interpolation indices are checked once. -/
theorem exactFinal_challengeCandidateHom_eq_zero
    (lanes : Fin 4 → FinalWord E)
    (strategy : ProximateStrategy E (Fin 262144)
      (FinalMessage E))
    (coefficients :
      CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
        finalCurveZBound → E)
    (kernel : curveInterpolationMap (exactFinalGRSConversion (K := E)).points
      lanes coefficients = 0)
    (gamma : E)
    (valid : ValidResponse exactFinalEncoder 9557 lanes strategy
      gamma) :
    challengeCandidateHom gamma
      ((exactFinalGRSConversion (K := E)).messagePolynomial
        (strategy.candidate gamma))
      (curveTrivariatePolynomial coefficients) = 0 := by
  have root := exactFinalValidCandidate_substitute_eq_zero lanes strategy
    coefficients kernel gamma valid
  exact final_challengeCandidateHom_curveTrivariatePolynomial_eq_zero
    (by norm_num [finalCurveXBound, finalCurveYRows]) coefficients gamma
      ((exactFinalGRSConversion (K := E)).messagePolynomial (strategy.candidate gamma))
        root

#print axioms final_challengeCandidateHom_curveTrivariatePolynomial_eq_zero
#print axioms exactFinal_challengeCandidateHom_eq_zero

end

end AspisWide.Terminal
