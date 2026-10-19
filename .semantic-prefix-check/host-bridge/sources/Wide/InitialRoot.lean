import Wide.Terminal

/-!
# Exact initial V7 specialization root
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

structure Width29GoodChallengePackage
    (K Domain Message : Type*)
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) where
  challenges : Finset K
  challenges_eq : challenges =
    width29GoodChallenges encoder agreementThreshold lanes strategy
  valid : ∀ gamma ∈ challenges,
    gamma ≠ 0 ∧ Width29ValidResponse encoder agreementThreshold lanes strategy gamma

noncomputable def packageWidth29GoodChallenges
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 29 → Domain → K)
    (strategy : Width29ProximateStrategy K Domain Message) :
    Width29GoodChallengePackage K Domain Message encoder agreementThreshold
      lanes strategy where
  challenges := width29GoodChallenges encoder agreementThreshold lanes strategy
  challenges_eq := rfl
  valid := by
    intro gamma member
    exact (mem_width29GoodChallenges_iff encoder agreementThreshold lanes
      strategy gamma).mp member

/-- Symbolic bridge between the interpolation module's specialized
bivariate polynomial and the factor module's trivariate candidate-root map. -/
theorem challengeCandidateHom_curveTrivariatePolynomial_eq_zero
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
set_option maxHeartbeats 2000000 in
-- The exact `Fin 1024`/width-29 dependent indices make normalization of the
-- specialized initial interpolant substantially more expensive than the
-- generic symbolic bridge above.
/-- Convert the exact initial interpolation-specialization statement to the
branch selector's trivariate root convention.  This declaration is kept
opaque so its large dependent interpolation indices are checked once. -/
theorem exactInitial_challengeCandidateHom_eq_zero
    (lanes : Fin 29 → InitialWord E)
    (strategy : Width29ProximateStrategy E (Fin 1048576)
      (InitialMessage E))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → E)
    (kernel : curveInterpolationMap (exactInitialGRSConversion (K := E)).points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (gamma : E)
    (valid : Width29ValidResponse exactInitialEncoder 38229 lanes strategy
      gamma) :
    challengeCandidateHom gamma
      ((exactInitialGRSConversion (K := E)).messagePolynomial
        (strategy.candidate gamma))
      (curveTrivariatePolynomial coefficients) = 0 := by
  have root := exactInitialValidCandidate_substitute_eq_zero lanes strategy
    coefficients kernel gamma valid
  exact challengeCandidateHom_curveTrivariatePolynomial_eq_zero
    (by norm_num [initialCurveXBound, initialCurveYRows]) coefficients gamma
      ((exactInitialGRSConversion (K := E)).messagePolynomial (strategy.candidate gamma))
        root

#print axioms challengeCandidateHom_curveTrivariatePolynomial_eq_zero
#print axioms exactInitial_challengeCandidateHom_eq_zero

end

end AspisWide.Terminal
