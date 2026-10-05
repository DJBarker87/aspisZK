import Wide.InitialBranch

/-!
# Exact initial V7 fixed-branch selection

This module serializes the weighted pigeonhole/frequency output before the
selected branch is passed to the finite-characteristic Hensel lift.  Keeping
those two large proof terms in separate declarations bounds kernel memory.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisWide.Terminal

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]


open Polynomial
open AspisWide.Agreement
open AspisWide.Interpolation
open AspisWide.Factors
open AspisWide.LocalFactors
open AspisWide.Smooth
open AspisWide.FactorBudgets
open AspisWide.OuterSelection
open AspisWide.RegularHensel
open AspisWide.RegularWeights
open AspisWide.GRSConversion
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisV6Width29CorrelatedAgreement
open AspisCircleGroupOrder (P)

noncomputable section

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
-- The fixed-branch selector expands exact width-29 weighted-degree budgets;
-- isolating it here lets Lean serialize that proof before the Hensel lift.
theorem exists_exactV7Initial_weighted_fixed_branch
    (lanes : Fin 29 → InitialWord E)
    (strategy : Width29ProximateStrategy E (Fin 1048576)
      (InitialMessage E))
    (coefficients :
      CurveMonomialIndex 1024 28 initialCurveXBound initialCurveYRows
        initialCurveZBound → E)
    (coefficientsNeZero : coefficients ≠ 0)
    (kernel : curveInterpolationMap (exactInitialGRSConversion (K := E)).points
      (exactInitialNormalizedLanes lanes) coefficients = 0)
    (challenges : Finset E)
    (validOn : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (outerMany :
      initialCurveZBound + 224 * initialCurveYRows * initialCurveZBound +
          58 * (1024 + 1) * initialCurveYRows ^ 2 * initialCurveZBound +
            (28 * 1048576 + 1) * initialCurveYRows < challenges.card) :
    ∃ (globalFactor : TrivariatePolynomial E)
        (x₀ : E)
        (localFactor : BivariatePolynomial E)
        (selected : Finset E),
      globalFactor ∈ curvePrimeFactors
          (curveTrivariatePolynomial coefficients) ∧
      0 < globalFactor.natDegree ∧
      (Polynomial.Bivariate.swap
        (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0 ∧
      localFactor ∈ bivariatePrimeFactors
        (specializeEvaluationPoint x₀ globalFactor) ∧
      0 < localFactor.natDegree ∧
      29 * fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 28 localFactor)
          (trivariateYZWeight 28 globalFactor) +
        (28 * 1048576 + 1) < selected.card ∧
      selected ⊆ challenges ∧
      ∀ gamma ∈ selected,
        challengeCandidateHom gamma
            ((exactInitialGRSConversion (K := E)).messagePolynomial
              (strategy.candidate gamma)) globalFactor = 0 ∧
        SimpleSpecializedRoot globalFactor x₀ gamma
            ((exactInitialGRSConversion (K := E)).messagePolynomial
              (strategy.candidate gamma)) ∧
        localChallengeCandidateHom gamma
            (((exactInitialGRSConversion (K := E)).messagePolynomial
              (strategy.candidate gamma)).eval x₀) localFactor = 0 ∧
        gamma ∉ localPoleChallengeSet localFactor := by
  classical
  have polynomialNeZero : curveTrivariatePolynomial coefficients ≠ 0 :=
    curveTrivariatePolynomial_ne_zero coefficients coefficientsNeZero
  have candidateRoot : ∀ gamma ∈ challenges,
      challengeCandidateHom gamma
        ((exactInitialGRSConversion (K := E)).messagePolynomial
          (strategy.candidate gamma))
        (curveTrivariatePolynomial coefficients) = 0 := by
    intro gamma gammaMem
    exact exactInitial_challengeCandidateHom_eq_zero lanes strategy coefficients
      kernel gamma (validOn gamma gammaMem)
  exact exists_weighted_fixed_branch
    (curveTrivariatePolynomial coefficients) polynomialNeZero
    (fun gamma => (exactInitialGRSConversion (K := E)).messagePolynomial
      (strategy.candidate gamma)) challenges 1024 28 initialCurveYRows
    initialCurveZBound (28 * 1048576 + 1)
    (by norm_num [initialCurveYRows])
    (by norm_num [initialCurveZBound])
    (curveTrivariatePolynomial_natDegree_lt
      (by norm_num [initialCurveYRows]) coefficients)
    ((curveTrivariatePolynomial_xNatDegree_lt
      (by norm_num [initialCurveXBound]) coefficients).trans_le <| by
        norm_num [initialCurveXBound])
    (curveTrivariatePolynomial_zNatDegree_lt
      (by norm_num [initialCurveZBound]) coefficients)
    (trivariateYZWeight_curveTrivariatePolynomial_lt
      (by norm_num [initialCurveZBound]) coefficients)
    candidateRoot outerMany

#print axioms exists_exactV7Initial_weighted_fixed_branch

end

end AspisWide.Terminal
