import Wide.FinalBranch

/-!
# Exact final V7 fixed-branch selection

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
open AspisWide.FinalEncoder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisCircleGroupOrder (P)

noncomputable section

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
-- The fixed-branch selector expands exact degree-three weighted-degree budgets;
-- isolating it here lets Lean serialize that proof before the Hensel lift.
theorem exists_exactV7Final_weighted_fixed_branch
    (lanes : Fin 4 → FinalWord E)
    (strategy : ProximateStrategy E (Fin 262144)
      (FinalMessage E))
    (coefficients :
      CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
        finalCurveZBound → E)
    (coefficientsNeZero : coefficients ≠ 0)
    (kernel : curveInterpolationMap (exactFinalGRSConversion (K := E)).points
      lanes coefficients = 0)
    (challenges : Finset E)
    (validOn : ∀ gamma ∈ challenges,
      ValidResponse exactFinalEncoder 9557 lanes strategy gamma)
    (outerMany :
      finalCurveZBound + 224 * finalCurveYRows * finalCurveZBound +
          58 * (255 + 1) * finalCurveYRows ^ 2 * finalCurveZBound +
            (3 * 262144 + 1) * finalCurveYRows < challenges.card) :
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
      29 * fixedBranchEvaluationBudget 255 3 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 3 localFactor)
          (trivariateYZWeight 3 globalFactor) +
        (3 * 262144 + 1) < selected.card ∧
      selected ⊆ challenges ∧
      ∀ gamma ∈ selected,
        challengeCandidateHom gamma
            ((exactFinalGRSConversion (K := E)).messagePolynomial
              (strategy.candidate gamma)) globalFactor = 0 ∧
        SimpleSpecializedRoot globalFactor x₀ gamma
            ((exactFinalGRSConversion (K := E)).messagePolynomial
              (strategy.candidate gamma)) ∧
        localChallengeCandidateHom gamma
            (((exactFinalGRSConversion (K := E)).messagePolynomial
              (strategy.candidate gamma)).eval x₀) localFactor = 0 ∧
        gamma ∉ localPoleChallengeSet localFactor := by
  classical
  have polynomialNeZero : curveTrivariatePolynomial coefficients ≠ 0 :=
    curveTrivariatePolynomial_ne_zero coefficients coefficientsNeZero
  have candidateRoot : ∀ gamma ∈ challenges,
      challengeCandidateHom gamma
        ((exactFinalGRSConversion (K := E)).messagePolynomial
          (strategy.candidate gamma))
        (curveTrivariatePolynomial coefficients) = 0 := by
    intro gamma gammaMem
    exact exactFinal_challengeCandidateHom_eq_zero lanes strategy coefficients
      kernel gamma (validOn gamma gammaMem)
  exact exists_weighted_fixed_branch
    (curveTrivariatePolynomial coefficients) polynomialNeZero
    (fun gamma => (exactFinalGRSConversion (K := E)).messagePolynomial
      (strategy.candidate gamma)) challenges 255 3 finalCurveYRows
    finalCurveZBound (3 * 262144 + 1)
    (by norm_num [finalCurveYRows])
    (by norm_num [finalCurveZBound])
    (curveTrivariatePolynomial_natDegree_lt
      (by norm_num [finalCurveYRows]) coefficients)
    ((curveTrivariatePolynomial_xNatDegree_lt
      (by norm_num [finalCurveXBound]) coefficients).trans_le <| by
        norm_num [finalCurveXBound])
    (curveTrivariatePolynomial_zNatDegree_lt
      (by norm_num [finalCurveZBound]) coefficients)
    (trivariateYZWeight_curveTrivariatePolynomial_lt
      (by norm_num [finalCurveZBound]) coefficients)
    candidateRoot outerMany

#print axioms exists_exactV7Final_weighted_fixed_branch

end

end AspisWide.Terminal
