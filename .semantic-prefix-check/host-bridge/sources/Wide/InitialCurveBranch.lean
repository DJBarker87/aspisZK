import Wide.Cardinality
import Wide.InitialSelection

/-!
# Exact initial V7 selected branch to released curve

The explicit branch-to-message lift is serialized separately from elimination
of the outer branch-selection existential to bound kernel memory.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisWide.Terminal

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]


open Polynomial
open AspisWide.Agreement
open AspisWide.Factors
open AspisWide.LocalFactors
open AspisWide.Smooth
open AspisWide.RegularHensel
open AspisWide.RegularWeights
open AspisWide.FactorBudgets
open AspisWide.GRSConversion
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisV6Width29CorrelatedAgreement
open AspisCircleGroupOrder (P)

noncomputable section

private theorem exists_strengthen
    {A : Type*} {P : A → Prop} {Q : Prop}
    (existsWitness : ∃ value, P value) (property : Q) :
    ∃ value, Q ∧ P value := by
  obtain ⟨value, witness⟩ := existsWitness
  exact ⟨value, property, witness⟩

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
-- This theorem checks the exact finite-characteristic Hensel/message-image
-- bridge once for the width-29 dependent candidate family.
theorem exists_exactV7Initial_components_of_selected_branch
    (lanes : Fin 29 → InitialWord E)
    (strategy : Width29ProximateStrategy E (Fin 1048576)
      (InitialMessage E))
    (challenges : Finset E)
    (validOn : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma)
    (globalFactor : TrivariatePolynomial E)
    (x₀ : E)
    (localFactor : BivariatePolynomial E)
    (selected : Finset E)
    (globalPositive : 0 < globalFactor.natDegree)
    (certificateAtPoint : (Polynomial.Bivariate.swap
      (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0)
    (localMem : localFactor ∈ bivariatePrimeFactors
      (specializeEvaluationPoint x₀ globalFactor))
    (localPositive : 0 < localFactor.natDegree)
    (selectedLarge :
      29 * fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 28 localFactor)
          (trivariateYZWeight 28 globalFactor) +
        (28 * 1048576 + 1) < selected.card)
    (selectedSubset : selected ⊆ challenges)
    (selectedSpec : ∀ gamma ∈ selected,
      challengeCandidateHom gamma
          ((exactInitialGRSConversion (K := E)).messagePolynomial
            (strategy.candidate gamma)) globalFactor = 0 ∧
      SimpleSpecializedRoot globalFactor x₀ gamma
          ((exactInitialGRSConversion (K := E)).messagePolynomial
            (strategy.candidate gamma)) ∧
      localChallengeCandidateHom gamma
          (((exactInitialGRSConversion (K := E)).messagePolynomial
            (strategy.candidate gamma)).eval x₀) localFactor = 0 ∧
      gamma ∉ localPoleChallengeSet localFactor) :
    ∃ components : Fin 29 → InitialMessage E,
      28 * Fintype.card (Fin 1048576) < selected.card ∧
      ∀ gamma ∈ selected,
        Width29CandidateOnCurve exactInitialEncoder strategy components
          gamma := by
  have selectedValid : ∀ gamma ∈ selected,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma := by
    intro gamma gammaMem
    exact validOn gamma (selectedSubset gammaMem)
  have selectedCard :
      28 * Fintype.card (Fin 1048576) < selected.card := by
    with_reducible
      exact AspisWide.Cardinality.card_fin_lt_of_budget
        (domainSize := 1048576) (curveDegree := 28)
        (budget := 29 * fixedBranchEvaluationBudget 1024 28 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 28 localFactor)
          (trivariateYZWeight 28 globalFactor))
        (count := selected.card) selectedLarge
  exact exists_strengthen
    (exists_exactV7Initial_components_of_branchSelection lanes strategy
      globalFactor x₀ localFactor selected globalPositive certificateAtPoint
      localMem localPositive selectedLarge selectedValid selectedSpec)
    selectedCard

#print axioms exists_exactV7Initial_components_of_selected_branch

end

end AspisWide.Terminal
