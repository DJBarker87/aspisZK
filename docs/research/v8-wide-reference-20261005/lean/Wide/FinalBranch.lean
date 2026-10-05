import Wide.FinalRoot

/-!
# Exact final V7 branch-to-message lift
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
open AspisWide.FunctionField
open AspisWide.PowerSeriesLift
open AspisWide.RegularHensel
open AspisWide.RegularWeights
open AspisWide.FactorBudgets
open AspisWide.ConcreteBranch
open AspisWide.OuterSelection
open AspisWide.GRSConversion
open AspisWide.FinalEncoder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.FinalEncoder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisCircleGroupOrder (P)

noncomputable section

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
/-- Close one selected final branch through finite-characteristic Hensel
lifting and the exact released-message image theorem. -/
theorem exists_exactV7Final_components_of_branchSelection
    (lanes : Fin 4 → FinalWord E)
    (strategy : ProximateStrategy E (Fin 262144)
      (FinalMessage E))
    (globalFactor : TrivariatePolynomial E)
    (x₀ : E) (localFactor : BivariatePolynomial E)
    (selected : Finset E)
    (globalPositive : 0 < globalFactor.natDegree)
    (certificateAtPoint : (Polynomial.Bivariate.swap
      (separabilityCertificate globalFactor)).eval (C x₀) ≠ 0)
    (localMem : localFactor ∈ bivariatePrimeFactors
      (specializeEvaluationPoint x₀ globalFactor))
    (localPositive : 0 < localFactor.natDegree)
    (selectedLarge :
      29 * fixedBranchEvaluationBudget 255 3 globalFactor.natDegree
          localFactor.natDegree (localBivariateWeight 3 localFactor)
          (trivariateYZWeight 3 globalFactor) +
        (3 * 262144 + 1) < selected.card)
    (selectedValid : ∀ gamma ∈ selected,
      ValidResponse exactFinalEncoder 9557 lanes strategy gamma)
    (selectedSpec : ∀ gamma ∈ selected,
      challengeCandidateHom gamma
          ((exactFinalGRSConversion (K := E)).messagePolynomial
            (strategy.candidate gamma)) globalFactor = 0 ∧
      SimpleSpecializedRoot globalFactor x₀ gamma
          ((exactFinalGRSConversion (K := E)).messagePolynomial
            (strategy.candidate gamma)) ∧
      localChallengeCandidateHom gamma
          (((exactFinalGRSConversion (K := E)).messagePolynomial
            (strategy.candidate gamma)).eval x₀) localFactor = 0 ∧
      gamma ∉ localPoleChallengeSet localFactor) :
    ∃ components : Fin 4 → FinalMessage E,
      ∀ gamma ∈ selected,
        CandidateOnCurve exactFinalEncoder strategy components
          gamma := by
  classical
  have parentNeZero : specializeEvaluationPoint x₀ globalFactor ≠ 0 :=
    specializeEvaluationPoint_ne_zero_of_certificate globalFactor x₀
      globalPositive certificateAtPoint
  letI : Fact (Irreducible (localFactorOverRational localFactor)) :=
    ⟨localFactorOverRational_irreducible
      (specializeEvaluationPoint x₀ globalFactor) localFactor parentNeZero
        localMem localPositive⟩
  have localNeZero : localFactor ≠ 0 :=
    (bivariatePrimeFactors_prime _ parentNeZero localFactor localMem).ne_zero
  obtain ⟨root, rootEquation, rootConstant⟩ :=
    exists_exactV7_fixedBranch_powerSeriesRoot globalFactor x₀
      certificateAtPoint localFactor localMem localPositive
  have etaNeZero := exactV7_regularizedHenselDerivative_ne_zero globalFactor
    x₀ certificateAtPoint localFactor localMem localPositive
  have localRoot : ∀ gamma ∈ selected,
      localFactor.eval₂ (Polynomial.evalRingHom gamma)
        (((exactFinalGRSConversion (K := E)).messagePolynomial
          (strategy.candidate gamma)).eval x₀) = 0 := by
    intro gamma gammaMem
    rw [Polynomial.eval₂_eq_eval_map]
    exact (selectedSpec gamma gammaMem).2.2.1
  exact exists_exactFinal_components_of_fixed_branch lanes strategy
    globalFactor globalPositive x₀ localFactor localNeZero localPositive root
    rootEquation rootConstant etaNeZero selected selectedValid localRoot
    (fun gamma gammaMem => (selectedSpec gamma gammaMem).1)
    (fun gamma gammaMem => (selectedSpec gamma gammaMem).2.1)
    (fun gamma gammaMem => (selectedSpec gamma gammaMem).2.2.2)
    selectedLarge

#print axioms exists_exactV7Final_components_of_branchSelection

end

end AspisWide.Terminal
