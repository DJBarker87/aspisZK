import Wide.FinalCurve

/-!
# Terminal exact V7 correlated-agreement instances

This file instantiates the weighted irreducible-branch selector, the explicit
finite-characteristic Hensel lift, and the released-message fixed-branch
wrappers for the two deployed V7 codes.
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

/-- Opaque generic elimination of good-challenge membership.  Keeping the
encoder abstract prevents elaboration from unfolding either concrete V7
encoder merely to project the validity conjunct. -/
theorem validResponse_of_mem_goodChallenges
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) (z : K)
    (member : z ∈ goodChallenges encoder agreementThreshold lanes strategy) :
    ValidResponse encoder agreementThreshold lanes strategy z :=
  (mem_goodChallenges_iff encoder agreementThreshold lanes strategy z).mp
    member

theorem all_goodChallenges_valid
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) :
    ∀ z ∈ goodChallenges encoder agreementThreshold lanes strategy,
      ValidResponse encoder agreementThreshold lanes strategy z := by
  intro z member
  exact validResponse_of_mem_goodChallenges encoder agreementThreshold lanes
    strategy z member

structure GoodChallengePackage
    (K Domain Message : Type*)
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) where
  challenges : Finset K
  challenges_eq : challenges =
    goodChallenges encoder agreementThreshold lanes strategy
  valid : ∀ z ∈ challenges,
    ValidResponse encoder agreementThreshold lanes strategy z

noncomputable def packageGoodChallenges
    {K Domain Message : Type*}
    [Field K] [Fintype K] [DecidableEq K]
    [Fintype Domain] [DecidableEq Domain]
    (encoder : Message → Domain → K) (agreementThreshold : Nat)
    (lanes : Fin 4 → Domain → K)
    (strategy : ProximateStrategy K Domain Message) :
    GoodChallengePackage K Domain Message encoder agreementThreshold lanes
      strategy where
  challenges := goodChallenges encoder agreementThreshold lanes strategy
  challenges_eq := rfl
  valid := all_goodChallenges_valid encoder agreementThreshold lanes strategy


set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
set_option linter.constructorNameAsVariable false in
/-- The exact released final V7 `256 → 2^18` encoder satisfies the complete
degree-three curve-decodability predicate at the unchanged release cap. -/
theorem exactV7FinalDegreeThreeCurveDecodable :
    DegreeThreeCurveDecodable (exactFinalEncoder (K := E)) 9557 foldChallengeCap := by
  classical
  let encoder :
      AspisV6OneFoldCandidateExtraction.FinalCoefficients E →
        Fin 262144 → E := exactFinalEncoder
  change DegreeThreeCurveDecodable encoder 9557 foldChallengeCap
  intro lanes strategy manyGood
  obtain ⟨challenges, challengesEq, validOn⟩ :=
    packageGoodChallenges encoder 9557 lanes strategy
  have outerMany :
      finalCurveZBound + 224 * finalCurveYRows * finalCurveZBound +
          58 * (255 + 1) * finalCurveYRows ^ 2 * finalCurveZBound +
            (3 * 262144 + 1) * finalCurveYRows <
              challenges.card := by
    apply lt_trans (b := foldChallengeCap)
    · norm_num [finalCurveZBound, finalCurveYRows, foldChallengeCap]
    · rw [challengesEq]
      exact manyGood
  obtain ⟨componentMessages, selected, selectedSubset, selectedLarge, onCurve⟩ :=
    exists_exactV7Final_curve_of_valid_challenges lanes strategy challenges
      validOn outerMany
  refine ⟨componentMessages, selected, ?_, selectedLarge, onCurve⟩
  intro z zMem
  rw [← challengesEq]
  exact selectedSubset zMem

/-- V7-specific discharge of the historical published one-fold interface. -/
theorem exactV7FinalPublishedOneFoldCurveDecodability :
    PublishedOneFoldCurveDecodability (exactFinalLinear (K := E)) := by
  change DegreeThreeCurveDecodable (exactFinalEncoder (K := E)) 9557 foldChallengeCap
  exact exactV7FinalDegreeThreeCurveDecodable

#print axioms exactV7FinalDegreeThreeCurveDecodable
#print axioms exactV7FinalPublishedOneFoldCurveDecodability


end

end AspisWide.Terminal
