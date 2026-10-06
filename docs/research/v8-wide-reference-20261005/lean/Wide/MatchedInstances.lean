import Wide.DegreeThreeMatched
import Wide.Instances

/-! Exact final-encoder instances of the matched degree-three bound. -/
set_option autoImplicit false
namespace AspisWide.MatchedInstances
open AspisWide.DegreeThreeMatched
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.FinalEncoder AspisWide.Agreement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- For the exact injective linear encoder, matching encoded words is exactly
matching the response message to the scalar-power sum of component messages. -/
theorem final_matchingDecomposition_iff
    (lanes : Fin 4 → FinalWord K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalMessage K)) (z : K) :
    HasMatchingDecomposition exactFinalEncoder lanes strategy z ↔
      ∃ components : Fin 4 → FinalMessage K,
        strategy.support z ⊆ jointAgreementSet exactFinalEncoder lanes components ∧
        strategy.candidate z = exactFinalMessageCurve components z := by
  constructor
  · rintro ⟨components, support, onCurve⟩
    refine ⟨components, support, exactFinalEncoder_injective ?_⟩
    exact onCurve.trans (exactFinalEncoder_messageCurve components z).symm
  · rintro ⟨components, support, candidate⟩
    refine ⟨components, support, ?_⟩
    change exactFinalEncoder (strategy.candidate z) = _
    rw [candidate]
    exact exactFinalEncoder_messageCurve components z

theorem exactFinal_bad_response_challenges_card_le
    (lanes : Fin 4 → FinalWord K)
    (strategy : ProximateStrategy K (Fin 262144) (FinalMessage K)) :
    (goodChallenges exactFinalEncoder 9557 lanes
      (badStrategy exactFinalEncoder 9557 lanes strategy)).card ≤ foldChallengeCap :=
  degreeThree_bad_response_challenges_card_le exactFinalEncoder 9557 foldChallengeCap
    AspisWide.Terminal.exactV7FinalDegreeThreeCurveDecodable lanes strategy

theorem wideFinal_bad_response_challenges_card_le
    (lanes : Fin 4 → FinalWord AspisWideTower.WideExact)
    (strategy : ProximateStrategy AspisWideTower.WideExact (Fin 262144)
      (FinalMessage AspisWideTower.WideExact)) :
    (goodChallenges exactFinalEncoder 9557 lanes
      (badStrategy exactFinalEncoder 9557 lanes strategy)).card ≤ foldChallengeCap := by
  classical
  exact exactFinal_bad_response_challenges_card_le lanes strategy

#print axioms final_matchingDecomposition_iff
#print axioms exactFinal_bad_response_challenges_card_le
#print axioms wideFinal_bad_response_challenges_card_le
end AspisWide.MatchedInstances
