import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.K1.V7Tag73VariablePrefixK14Probability

/-!
# Restored-gamma K1.4 provider at the minimal initial-lane interface

The width-29 theorem depends on the 29 initial lanes, not on the complete
two-tree `ExtractedWords` or a restored operational certificate.  The response
family therefore chooses from the compact mathematical property actually used
by the curve theorem.  A literal source failure later supplies existence of
such a response; it is never stored inside the choice function.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14InitialLaneProvider

open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

/-- The compact property of one response used by the width-29 theorem. -/
def InitialLaneBadResponseRealized
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialLanes)
    (gamma : QM31Exact)
    (response : InitialMessage QM31Exact) : Prop :=
  ∃ selected : ExactCandidatePair,
    selected.1 = response ∧
    gamma ≠ 0 ∧
    Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
      (selectedCandidateStrategy decoder lanes selected) gamma ∧
    ¬ HasMatchingWidth29Decomposition decoder.initialEncoder lanes
      (selectedCandidateStrategy decoder lanes selected) gamma

/-- Any literal width-29 decomposition failure supplies one compact bad
response after transporting only the 29 initial lanes. -/
theorem initialLaneBadResponseRealizedOfFailure
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : ExtractedWords)
    (lanes : Width29InitialLanes)
    (gamma : QM31Exact)
    (disclosedFinal : FinalMessage QM31Exact)
    (schedule : ExactSchedule)
    (lanesExact : extractedWidth29InitialWords words = lanes)
    (gammaNonzero : gamma ≠ 0)
    (failure : Width29DecompositionFailure decoder words gamma disclosedFinal
      schedule) :
    ∃ response, InitialLaneBadResponseRealized decoder lanes gamma response := by
  subst lanes
  let selected := Classical.choose failure
  have selectedFacts := Classical.choose_spec failure
  have selectedExact := selectedFacts.1
  have noMatching := selectedFacts.2
  have valid := selected_chain_yields_valid_width29_response decoder words gamma
    disclosedFinal schedule selected selectedExact
  exact ⟨selected.1, selected, rfl, gammaNonzero, valid, noMatching⟩

/-- A total response family fixed by the decoder and the pre-gamma lanes.
At a gamma admitting any bad response it selects one; otherwise it uses the
caller-supplied default.  The nuisance skeleton is deliberately ignored. -/
noncomputable def restoredGammaInitialLaneResponse
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialLanes)
    (defaultResponse : InitialMessage QM31Exact) : VariablePrefixK14Response := by
  classical
  exact fun _ gamma =>
    if available : ∃ response, InitialLaneBadResponseRealized decoder lanes
        gamma response then
      Classical.choose available
    else defaultResponse

/-- Opaque name for the finite bad-gamma target.  Keeping this expression
folded prevents source-heavy consumers from repeatedly normalizing the full
width-29 strategy. -/
noncomputable def restoredGammaInitialLaneFailureTarget
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialLanes)
    (defaultResponse : InitialMessage QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact :=
  variablePrefixK14InitialLanesFailureGammaTarget decoder lanes
    (restoredGammaInitialLaneResponse decoder lanes defaultResponse) skeleton

/-- The opaque target retains the exact degree-28 cap. -/
theorem restored_gamma_initial_lane_failure_target_card_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (lanes : Width29InitialLanes)
    (defaultResponse : InitialMessage QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton) :
    (restoredGammaInitialLaneFailureTarget decoder lanes defaultResponse
      skeleton).card ≤ initialBatchChallengeCap := by
  unfold restoredGammaInitialLaneFailureTarget
  exact variable_prefix_k14_initial_lanes_failure_target_card_le decoder
    initialEncoderExact published lanes
      (restoredGammaInitialLaneResponse decoder lanes defaultResponse) skeleton

/-- Every realized bad response is counted by the single response family at
that gamma, independently of which witness supplied existence. -/
theorem realized_bad_response_mem_initial_lane_failure_target
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialLanes)
    (defaultResponse : InitialMessage QM31Exact)
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : QM31Exact)
    (available : ∃ response,
      InitialLaneBadResponseRealized decoder lanes gamma response) :
    gamma ∈ restoredGammaInitialLaneFailureTarget decoder lanes
      defaultResponse skeleton := by
  classical
  let chosen := Classical.choose available
  have chosenRealized := Classical.choose_spec available
  unfold InitialLaneBadResponseRealized at chosenRealized
  let selected := Classical.choose chosenRealized
  have selectedFacts := Classical.choose_spec chosenRealized
  have selectedExact := selectedFacts.1
  have gammaNonzero := selectedFacts.2.1
  have valid := selectedFacts.2.2.1
  have noMatching := selectedFacts.2.2.2
  have responseAt :
      restoredGammaInitialLaneResponse decoder lanes defaultResponse skeleton
          gamma = selected.1 := by
    unfold restoredGammaInitialLaneResponse
    rw [dif_pos available]
    exact selectedExact.symm
  have fixedMember : gamma ∈
      width29GoodChallenges decoder.initialEncoder
        AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
        (width29BadStrategy decoder.initialEncoder
          AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
          (selectedCandidateStrategy decoder lanes selected)) := by
    rw [mem_width29BadStrategy_good_iff]
    exact ⟨gammaNonzero, valid, noMatching⟩
  unfold restoredGammaInitialLaneFailureTarget
  unfold variablePrefixK14InitialLanesFailureGammaTarget
  rw [mem_width29BadStrategy_good_iff] at fixedMember ⊢
  let response :=
    restoredGammaInitialLaneResponse decoder lanes defaultResponse skeleton
  have responseAt' : response gamma = selected.1 := responseAt
  have supportEq := restoredWidth29Strategy_support_eq_selected decoder lanes
    selected response gamma responseAt'
  have restoredValid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
      (restoredWidth29Strategy decoder lanes response) gamma := by
    constructor
    · rw [supportEq]
      exact fixedMember.2.1.1
    · intro index member
      rw [supportEq] at member
      have fixedAgreement := fixedMember.2.1.2 index member
      rw [restoredWidth29Strategy_candidate, responseAt']
      rw [selectedCandidateStrategy_candidate] at fixedAgreement
      exact fixedAgreement
  have restoredNoMatching : ¬ HasMatchingWidth29Decomposition
      decoder.initialEncoder lanes
      (restoredWidth29Strategy decoder lanes response) gamma := by
    intro restoredMatching
    apply fixedMember.2.2
    rcases restoredMatching with ⟨components, shared, onCurve⟩
    refine ⟨components, ?_, ?_⟩
    · rw [← supportEq]
      exact shared
    · unfold Width29CandidateOnCurve at onCurve ⊢
      rw [restoredWidth29Strategy_candidate, responseAt'] at onCurve
      rw [selectedCandidateStrategy_candidate]
      exact onCurve
  exact ⟨fixedMember.1, restoredValid, restoredNoMatching⟩

attribute [irreducible] restoredGammaInitialLaneFailureTarget

#print axioms InitialLaneBadResponseRealized
#print axioms initialLaneBadResponseRealizedOfFailure
#print axioms restoredGammaInitialLaneResponse
#print axioms restoredGammaInitialLaneFailureTarget
#print axioms restored_gamma_initial_lane_failure_target_card_le
#print axioms realized_bad_response_mem_initial_lane_failure_target

end
end AspisK1.V7Tag73GammaRestoredK14InitialLaneProvider
