import AspisFormal.K1.V7Tag73ExactFixedK13K14FailureReduction
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting
import AspisFormal.K1.V7Tag73VariablePrefixGammaProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningCore

/-!
# Variable-prefix probability bound for the exact Tag-73 K1.4 failure

The production gamma sampler consumes a variable successful prefix, so the
older fixed raw-duplex K1.4 theorem is not its release law.  This leaf installs
the same published width-29 target on the exact chronological nuisance/value
factorization.  The selected response family may depend on the complete
pre-gamma nuisance skeleton, but not on the returned nonzero gamma.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73VariablePrefixK14Probability

open MeasureTheory
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces
open AspisV6Width29CorrelatedAgreement

noncomputable section

noncomputable instance : Nonempty SuccessfulGammaPrefixTape :=
  Nonempty.map successfulGammaPrefixFlatRoutingEquiv.symm inferInstance

/-- Lightweight transport of the already-proved routed factorization to the
literal chronological successful-prefix subtype. -/
theorem successfulGammaPrefixFactorization_law_k14 :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).map
        successfulGammaPrefixFactorization =
      variablePrefixSkeletonValueJointLaw := by
  calc
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).map
        successfulGammaPrefixFactorization =
      PMF.uniformOfFintype
        (VariableGammaCompleteSkeleton × NonzeroQM31Exact) :=
      AspisV5RankOneOpeningHiding.uniform_map_equiv
        successfulGammaPrefixFactorization
    _ = variablePrefixSkeletonValueJointLaw :=
      variablePrefixSkeletonValueJointLaw_eq_uniform.symm

def successfulGammaPrefixSkeletonDependentEventK14
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact) :
    Set SuccessfulGammaPrefixTape :=
  successfulGammaPrefixFactorization ⁻¹'
    variablePrefixSkeletonDependentGammaEvent target

theorem successful_gamma_prefix_skeleton_dependent_probability_le_k14
    (target : VariableGammaCompleteSkeleton → Finset QM31Exact)
    (cap : Nat)
    (targetCap : ∀ skeleton, (target skeleton).card ≤ cap) :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (successfulGammaPrefixSkeletonDependentEventK14 target) ≤
      (cap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  calc
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (successfulGammaPrefixSkeletonDependentEventK14 target) =
      ((PMF.uniformOfFintype SuccessfulGammaPrefixTape).map
          successfulGammaPrefixFactorization).toOuterMeasure
        (variablePrefixSkeletonDependentGammaEvent target) := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl
    _ = variablePrefixSkeletonValueJointLaw.toOuterMeasure
        (variablePrefixSkeletonDependentGammaEvent target) := by
      rw [successfulGammaPrefixFactorization_law_k14]
    _ ≤ _ := variablePrefix_skeleton_dependent_gamma_probability_le
      target cap targetCap

/-- One pre-gamma selected-branch provider per complete chronological nuisance
skeleton. -/
abbrev VariablePrefixK14Provider
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords) :=
  VariableGammaCompleteSkeleton → RestoredSelectedBranchProvider decoder words

/-! ## Initial-lane-only probability interface

The published width-29 theorem observes only the 29 initial lanes.  Keeping
the full `ExtractedWords` index in the release-facing probability interface
would incorrectly force the folded C2 word and every unused Merkle leaf to be
constant across the gamma fibre.  The response may depend on gamma; the
initial lanes may not. -/

abbrev Width29InitialLanes := Fin 29 → InitialWord QM31Exact

abbrev VariablePrefixK14Response :=
  VariableGammaCompleteSkeleton → QM31Exact → InitialMessage QM31Exact

/-- Width-29 bad-gamma target with exactly the data used by the published
curve theorem: fixed initial lanes and a nuisance-dependent response family. -/
noncomputable def variablePrefixK14InitialLanesFailureGammaTarget
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialLanes)
    (response : VariablePrefixK14Response)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact :=
  width29GoodChallenges decoder.initialEncoder
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
    (width29BadStrategy decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold lanes
      (restoredWidth29Strategy decoder lanes (response skeleton)))

/-- The degree-28 cap does not depend on a full extracted two-tree word. -/
theorem variable_prefix_k14_initial_lanes_failure_target_card_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (lanes : Width29InitialLanes)
    (response : VariablePrefixK14Response)
    (skeleton : VariableGammaCompleteSkeleton) :
    (variablePrefixK14InitialLanesFailureGammaTarget decoder lanes response
      skeleton).card ≤ initialBatchChallengeCap := by
  have decoderPublished : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder := by
    rw [initialEncoderExact]
    exact published
  exact initial_bad_response_challenges_card_le decoder.initialEncoder
    decoderPublished lanes (restoredWidth29Strategy decoder lanes
      (response skeleton))

def variablePrefixK14InitialLanesFailureFlatEvent
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialLanes)
    (response : VariablePrefixK14Response) : Set SuccessfulGammaPrefixTape :=
  successfulGammaPrefixSkeletonDependentEventK14
    (variablePrefixK14InitialLanesFailureGammaTarget decoder lanes response)

/-- Exact successful-prefix probability bound at the minimal initial-lane
interface. -/
theorem variable_prefix_k14_initial_lanes_failure_flat_probability_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (lanes : Width29InitialLanes)
    (response : VariablePrefixK14Response) :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (variablePrefixK14InitialLanesFailureFlatEvent decoder lanes response) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply successful_gamma_prefix_skeleton_dependent_probability_le_k14
  intro skeleton
  exact variable_prefix_k14_initial_lanes_failure_target_card_le decoder
    initialEncoderExact published lanes response skeleton

/-- Failed bounded-sampler executions add no event mass, exactly as in the
legacy full-word wrapper. -/
theorem variable_prefix_k14_initial_lanes_failure_total_probability_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (lanes : Width29InitialLanes)
    (response : VariablePrefixK14Response) :
    (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
        (successfulSubtypeEvent GammaPrefixSucceeds
          (variablePrefixK14InitialLanesFailureFlatEvent decoder lanes
            response)) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact (uniform_successful_subtype_event_probability_le GammaPrefixSucceeds
      (variablePrefixK14InitialLanesFailureFlatEvent decoder lanes response)).trans
    (variable_prefix_k14_initial_lanes_failure_flat_probability_le decoder
      initialEncoderExact published lanes response)

/-- The exact width-29 bad-gamma set selected before the returned gamma. -/
noncomputable def variablePrefixK14FailureGammaTarget
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixK14Provider decoder words)
    (skeleton : VariableGammaCompleteSkeleton) : Finset QM31Exact :=
  let family := restoredSelectedChainFamilyOfK13Provider (provider skeleton)
  width29GoodChallenges decoder.initialEncoder
    AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
    (width29BadStrategy decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
      (extractedWidth29InitialWords words)
      (restoredWidth29Strategy decoder (extractedWidth29InitialWords words)
        family.response))

/-- The published degree-28 theorem bounds every nuisance-dependent target. -/
theorem variable_prefix_k14_failure_target_card_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixK14Provider decoder words)
    (skeleton : VariableGammaCompleteSkeleton) :
    (variablePrefixK14FailureGammaTarget provider skeleton).card ≤
      initialBatchChallengeCap := by
  have decoderPublished : PublishedInitialWidth29CurveDecodability
      decoder.initialEncoder := by
    rw [initialEncoderExact]
    exact published
  exact restored_width29_bad_challenges_card_le decoder decoderPublished words
    (restoredSelectedChainFamilyOfK13Provider
      (provider skeleton)).response

def variablePrefixK14FailureFlatEvent
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixK14Provider decoder words) :
    Set SuccessfulGammaPrefixTape :=
  successfulGammaPrefixSkeletonDependentEventK14
    (variablePrefixK14FailureGammaTarget provider)

/-- Exact K1.4 bound on the chronological successful gamma-prefix subtype. -/
theorem variable_prefix_k14_failure_flat_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixK14Provider decoder words) :
    (PMF.uniformOfFintype SuccessfulGammaPrefixTape).toOuterMeasure
        (variablePrefixK14FailureFlatEvent provider) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  apply successful_gamma_prefix_skeleton_dependent_probability_le_k14
  intro skeleton
  exact variable_prefix_k14_failure_target_card_le initialEncoderExact published
    provider skeleton

/-- Failed sampler executions add no K1.4 event mass, giving the same bound on
the literal twelve-output/twelve-advance production tape. -/
theorem variable_prefix_k14_failure_total_probability_le
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (provider : VariablePrefixK14Provider decoder words) :
    (PMF.uniformOfFintype TotalGammaDuplexTape).toOuterMeasure
        (successfulSubtypeEvent GammaPrefixSucceeds
          (variablePrefixK14FailureFlatEvent provider)) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal) := by
  exact (uniform_successful_subtype_event_probability_le GammaPrefixSucceeds
      (variablePrefixK14FailureFlatEvent provider)).trans
    (variable_prefix_k14_failure_flat_probability_le initialEncoderExact
      published provider)

end

#print axioms variable_prefix_k14_failure_target_card_le
#print axioms variable_prefix_k14_failure_flat_probability_le
#print axioms variable_prefix_k14_failure_total_probability_le
#print axioms variablePrefixK14InitialLanesFailureGammaTarget
#print axioms variable_prefix_k14_initial_lanes_failure_target_card_le
#print axioms variable_prefix_k14_initial_lanes_failure_flat_probability_le
#print axioms variable_prefix_k14_initial_lanes_failure_total_probability_le

end AspisK1.V7Tag73VariablePrefixK14Probability
