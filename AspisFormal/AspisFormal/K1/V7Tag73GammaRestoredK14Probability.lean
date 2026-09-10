import AspisFormal.K1.V7Tag73ExactInternalCurveProbability
import AspisFormal.K1.V7Tag73ExactRestoredGammaFullRouting
import AspisFormal.K1.V7Tag73GammaRestoredK14Scope
import AspisFormal.K1.V7Tag73K14RestrictedBoundGammaClosure

/-!
# Width-29 probability for the typed gamma-restoration child

This is the honest probability boundary for restoration-native K1.4.  Unlike
the older restoration-wide event, its certificate must name a child whose
`parentRequest` is the typed block-zero gamma request on the accepted root.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73GammaRestoredK14Probability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14MeasureTransport
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Pre-gamma data for the child selected by the typed gamma restoration
request.  `covered` is deterministic source alignment; it contains neither a
probability bound nor a K1.4 conclusion. -/
structure ExactTag73GammaRestoredK14Source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  words : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    AspisPool.V7MerkleQueryExtractor.ExtractedWords
  provider : ∀ hidden residual,
    VariablePrefixK14Provider decoder (words hidden residual)
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder)
        hidden ⊆
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration
          hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
            (variablePrefixK14FailureGammaTarget (provider hidden residual)))

/-- The concrete V7 width-29 theorem bounds the correctly scoped event. -/
theorem exact_gamma_restored_operational_k14_width29_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73GammaRestoredK14Source transitionFuel configuration
      projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder) ≤
      exactK14IdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)
  apply hidden_tape_variable_prefix_k14_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length
    (fun hidden ↦ exactCompilerRestoredGammaCoordinates transitionFuel
      configuration hidden)
    (fun hidden residual ↦
      variablePrefixK14FailureGammaTarget (source.provider hidden residual))
    initialBatchChallengeCap
  · intro hidden residual skeleton
    exact variable_prefix_k14_failure_target_card_le initialEncoderExact
      exactV7InitialPublishedWidth29CurveDecodability
      (source.provider hidden residual) skeleton
  · exact source.covered

#print axioms ExactTag73GammaRestoredK14Source
#print axioms exact_gamma_restored_operational_k14_width29_probability_le

end
end AspisK1.V7Tag73GammaRestoredK14Probability
