import AspisFormal.K1.V7Tag73ExactInternalCurveProbability
import AspisFormal.K1.V7Tag73ExactRestoredOperationalStages
import AspisFormal.K1.V7Tag73K14RestrictedBoundGammaClosure

/-!
# Restoration-wide selected-node K1.4 probability

This specializes the variable-prefix gamma/width-29 argument to the exact
node selected by the corrected restoration-wide K1.3 classifier.  The
width-29 mathematics and concrete V7 curve theorem are installed internally;
the remaining source boundary contains only the pre-gamma word/provider
family and its deterministic event inclusion.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK14Probability

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalStages
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaPrefixCausalController
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

/-- Pre-gamma source data for the literal selected restored-node K1.4 event.
There is no probability bound or K1.4 conclusion field. -/
structure ExactTag73RestoredOperationalK14Source
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
        (clean ∩ exactTag73RestoredOperationalK14Width29Event transitionFuel
          configuration projection fixedInstance decoder) hidden ⊆
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
            (variablePrefixK14FailureGammaTarget (provider hidden residual)))

/-- Exact compiler-law width-29 bound for the node selected by the
restoration-wide classifier.  The concrete V7 width-29 theorem is kernel
proved and is not a parameter. -/
theorem exact_restored_operational_k14_width29_probability_le
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
    (source : ExactTag73RestoredOperationalK14Source transitionFuel
      configuration projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73RestoredOperationalK14Width29Event transitionFuel
          configuration projection fixedInstance decoder) ≤
      exactK14IdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩ exactTag73RestoredOperationalK14Width29Event transitionFuel
          configuration projection fixedInstance decoder) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)
  apply hidden_tape_variable_prefix_k14_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length
    (fun hidden ↦ exactCompilerGammaPrefixCoordinates parameters
      transitionFuel (exactPlainRomCursor configuration hidden).erase)
    (fun hidden residual ↦
      variablePrefixK14FailureGammaTarget (source.provider hidden residual))
    initialBatchChallengeCap
  · intro hidden residual skeleton
    exact variable_prefix_k14_failure_target_card_le initialEncoderExact
      exactV7InitialPublishedWidth29CurveDecodability
      (source.provider hidden residual) skeleton
  · exact source.covered

end


#print axioms ExactTag73RestoredOperationalK14Source
#print axioms exact_restored_operational_k14_width29_probability_le

end AspisK1.V7Tag73ExactRestoredOperationalK14Probability
