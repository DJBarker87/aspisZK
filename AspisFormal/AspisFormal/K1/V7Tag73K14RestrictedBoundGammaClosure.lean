import AspisFormal.K1.V7Tag73K14BoundGammaClosure
import AspisFormal.K1.V7Tag73K13K14EventComposition

/-!
# Compiler-clean Tag-73 K1.4 width-29 bound

K1.6 consumes the width-29 error only on its legal same-tape event.  This
module fixes the gamma coordinates to the deployed controller while requiring
source inclusion only on that exact slice.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K14RestrictedBoundGammaClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteStageAssembly
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73K13K14EventComposition
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14MeasureTransport
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Deterministic width-29 source data on one compiler-clean slice. -/
structure ExactTag73RestrictedK14BoundGammaSource
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
        (clean ∩ exactTag73K14Width29Event transitionFuel configuration
          projection fixedInstance decoder) hidden ⊆
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
            (variablePrefixK14FailureGammaTarget (provider hidden residual)))

/-- Exact compiler-law width-29 bound on the compiler-clean slice. -/
theorem exact_tag73_restricted_k14_width29_probability_le
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
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (source : ExactTag73RestrictedK14BoundGammaSource transitionFuel
      configuration projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73K14Width29Event transitionFuel configuration
          projection fixedInstance decoder) ≤ exactK14IdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩ exactTag73K14Width29Event transitionFuel configuration
          projection fixedInstance decoder) ≤
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
      published (source.provider hidden residual) skeleton
  · exact source.covered

/-- Assemble the concrete K1.4 classifier directly on the same compiler-clean
slice. -/
theorem exact_restricted_assembled_k14_error_measure_bound
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (k15 : ExactTag73K15Classifier transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (width29Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactTag73K14Width29Event transitionFuel configuration
            projection fixedInstance decoder) ≤ exactK14IdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ k14CoherentChainErrorEvent
          (exactTag73ProofRelevantStages transitionFuel configuration projection
            fixedInstance relation decoder decoderBinding k15)) ≤
      exactK14IdealRawError := by
  apply (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      ?_ |>.trans width29Bound
  intro sample member
  exact ⟨member.1,
    assembled_k14_error_subset_width29 transitionFuel configuration projection
      fixedInstance relation decoder decoderBinding k15 member.2⟩

#print axioms ExactTag73RestrictedK14BoundGammaSource
#print axioms exact_tag73_restricted_k14_width29_probability_le
#print axioms exact_restricted_assembled_k14_error_measure_bound

end
end AspisK1.V7Tag73K14RestrictedBoundGammaClosure
