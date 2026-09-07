import AspisFormal.K1.V7Tag73GammaPrefixCausalController
import AspisFormal.K1.V7Tag73VariablePrefixK14ActualLaw

/-!
# Exact Tag-73 K1.4 closure at the bound gamma coordinate

The generic variable-prefix probability theorem accepts an arbitrary tape
equivalence.  This module fixes that equivalence to the causal gamma-prefix
controller of the deployed exact compiler.  What remains is deterministic
source data: the pre-gamma word, the scheduler-native response family, and
inclusion of the literal K1.4 failure in its width-29 target.

No probability inequality, independence premise, or caller-selected gamma
coordinate remains in the source interface.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K14BoundGammaClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14ActualLaw
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- The deterministic production seam left after fixing the gamma coordinates
to the deployed pre-answer controller. -/
structure ExactTag73K14BoundGammaSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) where
  words : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    AspisPool.V7MerkleQueryExtractor.ExtractedWords
  provider : ∀ hidden residual,
    VariablePrefixK14Provider decoder (words hidden residual)
  covered : ∀ hidden,
    jointEventSlice
        (exactTag73K14Width29Event transitionFuel configuration projection
          fixedInstance decoder) hidden ⊆
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
            (variablePrefixK14FailureGammaTarget
              (provider hidden residual)))

/-- Release-facing K1.4 probability theorem.  The returned width-29 bound is
under the exact compiler joint law and its gamma coordinates are definitionally
the deployed causal-controller coordinates. -/
theorem exact_tag73_k14_width29_probability_le_of_bound_gamma_source
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
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (source : ExactTag73K14BoundGammaSource transitionFuel configuration
      projection fixedInstance decoder) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73K14Width29Event transitionFuel configuration projection
          fixedInstance decoder) ≤ exactK14IdealRawError := by
  exact exact_tag73_k14_width29_probability_le_of_variable_prefix_source
    hiddenLaw initialEncoderExact published
    (fun hidden ↦ exactCompilerGammaPrefixCoordinates parameters transitionFuel
      (exactPlainRomCursor configuration hidden).erase)
    source.words source.provider source.covered

#print axioms ExactTag73K14BoundGammaSource
#print axioms exact_tag73_k14_width29_probability_le_of_bound_gamma_source

end

end AspisK1.V7Tag73K14BoundGammaClosure
