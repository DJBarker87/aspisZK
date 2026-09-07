import AspisFormal.K1.V7Tag73ExactRestoredK15Events
import AspisFormal.K1.V7Tag73GammaPrefixCausalController
import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger
import AspisFormal.K1.V7Tag73RestoredCausalK15Stage
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatProbability
import AspisFormal.K1.V7Tag73VariablePrefixGammaProbability
import AspisFormal.K1.V7Tag73VariablePrefixRestoredK15ConditioningBridge

/-!
# Exact Tag-73 K1.5 restored residual at the bound gamma coordinate

This module fixes the restoration-aware K1.5 probability transport to the
same deployed pre-answer gamma controller used by K1.4.  The remaining source
record contains only deterministic pre-gamma data and literal event inclusion.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15BoundGammaClosure

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredK15Events
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73RestoredCausalK15Stage
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaProbability
open AspisK1.V7Tag73VariablePrefixRestoredK15ConditioningBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Deterministic source seam for the single restoration-aware K1.5 gamma
residual.  Its response family is fixed on each non-gamma residual before the
returned nonzero gamma is supplied. -/
structure ExactTag73K15BoundGammaSource
    {HiddenTape TapeIdentity Observation Payload : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon) where
  words : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    AspisPool.V7MerkleQueryExtractor.ExtractedWords
  provider : ∀ hidden residual,
    VariablePrefixRestoredK15PreGammaProvider decoder (words hidden residual)
  covered : ∀ hidden,
    jointEventSlice (exactTag73RestoredK15ResidualEvent environment) hidden ⊆
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ variablePrefixRestoredK15ResidualFlatEvent
            (provider hidden residual))

/-- Exact raw bound for the restored K1.5 residual under the production joint
law.  No probability inequality is accepted from the source layer. -/
theorem exact_tag73_restored_k15_residual_probability_le_of_bound_gamma_source
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters}
    {projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload}
    {fixedInstance : PublicInstance V5PublicStatement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {decoderBinding : InitialProjectionBinding decoder}
    {basis : Basis (Fin 4) F QM31Exact}
    {rc : RoundConstants}
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    {poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode}
    {environment : ExactTag73RestoredCausalK15Environment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon}
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (source : ExactTag73K15BoundGammaSource transitionFuel configuration
      projection fixedInstance decoder decoderBinding basis rc poseidon
      environment) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73RestoredK15ResidualEvent environment) ≤
      exactK14IdealRawError := by
  exact exact_compiler_dependent_variable_prefix_restored_k15_residual_event_probability_le
    hiddenLaw (exactCompilerTargetCaps parameters).length
      (fun hidden ↦ exactCompilerGammaPrefixCoordinates parameters transitionFuel
        (exactPlainRomCursor configuration hidden).erase)
      published source.words source.provider
      (exactTag73RestoredK15ResidualEvent environment) source.covered

#print axioms ExactTag73K15BoundGammaSource
#print axioms
  exact_tag73_restored_k15_residual_probability_le_of_bound_gamma_source

end

end AspisK1.V7Tag73K15BoundGammaClosure
