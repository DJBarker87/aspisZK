import AspisFormal.K1.V7Tag73K15BoundGammaClosure

/-!
# Compiler-clean Tag-73 K1.5 restored-gamma bound

This is the exact event shape consumed by K1.6.  The compiler already charges
its causal target event, so the gamma source need only cover the residual on
the legal same-tape slice.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73K15RestrictedBoundGammaClosure

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

/-- Source data for the restored-gamma event only on a fixed compiler-clean
slice.  All data remain chosen before the returned nonzero gamma. -/
structure ExactTag73RestrictedK15BoundGammaSource
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
      poseidon)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  words : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    AspisPool.V7MerkleQueryExtractor.ExtractedWords
  provider : ∀ hidden residual,
    VariablePrefixRestoredK15PreGammaProvider decoder (words hidden residual)
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactTag73RestoredK15ResidualEvent environment) hidden ⊆
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ variablePrefixRestoredK15ResidualFlatEvent
            (provider hidden residual))

/-- Exact raw restored-gamma bound on the compiler-clean slice. -/
theorem exact_tag73_restricted_restored_k15_residual_probability_le
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
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (published : PublishedInitialWidth29CurveDecodability exactInitialEncoder)
    (source : ExactTag73RestrictedK15BoundGammaSource transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon environment clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73RestoredK15ResidualEvent environment) ≤
      exactK14IdealRawError := by
  exact
    exact_compiler_dependent_variable_prefix_restored_k15_residual_event_probability_le
      hiddenLaw (exactCompilerTargetCaps parameters).length
      (fun hidden ↦ exactCompilerGammaPrefixCoordinates parameters
        transitionFuel (exactPlainRomCursor configuration hidden).erase)
      published source.words source.provider
      (clean ∩ exactTag73RestoredK15ResidualEvent environment) source.covered

#print axioms ExactTag73RestrictedK15BoundGammaSource
#print axioms exact_tag73_restricted_restored_k15_residual_probability_le

end
end AspisK1.V7Tag73K15RestrictedBoundGammaClosure
