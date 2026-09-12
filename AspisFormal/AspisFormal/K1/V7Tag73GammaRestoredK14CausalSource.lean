import AspisFormal.K1.V7Tag73GammaRestoredK14Probability
import AspisFormal.K1.V7Tag73RestoredGammaFibreK14Membership

/-!
# Deterministic causal source for scoped restored-gamma K1.4

This file fixes the response provider to the literal counterfactual compiler
fibre.  The remaining source field is pointwise causal alignment: every clean
scoped failure must land in that fibre's successful-sampler target.  It is a
deterministic statement and contains no probability inequality.  Separate
leaves construct the compact compiler target and prove its width-29
membership, so subsequent source work can discharge this field from the
scheduler/root-sweep trace without choosing an arbitrary response family.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14CausalSource

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14Probability
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredGammaFibreK14Membership
open AspisK1.V7Tag73RestoredGammaFibreK14Provider
open AspisK1.V7Tag73RestoredGammaFibreK14Target
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The pre-fixed provider determined by a word function, defaults, hidden
tape, and non-gamma residual.  Naming it prevents source consumers from
re-elaborating the full dependent counterfactual expression. -/
noncomputable def exactGammaRestoredK14CausalProvider
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
      AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters) :
    VariablePrefixK14Provider decoder (words hidden residual) :=
  restoredGammaFibreVariableK14Provider transitionFuel configuration
    projection fixedInstance decoder (words hidden residual) hidden residual
      defaultResponse defaultDisclosedFinal defaultSchedule defaultSelected

/-- Exact pointwise pre-gamma alignment.  There is no probability inequality
or caller-selected post-gamma response family in this record. -/
structure ExactTag73GammaRestoredK14CausalSource
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
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : ExactSchedule
  defaultSelected : ExactCandidatePair
  alignedAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance (hidden, answers))
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (_failure : Width29DecompositionFailure decoder
        k13.certificate.classified.k12.words
        (restoredOperationalK13View k13.certificate.data).gamma
        (restoredOperationalK13View k13.certificate.data).disclosedFinal
        (restoredOperationalK13View k13.certificate.data).schedule),
    answers ∈
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration
        hidden) ⁻¹'
      dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
        (fun residual => successfulGammaPrefixSkeletonDependentEventK14
          (variablePrefixK14FailureGammaTarget
            (exactGammaRestoredK14CausalProvider transitionFuel configuration
              projection fixedInstance decoder words defaultResponse
                defaultDisclosedFinal defaultSchedule defaultSelected hidden
                  residual)))

#print axioms exactGammaRestoredK14CausalProvider
#print axioms ExactTag73GammaRestoredK14CausalSource

end
end AspisK1.V7Tag73GammaRestoredK14CausalSource
