import AspisFormal.K1.V7Tag73K13CandidateDirectedProbabilityClosure
import AspisFormal.K1.V7Tag73ExactFixedInstanceEvent

/-! # Compiler-clean candidate-directed K1.3 causal source -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanCausalSource

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
open AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One pre-fixed finite trial family, plus the deterministic mapping from
each compiler-clean concrete collision to a member of that family. -/
structure ExactCleanCandidateDirectedK13CausalSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) where
  trials : ExactCompilerCandidateDirectedQueryBatchTrials
    (HiddenTape := HiddenTape)
    (FoldTrial := ExactCompilerExposureTrial parameters)
    (FinalTrial := ExactCompilerExposureTrial parameters) parameters
  collisionMapped : ∀
      (sample : ExactCompilerSample HiddenTape parameters),
    sample ∈ exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
      projection fixedInstance →
    ∀ (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
    ExactTag73K13CollisionCertificate source input k12 →
    ∃ candidate foldTrial finalTrial,
      sample ∈ trials.event candidate foldTrial finalTrial

#print axioms ExactCleanCandidateDirectedK13CausalSource

end
end AspisK1.V7Tag73K13CleanCausalSource
