import AspisFormal.K1.V7Tag73K13CleanCausalSource
import AspisFormal.K1.V7Tag73K13CleanTrialEvent

/-! # Pre-fixed finite trial family for compiler-clean K1.3 -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanTrials

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
open AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CleanTarget
open AspisK1.V7Tag73K13CleanTrialEvent
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

noncomputable def exactCleanCandidateDirectedQueryBatchTrials
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
      projection fixedInstance decoder) :
    ExactCompilerCandidateDirectedQueryBatchTrials
      (HiddenTape := HiddenTape)
      (FoldTrial := ExactCompilerExposureTrial parameters)
      (FinalTrial := ExactCompilerExposureTrial parameters) parameters where
  event := exactCleanCandidateDirectedTrialEvent transitionFuel configuration
    projection fixedInstance decoder source
  router := fun candidate foldTrial finalTrial hidden =>
    exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
      foldTrial.val finalTrial.val candidate
      (exactPlainRomCursor configuration hidden).erase
  target := exactCleanCandidateDirectedTarget source
  targetCard := exactCleanCandidateDirectedTarget_card_le source
  covered := exactCleanCandidateDirectedTrialEvent_covered transitionFuel
    configuration projection fixedInstance decoder source

#print axioms exactCleanCandidateDirectedQueryBatchTrials

end
end AspisK1.V7Tag73K13CleanTrials
