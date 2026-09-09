import AspisFormal.K1.V7Tag73K13CleanTarget
import AspisFormal.K1.V7Tag73K13CandidateDirectedProbabilityClosure

/-! # One compiler-clean candidate-directed K1.3 trial event -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanTrialEvent

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CleanTarget
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

def exactCleanCandidateDirectedTrialEvent
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
      projection fixedInstance decoder)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters) :
    Set (ExactCompilerSample HiddenTape parameters) := fun sample =>
  let coordinates := exactCandidateDirectedRegroupedCoordinates
    transitionFuel configuration candidate foldTrial finalTrial sample.1 sample.2
  coordinates.2 ∈ foldFinalWorkQueryBatchDependentEvent
    (exactCleanCandidateDirectedTarget source candidate foldTrial finalTrial
      sample.1 coordinates.1)

#print axioms exactCleanCandidateDirectedTrialEvent

/-- The trial event is definitionally the dependent-coordinate event required
by the generic probability theorem.  Isolating this reduction keeps record
assembly cheap. -/
theorem exactCleanCandidateDirectedTrialEvent_covered
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
      projection fixedInstance decoder)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape) :
    jointEventSlice
        (exactCleanCandidateDirectedTrialEvent transitionFuel configuration
          projection fixedInstance decoder source candidate foldTrial finalTrial)
        hidden ⊆
      ((exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
        (exactCompilerFoldArmedCandidateQueryBatchRouter parameters
          transitionFuel foldTrial.val finalTrial.val candidate
          (exactPlainRomCursor configuration hidden).erase)).trans
        (foldFinalWorkQueryBatchCoordinateRegroup
          (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters)
          AlphaZeroDigestBlocks Q16CandidateDigestForest)) ⁻¹' {
        coordinates | coordinates.2 ∈
          foldFinalWorkQueryBatchDependentEvent
            (exactCleanCandidateDirectedTarget source candidate foldTrial
              finalTrial hidden coordinates.1) } := by
  intro tape member
  exact member

#print axioms exactCleanCandidateDirectedTrialEvent_covered

end
end AspisK1.V7Tag73K13CleanTrialEvent
