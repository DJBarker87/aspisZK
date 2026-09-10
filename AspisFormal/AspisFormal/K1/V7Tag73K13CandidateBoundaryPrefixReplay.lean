import AspisFormal.K1.V7Tag73CandidateQueryBatchPreBoundaryLabels
import AspisFormal.K1.V7Tag73K13CandidateWitnessBaseCoordinates

/-!
# Candidate-witness replay to the query-batch boundary

The exact selected candidate identities let the generic 542-coordinate replay
theorem reach the literal accepted-source prefix immediately before the
query-batch domain answer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CandidateBoundaryPrefixReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateQueryBatchPreAnswerPrefix
open AspisK1.V7Tag73CandidateQueryBatchPreBoundaryLabels
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactCandidateAdvanceFreshness
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CandidateWitnessBaseCoordinates
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The right compiler tape replays the complete left accepted-root prefix up
to (but not including) the selected query-batch answer. -/
theorem candidate_witness_boundary_prefix_replays
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (blockAdvance queryBatchDigest : Digest256)
        (prior later : List UnifiedExposureRecord) (actor : QueryActor)
        (rightRemaining : List Digest256),
      exactFixedRootRecords left.input.package.root =
        prior ++
          (.machineFresh actor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: later ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              right.answers)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  obtain ⟨selectedRoom, selectedFinal⟩ := left.selected.2.1
  obtain ⟨boundaryFinal, target, blockAdvance, queryBatchDigest, prior, later,
      actor, rootExact, boundaryFinalExact, targetCounter, targetBlock,
      onlyBase⟩ :=
    exact_selected_candidate_boundary_prior_has_only_base_labels
      transitionRoom left.input foldTrial 0
  have targetExact : target = candidate :=
    selected_terminal_slot_eq_witness_candidate left targetCounter targetBlock
  subst target
  have finalExact : boundaryFinal = finalTrial := by
    exact boundaryFinalExact.trans selectedFinal.symm
  subst boundaryFinal
  have baseExact := candidate_witnesses_have_equal_base_coordinates left right
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_candidate_coordinates_force_pre_query_batch_prefix left.input
      foldTrial finalTrial candidate prior
      ((.machineFresh actor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) :: later)
      (by simpa only [List.cons_append] using rootExact) programmedCover
      right.answers baseExact (by simpa only [finalExact] using onlyBase)
  exact ⟨blockAdvance, queryBatchDigest, prior, later, actor, rightRemaining,
    rootExact, rightPrefix⟩

/-- Two witnesses in the same candidate-directed fibre replay each other's
complete literal accepted-root prefix before the selected query-batch answer.
This symmetric form is the deterministic input needed by the subsequent
first-exposure alignment argument: it retains both concrete boundary
decompositions while making no equality claim about the two challenge
answers. -/
theorem candidate_witness_boundary_prefixes_mutually_replay
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (leftBlockAdvance leftQueryBatchDigest rightBlockAdvance
        rightQueryBatchDigest : Digest256)
        (leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord)
        (leftActor rightActor : QueryActor)
        (leftRemaining rightRemaining : List Digest256),
      exactFixedRootRecords left.input.package.root =
        leftPrior ++
          (.machineFresh leftActor
            (bytes leftBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            leftQueryBatchDigest : UnifiedExposureRecord) :: leftLater ∧
      exactFixedRootRecords right.input.package.root =
        rightPrior ++
          (.machineFresh rightActor
            (bytes rightBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            rightQueryBatchDigest : UnifiedExposureRecord) :: rightLater ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              right.answers)) =
        leftPrior.map UnifiedExposureRecord.answer ++ rightRemaining ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              left.answers)) =
        rightPrior.map UnifiedExposureRecord.answer ++ leftRemaining := by
  obtain ⟨leftBlockAdvance, leftQueryBatchDigest, leftPrior, leftLater,
      leftActor, rightRemaining, leftRoot, rightReplaysLeft⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      left right
  obtain ⟨rightBlockAdvance, rightQueryBatchDigest, rightPrior, rightLater,
      rightActor, leftRemaining, rightRoot, leftReplaysRight⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      right left
  exact ⟨leftBlockAdvance, leftQueryBatchDigest, rightBlockAdvance,
    rightQueryBatchDigest, leftPrior, leftLater, rightPrior, rightLater,
    leftActor, rightActor, leftRemaining, rightRemaining, leftRoot, rightRoot,
    rightReplaysLeft, leftReplaysRight⟩

/-- Replaying the left boundary prefix on the right tape reaches the literal
left query-batch request before consuming its answer.  The request is
recovered from the scheduler cursor, rather than inferred from a logical
role attached after the hash lookup. -/
theorem candidate_witness_boundary_request_replays
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (blockAdvance queryBatchDigest : Digest256)
        (prior later : List UnifiedExposureRecord) (actor : QueryActor)
        (rightRemaining : List Digest256),
      exactFixedRootRecords left.input.package.root =
        prior ++
          (.machineFresh actor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: later ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              right.answers)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining ∧
      let base : IndexedUnifiedExposureController
          (globalFull256OracleCallCap parameters) Digest256
          FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
        candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val 0
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel candidate base completeFoldAlphaQ16DagMemory
      let initial := exactCandidateDirectedQueryBatchInitialState left.input
      unifiedInputBeforeAnswer? transitionFuel
          (indexedStateAfterRecords transitionFuel controller prior
            initial).cursor =
        some (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel]) := by
  obtain ⟨blockAdvance, queryBatchDigest, prior, later, actor,
      rightRemaining, rootExact, rightPrefix⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      left right
  let base : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    candidateCompleteBaseController transitionFuel foldTrial.val finalTrial.val 0
  let controller := extendControllerThroughCandidateQueryBatch
    transitionFuel candidate base completeFoldAlphaQ16DagMemory
  let initial := exactCandidateDirectedQueryBatchInitialState left.input
  have alignedRaw :=
    exact_root_records_aligned_for_candidate_directed_controller left.input
      foldTrial finalTrial 0 candidate
  have aligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords left.input.package.root) := by
    simpa [controller, base, initial] using alignedRaw
  have selectedAligned := aligned prior
    (.machineFresh actor
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest)
    later rootExact
  have requestExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller prior initial).cursor
    actor (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
    queryBatchDigest selectedAligned
  exact ⟨blockAdvance, queryBatchDigest, prior, later, actor, rightRemaining,
    rootExact, rightPrefix, by
      simpa only [UnifiedExposureRecord.answer] using requestExact⟩

#print axioms candidate_witness_boundary_prefix_replays
#print axioms candidate_witness_boundary_prefixes_mutually_replay
#print axioms candidate_witness_boundary_request_replays

end
end AspisK1.V7Tag73K13CandidateBoundaryPrefixReplay
