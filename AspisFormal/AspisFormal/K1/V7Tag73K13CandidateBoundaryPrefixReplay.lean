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
open AspisK1.V7Tag73CandidateQueryBatchPreAnswerPrefix
open AspisK1.V7Tag73CandidateQueryBatchPreBoundaryLabels
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CandidateWitnessBaseCoordinates
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

#print axioms candidate_witness_boundary_prefix_replays

end
end AspisK1.V7Tag73K13CandidateBoundaryPrefixReplay
