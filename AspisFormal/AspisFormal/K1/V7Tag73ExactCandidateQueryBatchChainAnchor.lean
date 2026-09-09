import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchBoundaryArming
import AspisFormal.K1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin
import AspisFormal.K1.V7Tag73K13PreQ16ViewAgreement

/-!
# Candidate-directed query-batch chain anchor

The fixed selected candidate and the deployed query-batch sampler meet at the
same canonical post-q16 digest.  This joins the controller's exact boundary
arming with the complete consumed query-batch duplex chain without appealing
to SHA-256 injectivity or to uniqueness of an arbitrary existential witness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchChainAnchor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCandidateQueryBatchBoundaryArming
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16ViewAgreement
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- One accepted-source witness supplies both the pre-fixed candidate arming
and the exact query-batch chain rooted at the digest installed there. -/
theorem exact_selected_candidate_arms_complete_query_batch_chain
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    ∃ (finalTrial : ExactCompilerExposureTrial parameters)
        (target : Q16DigestSlot) (blockAdvance queryBatchDigest : Digest256)
        (outputs advances : List Digest256)
        (boundaryPrior boundaryLater : List UnifiedExposureRecord)
        (boundaryActor : QueryActor),
      exactFixedRootRecords input.package.root =
        boundaryPrior ++
          (.machineFresh boundaryActor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: boundaryLater ∧
      ExactRootOrderedQ16Chain input
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest outputs advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse
          .queryBatch).blocksUsed ∧
      advances.length = outputs.length ∧
      let base := candidateCompleteBaseController transitionFuel foldTrial.val
        finalTrial.val boundaryIndex
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base completeFoldAlphaQ16DagMemory
      let initial := exactCandidateDirectedQueryBatchInitialState input
      let beforeBoundary := indexedStateAfterRecords transitionFuel controller
        boundaryPrior initial
      let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
        queryBatchDigest
      beforeBoundary.memory.2.q16.advances target = some blockAdvance ∧
      beforeBoundary.memory.2.queryBatch.boundarySeen = false ∧
      beforeBoundary.memory.2.queryBatch.producers = [] ∧
      afterBoundary.memory.2.queryBatch =
        { boundarySeen := true
          producers :=
            [{ digest := queryBatchDigest, block := 0,
               sourceInput := bytes blockAdvance ++
                 [domAbsorb, queryBatchChallengeLabel] }]
          usedSlots := beforeBoundary.memory.2.queryBatch.usedSlots } := by
  obtain ⟨finalTrial, target, blockAdvance, queryBatchDigest, beforeDomain,
      boundaryPrior, boundaryLater, boundaryActor, boundaryRoot,
      terminalExact, boundaryStart, targetExact, unseen, empty, armed⟩ :=
    exact_selected_candidate_query_batch_boundary_arms transitionRoom input
      foldTrial boundaryIndex
  obtain ⟨producerInput, initialDigest, outputs, advances, producerLookup,
      ⟨chainBeforeDomain, producerInputExact, chainStart⟩, chain,
      outputsLength, advancesLength⟩ :=
    exact_operational_query_batch_domain_and_chain transitionRoom input
  have chainDigestExact : chainBeforeDomain.digest = blockAdvance := by
    exact chainStart.trans (boundaryStart.symm.trans terminalExact.symm)
  have producerInputCanonical : producerInput =
      bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel] := by
    rw [producerInputExact, chainDigestExact]
  have boundaryMember :
      (.machineFresh boundaryActor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) ∈
      exactFixedRootRecords input.package.root := by
    rw [boundaryRoot]
    simp
  have boundaryLookup := exact_root_machineFresh_has_operational_lookup input
    boundaryActor
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest boundaryMember
  have initialDigestExact : initialDigest = queryBatchDigest := by
    rw [producerInputCanonical] at producerLookup
    exact Option.some.inj (producerLookup.symm.trans boundaryLookup)
  have canonicalChain : ExactRootOrderedQ16Chain input
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest outputs advances := by
    simpa [producerInputCanonical, initialDigestExact] using chain
  exact ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs, advances,
    boundaryPrior, boundaryLater, boundaryActor, boundaryRoot, canonicalChain,
    outputsLength, advancesLength, targetExact, unseen, empty, armed⟩

#print axioms exact_selected_candidate_arms_complete_query_batch_chain

end
end AspisK1.V7Tag73ExactCandidateQueryBatchChainAnchor
