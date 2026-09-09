import AspisFormal.K1.V7Tag73ExactDagQ16TerminalProducer
import AspisFormal.K1.V7Tag73ExactSelectedQ16QueryBatchBoundary

/-!
# Installed selected-q16 anchor for candidate-directed query batching

The accepted final-work trial installs block zero for the selected q16
candidate.  Following the exact ordered advance chain installs the precise
last-block parent whose advance answer becomes the query-batch boundary
state.  This closes the source-to-DAG part of candidate-directed arming.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchAnchorInstalled

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactDagQ16TerminalProducer
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSelectedQ16QueryBatchBoundary
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Exact accepted-source endpoint required by the candidate-directed
observer: one concrete target slot, its installed parent producer, its literal
advance record, and the following query-batch-domain lookup. -/
theorem exact_selected_candidate_query_batch_anchor_is_installed
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
      fixedInstance sample) :
    ∃ (trial : ExactCompilerExposureTrial parameters)
        (target : Q16DigestSlot) (blockProducerInput : ShaInput)
        (blockDigest blockAdvance : Digest256)
        (beforeDomain beforeQueryBatch : EvalState),
      target.1 = (exactOperationalTape input).search.selectedCounter ∧
      target.2.val + 1 =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
      ExactDagProducerInstalled input trial
        (Q16DagProducer.mk blockDigest target blockProducerInput) ∧
      tableLookup (exactOperationalTable input) blockProducerInput =
        some blockDigest ∧
      tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) = some blockAdvance ∧
      (∃ before middle after,
        exactRootFreshQueries input =
          before ++ (blockProducerInput, blockDigest) :: middle ++
            (gammaAdvanceInput blockDigest, blockAdvance) :: after) ∧
      blockAdvance = beforeDomain.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest := by
  obtain ⟨producerInput, initialDigest, outputs, advances, beforeDomain,
      beforeQueryBatch, producerLookup, producerExact, chain, outputsLength,
      advancesLength, terminalBoundary, boundaryLookup⟩ :=
    exact_selected_q16_terminal_is_query_batch_boundary transitionRoom input
  obtain ⟨_prefinalDigest, _workAnswer, base, trial, _workAccepted,
      _prefinalOrigin, baseExact, _pairLabeled, _workLabeled,
      initialInstalled⟩ :=
    exact_compiler_accepted_dag_trial_installs_all_candidates transitionRoom
      input
  have canonicalLookup := exact_operational_q16_candidate_absorb_lookup input
    (exactOperationalTape input).search.selectedCounter (Nat.le_refl _)
  have initialExact : initialDigest =
      exactOperationalQ16InitialDigest input
        (exactOperationalTape input).search.selectedCounter := by
    have sameSome : some initialDigest = some
        (exactOperationalQ16InitialDigest input
          (exactOperationalTape input).search.selectedCounter) := by
      rw [producerExact] at producerLookup
      exact producerLookup.symm.trans canonicalLookup
    exact Option.some.inj sameSome
  let firstSlot : Q16DigestSlot :=
    ((exactOperationalTape input).search.selectedCounter, ⟨0, by omega⟩)
  let firstProducer := Q16DagProducer.mk initialDigest firstSlot producerInput
  have firstInstalled : ExactDagProducerInstalled input trial firstProducer := by
    have raw := initialInstalled
      (exactOperationalTape input).search.selectedCounter (Nat.le_refl _)
    simpa [firstProducer, firstSlot, producerExact, initialExact, baseExact]
      using raw
  have nonempty : 0 < outputs.length := by
    rw [outputsLength]
    have positive :=
      (exactOperationalTape input).search.selectedSchedule.atLeastTwoBlocks
    omega
  have lengthCap : firstSlot.2.val + outputs.length ≤ 8 := by
    simp [firstSlot, outputsLength]
    exact (exactOperationalTape input).search.selectedSchedule
      |>.withinSixtyFourDraws
  obtain ⟨prefixOutputs, _prefixAdvances, blockProducerInput, blockDigest,
      _blockOutput, blockAdvance, lastBound, _outputsExact, _advancesExact,
      _prefixChain, blockProducerLookup, _blockOutputLookup,
      blockAdvanceLookup, blockOrder, _predecessorExact, lastExact,
      lastInstalled⟩ :=
    exact_ordered_q16_chain_last_parent_is_installed input trial
      (exactOperationalTape input).search.selectedCounter firstSlot.2 chain
      nonempty lengthCap firstInstalled
  let target : Q16DigestSlot :=
    ((exactOperationalTape input).search.selectedCounter,
      ⟨firstSlot.2.val + prefixOutputs.length, lastBound⟩)
  have targetBlock : target.2.val + 1 =
      (exactOperationalTape input).search.selectedSchedule.blocksUsed := by
    have outputCount : prefixOutputs.length + 1 = outputs.length := by
      rw [show outputs = prefixOutputs ++ [_] from
        (by assumption)]
      simp
    simp [target, firstSlot]
    omega
  have installedAtTarget : ExactDagProducerInstalled input trial
      (Q16DagProducer.mk blockDigest target blockProducerInput) := by
    simpa [target] using lastInstalled
  refine ⟨trial, target, blockProducerInput, blockDigest, blockAdvance,
    beforeDomain, beforeQueryBatch, rfl, targetBlock, installedAtTarget,
    blockProducerLookup, blockAdvanceLookup, blockOrder, ?_, boundaryLookup⟩
  exact lastExact.symm.trans terminalBoundary

#print axioms exact_selected_candidate_query_batch_anchor_is_installed

end
end AspisK1.V7Tag73ExactCandidateQueryBatchAnchorInstalled
