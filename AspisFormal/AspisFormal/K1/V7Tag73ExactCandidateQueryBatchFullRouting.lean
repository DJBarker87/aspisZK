import AspisFormal.K1.V7Tag73ExactQueryBatchAlphaProducerSeparation
import AspisFormal.K1.V7Tag73ExactCandidateDirectedRootRouting
import AspisFormal.K1.V7Tag73ExactFoldWorkExposureTrial

/-!
# Full candidate routing of the selected query batch

The armed 24-slot query-batch controller is lifted into the actual 542-slot
candidate router.  Earlier fold/alpha/final-work/q16 coordinates retain
priority, so the proof explicitly establishes that every consumed query-batch
child is residual for the complete 518-slot base before assigning its right
summand slot.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchFullRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCandidateAdvanceFreshness
open AspisK1.V7Tag73ExactCandidateDirectedRootRouting
open AspisK1.V7Tag73ExactCandidateQueryBatchChainRouting
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldWorkExposureTrial
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchAlphaProducerSeparation
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- One armed output preference lifts to the right summand of the exact full
candidate controller. -/
theorem exact_armed_query_batch_output_lifts_to_full_candidate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) (target : Q16DigestSlot)
    (foldDigest foldAnswer : Digest256) (foldActor : QueryActor)
    (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root = foldPrior ++
      (.machineFresh foldActor
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        foldAnswer : UnifiedExposureRecord) :: foldLater)
    (foldTrialExact : foldTrial.val = foldPrior.length)
    (blockAdvance queryBatchDigest : Digest256)
    (outputs advances : List Digest256)
    (chain : ExactRootOrderedQ16Chain input
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest outputs advances)
    (advancesLength : advances.length = outputs.length)
    (boundaryPrior suffix : List UnifiedExposureRecord)
    (boundaryActor : QueryActor)
    (rootExact : exactFixedRootRecords input.package.root = boundaryPrior ++
      (.machineFresh boundaryActor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) :: suffix)
    (smallInitial : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters)
      QueryBatchPrefixControllerMemory)
    (smallInitialExact : smallInitial = queryBatchIndexedState
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).afterAnswer transitionFuel
          (indexedStateAfterRecords transitionFuel
            (extendControllerThroughCandidateQueryBatch transitionFuel target
              (candidateCompleteBaseController transitionFuel foldTrial.val
                finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
            boundaryPrior (exactCandidateDirectedQueryBatchInitialState input))
          queryBatchDigest))
    (smallInitialArmed : smallInitial.memory.boundarySeen = true)
    (index : Nat) (inOutputs : index < outputs.length)
    (slot : Fin 12)
    (outputPrefix later : List UnifiedExposureRecord)
    (outputActor : QueryActor)
    (suffixExact : suffix = outputPrefix ++
      (.machineFresh outputActor
        (bytes (gammaChainState queryBatchDigest advances index) ++
          [domSqueeze]) outputs[index] : UnifiedExposureRecord) :: later)
    (smallPreferred : armedQueryBatchPreferredSlot transitionFuel
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) outputPrefix smallInitial) =
      some (slot, false)) :
    ∃ fullPrior,
      exactFixedRootRecords input.package.root = fullPrior ++
        (.machineFresh outputActor
          (bytes (gammaChainState queryBatchDigest advances index) ++
            [domSqueeze]) outputs[index] : UnifiedExposureRecord) :: later ∧
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (extendControllerThroughCandidateQueryBatch transitionFuel target
            (candidateCompleteBaseController transitionFuel foldTrial.val
              finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
          fullPrior (exactCandidateDirectedQueryBatchInitialState input)) =
        some (Sum.inr (slot, false)) := by
  let boundaryInput :=
    bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel]
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor boundaryInput queryBatchDigest
  let base := candidateCompleteBaseController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val boundaryIndex
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    target base completeFoldAlphaQ16DagMemory
  let fullInitial := exactCandidateDirectedQueryBatchInitialState input
  let beforeBoundary := indexedStateAfterRecords transitionFuel controller
    boundaryPrior fullInitial
  let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
    queryBatchDigest
  let fullPrior := boundaryPrior ++ boundaryRecord :: outputPrefix
  let fullReached := indexedStateAfterRecords transitionFuel controller
    fullPrior fullInitial
  let smallReached := indexedStateAfterRecords transitionFuel
    (armedQueryBatchController transitionFuel) outputPrefix smallInitial
  have decomposition : exactFixedRootRecords input.package.root = fullPrior ++
      (.machineFresh outputActor
        (bytes (gammaChainState queryBatchDigest advances index) ++
          [domSqueeze]) outputs[index] : UnifiedExposureRecord) :: later := by
    rw [rootExact, suffixExact]
    simp [fullPrior, boundaryRecord, boundaryInput, List.append_assoc]
  have stateMember : gammaChainState queryBatchDigest advances index ∈
      queryBatchDigest :: advances := by
    apply gamma_chain_state_mem_initial_cons_advances
    rw [advancesLength]
    exact inOutputs
  have baseResidual := exact_query_batch_state_output_is_518_residual input
    foldTrial finalTrial boundaryIndex foldDigest foldAnswer foldActor foldPrior
      foldLater foldExact foldTrialExact blockAdvance queryBatchDigest chain
      (gammaChainState queryBatchDigest advances index) stateMember
      outputs[index] outputActor fullPrior later decomposition
  have baseProjected : baseIndexedState fullReached =
      indexedStateAfterRecords transitionFuel base fullPrior
        (exactFoldAlphaFinalWorkQ16InitialState input) := by
    have projection := base_indexed_state_after_candidate_extended_records
      transitionFuel target base completeFoldAlphaQ16DagMemory fullPrior
        fullInitial
    have initialProjection : baseIndexedState fullInitial =
        exactFoldAlphaFinalWorkQ16InitialState input := by rfl
    rw [initialProjection] at projection
    simpa [fullReached, controller] using projection
  have baseNone : base.preferredSlot (baseIndexedState fullReached) = none := by
    rw [baseProjected]
    simpa [base, candidateCompleteBaseController] using baseResidual
  have afterBoundaryArmed :
      afterBoundary.memory.2.queryBatch.boundarySeen = true := by
    have armed := smallInitialArmed
    rw [smallInitialExact] at armed
    simpa [afterBoundary, queryBatchIndexedState] using armed
  have reachedSegment : fullReached =
      indexedStateAfterRecords transitionFuel controller outputPrefix
        afterBoundary := by
    simp [fullReached, fullPrior, afterBoundary, beforeBoundary,
      boundaryRecord, controller, indexed_state_after_records_append,
      UnifiedExposureRecord.answer]
  have queryProjection : queryBatchIndexedState fullReached = smallReached := by
    rw [reachedSegment]
    have projected := query_batch_state_after_candidate_records
      transitionFuel target base completeFoldAlphaQ16DagMemory outputPrefix
        afterBoundary afterBoundaryArmed
    rw [projected]
    simpa [smallReached] using congrArg
      (fun state => indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) outputPrefix state)
      smallInitialExact.symm
  have fullAligned :=
    exact_root_records_aligned_for_candidate_directed_controller input
      foldTrial finalTrial boundaryIndex target
  have recordAligned : unifiedRecordAtAnswer transitionFuel
      fullReached.cursor outputs[index] =
        .machineFresh outputActor
          (bytes (gammaChainState queryBatchDigest advances index) ++
            [domSqueeze]) outputs[index] := by
    have selected := fullAligned fullPrior
      (.machineFresh outputActor
        (bytes (gammaChainState queryBatchDigest advances index) ++
          [domSqueeze]) outputs[index]) later decomposition
    simpa [fullReached, controller, fullInitial,
      UnifiedExposureRecord.answer] using selected
  have fullInputExact : unifiedInputBeforeAnswer? transitionFuel
      fullReached.cursor = some
        (bytes (gammaChainState queryBatchDigest advances index) ++
          [domSqueeze]) :=
    aligned_machine_record_has_exact_input transitionFuel fullReached.cursor
      outputActor
      (bytes (gammaChainState queryBatchDigest advances index) ++ [domSqueeze])
      outputs[index] recordAligned
  have smallPreferred' := smallPreferred
  change armedQueryBatchPreferredSlot transitionFuel smallReached =
    some (slot, false) at smallPreferred'
  rw [← queryProjection] at smallPreferred'
  unfold armedQueryBatchPreferredSlot at smallPreferred'
  simp only [queryBatchIndexedState] at smallPreferred'
  rw [fullInputExact] at smallPreferred'
  have queryPreferred : queryBatchDagPreferredSlotForInput fullReached.memory.2
      (bytes (gammaChainState queryBatchDigest advances index) ++
        [domSqueeze]) = some (slot, false) := by
    simpa [queryBatchIndexedState, queryBatchDagPreferredSlotForInput] using
      smallPreferred'
  have fullPreferred : controller.preferredSlot fullReached =
      some (Sum.inr (slot, false)) := by
    apply candidate_extended_uses_query_batch_label transitionFuel target base
      completeFoldAlphaQ16DagMemory fullReached _ (slot, false) baseNone
      fullInputExact queryPreferred
  exact ⟨fullPrior, decomposition, by
    simpa [controller, base, fullReached, fullInitial] using fullPreferred⟩

/-- One armed advance preference lifts to the right summand of the exact full
candidate controller. -/
theorem exact_armed_query_batch_advance_lifts_to_full_candidate
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) (target : Q16DigestSlot)
    (foldDigest foldAnswer : Digest256) (foldActor : QueryActor)
    (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root = foldPrior ++
      (.machineFresh foldActor
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        foldAnswer : UnifiedExposureRecord) :: foldLater)
    (foldTrialExact : foldTrial.val = foldPrior.length)
    (blockAdvance queryBatchDigest : Digest256)
    (boundaryPrior suffix : List UnifiedExposureRecord)
    (boundaryActor : QueryActor)
    (rootExact : exactFixedRootRecords input.package.root = boundaryPrior ++
      (.machineFresh boundaryActor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) :: suffix)
    (smallInitial : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters)
      QueryBatchPrefixControllerMemory)
    (smallInitialExact : smallInitial = queryBatchIndexedState
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).afterAnswer transitionFuel
          (indexedStateAfterRecords transitionFuel
            (extendControllerThroughCandidateQueryBatch transitionFuel target
              (candidateCompleteBaseController transitionFuel foldTrial.val
                finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
            boundaryPrior (exactCandidateDirectedQueryBatchInitialState input))
          queryBatchDigest))
    (smallInitialArmed : smallInitial.memory.boundarySeen = true)
    (state advanced : Digest256) (slot : Fin 12)
    (advancePrefix later : List UnifiedExposureRecord)
    (advanceActor : QueryActor)
    (suffixExact : suffix = advancePrefix ++
      (.machineFresh advanceActor
        (bytes state ++ [domAdvance]) advanced : UnifiedExposureRecord) :: later)
    (smallPreferred : armedQueryBatchPreferredSlot transitionFuel
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) advancePrefix smallInitial) =
      some (slot, true)) :
    ∃ fullPrior,
      exactFixedRootRecords input.package.root = fullPrior ++
        (.machineFresh advanceActor (bytes state ++ [domAdvance]) advanced :
          UnifiedExposureRecord) :: later ∧
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (extendControllerThroughCandidateQueryBatch transitionFuel target
            (candidateCompleteBaseController transitionFuel foldTrial.val
              finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
          fullPrior (exactCandidateDirectedQueryBatchInitialState input)) =
        some (Sum.inr (slot, true)) := by
  let boundaryInput :=
    bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel]
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor boundaryInput queryBatchDigest
  let base := candidateCompleteBaseController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val boundaryIndex
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    target base completeFoldAlphaQ16DagMemory
  let fullInitial := exactCandidateDirectedQueryBatchInitialState input
  let beforeBoundary := indexedStateAfterRecords transitionFuel controller
    boundaryPrior fullInitial
  let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
    queryBatchDigest
  let fullPrior := boundaryPrior ++ boundaryRecord :: advancePrefix
  let fullReached := indexedStateAfterRecords transitionFuel controller
    fullPrior fullInitial
  let smallReached := indexedStateAfterRecords transitionFuel
    (armedQueryBatchController transitionFuel) advancePrefix smallInitial
  have decomposition : exactFixedRootRecords input.package.root = fullPrior ++
      (.machineFresh advanceActor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later := by
    rw [rootExact, suffixExact]
    simp [fullPrior, boundaryRecord, boundaryInput, gammaAdvanceInput,
      List.append_assoc]
  have baseResidual := exact_query_batch_state_advance_is_518_residual input
    foldTrial finalTrial boundaryIndex foldDigest foldAnswer foldActor foldPrior
      foldLater foldExact foldTrialExact state advanced advanceActor fullPrior
      later decomposition
  have baseProjected : baseIndexedState fullReached =
      indexedStateAfterRecords transitionFuel base fullPrior
        (exactFoldAlphaFinalWorkQ16InitialState input) := by
    have projection := base_indexed_state_after_candidate_extended_records
      transitionFuel target base completeFoldAlphaQ16DagMemory fullPrior
        fullInitial
    have initialProjection : baseIndexedState fullInitial =
        exactFoldAlphaFinalWorkQ16InitialState input := by rfl
    rw [initialProjection] at projection
    simpa [fullReached, controller] using projection
  have baseNone : base.preferredSlot (baseIndexedState fullReached) = none := by
    rw [baseProjected]
    simpa [base, candidateCompleteBaseController] using baseResidual
  have afterBoundaryArmed :
      afterBoundary.memory.2.queryBatch.boundarySeen = true := by
    have armed := smallInitialArmed
    rw [smallInitialExact] at armed
    simpa [afterBoundary, queryBatchIndexedState] using armed
  have reachedSegment : fullReached =
      indexedStateAfterRecords transitionFuel controller advancePrefix
        afterBoundary := by
    simp [fullReached, fullPrior, afterBoundary, beforeBoundary,
      boundaryRecord, controller, indexed_state_after_records_append,
      UnifiedExposureRecord.answer]
  have queryProjection : queryBatchIndexedState fullReached = smallReached := by
    rw [reachedSegment]
    have projected := query_batch_state_after_candidate_records
      transitionFuel target base completeFoldAlphaQ16DagMemory advancePrefix
        afterBoundary afterBoundaryArmed
    rw [projected]
    simpa [smallReached] using congrArg
      (fun state => indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) advancePrefix state)
      smallInitialExact.symm
  have fullAligned :=
    exact_root_records_aligned_for_candidate_directed_controller input
      foldTrial finalTrial boundaryIndex target
  have recordAligned : unifiedRecordAtAnswer transitionFuel
      fullReached.cursor advanced =
        .machineFresh advanceActor (gammaAdvanceInput state) advanced := by
    have selected := fullAligned fullPrior
      (.machineFresh advanceActor (gammaAdvanceInput state) advanced) later
        decomposition
    simpa [fullReached, controller, fullInitial,
      UnifiedExposureRecord.answer] using selected
  have fullInputExact : unifiedInputBeforeAnswer? transitionFuel
      fullReached.cursor = some (gammaAdvanceInput state) :=
    aligned_machine_record_has_exact_input transitionFuel fullReached.cursor
      advanceActor (gammaAdvanceInput state) advanced recordAligned
  have smallPreferred' := smallPreferred
  change armedQueryBatchPreferredSlot transitionFuel smallReached =
    some (slot, true) at smallPreferred'
  rw [← queryProjection] at smallPreferred'
  unfold armedQueryBatchPreferredSlot at smallPreferred'
  simp only [queryBatchIndexedState] at smallPreferred'
  rw [fullInputExact] at smallPreferred'
  have queryPreferred : queryBatchDagPreferredSlotForInput fullReached.memory.2
      (gammaAdvanceInput state) = some (slot, true) := by
    simpa [queryBatchIndexedState, queryBatchDagPreferredSlotForInput] using
      smallPreferred'
  have fullPreferred : controller.preferredSlot fullReached =
      some (Sum.inr (slot, true)) := by
    apply candidate_extended_uses_query_batch_label transitionFuel target base
      completeFoldAlphaQ16DagMemory fullReached _ (slot, true) baseNone
      fullInputExact queryPreferred
  exact ⟨fullPrior, by simpa [gammaAdvanceInput] using decomposition, by
    simpa [controller, base, fullReached, fullInitial] using fullPreferred⟩

/-- The selected accepted execution supplies one actual fold trial, one exact
alpha boundary, one selected final-work/q16 candidate, and every query-batch
answer at its right-summand coordinate in the shared 542-slot router. -/
theorem exact_selected_candidate_query_batch_is_fully_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
        (boundaryIndex : Nat) (target : Q16DigestSlot)
        (outputs advances : List Digest256),
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse
          .queryBatch).blocksUsed ∧
      advances.length = outputs.length ∧
      (∀ index (inOutputs : index < outputs.length),
        ∃ slot : Fin 12, slot.val = index ∧
          causalRoutedAnswer? (Sum.inr (slot, false))
            (exactCompilerCandidateDirectedQueryBatchRouter parameters
              transitionFuel foldTrial.val finalTrial.val boundaryIndex target
              (exactPlainRomCursor configuration sample.1).erase)
            (foldAlphaQ16QueryBatchNamedSlotInputTape
              (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
                sample.2)) = some outputs[index]) ∧
      (∀ index (inAdvances : index < advances.length),
        ∃ slot : Fin 12, slot.val = index ∧
          causalRoutedAnswer? (Sum.inr (slot, true))
            (exactCompilerCandidateDirectedQueryBatchRouter parameters
              transitionFuel foldTrial.val finalTrial.val boundaryIndex target
              (exactPlainRomCursor configuration sample.1).erase)
            (foldAlphaQ16QueryBatchNamedSlotInputTape
              (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
                sample.2)) = some advances[index]) := by
  obtain ⟨boundaryIndex, alphaPrior, alphaLater, alphaActor,
      alphaProducerInput, alphaDigest, alphaRootExact, alphaIndexExact,
      alphaBoundary, alphaInstalled⟩ :=
    exact_compiler_alpha_zero_boundary_installs_block_zero transitionRoom input
  obtain ⟨foldDigest, foldAnswer, foldTrial, foldPrior, foldLater, foldActor,
      foldAccepted, foldExact, foldTrialExact⟩ :=
    exact_compiler_accepted_fold_work_has_exposure_trial input
  obtain ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs,
      advances, boundaryPrior, suffix, boundaryActor, smallInitial, rootExact,
      chain, outputsLength, advancesLength, smallInitialExact,
      smallInitialMemory, outputPreferred, advancePreferred⟩ :=
    exact_selected_candidate_armed_query_batch_has_preferred_slots
      transitionRoom input foldTrial boundaryIndex
  have smallInitialArmed : smallInitial.memory.boundarySeen = true := by
    rw [smallInitialMemory]
  refine ⟨foldTrial, finalTrial, boundaryIndex, target, outputs, advances,
    outputsLength, advancesLength, ?_, ?_⟩
  · intro index inOutputs
    obtain ⟨outputPrefix, later, outputActor, slot, suffixExact,
        smallPreferred, slotExact⟩ := outputPreferred index inOutputs
    obtain ⟨fullPrior, decomposition, fullPreferred⟩ :=
      exact_armed_query_batch_output_lifts_to_full_candidate input foldTrial
        finalTrial boundaryIndex target foldDigest foldAnswer foldActor foldPrior
        foldLater foldExact foldTrialExact blockAdvance queryBatchDigest outputs
        advances chain advancesLength boundaryPrior suffix boundaryActor
        rootExact smallInitial smallInitialExact smallInitialArmed index inOutputs
        slot outputPrefix later outputActor suffixExact smallPreferred
    refine ⟨slot, slotExact, ?_⟩
    exact exact_candidate_directed_root_answer_is_routed programmedCover input
      foldTrial finalTrial boundaryIndex target fullPrior later outputActor
      (bytes (gammaChainState queryBatchDigest advances index) ++ [domSqueeze])
      outputs[index] (Sum.inr (slot, false)) decomposition fullPreferred
  · intro index inAdvances
    obtain ⟨advancePrefix, later, advanceActor, slot, suffixExact,
        smallPreferred, slotExact⟩ := advancePreferred index inAdvances
    let state := gammaChainState queryBatchDigest advances index
    obtain ⟨fullPrior, decomposition, fullPreferred⟩ :=
      exact_armed_query_batch_advance_lifts_to_full_candidate input foldTrial
        finalTrial boundaryIndex target foldDigest foldAnswer foldActor foldPrior
        foldLater foldExact foldTrialExact blockAdvance queryBatchDigest
        boundaryPrior suffix boundaryActor rootExact smallInitial
        smallInitialExact smallInitialArmed state advances[index] slot
        advancePrefix later advanceActor (by
          simpa [state, gammaAdvanceInput] using suffixExact) smallPreferred
    refine ⟨slot, slotExact, ?_⟩
    exact exact_candidate_directed_root_answer_is_routed programmedCover input
      foldTrial finalTrial boundaryIndex target fullPrior later advanceActor
      (gammaAdvanceInput state) advances[index] (Sum.inr (slot, true))
      (by simpa [state, gammaAdvanceInput] using decomposition) fullPreferred

#print axioms exact_armed_query_batch_output_lifts_to_full_candidate
#print axioms exact_armed_query_batch_advance_lifts_to_full_candidate
#print axioms exact_selected_candidate_query_batch_is_fully_routed

end
end AspisK1.V7Tag73ExactCandidateQueryBatchFullRouting
