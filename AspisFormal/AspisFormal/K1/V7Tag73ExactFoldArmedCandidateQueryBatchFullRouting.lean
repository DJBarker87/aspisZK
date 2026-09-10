import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchFullRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection
import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedQueryBatchResidual
import AspisFormal.K1.V7Tag73ExactQueryBatchSuccessfulCoordinates

/-!
# Full production query-batch routing without an alpha-boundary index

The older production theorem supplies the exact selected query chain and its
literal root decompositions.  Projection agreement transfers each right-hand
query label to the dynamic fold-armed controller after proving its 518-slot
base residual.  The resulting 542-coordinate router is indexed only by fold
trial, final-work trial, and one q16 candidate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchFullRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCandidateQueryBatchChainRouting
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCandidateQueryBatchFullRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedQueryBatchResidual
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQueryBatchAlphaProducerSeparation
open AspisK1.V7Tag73ExactQueryBatchSuccessfulCoordinates
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A right-hand query-batch label selected by the older controller is also
selected by the fold-armed controller whenever the latter's base is residual.
Only cursor, extension-memory, and q16-DAG agreement are used. -/
theorem old_right_preferred_transfers_to_fold_armed
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
    (prior : List UnifiedExposureRecord)
    (slot : GammaPrefixDigestSlot)
    (oldPreferred :
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (extendControllerThroughCandidateQueryBatch transitionFuel target
            (candidateCompleteBaseController transitionFuel foldTrial.val
              finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
          prior (exactCandidateDirectedQueryBatchInitialState input)) =
        some (Sum.inr slot))
    (newBaseNone :
      (foldArmedCompleteController transitionFuel foldTrial.val
        finalTrial.val).preferredSlot
        (baseIndexedState
          (indexedStateAfterRecords transitionFuel
            (foldArmedCandidateQueryBatchController transitionFuel
              foldTrial.val finalTrial.val target) prior
            (exactFoldArmedCandidateQueryBatchInitialState input))) = none) :
    (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
      finalTrial.val target).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
          finalTrial.val target) prior
        (exactFoldArmedCandidateQueryBatchInitialState input)) =
      some (Sum.inr slot) := by
  let oldBase := candidateCompleteBaseController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val boundaryIndex
  let oldController := extendControllerThroughCandidateQueryBatch transitionFuel
    target oldBase completeFoldAlphaQ16DagMemory
  let oldReached := indexedStateAfterRecords transitionFuel oldController prior
    (exactCandidateDirectedQueryBatchInitialState input)
  let newBase := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val
  let newController := foldArmedCandidateQueryBatchController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val target
  let newReached := indexedStateAfterRecords transitionFuel newController prior
    (exactFoldArmedCandidateQueryBatchInitialState input)
  have agreement := exact_candidate_projection_agreement_after_records input
    foldTrial finalTrial boundaryIndex target prior
  change CandidateProjectionAgreement oldReached newReached at agreement
  change oldController.preferredSlot oldReached = some (Sum.inr slot) at oldPreferred
  change newBase.preferredSlot (baseIndexedState newReached) = none at newBaseNone
  cases basePreferred : oldBase.preferredSlot (baseIndexedState oldReached) with
  | some baseSlot =>
      have impossible : some (Sum.inl baseSlot) = some (Sum.inr slot) := by
        simpa [oldController, extendControllerThroughCandidateQueryBatch,
          basePreferred] using oldPreferred
      cases Option.some.inj impossible
  | none =>
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel
          oldReached.cursor with
      | none =>
          simp [oldController, extendControllerThroughCandidateQueryBatch,
            basePreferred, inputExact] at oldPreferred
      | some queryInput =>
          have queryPreferred : queryBatchDagPreferredSlotForInput
              oldReached.memory.2 queryInput = some slot := by
            simpa [oldController, extendControllerThroughCandidateQueryBatch,
              basePreferred, inputExact] using oldPreferred
          have newInputExact : unifiedInputBeforeAnswer? transitionFuel
              newReached.cursor = some queryInput := by
            rw [← agreement.2.1]
            exact inputExact
          have newQueryPreferred : queryBatchDagPreferredSlotForInput
              newReached.memory.2 queryInput = some slot := by
            rw [← agreement.2.2.1]
            exact queryPreferred
          change newController.preferredSlot newReached = some (Sum.inr slot)
          exact candidate_extended_uses_query_batch_label transitionFuel target
            newBase foldArmedCompleteDagMemory newReached queryInput slot
              newBaseNone newInputExact newQueryPreferred

/-- The selected accepted execution routes every actually consumed query-batch
output and advance through a 542-coordinate fold-armed router.  No alpha
boundary ordinal appears in the returned index family. -/
theorem exact_selected_fold_armed_candidate_query_batch_is_fully_routed
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
        (target : Q16DigestSlot) (outputs advances : List Digest256)
        (flat : SuccessfulGammaPrefixTape)
        (consumedDecoded : OrdinaryPrefixDecode)
        (consumedValue : QM31Exact),
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse
          .queryBatch).blocksUsed ∧
      foldTrial = (exactAcceptedFoldTrial input).trial ∧
      finalTrial =
        (exactAcceptedDagInstallation transitionRoom input).finalTrial ∧
      target.1 = (exactOperationalTape input).search.selectedCounter ∧
      target.2.val + 1 =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
      advances.length = outputs.length ∧
      (gammaOutputBlocks flat.1).take outputs.length = outputs ∧
      (List.ofFn flat.1.2).take advances.length = advances ∧
      decodeNonzeroPrefix 3 outputs = some consumedDecoded ∧
      decodeTagQM31ExactLE consumedDecoded.value = some consumedValue ∧
      exactOperationalChallenge input .queryBatch = consumedValue ∧
      exactOperationalChallenge input .queryBatch =
        (routedSuccessfulGammaValue
          (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      (∀ index (inOutputs : index < outputs.length),
        ∃ slot : Fin 12, slot.val = index ∧
          causalRoutedAnswer? (Sum.inr (slot, false))
            (exactCompilerFoldArmedCandidateQueryBatchRouter parameters
              transitionFuel foldTrial.val finalTrial.val target
              (exactPlainRomCursor configuration sample.1).erase)
            (foldAlphaQ16QueryBatchNamedSlotInputTape
              (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
                sample.2)) = some outputs[index]) ∧
      (∀ index (inAdvances : index < advances.length),
        ∃ slot : Fin 12, slot.val = index ∧
          causalRoutedAnswer? (Sum.inr (slot, true))
            (exactCompilerFoldArmedCandidateQueryBatchRouter parameters
              transitionFuel foldTrial.val finalTrial.val target
              (exactPlainRomCursor configuration sample.1).erase)
            (foldAlphaQ16QueryBatchNamedSlotInputTape
              (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
                sample.2)) = some advances[index]) := by
  let fold := exactAcceptedFoldTrial input
  obtain ⟨boundaryIndex, alphaPrior, alphaLater, alphaActor,
      alphaProducerInput, alphaDigest, alphaRootExact, alphaIndexExact,
      alphaBoundary, alphaInstalled⟩ :=
    exact_compiler_alpha_zero_boundary_installs_block_zero transitionRoom input
  obtain ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs,
      advances, boundaryPrior, suffix, boundaryActor, smallInitial, rootExact,
      finalTrialExact, targetCounter, targetBlock, chain, outputsLength,
      advancesLength, q16TerminalExact, smallInitialExact,
      smallInitialMemory, outputPreferred, advancePreferred⟩ :=
    exact_selected_candidate_armed_query_batch_has_preferred_slots
      transitionRoom input fold.trial boundaryIndex
  have smallInitialArmed : smallInitial.memory.boundarySeen = true := by
    rw [smallInitialMemory]
  obtain ⟨flat, _decoded, consumedDecoded, consumedValue, outputPrefix,
      advancePrefix, prefixRun, exactDecode, _decodedValue, _flatRun,
      _finalDecodedValue, operationalValue, challengeExact⟩ :=
    exact_query_batch_ordered_chain_has_successful_coordinates transitionRoom
      input
      ⟨(exactOperationalQ16Evaluator input).afterQ16, by
        rw [q16TerminalExact], rfl⟩ chain outputsLength
  refine ⟨fold.trial, finalTrial, target, outputs, advances, flat,
    consumedDecoded, consumedValue, outputsLength, rfl, finalTrialExact,
    targetCounter, targetBlock, advancesLength, outputPrefix, advancePrefix,
    prefixRun, exactDecode,
    operationalValue,
    challengeExact,
    ?_, ?_⟩
  · intro index inOutputs
    obtain ⟨outputPrefix, later, outputActor, slot, suffixExact,
        smallPreferred, slotExact⟩ := outputPreferred index inOutputs
    obtain ⟨fullPrior, decomposition, oldPreferred⟩ :=
      exact_armed_query_batch_output_lifts_to_full_candidate input fold.trial
        finalTrial boundaryIndex target fold.digest fold.answer fold.actor
        fold.prior fold.later fold.rootDecomposition fold.trialExact blockAdvance
        queryBatchDigest outputs advances chain advancesLength boundaryPrior
        suffix boundaryActor rootExact smallInitial smallInitialExact
        smallInitialArmed index inOutputs slot outputPrefix later outputActor
        suffixExact smallPreferred
    have stateMember : gammaChainState queryBatchDigest advances index ∈
        queryBatchDigest :: advances := by
      apply gamma_chain_state_mem_initial_cons_advances
      rw [advancesLength]
      exact inOutputs
    have newBaseNone := exact_fold_armed_query_batch_output_is_518_residual
      input fold finalTrial blockAdvance queryBatchDigest chain
      (gammaChainState queryBatchDigest advances index) stateMember
      outputs[index] outputActor fullPrior later decomposition
    have newPreferred := old_right_preferred_transfers_to_fold_armed input
      fold.trial finalTrial boundaryIndex target fullPrior (slot, false)
      oldPreferred (by
        rw [fold_armed_candidate_base_after_records input fold.trial finalTrial
          target fullPrior]
        exact newBaseNone)
    refine ⟨slot, slotExact, ?_⟩
    exact exact_fold_armed_candidate_root_answer_is_routed programmedCover input
      fold.trial finalTrial target fullPrior later outputActor
      (gammaOutputInput (gammaChainState queryBatchDigest advances index))
      outputs[index] (Sum.inr (slot, false)) decomposition newPreferred
  · intro index inAdvances
    obtain ⟨advancePrefix, later, advanceActor, slot, suffixExact,
        smallPreferred, slotExact⟩ := advancePreferred index inAdvances
    let state := gammaChainState queryBatchDigest advances index
    obtain ⟨fullPrior, decomposition, oldPreferred⟩ :=
      exact_armed_query_batch_advance_lifts_to_full_candidate input fold.trial
        finalTrial boundaryIndex target fold.digest fold.answer fold.actor
        fold.prior fold.later fold.rootDecomposition fold.trialExact blockAdvance
        queryBatchDigest boundaryPrior suffix boundaryActor rootExact
        smallInitial smallInitialExact smallInitialArmed state advances[index]
        slot advancePrefix later advanceActor (by
          simpa [state, gammaAdvanceInput] using suffixExact) smallPreferred
    have newBaseNone := exact_fold_armed_query_batch_advance_is_518_residual
      input fold finalTrial state advances[index] advanceActor fullPrior later
        (by simpa [state, gammaAdvanceInput] using decomposition)
    have newPreferred := old_right_preferred_transfers_to_fold_armed input
      fold.trial finalTrial boundaryIndex target fullPrior (slot, true)
      oldPreferred (by
        rw [fold_armed_candidate_base_after_records input fold.trial finalTrial
          target fullPrior]
        exact newBaseNone)
    refine ⟨slot, slotExact, ?_⟩
    exact exact_fold_armed_candidate_root_answer_is_routed programmedCover input
      fold.trial finalTrial target fullPrior later advanceActor
      (gammaAdvanceInput state) advances[index] (Sum.inr (slot, true))
      (by simpa [state, gammaAdvanceInput] using decomposition) newPreferred

#print axioms old_right_preferred_transfers_to_fold_armed
#print axioms exact_selected_fold_armed_candidate_query_batch_is_fully_routed

end
end AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchFullRouting
