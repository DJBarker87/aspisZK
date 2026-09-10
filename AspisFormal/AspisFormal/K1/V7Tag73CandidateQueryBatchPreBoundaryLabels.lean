import AspisFormal.K1.V7Tag73CandidateQueryBatchPreAnswerPrefix
import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchBoundaryArming
import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection

/-!
# Candidate-directed labels before the query-batch boundary

The candidate-directed extension cannot emit a query-batch output/advance
label before its boundary has armed.  This is proved from the executable
controller update: once armed the boundary flag is monotone, while an
unarmed state with no producers either remains empty or arms with a producer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace AspisK1.V7Tag73CandidateQueryBatchPreBoundaryLabels

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCandidateQueryBatchBoundaryArming
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Once armed, the candidate-directed query-batch boundary remains armed
through every later exposure record. -/
theorem candidate_boundary_seen_persists_over_records
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      state.memory.2.queryBatch.boundarySeen = true →
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.queryBatch.boundarySeen = true := by
  intro records
  induction records with
  | nil =>
      intro state seen
      exact seen
  | cons record records ih =>
      intro state seen
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base dagOf
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextSeen : next.memory.2.queryBatch.boundarySeen = true := by
        simp only [next, controller,
          IndexedUnifiedExposureController.afterAnswer,
          extendControllerThroughCandidateQueryBatch]
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor
        · simpa [inputExact] using seen
        · simp only [inputExact]
          simp [candidateDirectedQueryBatchAfterInput, seen]
      rw [indexed_state_after_records_cons]
      exact ih next nextSeen

/-- An update from the canonical unarmed/empty extension cannot finish
unarmed while manufacturing a producer. -/
theorem candidate_unseen_empty_after_answer_is_empty
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (answer : Digest256)
    (unseen : state.memory.2.queryBatch.boundarySeen = false)
    (empty : state.memory.2.queryBatch.producers = [])
    (nextUnseen :
      ((extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf).afterAnswer transitionFuel state answer).memory.2.queryBatch.boundarySeen =
          false) :
    ((extendControllerThroughCandidateQueryBatch transitionFuel target base
      dagOf).afterAnswer transitionFuel state answer).memory.2.queryBatch.producers =
        [] := by
  simp only [IndexedUnifiedExposureController.afterAnswer,
    extendControllerThroughCandidateQueryBatch] at nextUnseen ⊢
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor
  · simpa [inputExact] using empty
  · simp only [inputExact] at nextUnseen ⊢
    unfold candidateDirectedQueryBatchAfterInput at nextUnseen ⊢
    simp only [unseen, Bool.not_false, if_true]
    split <;> simp_all
    split <;> simp_all

/-- If replay of a prefix ends before the boundary, every named label in that
prefix belongs to the established base controller. -/
theorem candidate_prefix_ending_unseen_has_only_base_labels
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      state.memory.2.queryBatch.boundarySeen = false →
      state.memory.2.queryBatch.producers = [] →
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.queryBatch.boundarySeen = false →
      ∀ slot ∈ namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel
            (extendControllerThroughCandidateQueryBatch transitionFuel target
              base dagOf) state records),
        ∃ baseSlot : Slot, slot = Sum.inl baseSlot := by
  intro records
  induction records with
  | nil =>
      intro state _unseen _empty _finalUnseen slot member
      simp at member
  | cons record records ih =>
      intro state unseen empty finalUnseen slot member
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base dagOf
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextUnseen : next.memory.2.queryBatch.boundarySeen = false := by
        cases nextSeen : next.memory.2.queryBatch.boundarySeen with
        | false => rfl
        | true =>
            have persists := candidate_boundary_seen_persists_over_records
              transitionFuel target base dagOf records next nextSeen
            rw [show indexedStateAfterRecords transitionFuel controller
                records next =
              indexedStateAfterRecords transitionFuel controller
                (record :: records) state by
                  rw [indexed_state_after_records_cons],
              finalUnseen] at persists
            contradiction
      have nextEmpty : next.memory.2.queryBatch.producers = [] := by
        exact candidate_unseen_empty_after_answer_is_empty transitionFuel target
          base dagOf state record.answer unseen empty (by
            simpa [next, controller] using nextUnseen)
      have headShape : ∀ headSlot,
          controller.preferredSlot state = some headSlot →
          ∃ baseSlot : Slot, headSlot = Sum.inl baseSlot := by
        intro headSlot preferred
        cases basePreferred : base.preferredSlot (baseIndexedState state) with
        | some baseSlot =>
            refine ⟨baseSlot, ?_⟩
            have selected : (some (Sum.inl baseSlot) :
                Option (Slot ⊕ GammaPrefixDigestSlot)) = some headSlot := by
              simpa [controller, extendControllerThroughCandidateQueryBatch,
                basePreferred] using preferred
            exact (Option.some.inj selected).symm
        | none =>
            cases inputExact : unifiedInputBeforeAnswer? transitionFuel
                state.cursor <;>
              simp [controller, extendControllerThroughCandidateQueryBatch,
                basePreferred, inputExact, queryBatchDagPreferredSlotForInput,
                empty, queryBatchPrefixOutputSlot?,
                queryBatchPrefixAdvanceSlot?] at preferred
      rw [indexed_controller_labeled_records_cons] at member
      change slot ∈ namedTraceSlots
        ((controller.preferredSlot state, record.answer) ::
          indexedControllerLabeledRecords transitionFuel controller next
            records) at member
      cases preferred : controller.preferredSlot state with
      | none =>
          rw [preferred] at member
          simp only [named_trace_slots_none_cons] at member
          exact ih next nextUnseen nextEmpty (by
            simpa [next, controller, indexed_state_after_records_cons] using
              finalUnseen) slot member
      | some headSlot =>
          rw [preferred] at member
          simp only [named_trace_slots_some_cons, List.mem_cons] at member
          rcases member with headExact | tailMember
          · subst slot
            exact headShape headSlot preferred
          · exact ih next nextUnseen nextEmpty (by
              simpa [next, controller, indexed_state_after_records_cons] using
                finalUnseen) slot tailMember

/-- The literal accepted-source prefix immediately before the selected
query-batch boundary has only established 518-slot base labels in the
fold-armed controller. -/
theorem exact_selected_candidate_boundary_prior_has_only_base_labels
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
        (boundaryPrior boundaryLater : List UnifiedExposureRecord)
        (boundaryActor : QueryActor),
      exactFixedRootRecords input.package.root =
        boundaryPrior ++
          (.machineFresh boundaryActor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: boundaryLater ∧
      finalTrial =
        (exactAcceptedDagInstallation transitionRoom input).finalTrial ∧
      (∀ slot ∈ namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel
            (foldArmedCandidateQueryBatchController transitionFuel
              foldTrial.val finalTrial.val target)
            (exactFoldArmedCandidateQueryBatchInitialState input)
            boundaryPrior),
        ∃ baseSlot : FoldAlphaFinalWorkQ16DigestSlot,
          slot = Sum.inl baseSlot) := by
  obtain ⟨finalTrial, target, blockAdvance, queryBatchDigest, _beforeDomain,
      boundaryPrior, boundaryLater, boundaryActor, rootExact,
      finalTrialExact, _blockAdvanceExact, _boundaryStart,
      _targetExact, oldUnseen, oldEmpty, _armed⟩ :=
    exact_selected_candidate_query_batch_boundary_arms transitionRoom
      input foldTrial boundaryIndex
  let oldController := extendControllerThroughCandidateQueryBatch
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel target
      (candidateCompleteBaseController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel foldTrial.val
        finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
  let oldBefore := indexedStateAfterRecords transitionFuel oldController
    boundaryPrior (exactCandidateDirectedQueryBatchInitialState input)
  let newController := foldArmedCandidateQueryBatchController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel foldTrial.val finalTrial.val target
  let newBefore := indexedStateAfterRecords transitionFuel newController
    boundaryPrior (exactFoldArmedCandidateQueryBatchInitialState input)
  have agreement := exact_candidate_projection_agreement_after_records input
    foldTrial finalTrial boundaryIndex target boundaryPrior
  change CandidateProjectionAgreement oldBefore newBefore at agreement
  have newUnseen : newBefore.memory.2.queryBatch.boundarySeen = false := by
    rw [← agreement.2.2.1]
    exact oldUnseen
  have newInitialUnseen :
      (exactFoldArmedCandidateQueryBatchInitialState input).memory.2.queryBatch.boundarySeen =
        false := by rfl
  have newInitialEmpty :
      (exactFoldArmedCandidateQueryBatchInitialState input).memory.2.queryBatch.producers =
        [] := by rfl
  have onlyBase := candidate_prefix_ending_unseen_has_only_base_labels
    transitionFuel target
      (foldArmedCompleteController transitionFuel foldTrial.val finalTrial.val)
      foldArmedCompleteDagMemory boundaryPrior
      (exactFoldArmedCandidateQueryBatchInitialState input) newInitialUnseen
      newInitialEmpty (by
        simpa [newController, newBefore,
          foldArmedCandidateQueryBatchController] using newUnseen)
  exact ⟨finalTrial, target, blockAdvance, queryBatchDigest, boundaryPrior,
    boundaryLater, boundaryActor, rootExact, finalTrialExact, by
      simpa [foldArmedCandidateQueryBatchController] using onlyBase⟩

#print axioms candidate_boundary_seen_persists_over_records
#print axioms candidate_unseen_empty_after_answer_is_empty
#print axioms candidate_prefix_ending_unseen_has_only_base_labels
#print axioms exact_selected_candidate_boundary_prior_has_only_base_labels

end
end AspisK1.V7Tag73CandidateQueryBatchPreBoundaryLabels
