import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchLabelsNodup
import AspisFormal.K1.V7Tag73FoldArmedCompleteLabelsNodup

/-!
# One-shot labels for the fold-armed candidate query-batch controller

This replaces the older separately guessed alpha-boundary index with the
fold-armed controller.  The selected fold-work answer causally installs the
exact alpha boundary, while the candidate-directed extension still fixes only
one of the 512 q16 terminal slots.  The complete 542 labels remain one-shot on
every answer stream.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateDirectedQueryBatchLabelsNodup
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedCompleteLabelsNodup
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def foldArmedCompleteDagMemory
    (memory : FoldArmedCompleteMemory) : FinalWorkQ16DagMemory :=
  memory.2.2

def foldArmedCandidateQueryBatchController
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16QueryBatchDigestSlot
      (ExtendedControllerMemory FoldArmedCompleteMemory) :=
  extendControllerThroughCandidateQueryBatch transitionFuel target
    (foldArmedCompleteController transitionFuel foldExposureIndex
      finalExposureIndex) foldArmedCompleteDagMemory

def foldArmedCandidateSlotUsed
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory)) :
    FoldAlphaFinalWorkQ16QueryBatchDigestSlot → Prop
  | .inl slot => foldArmedCompleteSlotUsed (baseIndexedState state) slot
  | .inr slot => slot ∈ state.memory.2.queryBatch.usedSlots

theorem fold_armed_candidate_slot_used_mono
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory))
    (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (used : foldArmedCandidateSlotUsed state slot) :
    foldArmedCandidateSlotUsed
      ((foldArmedCandidateQueryBatchController transitionFuel
        foldExposureIndex finalExposureIndex target).afterAnswer
          transitionFuel state answer) slot := by
  cases slot with
  | inl baseSlot =>
      change foldArmedCompleteSlotUsed
        ((foldArmedCompleteController transitionFuel foldExposureIndex
          finalExposureIndex).afterAnswer transitionFuel
            (baseIndexedState state) answer) baseSlot
      exact fold_armed_complete_slot_used_mono transitionFuel
        foldExposureIndex finalExposureIndex (baseIndexedState state) answer
          baseSlot used
  | inr querySlot =>
      change querySlot ∈ state.memory.2.queryBatch.usedSlots at used
      change querySlot ∈
        (match unifiedInputBeforeAnswer? transitionFuel state.cursor with
        | some input => candidateDirectedQueryBatchAfterInput target
            (foldArmedCompleteDagMemory (baseIndexedState state).memory)
            state.memory.2 input answer
        | none => state.memory.2).queryBatch.usedSlots
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none => simpa [inputExact] using used
      | some input =>
          simpa [inputExact] using candidate_query_batch_used_slots_mono target
            (foldArmedCompleteDagMemory (baseIndexedState state).memory)
              state.memory.2 input answer used

theorem fold_armed_candidate_preferred_fresh
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory))
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (preferred :
      (foldArmedCandidateQueryBatchController transitionFuel foldExposureIndex
        finalExposureIndex target).preferredSlot state = some slot) :
    ¬ foldArmedCandidateSlotUsed state slot := by
  let base := foldArmedCompleteController
    (globalOracleCalls := globalOracleCalls) transitionFuel foldExposureIndex
      finalExposureIndex
  cases basePreferred : base.preferredSlot (baseIndexedState state) with
  | some baseSlot =>
      have slotExact : slot = .inl baseSlot := by
        simpa [foldArmedCandidateQueryBatchController,
          extendControllerThroughCandidateQueryBatch, base,
          basePreferred] using preferred.symm
      subst slot
      exact fold_armed_complete_preferred_slot_fresh transitionFuel
        foldExposureIndex finalExposureIndex (baseIndexedState state) baseSlot
          basePreferred
  | none =>
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none =>
          simp [foldArmedCandidateQueryBatchController,
            extendControllerThroughCandidateQueryBatch, base, basePreferred,
            inputExact] at preferred
      | some input =>
          cases queryPreferred : queryBatchDagPreferredSlotForInput
              state.memory.2 input with
          | none =>
              simp [foldArmedCandidateQueryBatchController,
                extendControllerThroughCandidateQueryBatch, base,
                basePreferred, inputExact, queryPreferred] at preferred
          | some querySlot =>
              have slotExact : slot = .inr querySlot := by
                simpa [foldArmedCandidateQueryBatchController,
                  extendControllerThroughCandidateQueryBatch, base,
                  basePreferred, inputExact, queryPreferred] using
                    preferred.symm
              subst slot
              exact
                AspisK1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup.query_batch_extension_preferred_fresh
                  state.memory.2 input querySlot queryPreferred

theorem fold_armed_candidate_preferred_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory))
    (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (coherent : FoldArmedOuterCoherent foldExposureIndex
      (baseIndexedState state))
    (preferred :
      (foldArmedCandidateQueryBatchController transitionFuel foldExposureIndex
        finalExposureIndex target).preferredSlot state = some slot) :
    foldArmedCandidateSlotUsed
      ((foldArmedCandidateQueryBatchController transitionFuel foldExposureIndex
        finalExposureIndex target).afterAnswer transitionFuel state answer)
      slot := by
  let base := foldArmedCompleteController
    (globalOracleCalls := globalOracleCalls) transitionFuel foldExposureIndex
      finalExposureIndex
  cases basePreferred : base.preferredSlot (baseIndexedState state) with
  | some baseSlot =>
      have slotExact : slot = .inl baseSlot := by
        simpa [foldArmedCandidateQueryBatchController,
          extendControllerThroughCandidateQueryBatch, base,
          basePreferred] using preferred.symm
      subst slot
      change foldArmedCompleteSlotUsed
        (base.afterAnswer transitionFuel (baseIndexedState state) answer)
          baseSlot
      exact fold_armed_complete_preferred_slot_used_after_answer
        transitionFuel foldExposureIndex finalExposureIndex
          (baseIndexedState state) answer baseSlot coherent basePreferred
  | none =>
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none =>
          simp [foldArmedCandidateQueryBatchController,
            extendControllerThroughCandidateQueryBatch, base, basePreferred,
            inputExact] at preferred
      | some input =>
          cases queryPreferred : queryBatchDagPreferredSlotForInput
              state.memory.2 input with
          | none =>
              simp [foldArmedCandidateQueryBatchController,
                extendControllerThroughCandidateQueryBatch, base,
                basePreferred, inputExact, queryPreferred] at preferred
          | some querySlot =>
              have slotExact : slot = .inr querySlot := by
                simpa [foldArmedCandidateQueryBatchController,
                  extendControllerThroughCandidateQueryBatch, base,
                  basePreferred, inputExact, queryPreferred] using
                    preferred.symm
              subst slot
              have queryUsed := candidate_query_batch_preferred_used_after_input
                target
                (foldArmedCompleteDagMemory (baseIndexedState state).memory)
                state.memory.2 input answer querySlot queryPreferred
              simpa [foldArmedCandidateSlotUsed,
                foldArmedCandidateQueryBatchController,
                IndexedUnifiedExposureController.afterAnswer,
                extendControllerThroughCandidateQueryBatch, inputExact] using
                  queryUsed

theorem fold_armed_candidate_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory FoldArmedCompleteMemory)),
      FoldArmedOuterCoherent foldExposureIndex (baseIndexedState state) →
      let controller := foldArmedCandidateQueryBatchController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalExposureIndex target
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          ¬ foldArmedCandidateSlotUsed state slot := by
  intro records
  induction records with
  | nil =>
      intro state _coherent
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state coherent
      let controller := foldArmedCandidateQueryBatchController
        (globalOracleCalls := globalOracleCalls) transitionFuel
          foldExposureIndex finalExposureIndex target
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextCoherent : FoldArmedOuterCoherent foldExposureIndex
          (baseIndexedState next) := by
        have preserved := fold_armed_outer_coherent_after_answer
          transitionFuel foldExposureIndex finalExposureIndex
            (baseIndexedState state) record.answer coherent
        simpa [next, controller, foldArmedCandidateQueryBatchController] using
          preserved
      have tail := ih next nextCoherent
      have usedMono : ∀ slot, foldArmedCandidateSlotUsed state slot →
          foldArmedCandidateSlotUsed next slot := by
        intro slot used
        simpa [next, controller] using fold_armed_candidate_slot_used_mono
          transitionFuel foldExposureIndex finalExposureIndex target state
            record.answer slot used
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            ¬ foldArmedCandidateSlotUsed state slot
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1 (fun slot member used ↦
            tail.2 slot member (usedMono slot used))
      | some slot =>
          have slotFresh : ¬ foldArmedCandidateSlotUsed state slot :=
            fold_armed_candidate_preferred_fresh transitionFuel
              foldExposureIndex finalExposureIndex target state slot
                (by simpa [controller] using preferred)
          have nextUsed : foldArmedCandidateSlotUsed next slot := by
            simpa [next, controller] using
              fold_armed_candidate_preferred_used_after_answer transitionFuel
                foldExposureIndex finalExposureIndex target state record.answer
                  slot coherent (by simpa [controller] using preferred)
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), ¬ foldArmedCandidateSlotUsed state candidate := by
            intro candidate member used
            exact tail.2 candidate member (usedMono candidate used)
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          constructor
          · exact List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩
          · intro candidate member
            simp only [List.mem_cons] at member
            rcases member with equal | tailMember
            · subst candidate
              exact slotFresh
            · exact tailAvoidsInitial candidate tailMember

theorem fold_armed_candidate_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory))
    (coherent : FoldArmedOuterCoherent foldExposureIndex
      (baseIndexedState state)) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (foldArmedCandidateQueryBatchController transitionFuel
          foldExposureIndex finalExposureIndex target) state records)).Nodup :=
  (fold_armed_candidate_labeled_records_nodup_and_avoid_initial
    transitionFuel foldExposureIndex finalExposureIndex target records state
      coherent).1

#print axioms foldArmedCompleteDagMemory
#print axioms foldArmedCandidateQueryBatchController
#print axioms foldArmedCandidateSlotUsed
#print axioms fold_armed_candidate_slot_used_mono
#print axioms fold_armed_candidate_preferred_fresh
#print axioms fold_armed_candidate_preferred_used_after_answer
#print axioms fold_armed_candidate_labeled_records_named_slots_nodup

end
end AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
