import AspisFormal.K1.V7Tag73CausalFoldAlphaQ16QueryBatchController
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# Duplicate-free labels for the 542-slot K1.3 controller

The query-batch extension gives priority to the existing 518-slot
fold/alpha/final-work/q16 controller.  This file proves that the combined
controller nevertheless emits every sum-tagged slot at most once.  The proof
tracks the established base used-slot invariant and the query-batch
extension's literal `usedSlots` set; it is independent of honest execution or
of any probability assumption.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup

open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsAokExperiment

noncomputable section

def foldAlphaQ16QueryBatchSlotUsed
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory)) :
    FoldAlphaFinalWorkQ16QueryBatchDigestSlot → Prop
  | .inl slot => foldAlphaFinalWorkQ16SlotUsed (baseIndexedState state) slot
  | .inr slot => slot ∈ state.memory.2.queryBatch.usedSlots

theorem query_batch_extension_used_slots_exact
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) :
    (queryBatchDagExtensionAfterInput dag memory input answer).queryBatch.usedSlots =
      match queryBatchDagPreferredSlotForInput memory input with
      | none => memory.queryBatch.usedSlots
      | some slot => insert slot memory.queryBatch.usedSlots := by
  by_cases unseen : memory.queryBatch.boundarySeen = false
  · cases selected : firstCompactQ16Continuation? memory.q16 with
    | none =>
        simp [queryBatchDagExtensionAfterInput, unseen, selected]
        rfl
    | some continuation =>
        by_cases boundaryInput :
            input = bytes continuation ++ [domAbsorb, queryBatchChallengeLabel]
        · simp [queryBatchDagExtensionAfterInput, unseen, selected,
            boundaryInput]
          rfl
        · simp [queryBatchDagExtensionAfterInput, unseen, selected,
            boundaryInput]
          rfl
  · have seen : memory.queryBatch.boundarySeen = true := by
      exact Bool.eq_true_of_not_eq_false unseen
    simp [queryBatchDagExtensionAfterInput, seen]
    rfl

theorem query_batch_extension_used_slots_mono
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) :
    memory.queryBatch.usedSlots ⊆
      (queryBatchDagExtensionAfterInput dag memory input answer).queryBatch.usedSlots := by
  intro slot member
  rw [query_batch_extension_used_slots_exact]
  cases preferred : queryBatchDagPreferredSlotForInput memory input with
  | none => simpa [preferred] using member
  | some selected => simpa [preferred] using Finset.mem_insert_of_mem member

theorem query_batch_extension_preferred_fresh
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (slot : GammaPrefixDigestSlot)
    (preferred : queryBatchDagPreferredSlotForInput memory input = some slot) :
    slot ∉ memory.queryBatch.usedSlots := by
  unfold queryBatchDagPreferredSlotForInput at preferred
  cases candidateExact :
      ((queryBatchPrefixOutputSlot? memory.queryBatch.producers input).or
        (queryBatchPrefixAdvanceSlot? memory.queryBatch.producers input)) with
  | none => simp [candidateExact] at preferred
  | some candidate =>
      by_cases used : candidate ∈ memory.queryBatch.usedSlots
      · simp [candidateExact, used] at preferred
      · have exact : candidate = slot := by
          simpa [candidateExact, used] using preferred
        simpa [← exact] using used

theorem query_batch_extension_preferred_used_after_input
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) (slot : GammaPrefixDigestSlot)
    (preferred : queryBatchDagPreferredSlotForInput memory input = some slot) :
    slot ∈ (queryBatchDagExtensionAfterInput dag memory input answer).queryBatch.usedSlots := by
  rw [query_batch_extension_used_slots_exact, preferred]
  exact Finset.mem_insert_self slot memory.queryBatch.usedSlots

theorem fold_alpha_q16_query_batch_slot_used_mono
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (answer : Digest256) (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (used : foldAlphaQ16QueryBatchSlotUsed state slot) :
    foldAlphaQ16QueryBatchSlotUsed
      ((foldAlphaQ16QueryBatchController globalOracleCalls transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex).afterAnswer
          transitionFuel state answer) slot := by
  cases slot with
  | inl baseSlot =>
      change foldAlphaFinalWorkQ16SlotUsed
        ((foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
            (alphaZeroCausalController transitionFuel boundaryIndex))).afterAnswer
              transitionFuel (baseIndexedState state) answer) baseSlot
      exact fold_alpha_final_work_q16_slot_used_mono transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex
          (baseIndexedState state) answer baseSlot used
  | inr querySlot =>
      change querySlot ∈ state.memory.2.queryBatch.usedSlots at used
      change querySlot ∈
        (match unifiedInputBeforeAnswer? transitionFuel state.cursor with
          | some input => queryBatchDagExtensionAfterInput
              (completeFoldAlphaQ16DagMemory (baseIndexedState state).memory)
              state.memory.2 input answer
          | none => state.memory.2).queryBatch.usedSlots
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none => simpa [inputExact] using used
      | some input =>
          simpa [inputExact] using query_batch_extension_used_slots_mono
            (completeFoldAlphaQ16DagMemory (baseIndexedState state).memory)
              state.memory.2 input answer used

theorem fold_alpha_q16_query_batch_preferred_fresh
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (preferred :
      (foldAlphaQ16QueryBatchController globalOracleCalls transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex).preferredSlot state =
          some slot) :
    ¬ foldAlphaQ16QueryBatchSlotUsed state slot := by
  let base : IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    foldAlphaFinalWorkQ16Controller foldExposureIndex
    (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
      (alphaZeroCausalController transitionFuel boundaryIndex))
  cases basePreferred : base.preferredSlot (baseIndexedState state) with
  | some baseSlot =>
      have slotExact : slot = .inl baseSlot := by
        simpa [foldAlphaQ16QueryBatchController,
          extendControllerThroughQueryBatch, base, basePreferred] using
            preferred.symm
      subst slot
      exact fold_alpha_final_work_q16_preferred_slot_fresh transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex
          (baseIndexedState state) baseSlot basePreferred
  | none =>
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none =>
          simp [foldAlphaQ16QueryBatchController,
            extendControllerThroughQueryBatch, base, basePreferred, inputExact]
              at preferred
      | some input =>
          cases queryPreferred : queryBatchDagPreferredSlotForInput
              state.memory.2 input with
          | none =>
              simp [foldAlphaQ16QueryBatchController,
                extendControllerThroughQueryBatch, base, basePreferred,
                inputExact, queryPreferred] at preferred
          | some querySlot =>
              have slotExact : slot = .inr querySlot := by
                simpa [foldAlphaQ16QueryBatchController,
                  extendControllerThroughQueryBatch, base, basePreferred,
                  inputExact, queryPreferred] using preferred.symm
              subst slot
              exact query_batch_extension_preferred_fresh state.memory.2 input
                querySlot queryPreferred

theorem fold_alpha_q16_query_batch_preferred_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (preferred :
      (foldAlphaQ16QueryBatchController globalOracleCalls transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex).preferredSlot state =
          some slot) :
    foldAlphaQ16QueryBatchSlotUsed
      ((foldAlphaQ16QueryBatchController globalOracleCalls transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex).afterAnswer
          transitionFuel state answer) slot := by
  let base : IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    foldAlphaFinalWorkQ16Controller foldExposureIndex
    (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
      (alphaZeroCausalController transitionFuel boundaryIndex))
  cases basePreferred : base.preferredSlot (baseIndexedState state) with
  | some baseSlot =>
      have slotExact : slot = .inl baseSlot := by
        simpa [foldAlphaQ16QueryBatchController,
          extendControllerThroughQueryBatch, base, basePreferred] using
            preferred.symm
      subst slot
      change foldAlphaFinalWorkQ16SlotUsed
        (base.afterAnswer transitionFuel (baseIndexedState state) answer)
          baseSlot
      exact fold_alpha_final_work_q16_preferred_slot_used_after_answer
        transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
          (baseIndexedState state) answer baseSlot basePreferred
  | none =>
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none =>
          simp [foldAlphaQ16QueryBatchController,
            extendControllerThroughQueryBatch, base, basePreferred, inputExact]
              at preferred
      | some input =>
          cases queryPreferred : queryBatchDagPreferredSlotForInput
              state.memory.2 input with
          | none =>
              simp [foldAlphaQ16QueryBatchController,
                extendControllerThroughQueryBatch, base, basePreferred,
                inputExact, queryPreferred] at preferred
          | some querySlot =>
              have slotExact : slot = .inr querySlot := by
                simpa [foldAlphaQ16QueryBatchController,
                  extendControllerThroughQueryBatch, base, basePreferred,
                  inputExact, queryPreferred] using preferred.symm
              subst slot
              have queryUsed :=
                query_batch_extension_preferred_used_after_input
                  (completeFoldAlphaQ16DagMemory
                    (baseIndexedState state).memory)
                  state.memory.2 input answer querySlot queryPreferred
              simpa [foldAlphaQ16QueryBatchSlotUsed,
                foldAlphaQ16QueryBatchController,
                IndexedUnifiedExposureController.afterAnswer,
                extendControllerThroughQueryBatch, inputExact] using queryUsed

theorem fold_alpha_q16_query_batch_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory CompleteFoldAlphaQ16Memory)),
      let controller := foldAlphaQ16QueryBatchController globalOracleCalls
        transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          ¬ foldAlphaQ16QueryBatchSlotUsed state slot := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller := foldAlphaQ16QueryBatchController globalOracleCalls
        transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : ∀ slot, foldAlphaQ16QueryBatchSlotUsed state slot →
          foldAlphaQ16QueryBatchSlotUsed next slot := by
        intro slot used
        simpa [next, controller] using
          fold_alpha_q16_query_batch_slot_used_mono transitionFuel
            foldExposureIndex finalExposureIndex boundaryIndex state
              record.answer slot used
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            ¬ foldAlphaQ16QueryBatchSlotUsed state slot
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1 (fun slot member used =>
            tail.2 slot member (usedMono slot used))
      | some slot =>
          have slotFresh : ¬ foldAlphaQ16QueryBatchSlotUsed state slot :=
            fold_alpha_q16_query_batch_preferred_fresh transitionFuel
              foldExposureIndex finalExposureIndex boundaryIndex state slot
                (by simpa [controller] using preferred)
          have nextUsed : foldAlphaQ16QueryBatchSlotUsed next slot := by
            simpa [next, controller] using
              fold_alpha_q16_query_batch_preferred_used_after_answer
                transitionFuel foldExposureIndex finalExposureIndex
                  boundaryIndex state record.answer slot
                    (by simpa [controller] using preferred)
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), ¬ foldAlphaQ16QueryBatchSlotUsed state candidate := by
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

theorem fold_alpha_q16_query_batch_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory)) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (foldAlphaQ16QueryBatchController globalOracleCalls transitionFuel
          foldExposureIndex finalExposureIndex boundaryIndex)
        state records)).Nodup :=
  (fold_alpha_q16_query_batch_labeled_records_nodup_and_avoid_initial
    transitionFuel foldExposureIndex finalExposureIndex boundaryIndex records
      state).1

#print axioms foldAlphaQ16QueryBatchSlotUsed
#print axioms query_batch_extension_used_slots_exact
#print axioms query_batch_extension_used_slots_mono
#print axioms query_batch_extension_preferred_fresh
#print axioms query_batch_extension_preferred_used_after_input
#print axioms fold_alpha_q16_query_batch_slot_used_mono
#print axioms fold_alpha_q16_query_batch_preferred_fresh
#print axioms fold_alpha_q16_query_batch_preferred_used_after_answer
#print axioms fold_alpha_q16_query_batch_labeled_records_named_slots_nodup

end
end AspisK1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup
