import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchController
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup
import AspisFormal.K1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# Duplicate-free labels for a candidate-directed K1.3 controller

Fixing one q16 terminal slot changes only the condition that arms the
query-batch extension.  The used-slot accounting is otherwise identical:
every preferred query-batch slot is fresh, becomes used with its answer, and
stays used.  Together with the established 518-slot base invariant this makes
all sum-tagged labels one-shot on every answer stream.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateDirectedQueryBatchLabelsNodup

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16LabelsNodup
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def candidateDirectedSlotUsed
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory)) :
    FoldAlphaFinalWorkQ16QueryBatchDigestSlot → Prop
  | .inl slot => foldAlphaFinalWorkQ16SlotUsed (baseIndexedState state) slot
  | .inr slot => slot ∈ state.memory.2.queryBatch.usedSlots

theorem candidate_query_batch_used_slots_exact
    (target : Q16DigestSlot)
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) :
    (candidateDirectedQueryBatchAfterInput target dag memory input answer
      ).queryBatch.usedSlots =
      match queryBatchDagPreferredSlotForInput memory input with
      | none => memory.queryBatch.usedSlots
      | some slot => insert slot memory.queryBatch.usedSlots := by
  by_cases unseen : memory.queryBatch.boundarySeen = false
  · cases selected : candidateContinuation? target memory.q16 with
    | none =>
        simp [candidateDirectedQueryBatchAfterInput, unseen, selected]
        rfl
    | some continuation =>
        by_cases boundaryInput :
            input = bytes continuation ++ [domAbsorb, queryBatchChallengeLabel]
        · simp [candidateDirectedQueryBatchAfterInput, unseen, selected,
            boundaryInput]
          rfl
        · simp [candidateDirectedQueryBatchAfterInput, unseen, selected,
            boundaryInput]
          rfl
  · have seen : memory.queryBatch.boundarySeen = true :=
      Bool.eq_true_of_not_eq_false unseen
    simp [candidateDirectedQueryBatchAfterInput, seen]
    rfl

theorem candidate_query_batch_used_slots_mono
    (target : Q16DigestSlot)
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) :
    memory.queryBatch.usedSlots ⊆
      (candidateDirectedQueryBatchAfterInput target dag memory input answer
        ).queryBatch.usedSlots := by
  intro slot member
  rw [candidate_query_batch_used_slots_exact]
  cases preferred : queryBatchDagPreferredSlotForInput memory input with
  | none => simpa [preferred] using member
  | some selected => simpa [preferred] using Finset.mem_insert_of_mem member

theorem candidate_query_batch_preferred_used_after_input
    (target : Q16DigestSlot)
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) (slot : GammaPrefixDigestSlot)
    (preferred : queryBatchDagPreferredSlotForInput memory input = some slot) :
    slot ∈ (candidateDirectedQueryBatchAfterInput target dag memory input answer
      ).queryBatch.usedSlots := by
  rw [candidate_query_batch_used_slots_exact, preferred]
  exact Finset.mem_insert_self slot memory.queryBatch.usedSlots

theorem candidate_directed_slot_used_mono
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (target : Q16DigestSlot)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (answer : Digest256) (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (used : candidateDirectedSlotUsed state slot) :
    candidateDirectedSlotUsed
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
            (alphaZeroCausalController transitionFuel boundaryIndex)))
        completeFoldAlphaQ16DagMemory).afterAnswer transitionFuel state answer)
      slot := by
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
          | some input => candidateDirectedQueryBatchAfterInput target
              (completeFoldAlphaQ16DagMemory (baseIndexedState state).memory)
              state.memory.2 input answer
          | none => state.memory.2).queryBatch.usedSlots
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none => simpa [inputExact] using used
      | some input =>
          simpa [inputExact] using candidate_query_batch_used_slots_mono target
            (completeFoldAlphaQ16DagMemory (baseIndexedState state).memory)
              state.memory.2 input answer used

theorem candidate_directed_preferred_fresh
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (target : Q16DigestSlot)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (preferred :
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
            (alphaZeroCausalController transitionFuel boundaryIndex)))
        completeFoldAlphaQ16DagMemory).preferredSlot state = some slot) :
    ¬ candidateDirectedSlotUsed state slot := by
  let base : IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    foldAlphaFinalWorkQ16Controller foldExposureIndex
      (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
        (alphaZeroCausalController transitionFuel boundaryIndex))
  cases basePreferred : base.preferredSlot (baseIndexedState state) with
  | some baseSlot =>
      have slotExact : slot = .inl baseSlot := by
        simpa [extendControllerThroughCandidateQueryBatch, base,
          basePreferred] using preferred.symm
      subst slot
      exact fold_alpha_final_work_q16_preferred_slot_fresh transitionFuel
        foldExposureIndex finalExposureIndex boundaryIndex
          (baseIndexedState state) baseSlot basePreferred
  | none =>
      cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none =>
          simp [extendControllerThroughCandidateQueryBatch, base,
            basePreferred, inputExact] at preferred
      | some input =>
          cases queryPreferred : queryBatchDagPreferredSlotForInput
              state.memory.2 input with
          | none =>
              simp [extendControllerThroughCandidateQueryBatch, base,
                basePreferred, inputExact, queryPreferred] at preferred
          | some querySlot =>
              have slotExact : slot = .inr querySlot := by
                simpa [extendControllerThroughCandidateQueryBatch, base,
                  basePreferred, inputExact, queryPreferred] using preferred.symm
              subst slot
              exact
                AspisK1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup.query_batch_extension_preferred_fresh
                  state.memory.2 input querySlot queryPreferred

theorem candidate_directed_preferred_used_after_answer
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (target : Q16DigestSlot)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (preferred :
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
            (alphaZeroCausalController transitionFuel boundaryIndex)))
        completeFoldAlphaQ16DagMemory).preferredSlot state = some slot) :
    candidateDirectedSlotUsed
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (foldAlphaFinalWorkQ16Controller foldExposureIndex
          (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
            (alphaZeroCausalController transitionFuel boundaryIndex)))
        completeFoldAlphaQ16DagMemory).afterAnswer transitionFuel state answer)
      slot := by
  let base : IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    foldAlphaFinalWorkQ16Controller foldExposureIndex
      (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
        (alphaZeroCausalController transitionFuel boundaryIndex))
  cases basePreferred : base.preferredSlot (baseIndexedState state) with
  | some baseSlot =>
      have slotExact : slot = .inl baseSlot := by
        simpa [extendControllerThroughCandidateQueryBatch, base,
          basePreferred] using preferred.symm
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
          simp [extendControllerThroughCandidateQueryBatch, base,
            basePreferred, inputExact] at preferred
      | some input =>
          cases queryPreferred : queryBatchDagPreferredSlotForInput
              state.memory.2 input with
          | none =>
              simp [extendControllerThroughCandidateQueryBatch, base,
                basePreferred, inputExact, queryPreferred] at preferred
          | some querySlot =>
              have slotExact : slot = .inr querySlot := by
                simpa [extendControllerThroughCandidateQueryBatch, base,
                  basePreferred, inputExact, queryPreferred] using preferred.symm
              subst slot
              have queryUsed := candidate_query_batch_preferred_used_after_input
                target
                (completeFoldAlphaQ16DagMemory (baseIndexedState state).memory)
                state.memory.2 input answer querySlot queryPreferred
              simpa [candidateDirectedSlotUsed,
                IndexedUnifiedExposureController.afterAnswer,
                extendControllerThroughCandidateQueryBatch, inputExact] using
                queryUsed

theorem candidate_directed_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (target : Q16DigestSlot) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory CompleteFoldAlphaQ16Memory)),
      let controller : IndexedUnifiedExposureController globalOracleCalls
          Digest256 FoldAlphaFinalWorkQ16QueryBatchDigestSlot
          (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
        extendControllerThroughCandidateQueryBatch transitionFuel target
          (foldAlphaFinalWorkQ16Controller foldExposureIndex
            (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
              (alphaZeroCausalController transitionFuel boundaryIndex)))
          completeFoldAlphaQ16DagMemory
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          ¬ candidateDirectedSlotUsed state slot := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller : IndexedUnifiedExposureController globalOracleCalls
          Digest256 FoldAlphaFinalWorkQ16QueryBatchDigestSlot
          (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
        extendControllerThroughCandidateQueryBatch transitionFuel target
          (foldAlphaFinalWorkQ16Controller foldExposureIndex
            (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
              (alphaZeroCausalController transitionFuel boundaryIndex)))
          completeFoldAlphaQ16DagMemory
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : ∀ slot, candidateDirectedSlotUsed state slot →
          candidateDirectedSlotUsed next slot := by
        intro slot used
        simpa [next, controller] using candidate_directed_slot_used_mono
          transitionFuel foldExposureIndex finalExposureIndex boundaryIndex
          target state record.answer slot used
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            ¬ candidateDirectedSlotUsed state slot
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1 (fun slot member used =>
            tail.2 slot member (usedMono slot used))
      | some slot =>
          have slotFresh : ¬ candidateDirectedSlotUsed state slot :=
            candidate_directed_preferred_fresh transitionFuel foldExposureIndex
              finalExposureIndex boundaryIndex target state slot
                (by simpa [controller] using preferred)
          have nextUsed : candidateDirectedSlotUsed next slot := by
            simpa [next, controller] using
              candidate_directed_preferred_used_after_answer transitionFuel
                foldExposureIndex finalExposureIndex boundaryIndex target state
                  record.answer slot (by simpa [controller] using preferred)
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), ¬ candidateDirectedSlotUsed state candidate := by
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

theorem candidate_directed_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (target : Q16DigestSlot)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory)) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target
          (foldAlphaFinalWorkQ16Controller foldExposureIndex
            (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
              (alphaZeroCausalController transitionFuel boundaryIndex)))
          completeFoldAlphaQ16DagMemory)
        state records)).Nodup :=
  (candidate_directed_labeled_records_nodup_and_avoid_initial transitionFuel
    foldExposureIndex finalExposureIndex boundaryIndex target records state).1

#print axioms candidateDirectedSlotUsed
#print axioms candidate_query_batch_used_slots_exact
#print axioms candidate_query_batch_used_slots_mono
#print axioms candidate_query_batch_preferred_used_after_input
#print axioms candidate_directed_slot_used_mono
#print axioms candidate_directed_preferred_fresh
#print axioms candidate_directed_preferred_used_after_answer
#print axioms candidate_directed_labeled_records_named_slots_nodup

end
end AspisK1.V7Tag73CandidateDirectedQueryBatchLabelsNodup
