import AspisFormal.K1.V7Tag73CausalFoldAlphaQ16QueryBatchController
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords
import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment

/-!
# Projection of the 542-slot controller to the established 518-slot trace

The query-batch extension is observationally conservative for every existing
fold/alpha/work/q16 label.  Replaying any answer list through the extended
controller reaches exactly the same base cursor, exposure index, and base
memory as replaying it through the old controller.  Projecting away right-hand
query-batch labels recovers the old labelled trace pointwise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExtendedQueryBatchControllerProjection

open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

@[simp] theorem base_indexed_state_after_extended_answer
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (answer : Digest256) :
    baseIndexedState
        ((extendControllerThroughQueryBatch transitionFuel base dagOf).afterAnswer
          transitionFuel state answer) =
      base.afterAnswer transitionFuel (baseIndexedState state) answer := by
  rfl

/-- The new extension cannot perturb any established base-controller state. -/
theorem base_indexed_state_after_extended_records
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory) :
    ∀ (records : List
        AspisK1.V7Tag73AtomicForkUniformScheduler.UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      baseIndexedState
          (indexedStateAfterRecords transitionFuel
            (extendControllerThroughQueryBatch transitionFuel base dagOf)
            records state) =
        indexedStateAfterRecords transitionFuel base records
          (baseIndexedState state) := by
  intro records
  induction records with
  | nil => intro state; rfl
  | cons record records ih =>
      intro state
      rw [indexed_state_after_records_cons,
        indexed_state_after_records_cons]
      simpa using ih
        ((extendControllerThroughQueryBatch transitionFuel base dagOf).afterAnswer
          transitionFuel state record.answer)

def projectBaseLabel {Slot : Type} : Option (Slot ⊕ GammaPrefixDigestSlot) →
    Option Slot
  | some (Sum.inl slot) => some slot
  | some (Sum.inr _) | none => none

def projectBaseLabeledAnswer {Slot : Type} :
    Option (Slot ⊕ GammaPrefixDigestSlot) × Digest256 →
      Option Slot × Digest256
  | (label, answer) => (projectBaseLabel label, answer)

theorem extended_preferred_projects_to_base
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory)) :
    projectBaseLabel
        ((extendControllerThroughQueryBatch transitionFuel base dagOf
          ).preferredSlot state) =
      base.preferredSlot (baseIndexedState state) := by
  unfold extendControllerThroughQueryBatch projectBaseLabel
  cases preferred : base.preferredSlot (baseIndexedState state) with
  | some slot => simp [preferred]
  | none =>
      simp only [preferred]
      cases inputExact :
          AspisK1.V7Tag73FinalWorkQ16CandidateController.unifiedInputBeforeAnswer?
            transitionFuel state.cursor with
      | none => simp [inputExact, projectBaseLabel]
      | some input =>
          cases queryPreferred :
              queryBatchDagPreferredSlotForInput state.memory.2 input with
          | none => simp [inputExact, queryPreferred, projectBaseLabel]
          | some slot => simp [inputExact, queryPreferred, projectBaseLabel]

/-- Projecting every extended label gives exactly the old labelled execution,
including at adversary-first records and cache-independent fork records. -/
theorem extended_labeled_records_project_to_base
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory) :
    ∀ (records : List
        AspisK1.V7Tag73AtomicForkUniformScheduler.UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      (indexedControllerLabeledRecords transitionFuel
          (extendControllerThroughQueryBatch transitionFuel base dagOf)
          state records).map projectBaseLabeledAnswer =
        indexedControllerLabeledRecords transitionFuel base
          (baseIndexedState state) records := by
  intro records
  induction records with
  | nil => intro state; rfl
  | cons record records ih =>
      intro state
      simp only [indexed_controller_labeled_records_cons, List.map_cons]
      apply congrArg₂ List.cons
      · apply Prod.ext
        · exact extended_preferred_projects_to_base transitionFuel base dagOf
            state
        · rfl
      · simpa using ih
          ((extendControllerThroughQueryBatch transitionFuel base dagOf
            ).afterAnswer transitionFuel state record.answer)

#print axioms base_indexed_state_after_extended_answer
#print axioms base_indexed_state_after_extended_records
#print axioms extended_preferred_projects_to_base
#print axioms extended_labeled_records_project_to_base

end
end AspisK1.V7Tag73ExtendedQueryBatchControllerProjection
