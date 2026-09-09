import AspisFormal.K1.V7Tag73GammaPrefixCausalController
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-! # One-shot gamma-prefix label invariant -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73GammaPrefixLabeledRecordsNodup

open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The memory update either preserves the used gamma slots or inserts the
slot selected before the current answer. -/
theorem gamma_prefix_after_memory_used_slots
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory) (answer : Digest256) :
    (gammaPrefixAfterMemory transitionFuel state answer).usedSlots =
      match gammaPrefixPreferredSlot transitionFuel state with
      | none => state.memory.usedSlots
      | some slot => insert slot state.memory.usedSlots := by
  unfold gammaPrefixAfterMemory
  cases inputExact : unifiedVerifierInputBeforeAnswer? transitionFuel
      state.cursor with
  | none =>
      simp [inputExact, gammaPrefixPreferredSlot]
  | some input =>
      simp only [inputExact]
      split <;> rfl

/-- Every selected gamma slot is fresh relative to the controller memory. -/
theorem gamma_prefix_preferred_slot_fresh
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory) (slot : GammaPrefixDigestSlot)
    (preferred : gammaPrefixPreferredSlot transitionFuel state = some slot) :
    slot ∉ state.memory.usedSlots := by
  unfold gammaPrefixPreferredSlot at preferred
  cases inputExact : unifiedVerifierInputBeforeAnswer? transitionFuel
      state.cursor with
  | none => simp [inputExact] at preferred
  | some input =>
      simp only [inputExact] at preferred
      cases candidateExact :
          (gammaPrefixOutputSlot? state.memory.producers input).or
            (gammaPrefixAdvanceSlot? state.memory.producers input) with
      | none => simp [candidateExact] at preferred
      | some candidate =>
          by_cases used : candidate ∈ state.memory.usedSlots
          · simp [candidateExact, used] at preferred
          · have candidateEq : candidate = slot := by
              have : some candidate = some slot := by
                simpa [candidateExact, used] using preferred
              exact Option.some.inj this
            simpa [← candidateEq] using used

/-- Named gamma-prefix labels are duplicate-free and avoid all slots already
used at the beginning of the replay segment. -/
theorem gamma_prefix_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        GammaPrefixControllerMemory),
      let labels := indexedControllerLabeledRecords transitionFuel
        (gammaPrefixCausalController transitionFuel) state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels, slot ∉ state.memory.usedSlots := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state
      let controller := gammaPrefixCausalController
        (globalOracleCalls := globalOracleCalls) transitionFuel
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : state.memory.usedSlots ⊆ next.memory.usedSlots := by
        intro slot member
        change slot ∈
          (gammaPrefixAfterMemory transitionFuel state record.answer).usedSlots
        rw [gamma_prefix_after_memory_used_slots]
        cases preferred : gammaPrefixPreferredSlot transitionFuel state with
        | none => exact member
        | some selected => exact Finset.mem_insert_of_mem member
      cases preferred : controller.preferredSlot state with
      | none =>
          have preferred' : gammaPrefixPreferredSlot transitionFuel state =
              none := by
            simpa [controller, gammaPrefixCausalController] using preferred
          simpa [indexedControllerLabeledRecords, controller, next, preferred,
            preferred', namedTraceSlots] using
            And.intro tail.1 (fun slot member used =>
              tail.2 slot member (usedMono used))
      | some slot =>
          have preferred' : gammaPrefixPreferredSlot transitionFuel state =
              some slot := by
            simpa [controller, gammaPrefixCausalController] using preferred
          have slotFresh : slot ∉ state.memory.usedSlots :=
            gamma_prefix_preferred_slot_fresh transitionFuel state slot
              preferred'
          have nextUsed : slot ∈ next.memory.usedSlots := by
            change slot ∈
              (gammaPrefixAfterMemory transitionFuel state
                record.answer).usedSlots
            rw [gamma_prefix_after_memory_used_slots, preferred']
            exact Finset.mem_insert_self slot state.memory.usedSlots
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), candidate ∉ state.memory.usedSlots := by
            intro candidate member used
            exact tail.2 candidate member (usedMono used)
          dsimp only
          rw [indexed_controller_labeled_records_cons, preferred]
          simp only [namedTraceSlots]
          constructor
          · exact List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩
          · intro candidate member
            rcases List.mem_cons.mp member with equal | tailMember
            · subst candidate
              exact slotFresh
            · exact tailAvoidsInitial candidate tailMember

theorem gamma_prefix_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      GammaPrefixControllerMemory) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (gammaPrefixCausalController transitionFuel) state records)).Nodup :=
  (gamma_prefix_labeled_records_nodup_and_avoid_initial transitionFuel records
    state).1

#print axioms gamma_prefix_after_memory_used_slots
#print axioms gamma_prefix_preferred_slot_fresh
#print axioms gamma_prefix_labeled_records_nodup_and_avoid_initial
#print axioms gamma_prefix_labeled_records_named_slots_nodup

end
end AspisK1.V7Tag73GammaPrefixLabeledRecordsNodup
