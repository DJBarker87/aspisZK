import AspisFormal.K1.V7Tag73CausalFoldAlphaQ16QueryBatchController

/-!
# Candidate-directed query-batch controller

The selected-first-compact query-batch controller can arm only after every
q16 output needed to decode the selected schedule has been observed.  An
adaptive prover may instead expose a candidate's advance chain and its
post-candidate query-batch coordinate before exposing the sibling q16 outputs.

This controller fixes one of the 512 q16 digest slots in advance.  Once the
advance answer for that slot has been causally observed, its exact
query-batch-domain child can arm without inspecting any future q16 output.
The complete K1.3 event can consequently be covered by the finite union over
the 512 possible terminal slots.  No raw SHA input is assigned a role after
its answer is seen.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateDirectedQueryBatchController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The already-returned advance answer at one pre-fixed q16 slot. -/
def candidateContinuation?
    (target : Q16DigestSlot) (observed : ObservedQ16Duplex) :
    Option Digest256 :=
  observed.advances target

/-- Extend the query-batch DAG relative to one q16 terminal-slot hypothesis.
The observer is still updated at every exposure; the hypothesis affects only
the pre-answer boundary arming predicate. -/
def candidateDirectedQueryBatchAfterInput
    (target : Q16DigestSlot)
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256) : QueryBatchDagExtensionMemory :=
  let nextQ16 := memory.q16.afterInput dag input answer
  let preferred := queryBatchDagPreferredSlotForInput memory input
  let nextUsed :=
    match preferred with
    | none => memory.queryBatch.usedSlots
    | some slot => insert slot memory.queryBatch.usedSlots
  let nextQueryBatch :=
    if !memory.queryBatch.boundarySeen then
      match candidateContinuation? target memory.q16 with
      | some continuation =>
          if input = bytes continuation ++
              [domAbsorb, queryBatchChallengeLabel] then
            { boundarySeen := true
              producers :=
                [{ digest := answer, block := 0, sourceInput := input }]
              usedSlots := nextUsed }
          else
            { memory.queryBatch with usedSlots := nextUsed }
      | none => { memory.queryBatch with usedSlots := nextUsed }
    else
      { boundarySeen := true
        producers := extendQueryBatchPrefixProducers
          memory.queryBatch.producers input answer
        usedSlots := nextUsed }
  { q16 := nextQ16, queryBatch := nextQueryBatch }

/-- The exact domain child of an already-observed target advance arms the
query-batch chain. -/
theorem exact_candidate_boundary_arms_query_batch
    (target : Q16DigestSlot)
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer continuation : Digest256)
    (unseen : memory.queryBatch.boundarySeen = false)
    (empty : memory.queryBatch.producers = [])
    (targetExact : memory.q16.advances target = some continuation)
    (inputExact : input = bytes continuation ++
      [domAbsorb, queryBatchChallengeLabel]) :
    (candidateDirectedQueryBatchAfterInput target dag memory input answer
      ).queryBatch =
      { boundarySeen := true
        producers := [{ digest := answer, block := 0, sourceInput := input }]
        usedSlots := memory.queryBatch.usedSlots } := by
  subst input
  simp [candidateDirectedQueryBatchAfterInput, candidateContinuation?,
    queryBatchDagPreferredSlotForInput, queryBatchPrefixOutputSlot?,
    queryBatchPrefixAdvanceSlot?, unseen, empty, targetExact]

/-- Until the target advance answer has been observed, a lookalike domain
input cannot claim this hypothesis's query-batch coordinates. -/
theorem missing_candidate_continuation_cannot_arm
    (target : Q16DigestSlot)
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256)
    (unseen : memory.queryBatch.boundarySeen = false)
    (empty : memory.queryBatch.producers = [])
    (missing : memory.q16.advances target = none) :
    (candidateDirectedQueryBatchAfterInput target dag memory input answer
      ).queryBatch = memory.queryBatch := by
  rcases memory with ⟨q16, queryBatch⟩
  rcases queryBatch with ⟨boundarySeen, producers, usedSlots⟩
  simp_all [candidateDirectedQueryBatchAfterInput, candidateContinuation?,
    queryBatchDagPreferredSlotForInput, queryBatchPrefixOutputSlot?,
    queryBatchPrefixAdvanceSlot?]

/-- Extend any established controller with one pre-fixed q16 terminal-slot
hypothesis. Existing labels retain priority. -/
def extendControllerThroughCandidateQueryBatch
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      (Slot ⊕ GammaPrefixDigestSlot) (ExtendedControllerMemory Memory) where
  preferredSlot := fun state ↦
    match base.preferredSlot (baseIndexedState state) with
    | some slot => some (Sum.inl slot)
    | none =>
        match unifiedInputBeforeAnswer? transitionFuel state.cursor with
        | some input =>
            (queryBatchDagPreferredSlotForInput state.memory.2 input).map
              Sum.inr
        | none => none
  afterMemory := fun state answer ↦
    let baseState := baseIndexedState state
    let nextBase := base.afterMemory baseState answer
    let nextExtension :=
      match unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | some input => candidateDirectedQueryBatchAfterInput target
          (dagOf baseState.memory) state.memory.2 input answer
      | none => state.memory.2
    (nextBase, nextExtension)

@[simp] theorem candidate_extended_base_after_memory
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (answer : Digest256) :
    ((extendControllerThroughCandidateQueryBatch transitionFuel target base
      dagOf).afterMemory state answer).1 =
        base.afterMemory (baseIndexedState state) answer := by
  rfl

@[simp] theorem candidate_extended_preserves_base_label
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (slot : Slot)
    (preferred : base.preferredSlot (baseIndexedState state) = some slot) :
    (extendControllerThroughCandidateQueryBatch transitionFuel target base
      dagOf).preferredSlot state = some (Sum.inl slot) := by
  simp [extendControllerThroughCandidateQueryBatch, preferred]

@[simp] theorem candidate_extended_uses_query_batch_label
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (input : ShaInput) (slot : GammaPrefixDigestSlot)
    (baseNone : base.preferredSlot (baseIndexedState state) = none)
    (inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input)
    (preferred : queryBatchDagPreferredSlotForInput state.memory.2 input =
      some slot) :
    (extendControllerThroughCandidateQueryBatch transitionFuel target base
      dagOf).preferredSlot state = some (Sum.inr slot) := by
  simp [extendControllerThroughCandidateQueryBatch, baseNone, inputExact,
    preferred]

#print axioms candidateContinuation?
#print axioms candidateDirectedQueryBatchAfterInput
#print axioms exact_candidate_boundary_arms_query_batch
#print axioms missing_candidate_continuation_cannot_arm
#print axioms extendControllerThroughCandidateQueryBatch
#print axioms candidate_extended_base_after_memory
#print axioms candidate_extended_preserves_base_label
#print axioms candidate_extended_uses_query_batch_label

end
end AspisK1.V7Tag73CandidateDirectedQueryBatchController
