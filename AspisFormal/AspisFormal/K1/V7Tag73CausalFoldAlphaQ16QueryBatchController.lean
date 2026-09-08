import AspisFormal.K1.V7Tag73AlphaZeroCausalController
import AspisFormal.K1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
import AspisFormal.K1.V7Tag73QueryBatchPrefixCausalController
import AspisFormal.K1.V7Tag73Q16SemanticFrontierBridge
import AspisFormal.K1.V7Tag73SamplerDecoder

/-!
# Adversary-first causal controller through the Tag-73 query batch

The standalone query-batch controller recognizes only verifier-origin fresh
queries.  That is insufficient for Fiat--Shamir: the prover may expose the
real coordinate first and the verifier can later receive a cache hit.

This controller instead extends the established final-work/q16 causal DAG.
It records q16 squeeze outputs and advances only when their inputs are
causally derived from the real saved q16 base.  Once the first compact
candidate can be decoded from a complete chronological prefix, its final
advance answer determines the unique post-q16 digest.  Only the exact
query-batch-domain input derived from that digest can arm the final duplex.
Thus an unrelated early 34-byte lookalike cannot steal the coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Answers observed at the two sides of each causally known q16 block. -/
structure ObservedQ16Duplex where
  outputs : Q16DigestSlot → Option Digest256
  advances : Q16DigestSlot → Option Digest256

def emptyObservedQ16Duplex : ObservedQ16Duplex :=
  { outputs := fun _ ↦ none
    advances := fun _ ↦ none }

def initialSomePrefix : List (Option Digest256) → List Digest256
  | some value :: rest => value :: initialSomePrefix rest
  | none :: _ | [] => []

def observedQ16OutputPrefix (observed : ObservedQ16Duplex)
    (counter : Fin 64) : List Digest256 :=
  initialSomePrefix
    (List.ofFn fun block : Fin 8 ↦ observed.outputs (counter, block))

def q16AdvanceSlot? (producers : List Q16DagProducer)
    (input : ShaInput) : Option Q16DigestSlot :=
  (producers.find? fun producer ↦
    decide (input = bytes producer.digest ++ [domAdvance])).map
      Q16DagProducer.slot

def ObservedQ16Duplex.afterInput (observed : ObservedQ16Duplex)
    (dag : FinalWorkQ16DagMemory) (input : ShaInput) (answer : Digest256) :
    ObservedQ16Duplex :=
  let outputs :=
    match q16DagOutputSlot? dag.producers input with
    | some slot =>
        if observed.outputs slot = none then
          Function.update observed.outputs slot (some answer)
        else observed.outputs
    | none => observed.outputs
  let advances :=
    match q16AdvanceSlot? dag.producers input with
    | some slot =>
        if observed.advances slot = none then
          Function.update observed.advances slot (some answer)
        else observed.advances
    | none => observed.advances
  { outputs := outputs, advances := advances }

theorem observed_q16_output_is_monotone
    (observed : ObservedQ16Duplex) (dag : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer existing : Digest256) (slot : Q16DigestSlot)
    (present : observed.outputs slot = some existing) :
    (observed.afterInput dag input answer).outputs slot = some existing := by
  simp only [ObservedQ16Duplex.afterInput]
  cases outputSlot : q16DagOutputSlot? dag.producers input with
  | none => simpa [outputSlot] using present
  | some selected =>
      by_cases selectedExact : selected = slot
      · subst selected
        simp [outputSlot, present]
      · by_cases vacant : observed.outputs selected = none
        · have slotNe : slot ≠ selected := Ne.symm selectedExact
          simp [outputSlot, vacant, Function.update, slotNe, present]
        · simp [outputSlot, vacant, present]

theorem observed_q16_advance_is_monotone
    (observed : ObservedQ16Duplex) (dag : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer existing : Digest256) (slot : Q16DigestSlot)
    (present : observed.advances slot = some existing) :
    (observed.afterInput dag input answer).advances slot = some existing := by
  simp only [ObservedQ16Duplex.afterInput]
  cases advanceSlot : q16AdvanceSlot? dag.producers input with
  | none => simpa [advanceSlot] using present
  | some selected =>
      by_cases selectedExact : selected = slot
      · subst selected
        simp [advanceSlot, present]
      · by_cases vacant : observed.advances selected = none
        · have slotNe : slot ≠ selected := Ne.symm selectedExact
          simp [advanceSlot, vacant, Function.update, slotNe, present]
        · simp [advanceSlot, vacant, present]

theorem observed_q16_output_installed
    (observed : ObservedQ16Duplex) (dag : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) (slot : Q16DigestSlot)
    (empty : observed.outputs slot = none)
    (selected : q16DagOutputSlot? dag.producers input = some slot) :
    (observed.afterInput dag input answer).outputs slot = some answer := by
  simp [ObservedQ16Duplex.afterInput, selected, empty]

theorem observed_q16_advance_installed
    (observed : ObservedQ16Duplex) (dag : FinalWorkQ16DagMemory)
    (input : ShaInput) (answer : Digest256) (slot : Q16DigestSlot)
    (empty : observed.advances slot = none)
    (selected : q16AdvanceSlot? dag.producers input = some slot) :
    (observed.afterInput dag input answer).advances slot = some answer := by
  simp [ObservedQ16Duplex.afterInput, selected, empty]

/-- The continuing digest after one decoded candidate is its last paired
advance answer. -/
def decodedCandidateContinuation?
    (observed : ObservedQ16Duplex) (counter : Fin 64)
    (schedule : QuerySchedule) : Option Digest256 :=
  let last : Fin 8 :=
    ⟨schedule.blocksUsed - 1, by
      have bounds := every_query_schedule_has_exact_deployed_block_cap schedule
      omega⟩
  observed.advances (counter, last)

/-- Scan only a complete chronological prefix.  An undecoded, aborted, or
advance-incomplete earlier candidate blocks selection of every later one. -/
def firstCompactContinuationFrom
    (observed : ObservedQ16Duplex) : List (Fin 64) → Option Digest256
  | [] => none
  | counter :: rest =>
      match decodeCandidateOutcome counter
          (observedQ16OutputPrefix observed counter) with
      | some (.schedule schedule) =>
          match decodedCandidateContinuation? observed counter schedule with
          | none => none
          | some continuation =>
              if semanticFrontierNodes schedule.positions ≤ 203 then
                some continuation
              else
                firstCompactContinuationFrom observed rest
      | some .samplerAbort | none => none

def firstCompactQ16Continuation?
    (observed : ObservedQ16Duplex) : Option Digest256 :=
  firstCompactContinuationFrom observed (List.ofFn id)

/-- A deterministic prefix certificate identifies the exact first compact
continuation without any probability or oracle-role assumption. -/
theorem first_compact_continuation_from_exact_prefix
    (observed : ObservedQ16Duplex)
    (prior rest : List (Fin 64)) (selected : Fin 64)
    (selectedSchedule : QuerySchedule) (continuation : Digest256)
    (priorNoncompact : ∀ counter ∈ prior,
      ∃ schedule priorContinuation,
        decodeCandidateOutcome counter
            (observedQ16OutputPrefix observed counter) =
          some (.schedule schedule) ∧
        decodedCandidateContinuation? observed counter schedule =
          some priorContinuation ∧
        203 < semanticFrontierNodes schedule.positions)
    (selectedDecoded : decodeCandidateOutcome selected
        (observedQ16OutputPrefix observed selected) =
      some (.schedule selectedSchedule))
    (selectedContinuation : decodedCandidateContinuation? observed selected
      selectedSchedule = some continuation)
    (selectedCompact : semanticFrontierNodes selectedSchedule.positions ≤ 203) :
    firstCompactContinuationFrom observed
        (prior ++ selected :: rest) = some continuation := by
  induction prior with
  | nil =>
      simp [firstCompactContinuationFrom, selectedDecoded,
        selectedContinuation, selectedCompact]
  | cons counter prior ih =>
      obtain ⟨schedule, priorContinuation, decoded, advanced, noncompact⟩ :=
        priorNoncompact counter (by simp)
      have notCompact : ¬semanticFrontierNodes schedule.positions ≤ 203 := by
        omega
      simp only [List.cons_append, firstCompactContinuationFrom, decoded,
        advanced, notCompact, if_false]
      apply ih
      intro later member
      exact priorNoncompact later (by simp [member])

/-- Additional memory needed after the existing 518-slot controller. -/
structure QueryBatchDagExtensionMemory where
  q16 : ObservedQ16Duplex
  queryBatch : QueryBatchPrefixControllerMemory

def inactiveQueryBatchDagExtensionMemory : QueryBatchDagExtensionMemory :=
  { q16 := emptyObservedQ16Duplex
    queryBatch := inactiveQueryBatchPrefixMemory }

def queryBatchDagPreferredSlotForInput
    (memory : QueryBatchDagExtensionMemory) (input : ShaInput) :
    Option GammaPrefixDigestSlot :=
  let candidate :=
    (queryBatchPrefixOutputSlot? memory.queryBatch.producers input).or
      (queryBatchPrefixAdvanceSlot? memory.queryBatch.producers input)
  match candidate with
  | none => none
  | some slot =>
      if slot ∈ memory.queryBatch.usedSlots then none else some slot

/-- Update the extension at every chronological full-output exposure,
independently of whether the actor is prover or verifier. -/
def queryBatchDagExtensionAfterInput
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
      match firstCompactQ16Continuation? memory.q16 with
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

/-- Product memory leaves the established 518-slot controller untouched. -/
abbrev ExtendedControllerMemory (Memory : Type) :=
  Memory × QueryBatchDagExtensionMemory

def baseIndexedState
    {globalOracleCalls : Nat} {Memory : Type}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory)) :
    IndexedUnifiedExposureState globalOracleCalls Memory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.1 }

/-- Extend an arbitrary existing controller, provided its memory exposes the
underlying q16 DAG.  Existing labels receive priority; clean-source
separation proves this never hides a required query-batch label. -/
def extendControllerThroughQueryBatch
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
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
      | some input => queryBatchDagExtensionAfterInput
          (dagOf baseState.memory) state.memory.2 input answer
      | none => state.memory.2
    (nextBase, nextExtension)

@[simp] theorem extended_controller_base_after_memory
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (answer : Digest256) :
    ((extendControllerThroughQueryBatch transitionFuel base dagOf).afterMemory
      state answer).1 =
        base.afterMemory (baseIndexedState state) answer := by
  rfl

@[simp] theorem extended_controller_preserves_base_label
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (slot : Slot)
    (preferred : base.preferredSlot (baseIndexedState state) = some slot) :
    (extendControllerThroughQueryBatch transitionFuel base dagOf).preferredSlot
      state = some (Sum.inl slot) := by
  simp [extendControllerThroughQueryBatch, preferred]

@[simp] theorem extended_controller_uses_query_batch_label
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
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
    (extendControllerThroughQueryBatch transitionFuel base dagOf).preferredSlot
      state = some (Sum.inr slot) := by
  simp [extendControllerThroughQueryBatch, baseNone, inputExact, preferred]

theorem exact_selected_boundary_arms_query_batch
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer continuation : Digest256)
    (unseen : memory.queryBatch.boundarySeen = false)
    (empty : memory.queryBatch.producers = [])
    (selected : firstCompactQ16Continuation? memory.q16 = some continuation)
    (inputExact : input = bytes continuation ++
      [domAbsorb, queryBatchChallengeLabel]) :
    (queryBatchDagExtensionAfterInput dag memory input answer).queryBatch =
      { boundarySeen := true
        producers := [{ digest := answer, block := 0, sourceInput := input }]
        usedSlots := memory.queryBatch.usedSlots } := by
  subst input
  simp [queryBatchDagExtensionAfterInput,
    queryBatchDagPreferredSlotForInput, queryBatchPrefixOutputSlot?,
    queryBatchPrefixAdvanceSlot?, unseen, empty, selected]

/-- Before a complete first-compact q16 continuation exists, even a raw input
with the query-batch label cannot arm the controller. -/
theorem no_selected_continuation_cannot_arm_query_batch
    (dag : FinalWorkQ16DagMemory)
    (memory : QueryBatchDagExtensionMemory)
    (input : ShaInput) (answer : Digest256)
    (unseen : memory.queryBatch.boundarySeen = false)
    (empty : memory.queryBatch.producers = [])
    (noSelected : firstCompactQ16Continuation? memory.q16 = none) :
    (queryBatchDagExtensionAfterInput dag memory input answer).queryBatch =
      memory.queryBatch := by
  rcases memory with ⟨q16, queryBatch⟩
  rcases queryBatch with ⟨boundarySeen, producers, usedSlots⟩
  simp_all [queryBatchDagExtensionAfterInput,
    queryBatchDagPreferredSlotForInput, queryBatchPrefixOutputSlot?,
    queryBatchPrefixAdvanceSlot?]

abbrev CompleteFoldAlphaQ16Memory :=
  FoldAlphaFinalWorkQ16ControllerMemory
    (AlphaFinalWorkQ16ControllerMemory AlphaZeroControllerMemory)

def completeFoldAlphaQ16DagMemory
    (memory : CompleteFoldAlphaQ16Memory) : FinalWorkQ16DagMemory :=
  memory.2.2

/-- The concrete 542-slot controller used by the corrected K1.3 source
factorization. -/
def foldAlphaQ16QueryBatchController
    (globalOracleCalls transitionFuel foldExposureIndex finalExposureIndex
      boundaryIndex : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16QueryBatchDigestSlot
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
  extendControllerThroughQueryBatch transitionFuel
    (foldAlphaFinalWorkQ16Controller foldExposureIndex
      (alphaFinalWorkQ16DagController transitionFuel finalExposureIndex
        (alphaZeroCausalController transitionFuel boundaryIndex)))
    completeFoldAlphaQ16DagMemory

def exactCompilerFoldAlphaQ16QueryBatchRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter parameters :=
  ((foldAlphaQ16QueryBatchController
      (globalFull256OracleCallCap parameters) transitionFuel foldExposureIndex
      finalExposureIndex boundaryIndex).machine transitionFuel).fullRouter
    ((exactCompilerTargetCaps parameters).length - 542)
    { exposureIndex := 0
      cursor := cursor
      memory :=
        ((false, (inactiveAlphaZeroMemory, inactiveDagMemory)),
          inactiveQueryBatchDagExtensionMemory) }

def exactCompilerFoldAlphaQ16QueryBatchCoordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :=
  exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
    (exactCompilerFoldAlphaQ16QueryBatchRouter parameters transitionFuel
      foldExposureIndex finalExposureIndex boundaryIndex cursor)

#print axioms firstCompactQ16Continuation?
#print axioms first_compact_continuation_from_exact_prefix
#print axioms observed_q16_output_is_monotone
#print axioms observed_q16_advance_is_monotone
#print axioms observed_q16_output_installed
#print axioms observed_q16_advance_installed
#print axioms queryBatchDagExtensionAfterInput
#print axioms extendControllerThroughQueryBatch
#print axioms extended_controller_base_after_memory
#print axioms extended_controller_preserves_base_label
#print axioms extended_controller_uses_query_batch_label
#print axioms exact_selected_boundary_arms_query_batch
#print axioms no_selected_continuation_cannot_arm_query_batch
#print axioms foldAlphaQ16QueryBatchController
#print axioms exactCompilerFoldAlphaQ16QueryBatchRouter
#print axioms exactCompilerFoldAlphaQ16QueryBatchCoordinates

end
end AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
