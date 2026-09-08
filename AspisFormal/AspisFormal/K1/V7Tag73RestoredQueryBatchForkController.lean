import AspisFormal.K1.V7Tag73CausalGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73QueryBatchPrefixCausalController
import AspisFormal.K1.V7Tag73RootQueryBatchForkBridge

/-!
# Causal query-batch coordinates after a typed restoration fork

The root-sweep dispatcher selects a typed query-batch squeeze before either
programmed answer is sampled.  Starting at that fork, the first two master
coordinates are therefore the output and advance halves of block zero.  Any
later sampler blocks are ordinary fresh exposures causally derived from the
new advance digest.

This module builds the corresponding pre-answer controller.  It labels both
fork actors and ordinary prover/verifier actors; after the first pair it uses
only the already-known producer digest to recognize the next output/advance
input.  The resulting coordinate map is an equivalence on the entire fixed
tape, including rejection and early halt.  Connecting the local suffix to the
stopping point in the complete root-sweep tape is a separate theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredQueryBatchForkController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalSlotMachineRouter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

inductive RestoredQueryBatchForkPhase where
  | firstOutput
  | firstAdvance (forkOutput : Digest256)
  | continuation
  deriving DecidableEq

structure RestoredQueryBatchForkMemory where
  phase : RestoredQueryBatchForkPhase
  chain : QueryBatchPrefixControllerMemory
  deriving DecidableEq

def initialRestoredQueryBatchForkMemory : RestoredQueryBatchForkMemory :=
  { phase := .firstOutput
    chain := inactiveQueryBatchPrefixMemory }

def restoredQueryBatchCandidateForInput
    (memory : QueryBatchPrefixControllerMemory) (input : ShaInput) :
    Option GammaPrefixDigestSlot :=
  let candidate :=
    (queryBatchPrefixOutputSlot? memory.producers input).or
      (queryBatchPrefixAdvanceSlot? memory.producers input)
  match candidate with
  | none => none
  | some slot => if slot ∈ memory.usedSlots then none else some slot

def RestoredQueryBatchForkMemory.preferredSlot
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      RestoredQueryBatchForkMemory) : Option GammaPrefixDigestSlot :=
  match state.memory.phase with
  | .firstOutput => some (⟨0, by decide⟩, false)
  | .firstAdvance _ => some (⟨0, by decide⟩, true)
  | .continuation =>
      match unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none => none
      | some input => restoredQueryBatchCandidateForInput state.memory.chain
          input

def firstPairUsedSlots : Finset GammaPrefixDigestSlot :=
  {(⟨0, by decide⟩, false), (⟨0, by decide⟩, true)}

def prefixAfterFirstPair (advance : Digest256) (sourceInput : ShaInput) :
    QueryBatchPrefixControllerMemory :=
  { boundarySeen := true
    producers :=
      [{ digest := advance
         block := ⟨1, by decide⟩
         sourceInput := sourceInput }]
    usedSlots := firstPairUsedSlots }

def RestoredQueryBatchForkMemory.afterAnswer
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      RestoredQueryBatchForkMemory)
    (answer : Digest256) : RestoredQueryBatchForkMemory :=
  match state.memory.phase with
  | .firstOutput =>
      { phase := .firstAdvance answer
        chain := state.memory.chain }
  | .firstAdvance _ =>
      { phase := .continuation
        chain := prefixAfterFirstPair answer
          ((unifiedInputBeforeAnswer? transitionFuel state.cursor).getD []) }
  | .continuation =>
      match unifiedInputBeforeAnswer? transitionFuel state.cursor with
      | none => state.memory
      | some input =>
          let nextUsed :=
            match restoredQueryBatchCandidateForInput state.memory.chain input with
            | none => state.memory.chain.usedSlots
            | some slot => insert slot state.memory.chain.usedSlots
          { phase := .continuation
            chain :=
              { boundarySeen := true
                producers := extendQueryBatchPrefixProducers
                  state.memory.chain.producers input answer
                usedSlots := nextUsed } }

def restoredQueryBatchForkController
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      GammaPrefixDigestSlot RestoredQueryBatchForkMemory where
  preferredSlot := RestoredQueryBatchForkMemory.preferredSlot transitionFuel
  afterMemory := RestoredQueryBatchForkMemory.afterAnswer transitionFuel

/-! ## Waiting for the typed fork in the complete compiler tape -/

/-- A causal start marker may inspect the complete current cursor but not the
answer about to be sampled.  This is the stopping-time interface used by the
root-sweep source proof. -/
inductive WaitingRestoredQueryBatchMemory where
  | waiting
  | active (forkMemory : RestoredQueryBatchForkMemory)
  deriving DecidableEq

def activeRestoredQueryBatchState
    {globalOracleCalls : Nat}
    (state : IndexedUnifiedExposureState globalOracleCalls
      WaitingRestoredQueryBatchMemory)
    (forkMemory : RestoredQueryBatchForkMemory) :
    IndexedUnifiedExposureState globalOracleCalls
      RestoredQueryBatchForkMemory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := forkMemory }

/-- Stay inert until the pre-answer marker identifies the selected typed
block-zero fork.  The marked answer itself is routed as block-zero output;
the marker therefore cannot depend on that answer. -/
def waitingRestoredQueryBatchForkController
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      GammaPrefixDigestSlot WaitingRestoredQueryBatchMemory where
  preferredSlot := fun state ↦
    match state.memory with
    | .waiting =>
        if startsHere state.cursor then some (⟨0, by decide⟩, false)
        else none
    | .active forkMemory =>
        (restoredQueryBatchForkController transitionFuel).preferredSlot
          (activeRestoredQueryBatchState state forkMemory)
  afterMemory := fun state answer ↦
    match state.memory with
    | .waiting =>
        if startsHere state.cursor then
          .active
            ((restoredQueryBatchForkController transitionFuel).afterMemory
              { exposureIndex := state.exposureIndex
                cursor := state.cursor
                memory := initialRestoredQueryBatchForkMemory }
              answer)
        else .waiting
    | .active forkMemory =>
        .active
          ((restoredQueryBatchForkController transitionFuel).afterMemory
            (activeRestoredQueryBatchState state forkMemory) answer)

@[simp] theorem waiting_controller_marks_block_zero_output
    {globalOracleCalls : Nat} (transitionFuel exposureIndex : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (marked : startsHere cursor = true) :
    (waitingRestoredQueryBatchForkController transitionFuel startsHere).preferredSlot
        { exposureIndex := exposureIndex
          cursor := cursor
          memory := WaitingRestoredQueryBatchMemory.waiting } =
      some (⟨0, by decide⟩, false) := by
  simp [waitingRestoredQueryBatchForkController, marked]

@[simp] theorem waiting_controller_marked_output_arms_adjacent_advance
    {globalOracleCalls : Nat} (transitionFuel exposureIndex : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (marked : startsHere cursor = true) (forkOutput : Digest256) :
    let controller := waitingRestoredQueryBatchForkController transitionFuel
      startsHere
    let initial : IndexedUnifiedExposureState globalOracleCalls
        WaitingRestoredQueryBatchMemory :=
      { exposureIndex := exposureIndex
        cursor := cursor
        memory := .waiting }
    let afterOutput := controller.afterAnswer transitionFuel initial forkOutput
    afterOutput.memory =
        .active
          { phase := .firstAdvance forkOutput
            chain := inactiveQueryBatchPrefixMemory } ∧
      controller.preferredSlot afterOutput =
        some (⟨0, by decide⟩, true) := by
  simp [waitingRestoredQueryBatchForkController, marked,
    IndexedUnifiedExposureController.afterAnswer,
    restoredQueryBatchForkController,
    RestoredQueryBatchForkMemory.afterAnswer,
    activeRestoredQueryBatchState, initialRestoredQueryBatchForkMemory,
    RestoredQueryBatchForkMemory.preferredSlot]

/-- Full compiler-tape coordinate equivalence at an arbitrary causal
root-sweep stopping point.  No exposure index is selected from the completed
tape: `startsHere` is evaluated by the pre-answer controller during the same
chronological run. -/
def exactCompilerWaitingRestoredQueryBatchCoordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters) → Bool)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerIndexedGammaPrefixCoordinates parameters transitionFuel
    (waitingRestoredQueryBatchForkController transitionFuel startsHere)
    .waiting cursor

@[simp] theorem initial_restored_query_batch_labels_first_output
    {globalOracleCalls : Nat} (transitionFuel exposureIndex : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    (restoredQueryBatchForkController transitionFuel).preferredSlot
        { exposureIndex := exposureIndex
          cursor := cursor
          memory := initialRestoredQueryBatchForkMemory } =
      some (⟨0, by decide⟩, false) := by
  rfl

@[simp] theorem restored_query_batch_labels_adjacent_advance
    {globalOracleCalls : Nat} (transitionFuel exposureIndex : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (forkOutput : Digest256) :
    let initial : IndexedUnifiedExposureState globalOracleCalls
        RestoredQueryBatchForkMemory :=
      { exposureIndex := exposureIndex
        cursor := cursor
        memory := initialRestoredQueryBatchForkMemory }
    ((restoredQueryBatchForkController transitionFuel).afterAnswer
        transitionFuel initial forkOutput).memory.phase =
        .firstAdvance forkOutput ∧
      (restoredQueryBatchForkController transitionFuel).preferredSlot
          ((restoredQueryBatchForkController transitionFuel).afterAnswer
            transitionFuel initial forkOutput) =
        some (⟨0, by decide⟩, true) := by
  exact ⟨rfl, rfl⟩

@[simp] theorem restored_query_batch_after_first_pair_starts_block_one
    {globalOracleCalls : Nat} (transitionFuel exposureIndex : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (forkOutput forkAdvance : Digest256) :
    let controller := restoredQueryBatchForkController
      (globalOracleCalls := globalOracleCalls) transitionFuel
    let initial : IndexedUnifiedExposureState globalOracleCalls
        RestoredQueryBatchForkMemory :=
      { exposureIndex := exposureIndex
        cursor := cursor
        memory := initialRestoredQueryBatchForkMemory }
    let afterOutput := controller.afterAnswer transitionFuel initial forkOutput
    let afterAdvance := controller.afterAnswer transitionFuel afterOutput
      forkAdvance
    afterAdvance.memory.phase = .continuation ∧
      afterAdvance.memory.chain = prefixAfterFirstPair forkAdvance
        ((unifiedInputBeforeAnswer? transitionFuel afterOutput.cursor).getD []) := by
  exact ⟨rfl, rfl⟩

/-- Exact finite coordinate factorization for the suffix beginning at a typed
query-batch block-zero fork.  The source theorem supplies that starting-cursor
fact; this equivalence then isolates the complete bounded duplex tape without
an independence premise. -/
def restoredQueryBatchForkSuffixCoordinates
    {globalOracleCalls : Nat} (transitionFuel residual : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    FreshAnswerTape Digest256
        (Fintype.card GammaPrefixDigestSlot + residual) ≃
      FreshAnswerTape Digest256 residual × TotalGammaDuplexTape :=
  ((restoredQueryBatchForkController transitionFuel).machine transitionFuel
      |>.fullCoordinateEquiv residual
        { exposureIndex := 0
          cursor := cursor
          memory := initialRestoredQueryBatchForkMemory }).trans
    ((Equiv.prodCongr gammaPrefixDigestSlotFunctionEquiv
      (Equiv.refl (FreshAnswerTape Digest256 residual))).trans
        (Equiv.prodComm TotalGammaDuplexTape
          (FreshAnswerTape Digest256 residual)))

#print axioms initial_restored_query_batch_labels_first_output
#print axioms restored_query_batch_labels_adjacent_advance
#print axioms restored_query_batch_after_first_pair_starts_block_one
#print axioms restoredQueryBatchForkSuffixCoordinates
#print axioms waiting_controller_marks_block_zero_output
#print axioms waiting_controller_marked_output_arms_adjacent_advance
#print axioms exactCompilerWaitingRestoredQueryBatchCoordinates

end
end AspisK1.V7Tag73RestoredQueryBatchForkController
