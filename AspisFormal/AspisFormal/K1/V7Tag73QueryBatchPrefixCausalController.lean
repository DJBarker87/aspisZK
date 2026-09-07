import AspisFormal.K1.V7Tag73CausalGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73FinalWorkQ16CandidateController
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Pre-answer causal controller for the query-batch duplex prefix

The final Tag-73 query-batch challenge is sampled immediately after the empty
query-batch-domain absorption. This controller recognizes that exact 34-byte
input before its answer is exposed, then routes the twelve possible nonzero
sampler output/advance pairs using only already-known producer digests.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73QueryBatchPrefixCausalController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

def queryBatchVerifierInputBeforeAnswer?
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Option ShaInput :=
  match seekUnifiedExposure transitionFuel cursor with
  | .machineFresh _limits _limitBound actor _state input _nextProgram
      _remainingFuel _coherent _totalRoom _freshRoom _missing _onReturned =>
      if actor = .verifier then some input else none
  | .forkOutput .. | .forkAdvance .. | .halted | .transitionLimit => none

/-- Exact empty-domain absorption: digest, absorb marker, and Tag-73's
query-batch challenge label. -/
def isQueryBatchPrefixBoundaryInput (input : ShaInput) : Bool :=
  input.length = 34 &&
    input[32]? = some domAbsorb &&
    input[33]? = some queryBatchChallengeLabel

@[simp] theorem literal_query_batch_domain_is_prefix_boundary
    (digest : Digest256) :
    isQueryBatchPrefixBoundaryInput
        (bytes digest ++ [domAbsorb, queryBatchChallengeLabel]) = true := by
  simp [isQueryBatchPrefixBoundaryInput]

structure QueryBatchPrefixProducer where
  digest : Digest256
  block : Fin 12
  sourceInput : ShaInput
  deriving DecidableEq, Repr

structure QueryBatchPrefixControllerMemory where
  boundarySeen : Bool
  producers : List QueryBatchPrefixProducer
  usedSlots : Finset GammaPrefixDigestSlot
  deriving DecidableEq

def inactiveQueryBatchPrefixMemory : QueryBatchPrefixControllerMemory :=
  { boundarySeen := false, producers := [], usedSlots := ∅ }

def queryBatchPrefixOutputSlot? (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) : Option GammaPrefixDigestSlot :=
  (producers.find? fun producer ↦
    decide (input = bytes producer.digest ++ [domSqueeze])).map
      (fun producer ↦ (producer.block, false))

def queryBatchPrefixAdvanceSlot? (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) : Option GammaPrefixDigestSlot :=
  (producers.find? fun producer ↦
    decide (input = bytes producer.digest ++ [domAdvance])).map
      (fun producer ↦ (producer.block, true))

def queryBatchPrefixPreferredSlot
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory) : Option GammaPrefixDigestSlot :=
  match queryBatchVerifierInputBeforeAnswer? transitionFuel state.cursor with
  | none => none
  | some input =>
      let candidate :=
        (queryBatchPrefixOutputSlot? state.memory.producers input).or
          (queryBatchPrefixAdvanceSlot? state.memory.producers input)
      match candidate with
      | none => none
      | some slot =>
          if slot ∈ state.memory.usedSlots then none else some slot

def extendQueryBatchPrefixProducers
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (answer : Digest256) :
    List QueryBatchPrefixProducer :=
  match producers.find? fun producer ↦
      decide (input = bytes producer.digest ++ [domAdvance]) with
  | none => producers
  | some producer =>
      if bounded : producer.block.val + 1 < 12 then
        producers ++ [QueryBatchPrefixProducer.mk answer
          ⟨producer.block.val + 1, bounded⟩ input]
      else producers

def queryBatchPrefixAfterMemory
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (answer : Digest256) : QueryBatchPrefixControllerMemory :=
  match queryBatchVerifierInputBeforeAnswer? transitionFuel state.cursor with
  | none => state.memory
  | some input =>
      let nextUsed :=
        match queryBatchPrefixPreferredSlot transitionFuel state with
        | none => state.memory.usedSlots
        | some slot => insert slot state.memory.usedSlots
      if !state.memory.boundarySeen &&
          isQueryBatchPrefixBoundaryInput input then
        { boundarySeen := true
          producers :=
            [{ digest := answer, block := 0, sourceInput := input }]
          usedSlots := nextUsed }
      else
        { boundarySeen := state.memory.boundarySeen
          producers := extendQueryBatchPrefixProducers state.memory.producers
            input answer
          usedSlots := nextUsed }

def queryBatchPrefixCausalController
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      GammaPrefixDigestSlot QueryBatchPrefixControllerMemory where
  preferredSlot := queryBatchPrefixPreferredSlot transitionFuel
  afterMemory := queryBatchPrefixAfterMemory transitionFuel

def exactCompilerQueryBatchPrefixRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalGammaPrefixRouter parameters :=
  exactCompilerIndexedGammaPrefixRouter parameters transitionFuel
    (queryBatchPrefixCausalController transitionFuel)
    inactiveQueryBatchPrefixMemory cursor

def exactCompilerQueryBatchPrefixCoordinates
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerCausalGammaPrefixCoordinates parameters
    (exactCompilerQueryBatchPrefixRouter parameters transitionFuel cursor)

theorem query_batch_prefix_after_initial_boundary
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (input : ShaInput) (answer : Digest256)
    (inputExact : queryBatchVerifierInputBeforeAnswer? transitionFuel
      state.cursor = some input)
    (unseen : state.memory.boundarySeen = false)
    (empty : state.memory.producers = [])
    (boundary : isQueryBatchPrefixBoundaryInput input = true) :
    queryBatchPrefixAfterMemory transitionFuel state answer =
      { boundarySeen := true
        producers :=
          [{ digest := answer, block := 0, sourceInput := input }]
        usedSlots := state.memory.usedSlots } := by
  simp [queryBatchPrefixAfterMemory, inputExact, unseen, empty,
    queryBatchPrefixPreferredSlot, boundary, queryBatchPrefixOutputSlot?,
    queryBatchPrefixAdvanceSlot?]

#print axioms literal_query_batch_domain_is_prefix_boundary
#print axioms queryBatchPrefixPreferredSlot
#print axioms queryBatchPrefixAfterMemory
#print axioms queryBatchPrefixCausalController
#print axioms exactCompilerQueryBatchPrefixRouter
#print axioms exactCompilerQueryBatchPrefixCoordinates
#print axioms query_batch_prefix_after_initial_boundary

end
end AspisK1.V7Tag73QueryBatchPrefixCausalController
