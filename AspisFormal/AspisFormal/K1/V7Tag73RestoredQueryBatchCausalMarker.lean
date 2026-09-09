import AspisFormal.K1.V7Tag73RestoredQueryBatchForkController

/-!
# Causal marker for a typed restored query-batch fork

The result-free scheduler cursor deliberately erases the logical role of a
restoration fork.  The role is nevertheless fixed before either fork answer:
it is stored in the selected `PreparedConcreteRestoration.transition`.

This file marks a cursor only when it is the literal guarded dispatcher for a
ready block-zero query-batch preparation.  The predicate may inspect the
current cursor and all already-constructed preparation data, but not the fork
output or advance answer.  It therefore gives the waiting coordinate
controller a genuine stopping-time marker without reintroducing the invalid
raw-SHA-input role classifier.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredQueryBatchCausalMarker

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RestoredQueryBatchForkController
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

/-- Proof-relevant recognition of the exact pre-answer dispatcher cursor for
one ready restored block-zero query-batch squeeze.  All four guard proofs are
about data already fixed at preparation time. -/
def IsTypedRestoredQueryBatchForkStart
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Prop :=
  ∃ (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (prepared : PreparedConcreteRestoration Statement Proof Payload)
      (role : PreparedRestorationPairRole)
      (resume : ConcreteRestorationReply →
        ConcreteRestorationAccumulator Statement Proof Payload →
          SchedulerNativeCursor globalOracleCalls
            (ConcreteRestorationClientRun Statement Proof Payload Result)),
    prepareConcreteRestorationFromStartProgram startProgram configuration
        accumulator prepared.request = .ready prepared ∧
      preparedRestorationPairRole? prepared = some role ∧
      role.owner = .challenge .queryBatch ∧
      role.block = 0 ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      configuration.oracleLimits.totalCalls ≤ globalOracleCalls ∧
      prepared.programmingBase.history.length + 2 ≤ globalOracleCalls ∧
      cursor =
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase

/-- Boolean stopping-time test consumed by the indexed causal controller. -/
def typedRestoredQueryBatchForkStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool := by
  classical
  exact if IsTypedRestoredQueryBatchForkStart (Result := Result) startProgram
    environment configuration cursor then true else false

@[simp] theorem typed_restored_query_batch_fork_starts_here_iff
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    typedRestoredQueryBatchForkStartsHere (Result := Result) startProgram
        environment configuration cursor = true ↔
      IsTypedRestoredQueryBatchForkStart (Result := Result) startProgram
        environment configuration cursor := by
  classical
  simp [typedRestoredQueryBatchForkStartsHere]

/-- A literal ready dispatcher with the typed block-zero role is recognized
before its first random fork answer is read. -/
theorem typed_query_batch_prepared_dispatch_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator prepared.request = .ready prepared)
    (roleExact : preparedRestorationPairRole? prepared = some role)
    (ownerExact : role.owner = .challenge .queryBatch)
    (blockExact : role.block = 0)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredQueryBatchForkStartsHere (Result := Result) startProgram
        environment configuration
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase = true := by
  rw [typed_restored_query_batch_fork_starts_here_iff]
  exact ⟨accumulator, prepared, role, resume, ready, roleExact, ownerExact,
    blockExact, coherent, globalRoom, pairRoom, rfl⟩

/-- The public one-request dispatcher exposes the same pre-answer marker when
its executable preparer returns the typed query-batch preparation.  This is
the bridge used inside the literal root-sweep client interpreter. -/
theorem typed_query_batch_dispatch_one_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (prepared : PreparedConcreteRestoration Statement Proof Payload)
    (role : PreparedRestorationPairRole)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (ready : prepareConcreteRestorationFromStartProgram startProgram
      configuration accumulator prepared.request = .ready prepared)
    (roleExact : preparedRestorationPairRole? prepared = some role)
    (ownerExact : role.owner = .challenge .queryBatch)
    (blockExact : role.block = 0)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredQueryBatchForkStartsHere (Result := Result) startProgram
        environment configuration
        (dispatchOneConcreteRestoration startProgram environment configuration
          accumulator prepared.request resume).erase = true := by
  simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration, ready]
  exact typed_query_batch_prepared_dispatch_is_marked startProgram environment
    configuration accumulator prepared role resume ready roleExact ownerExact
      blockExact coherent globalRoom pairRoom

/-- Every marked cursor is operationally at a fork-output request.  This is
the key fail-closed fact: a machine/cache-hit cursor cannot satisfy the typed
marker merely because its raw SHA input resembles a query-batch squeeze. -/
theorem marked_query_batch_cursor_seeks_fork_output
    {Statement Proof Payload Result : Type}
    {globalOracleCalls transitionFuel : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (marked : typedRestoredQueryBatchForkStartsHere (Result := Result)
      startProgram environment configuration cursor = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          UnifiedExposureCursor globalOracleCalls),
      seekUnifiedExposure (transitionFuel + 1) cursor =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next := by
  rw [typed_restored_query_batch_fork_starts_here_iff] at marked
  rcases marked with ⟨accumulator, prepared, role, resume, _ready, _roleExact,
    _ownerExact, _blockExact, coherent, globalRoom, pairRoom, cursorExact⟩
  subst cursor
  unfold dispatchPreparedRestoration
  rw [dif_pos coherent, dif_pos globalRoom, dif_pos pairRoom]
  simp only [SchedulerNativeCursor.erase, seekUnifiedExposure]
  exact ⟨prepared.programmingBase.history, pairRoom, prepared.outputInput,
    prepared.advanceInput, canonicalForkTemplate configuration, _, rfl⟩

/-- A native cursor whose erasure carries the typed marker is itself a literal
fork-pair node.  Erasure forgets the terminal result and continuation result
type, but it cannot turn a machine or terminal node into a fork node. -/
theorem native_cursor_with_typed_query_batch_marker_is_fork_pair
    {Statement Proof Payload ClientResult NativeResult : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : SchedulerNativeCursor globalOracleCalls NativeResult)
    (marked : typedRestoredQueryBatchForkStartsHere (Result := ClientResult)
      startProgram environment configuration cursor.erase = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor globalOracleCalls NativeResult),
      cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
        template next := by
  rw [typed_restored_query_batch_fork_starts_here_iff] at marked
  rcases marked with ⟨accumulator, prepared, role, resume, ready, roleExact,
    ownerExact, blockExact, coherent, globalRoom, pairRoom, cursorExact⟩
  unfold dispatchPreparedRestoration at cursorExact
  rw [dif_pos coherent, dif_pos globalRoom, dif_pos pairRoom] at cursorExact
  cases cursor with
  | returned result => cases cursorExact
  | failed reason => cases cursorExact
  | machine limits limitBound actor state program fuel coherent onReturned =>
      cases cursorExact
  | forkPair frozenHistory nativePairRoom outputInput advanceInput template next =>
      exact ⟨frozenHistory, nativePairRoom, outputInput, advanceInput,
        template, next, rfl⟩
  | forkAdvance frozenHistory nativePairRoom outputInput advanceInput template
      forkOutput next =>
      cases cursorExact

/-! ## Exposure-normalized causal marker -/

/-- The typed dispatcher is the next exposed coordinate of `cursor`.  The
equality is stated at the answer-independent record shape: frozen history,
both SHA inputs and the programming template must all agree.  The continuation
function is intentionally irrelevant to the random-oracle coordinate itself.
-/
def IsTypedRestoredQueryBatchExposureStart
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Prop :=
  ∃ target : UnifiedExposureCursor globalOracleCalls,
    IsTypedRestoredQueryBatchForkStart (Result := Result) startProgram
        environment configuration target ∧
      ∀ answer, unifiedRecordAtAnswer transitionFuel cursor answer =
        unifiedRecordAtAnswer transitionFuel target answer

/-- Boolean stopping-time marker used by the coordinate controller.  It may
normalize cached deterministic work before the next exposure, but it never
examines that exposure's answer. -/
def typedRestoredQueryBatchExposureStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool := by
  classical
  exact if IsTypedRestoredQueryBatchExposureStart (Result := Result)
    transitionFuel startProgram environment configuration cursor then true
  else false

@[simp] theorem typed_restored_query_batch_exposure_starts_here_iff
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    typedRestoredQueryBatchExposureStartsHere (Result := Result)
        transitionFuel startProgram environment configuration cursor = true ↔
      IsTypedRestoredQueryBatchExposureStart (Result := Result)
        transitionFuel startProgram environment configuration cursor := by
  classical
  simp [typedRestoredQueryBatchExposureStartsHere]

/-- A literal typed marker exposes a unified fork-pair cursor. -/
theorem unified_cursor_with_typed_query_batch_marker_is_fork_pair
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (marked : typedRestoredQueryBatchForkStartsHere (Result := Result)
      startProgram environment configuration cursor = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          UnifiedExposureCursor globalOracleCalls),
      cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
        template next := by
  rw [typed_restored_query_batch_fork_starts_here_iff] at marked
  rcases marked with ⟨accumulator, prepared, role, resume, ready, roleExact,
    ownerExact, blockExact, coherent, globalRoom, pairRoom, cursorExact⟩
  subst cursor
  unfold dispatchPreparedRestoration
  rw [dif_pos coherent, dif_pos globalRoom, dif_pos pairRoom]
  exact ⟨prepared.programmingBase.history, pairRoom, prepared.outputInput,
    prepared.advanceInput, canonicalForkTemplate configuration, _, rfl⟩

/-- Equality of one emitted record transports the typed role to the current
pre-answer exposure.  Since the target is a fork-output request, constructor
injectivity fixes every answer-independent field and the equality therefore
holds for all possible answers. -/
theorem typed_query_batch_exposure_marked_of_record_eq
    {Statement Proof Payload Result : Type}
    {globalOracleCalls transitionFuel : Nat}
    (positive : 0 < transitionFuel)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor target : UnifiedExposureCursor globalOracleCalls)
    (answer : Digest256)
    (targetMarked : typedRestoredQueryBatchForkStartsHere (Result := Result)
      startProgram environment configuration target = true)
    (recordExact : unifiedRecordAtAnswer transitionFuel cursor answer =
      unifiedRecordAtAnswer transitionFuel target answer) :
    typedRestoredQueryBatchExposureStartsHere (Result := Result)
        transitionFuel startProgram environment configuration cursor = true := by
  rw [typed_restored_query_batch_exposure_starts_here_iff]
  rw [typed_restored_query_batch_fork_starts_here_iff] at targetMarked
  refine ⟨target, targetMarked, ?_⟩
  obtain ⟨frozenHistory, pairRoom, outputInput, advanceInput, template, next,
      targetExact⟩ :=
    unified_cursor_with_typed_query_batch_marker_is_fork_pair startProgram
      environment configuration target (by
        rw [typed_restored_query_batch_fork_starts_here_iff]
        exact targetMarked)
  subst target
  cases transitionFuel with
  | zero => omega
  | succ fuel =>
      generalize requestExact : seekUnifiedExposure (fuel + 1) cursor = request
      cases request <;>
        simp only [unifiedRecordAtAnswer, requestExact, seekUnifiedExposure]
          at recordExact ⊢
      all_goals try { cases recordExact }
      intro other
      cases recordExact
      rfl

/-- The complete compiler tape, factored at the first typed restored
query-batch fork encountered by the literal scheduler. -/
def exactCompilerTypedRestoredQueryBatchCoordinates
    {Statement Proof Payload Result : Type}
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel : Nat)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerWaitingRestoredQueryBatchCoordinates parameters transitionFuel
    (typedRestoredQueryBatchExposureStartsHere (Result := Result)
      transitionFuel startProgram environment configuration) cursor

#print axioms IsTypedRestoredQueryBatchForkStart
#print axioms typed_restored_query_batch_fork_starts_here_iff
#print axioms typed_query_batch_prepared_dispatch_is_marked
#print axioms typed_query_batch_dispatch_one_is_marked
#print axioms marked_query_batch_cursor_seeks_fork_output
#print axioms native_cursor_with_typed_query_batch_marker_is_fork_pair
#print axioms IsTypedRestoredQueryBatchExposureStart
#print axioms typed_restored_query_batch_exposure_starts_here_iff
#print axioms unified_cursor_with_typed_query_batch_marker_is_fork_pair
#print axioms typed_query_batch_exposure_marked_of_record_eq
#print axioms exactCompilerTypedRestoredQueryBatchCoordinates

end
end AspisK1.V7Tag73RestoredQueryBatchCausalMarker
