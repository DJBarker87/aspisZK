import AspisFormal.K1.V7Tag73RestoredQueryBatchCausalMarker

/-!
# Block-indexed causal markers for restored query batching

The first restored query-batch marker deliberately recognizes only block zero.
That is sufficient to locate the sampler boundary, but not to identify every
later block consumed by the bounded nonzero sampler when an adversary exposed a
later SHA coordinate first.

This module retains the prepared restoration role for an arbitrary deployed
block.  The block is fixed before either fork answer is read.  No raw SHA-input
classifier, freshness premise, or completed-answer inspection is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredQueryBatchBlockMarker

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Proof-relevant recognition of the exact pre-answer dispatcher for one
specified deployed query-batch block. -/
def IsTypedRestoredQueryBatchBlockForkStart
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (block : Fin 12)
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
      role.block = block.val ∧
      HistoryTotalCoherent prepared.programmingBase ∧
      configuration.oracleLimits.totalCalls ≤ globalOracleCalls ∧
      prepared.programmingBase.history.length + 2 ≤ globalOracleCalls ∧
      cursor =
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase

/-- Boolean form consumed by pre-answer causal controllers. -/
def typedRestoredQueryBatchBlockForkStartsHere
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (block : Fin 12)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) : Bool := by
  classical
  exact if IsTypedRestoredQueryBatchBlockForkStart (Result := Result) block
    startProgram environment configuration cursor then true else false

@[simp] theorem typed_restored_query_batch_block_fork_starts_here_iff
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (block : Fin 12)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
        startProgram environment configuration cursor = true ↔
      IsTypedRestoredQueryBatchBlockForkStart (Result := Result) block
        startProgram environment configuration cursor := by
  classical
  simp [typedRestoredQueryBatchBlockForkStartsHere]

/-- A ready dispatcher carrying the specified block role is recognized before
its output and advance answers are sampled. -/
theorem typed_query_batch_block_prepared_dispatch_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (block : Fin 12)
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
    (blockExact : role.block = block.val)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
        startProgram environment configuration
        (dispatchPreparedRestoration startProgram environment configuration
          prepared accumulator resume).erase = true := by
  rw [typed_restored_query_batch_block_fork_starts_here_iff]
  exact ⟨accumulator, prepared, role, resume, ready, roleExact, ownerExact,
    blockExact, coherent, globalRoom, pairRoom, rfl⟩

/-- The public one-request dispatcher exposes the same block-indexed marker. -/
theorem typed_query_batch_block_dispatch_one_is_marked
    {Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (block : Fin 12)
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
    (blockExact : role.block = block.val)
    (coherent : HistoryTotalCoherent prepared.programmingBase)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoom : prepared.programmingBase.history.length + 2 ≤
      globalOracleCalls) :
    typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
        startProgram environment configuration
        (dispatchOneConcreteRestoration startProgram environment configuration
          accumulator prepared.request resume).erase = true := by
  simp only [dispatchOneConcreteRestoration, dispatchConcreteRestoration, ready]
  exact typed_query_batch_block_prepared_dispatch_is_marked block startProgram
    environment configuration accumulator prepared role resume ready roleExact
    ownerExact blockExact coherent globalRoom pairRoom

/-- Every block-indexed marked cursor is a real fork pair.  In particular a
machine/cache-hit cursor cannot acquire a logical block label merely because
its SHA input collides with the deployed coordinate. -/
theorem native_cursor_with_typed_query_batch_block_marker_is_fork_pair
    {Statement Proof Payload ClientResult NativeResult : Type}
    {globalOracleCalls : Nat}
    (block : Fin 12)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (cursor : SchedulerNativeCursor globalOracleCalls NativeResult)
    (marked : typedRestoredQueryBatchBlockForkStartsHere
      (Result := ClientResult) block startProgram environment configuration
      cursor.erase = true) :
    ∃ (frozenHistory : List QueryRecord)
        (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
        (outputInput advanceInput : ShaInput)
        (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor globalOracleCalls NativeResult),
      cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
        template next := by
  rw [typed_restored_query_batch_block_fork_starts_here_iff] at marked
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

#print axioms typed_restored_query_batch_block_fork_starts_here_iff
#print axioms typed_query_batch_block_prepared_dispatch_is_marked
#print axioms typed_query_batch_block_dispatch_one_is_marked
#print axioms native_cursor_with_typed_query_batch_block_marker_is_fork_pair

end
end AspisK1.V7Tag73RestoredQueryBatchBlockMarker
