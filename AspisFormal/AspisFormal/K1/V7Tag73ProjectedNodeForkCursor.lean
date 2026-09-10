import AspisFormal.K1.V7Tag73OperationalNodeCertificate
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal

/-!
# Recovering a restoration fork cursor from its projected trace

An operational child certificate retains the literal trace immediately before
its scheduled pair, but deliberately does not store a second copy of the live
scheduler cursor.  This module proves that the cursor is recoverable from the
deterministic answer prefix: the next normalized request is exactly the
scheduled fork output.  No transcript role or answer value is inferred from
the completed trace.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ProjectedNodeForkCursor

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization

universe u

/-- If a literal scheduler trace factors at one scheduled pair, replaying the
answers before that pair reaches a cursor whose next normalized request is
the exact fork output.  The pair-room proof and continuation are existential
because neither is serialized in `UnifiedExposureRecord`. -/
theorem seek_after_trace_prefix_is_scheduled_fork_output
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (prior later : List UnifiedExposureRecord)
    (scheduled : ScheduledForkCoins)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        prior ++ scheduledPairRecords scheduled ++ later) :
    ∃ (pairRoom : scheduled.frozenHistory.length + 2 ≤ globalOracleCalls)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor globalOracleCalls Result),
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor
            (prior.map UnifiedExposureRecord.answer)) =
        .forkOutput scheduled.frozenHistory pairRoom scheduled.outputInput
          scheduled.advanceInput scheduled.template next := by
  let outputRecord : UnifiedExposureRecord :=
    .forkOutput scheduled.frozenHistory scheduled.outputInput
      scheduled.advanceInput scheduled.template scheduled.forkOutput
  let advanceRecord : UnifiedExposureRecord := .forkAdvance scheduled
  have pairExact : scheduledPairRecords scheduled =
      [outputRecord, advanceRecord] := by
    rfl
  have priorExact := scheduler_native_prefix_records_eq_of_run_trace_prefix
    transitionFuel cursor answers prior
      (scheduledPairRecords scheduled ++ later) (by
        simpa [List.append_assoc] using traceExact)
  have throughOutputExact :=
    scheduler_native_prefix_records_eq_of_run_trace_prefix
      transitionFuel cursor answers (prior ++ [outputRecord])
        (advanceRecord :: later) (by
          rw [traceExact, pairExact]
          simp [List.append_assoc])
  rw [List.map_append, scheduler_native_prefix_records_append, priorExact] at throughOutputExact
  let reached := schedulerNativePrefixCursor transitionFuel cursor
    (prior.map UnifiedExposureRecord.answer)
  have oneStep :
      schedulerNativePrefixRecords transitionFuel
          reached
          [scheduled.forkOutput] = [outputRecord] := by
    have cancelled := (List.append_right_inj prior).mp throughOutputExact
    simpa [outputRecord, reached, UnifiedExposureRecord.answer] using cancelled
  cases requestExact : seekSchedulerNativeExposure transitionFuel reached with
  | returned result =>
      simp [schedulerNativePrefixRecords, requestExact, outputRecord,
        schedulerNativeRequestRecord] at oneStep
  | failed reason =>
      simp [schedulerNativePrefixRecords, requestExact, outputRecord,
        schedulerNativeRequestRecord] at oneStep
  | transitionLimit =>
      simp [schedulerNativePrefixRecords, requestExact, outputRecord,
        schedulerNativeRequestRecord] at oneStep
  | machineFresh limits limitBound actor state input nextProgram remainingFuel
      coherent totalRoom freshRoom missing onReturned =>
      simp [schedulerNativePrefixRecords, requestExact, outputRecord,
        schedulerNativeRequestRecord] at oneStep
  | forkOutput frozenHistory pairRoom outputInput advanceInput template next =>
      simp only [schedulerNativePrefixRecords, requestExact,
        schedulerNativeRequestRecord, List.cons.injEq] at oneStep
      have recordExact :
          UnifiedExposureRecord.forkOutput frozenHistory outputInput
              advanceInput template scheduled.forkOutput =
            UnifiedExposureRecord.forkOutput scheduled.frozenHistory
              scheduled.outputInput scheduled.advanceInput scheduled.template
              scheduled.forkOutput := by
        simpa [outputRecord] using oneStep.1
      have frozenExact : frozenHistory = scheduled.frozenHistory := by
        exact congrArg (fun record : UnifiedExposureRecord => match record with
          | UnifiedExposureRecord.forkOutput frozenHistory _ _ _ _ => frozenHistory
          | _ => []) recordExact
      have outputExact : outputInput = scheduled.outputInput := by
        exact congrArg (fun record : UnifiedExposureRecord => match record with
          | UnifiedExposureRecord.forkOutput _ outputInput _ _ _ => outputInput
          | _ => []) recordExact
      have advanceExact : advanceInput = scheduled.advanceInput := by
        exact congrArg (fun record : UnifiedExposureRecord => match record with
          | UnifiedExposureRecord.forkOutput _ _ advanceInput _ _ => advanceInput
          | _ => []) recordExact
      have templateExact : template = scheduled.template := by
        exact congrArg (fun record : UnifiedExposureRecord => match record with
          | UnifiedExposureRecord.forkOutput _ _ _ template _ => template
          | _ => scheduled.template) recordExact
      subst frozenHistory
      subst outputInput
      subst advanceInput
      subst template
      exact ⟨pairRoom, next, rfl⟩
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next =>
      simp [schedulerNativePrefixRecords, requestExact, outputRecord,
        schedulerNativeRequestRecord] at oneStep

#print axioms seek_after_trace_prefix_is_scheduled_fork_output

end AspisK1.V7Tag73ProjectedNodeForkCursor
