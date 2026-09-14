import AspisFormal.K1.V7Tag73SchedulerNativeResult

/-!
# Literal one-coordinate factorization of the existing native scheduler

This file DOES NOT define a replacement experiment. Each branch is a projection
of `runSchedulerNative`, and the unroll theorems connect the projection to the
existing interpreter. Cached calls stay inside the existing normalizer.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73NativeExposureStep
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AtomicPairReplay
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
noncomputable section
variable {G : Nat} {R : Type}

/-- The next native cursor after consuming exactly one tape coordinate. -/
def nativeNext (fuel : Nat) (cursor : SchedulerNativeCursor G R)
    (answer : Digest256) : SchedulerNativeCursor G R :=
  match seekSchedulerNativeExposure fuel cursor with
  | .returned result => .returned result
  | .failed reason => .failed reason
  | .transitionLimit => .failed .transitionLimit
  | .machineFresh limits bound actor state input nextProgram remainingFuel
      coherent _totalRoom _freshRoom _missing onReturned =>
      .machine limits bound actor (freshQueryState actor state input answer)
        (nextProgram answer) remainingFuel
        (fresh_query_state_preserves_history_total_coherent actor state input
          answer coherent) onReturned
  | .forkOutput history room outputInput advanceInput template next =>
      .forkAdvance history room outputInput advanceInput template answer next
  | .forkAdvance _history _room _outputInput _advanceInput template output next =>
      next (scheduledForkConfiguration template output answer)

/-- The SAME literal exposure record emitted by the interpreter's head step. -/
def nativeRecord (fuel : Nat) (cursor : SchedulerNativeCursor G R)
    (answer : Digest256) : UnifiedExposureRecord :=
  match seekSchedulerNativeExposure fuel cursor with
  | .returned _ => .padding answer
  | .failed _ => .padding answer
  | .transitionLimit => .padding answer
  | .machineFresh _limits _bound actor _state input _nextProgram _remainingFuel
      _coherent _totalRoom _freshRoom _missing _onReturned =>
      .machineFresh actor input answer
  | .forkOutput history _room outputInput advanceInput template _next =>
      .forkOutput history outputInput advanceInput template answer
  | .forkAdvance history _room outputInput advanceInput template output _next =>
      .forkAdvance
        { frozenHistory := history, outputInput := outputInput,
          advanceInput := advanceInput, template := template,
          forkOutput := output, forkAdvance := answer }

theorem native_run_terminal_unroll (fuel n : Nat)
    (cursor : SchedulerNativeCursor G R) (t : FreshAnswerTape Digest256 (n + 1)) :
    (runSchedulerNative fuel (n + 1) cursor t).terminal =
      (runSchedulerNative fuel n (nativeNext fuel cursor t.1) t.2).terminal := by
  unfold runSchedulerNative nativeNext
  cases h : seekSchedulerNativeExposure fuel cursor <;> rfl

theorem native_run_trace_unroll (fuel n : Nat)
    (cursor : SchedulerNativeCursor G R) (t : FreshAnswerTape Digest256 (n + 1)) :
    (runSchedulerNative fuel (n + 1) cursor t).trace =
      nativeRecord fuel cursor t.1 ::
        (runSchedulerNative fuel n (nativeNext fuel cursor t.1) t.2).trace := by
  unfold runSchedulerNative nativeNext nativeRecord
  cases h : seekSchedulerNativeExposure fuel cursor <;> rfl

theorem nativeRecord_answer (fuel : Nat) (cursor : SchedulerNativeCursor G R)
    (answer : Digest256) :
    (nativeRecord fuel cursor answer).answer = answer := by
  unfold nativeRecord
  cases h : seekSchedulerNativeExposure fuel cursor <;> rfl

/-- Only a supplied prefix is traversed. There is no suffix/tape argument. -/
def advancePrefix (fuel : Nat) :
    SchedulerNativeCursor G R → List Digest256 → SchedulerNativeCursor G R
  | cursor, [] => cursor
  | cursor, a :: rest => advancePrefix fuel (nativeNext fuel cursor a) rest

theorem advancePrefix_append (fuel : Nat) (cursor : SchedulerNativeCursor G R)
    (left right : List Digest256) :
    advancePrefix fuel cursor (left ++ right) =
      advancePrefix fuel (advancePrefix fuel cursor left) right := by
  induction left generalizing cursor with
  | nil => rfl
  | cons a rest ih => exact ih (nativeNext fuel cursor a)

/-- First-exposure request equality from equality of consumed prefixes. -/
theorem next_request_prefix_congr (fuel : Nat) (cursor : SchedulerNativeCursor G R)
    (left right : List Digest256) (same : left = right) :
    seekSchedulerNativeExposure fuel (advancePrefix fuel cursor left) =
      seekSchedulerNativeExposure fuel (advancePrefix fuel cursor right) := by
  rw [same]

/-- Terminal reflection for the existing length-indexed interpreter. -/
theorem native_terminal_eq_prefix_terminal (fuel n : Nat)
    (cursor : SchedulerNativeCursor G R) (t : FreshAnswerTape Digest256 n) :
    (runSchedulerNative fuel n cursor t).terminal =
      terminalAtExposureEnd fuel
        (advancePrefix fuel cursor (freshAnswerTapeToList t)) := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
      rw [native_run_terminal_unroll]
      simpa only [freshAnswerTapeToList, advancePrefix] using
        ih (nativeNext fuel cursor t.1) t.2

#print axioms native_run_terminal_unroll
#print axioms native_run_trace_unroll
#print axioms nativeRecord_answer
#print axioms advancePrefix_append
#print axioms native_terminal_eq_prefix_terminal
end
end AspisK1.V7Tag73NativeExposureStep
