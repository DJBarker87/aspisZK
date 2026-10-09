import FSV8AlphaRootLabeledTraceConstructor
import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73SchedulerCausalQ16Router

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlphaPrefixErasureBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73TranscriptSchedule
open FSV8AlphaRootLabeledTraceConstructor

noncomputable section

theorem alpha_step_eq_unified_request_next
    {globalOracleCalls : Nat} (fuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls) (answer : Digest256) :
    unifiedCursorAfterAnswer fuel cursor answer =
      unifiedRequestNext (seekUnifiedExposure fuel cursor) answer := by
  unfold unifiedCursorAfterAnswer
  cases h : seekUnifiedExposure fuel cursor <;> rfl

theorem alpha_state_after_answers_eq_erased_native_prefix
    {globalOracleCalls : Nat} {Result : Type}
    (round : Fin 4) (fuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    machineStateAfterAnswers (relationAlphaSlotMachine round fuel)
        cursor.erase answers =
      (schedulerNativePrefixCursor fuel cursor answers).erase := by
  induction answers generalizing cursor with
  | nil => rfl
  | cons answer rest ih =>
      change machineStateAfterAnswers (relationAlphaSlotMachine round fuel)
          (unifiedCursorAfterAnswer fuel cursor.erase answer) rest =
        (schedulerNativePrefixCursor fuel
          (schedulerNativeRequestNext
            (seekSchedulerNativeExposure fuel cursor) answer) rest).erase
      rw [alpha_step_eq_unified_request_next]
      rw [← erase_seek_scheduler_native_exposure fuel cursor]
      rw [← erase_scheduler_native_request_next]
      exact ih _

theorem alpha_seek_after_answers_eq_erased_native_request
    {globalOracleCalls : Nat} {Result : Type}
    (round : Fin 4) (fuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    seekUnifiedExposure fuel
        (machineStateAfterAnswers (relationAlphaSlotMachine round fuel)
          cursor.erase answers) =
      (seekSchedulerNativeExposure fuel
        (schedulerNativePrefixCursor fuel cursor answers)).erase := by
  rw [alpha_state_after_answers_eq_erased_native_prefix]
  exact (erase_seek_scheduler_native_exposure fuel
    (schedulerNativePrefixCursor fuel cursor answers)).symm

#print axioms alpha_step_eq_unified_request_next
#print axioms alpha_state_after_answers_eq_erased_native_prefix
#print axioms alpha_seek_after_answers_eq_erased_native_request
end
end AspisV8Completion.FSV8AlphaPrefixErasureBridge
