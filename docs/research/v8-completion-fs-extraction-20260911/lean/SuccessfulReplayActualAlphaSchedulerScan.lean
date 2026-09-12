import SuccessfulReplayAlphaBoundary
import AspisFormal.K1.V7Tag73SchedulerNativeTargetPause

/-!
# Scan the chronological scheduler at a replay-derived alpha boundary

This leaf searches the actual result-carrying scheduler for the alpha request
derived from one successful same-body replay.  It retains both total outcomes:
an exact fresh pause whose request is that literal byte input, or absence with
the exact unmodified scheduler run.  Cached requests are deliberately not
misclassified as fresh pauses.

The caller still has to construct the scheduler cursor from the V8 source
execution.  No matrix configuration, challenge value, or occurrence premise
is accepted here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.SuccessfulReplayActualAlphaSchedulerScan

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8PostOODGammaScript FSNonzeroQM31
open ExtractionCollectorSuccessfulReplay
open SuccessfulReplayAlphaBoundary
open FSV8AlphaChallengeInputBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeTargetPause

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

noncomputable section

/-- A successful replay determines the target searched by the chronological
scheduler.  The scan then either pauses at that exact fresh request and can
reconstruct the real run, or returns an absent result equal to the real run.
-/
theorem successful_replay_actual_alpha_scan
    {n m globalOracleCalls : Nat} {z : Fin 10 → K}
    {cuts : FSBoundedTranscript.RootCuts} {initialDigest : Block}
    {firstWork : Point → Script Bytes Block Unit n}
    {secondWork : Point → Point → Script Bytes Block Unit m}
    {Result : Type}
    (replay : SuccessfulReplay z cuts initialDigest firstWork secondWork)
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256) :
    ∃ afterAlphaNonce,
      IsActualAlphaBoundary replay afterAlphaNonce ∧
      ((∃ pause : SchedulerNativeFreshPause globalOracleCalls Result
            (alphaCandidateInput afterAlphaNonce),
          scanSchedulerNativeToInput transitionFuel
              (alphaCandidateInput afterAlphaNonce) cursor answers =
            .paused pause ∧
          pause.input = alphaCandidateInput afterAlphaNonce ∧
          pause.resumeRunWith transitionFuel pause.targetAnswer
              pause.remainingAnswers =
            runSchedulerNativeListRun transitionFuel cursor answers) ∨
        ∃ run : SchedulerNativeRun Result,
          scanSchedulerNativeToInput transitionFuel
              (alphaCandidateInput afterAlphaNonce) cursor answers =
            .absent run ∧
          run = runSchedulerNativeListRun transitionFuel cursor answers) := by
  obtain ⟨afterAlphaNonce, actual⟩ :=
    successful_replay_constructs_actual_alpha_boundary replay
  refine ⟨afterAlphaNonce, actual, ?_⟩
  generalize scanEq :
      scanSchedulerNativeToInput transitionFuel
        (alphaCandidateInput afterAlphaNonce) cursor answers = scan
  cases scan with
  | paused pause =>
      left
      refine ⟨pause, rfl, scheduler_native_fresh_pause_request_is_target pause,
        ?_⟩
      exact scan_scheduler_native_to_input_paused_resume_with_actual_exact
        transitionFuel (alphaCandidateInput afterAlphaNonce) cursor answers
          pause scanEq
  | absent run =>
      right
      refine ⟨run, rfl, ?_⟩
      exact scan_scheduler_native_to_input_absent_exact transitionFuel
        (alphaCandidateInput afterAlphaNonce) cursor answers run scanEq

#print axioms successful_replay_actual_alpha_scan

end
end AspisV8Completion.SuccessfulReplayActualAlphaSchedulerScan
