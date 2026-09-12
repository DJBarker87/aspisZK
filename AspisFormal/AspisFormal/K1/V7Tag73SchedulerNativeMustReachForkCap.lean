import AspisFormal.K1.V7Tag73ExactPlainRomTraceResourceCaps
import AspisFormal.K1.V7Tag73SchedulerNativeMustReach

/-!
# Fork-coordinate caps for scheduler-native must-reach certificates

The ordinary must-reach tree proves that every successful scheduler branch
passes a target cursor.  Gamma suffix capacity needs one additional numeric
fact: the number of fork coordinates consumed before that cursor.  Machine
segments cost zero in this counter, a complete fork pair costs two, and a
cursor already waiting for the second coin costs one.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeMustReachForkCap

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativeMustReach
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- A must-reach tree with an upper bound on fork coordinates before the
target.  The target itself is reached before consuming its next answer. -/
inductive SchedulerNativeCursorMustReachWithForkCap
    {globalOracleCalls : Nat} {Result : Type u}
    (target : SchedulerNativeCursor globalOracleCalls Result → Prop) :
    Nat → SchedulerNativeCursor globalOracleCalls Result → Prop where
  | here (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (holds : target cursor) :
      SchedulerNativeCursorMustReachWithForkCap target 0 cursor
  | machine
      {MachineResult : Type u}
      (limits : OracleLimits)
      (limitBound : limits.totalCalls ≤ globalOracleCalls)
      (actor : QueryActor) (state : OracleState)
      (program : OracleMachine MachineResult) (fuel : Nat)
      (coherent : HistoryTotalCoherent state)
      (onReturned : (result : MachineResult) → (state : OracleState) →
        HistoryTotalCoherent state →
          SchedulerNativeCursor globalOracleCalls Result)
      {forkCap : Nat}
      (safe : ∀ (result : MachineResult) (finalState : OracleState)
        (finalCoherent : HistoryTotalCoherent finalState),
        SchedulerNativeCursorMustReachWithForkCap target forkCap
          (onReturned result finalState finalCoherent)) :
      SchedulerNativeCursorMustReachWithForkCap target forkCap
        (.machine limits limitBound actor state program fuel coherent
          onReturned)
  | forkPair
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      {tailCap : Nat}
      (safe : ∀ scheduled : ScheduledForkCoins,
        scheduled.frozenHistory = frozenHistory →
        scheduled.outputInput = outputInput →
        scheduled.advanceInput = advanceInput →
        scheduled.template = template →
        SchedulerNativeCursorMustReachWithForkCap target tailCap
          (next scheduled.configuration)) :
      SchedulerNativeCursorMustReachWithForkCap target (2 + tailCap)
        (.forkPair frozenHistory pairRoom outputInput advanceInput template next)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      {tailCap : Nat}
      (safe : ∀ scheduled : ScheduledForkCoins,
        scheduled.frozenHistory = frozenHistory →
        scheduled.outputInput = outputInput →
        scheduled.advanceInput = advanceInput →
        scheduled.template = template →
        scheduled.forkOutput = forkOutput →
        SchedulerNativeCursorMustReachWithForkCap target tailCap
          (next scheduled.configuration)) :
      SchedulerNativeCursorMustReachWithForkCap target (1 + tailCap)
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next)
  | weaken
      {oldCap newCap : Nat}
      {cursor : SchedulerNativeCursor globalOracleCalls Result}
      (safe : SchedulerNativeCursorMustReachWithForkCap target oldCap cursor)
      (capLe : oldCap ≤ newCap) :
      SchedulerNativeCursorMustReachWithForkCap target newCap cursor

/-- Fork-cap certificates are monotone in the advertised allowance. -/
theorem scheduler_native_must_reach_fork_cap_mono
    {globalOracleCalls : Nat} {Result : Type u}
    {target : SchedulerNativeCursor globalOracleCalls Result → Prop}
    {oldCap newCap : Nat} {cursor : SchedulerNativeCursor globalOracleCalls Result}
    (safe : SchedulerNativeCursorMustReachWithForkCap target oldCap cursor)
    (capLe : oldCap ≤ newCap) :
    SchedulerNativeCursorMustReachWithForkCap target newCap cursor :=
  .weaken safe capLe

/-- Erasing the numeric annotation recovers the ordinary must-reach tree. -/
theorem scheduler_native_must_reach_of_fork_cap
    {globalOracleCalls : Nat} {Result : Type u}
    {target : SchedulerNativeCursor globalOracleCalls Result → Prop}
    {forkCap : Nat} {cursor : SchedulerNativeCursor globalOracleCalls Result}
    (safe : SchedulerNativeCursorMustReachWithForkCap target forkCap cursor) :
    SchedulerNativeCursorMustReach target cursor := by
  induction safe with
  | here cursor holds => exact .here cursor holds
  | machine limits limitBound actor state program fuel coherent onReturned safe
      ih =>
      exact .machine limits limitBound actor state program fuel coherent
        onReturned (fun result finalState finalCoherent =>
          ih result finalState finalCoherent)
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      exact .forkPair frozenHistory pairRoom outputInput advanceInput template
        next (fun scheduled frozenExact outputExact advanceExact templateExact =>
          ih scheduled frozenExact outputExact advanceExact templateExact)
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      exact .forkAdvance frozenHistory pairRoom outputInput advanceInput
        template forkOutput next
        (fun scheduled frozenExact outputExact advanceExact templateExact
            forkOutputExact =>
          ih scheduled frozenExact outputExact advanceExact templateExact
            forkOutputExact)
  | weaken safe _capLe ih => exact ih

/-- A successful literal run through a bounded tree reaches the target after
at most the advertised number of fork coordinates. -/
theorem returned_run_of_fork_capped_must_reach_contains_target
    {globalOracleCalls : Nat} {Result : Type u}
    (target : SchedulerNativeCursor globalOracleCalls Result → Prop)
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (targetFork : ∀ cursor, target cursor →
      ∃ (frozenHistory : List QueryRecord)
          (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
          (outputInput advanceInput : ShaInput)
          (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
          (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
            SchedulerNativeCursor globalOracleCalls Result),
        cursor = .forkPair frozenHistory pairRoom outputInput advanceInput
          template next) :
    ∀ (forkCap : Nat) (cursor : SchedulerNativeCursor globalOracleCalls Result),
      SchedulerNativeCursorMustReachWithForkCap target forkCap cursor →
      ∀ currentTransitionFuel, 0 < currentTransitionFuel →
      ∀ answers result,
        (runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
          cursor answers).terminal = .returned result →
        ∃ (prior later : List UnifiedExposureRecord)
            (selected : UnifiedExposureRecord)
            (targetCursor : SchedulerNativeCursor globalOracleCalls Result)
            (answer : Digest256),
          (runSchedulerNativeListRunFrom transitionFuel currentTransitionFuel
              cursor answers).trace = prior ++ selected :: later ∧
          forkCoordinateCount prior ≤ forkCap ∧
          target targetCursor ∧
          selected = schedulerNativeRequestRecord
            (seekSchedulerNativeExposure transitionFuel targetCursor) answer := by
  intro forkCap cursor reaches
  induction reaches with
  | here targetCursor holds =>
      intro current currentPositive answers result completed
      obtain ⟨frozenHistory, pairRoom, outputInput, advanceInput, template,
        next, targetExact⟩ := targetFork targetCursor holds
      subst targetCursor
      cases answers with
      | nil =>
          cases current with
          | zero => omega
          | succ current =>
              simp only [runSchedulerNativeListRunFrom,
                terminalAtExposureEnd, seekSchedulerNativeExposure] at completed
              cases completed
      | cons answer rest =>
          cases current with
          | zero => omega
          | succ current =>
              refine ⟨[],
                (runSchedulerNativeListRunFrom transitionFuel transitionFuel
                  (.forkAdvance frozenHistory pairRoom outputInput advanceInput
                    template answer next) rest).trace,
                .forkOutput frozenHistory outputInput advanceInput template
                  answer,
                .forkPair frozenHistory pairRoom outputInput advanceInput
                  template next,
                answer, ?_, by simp [forkCoordinateCount], holds, ?_⟩
              · simp only [runSchedulerNativeListRunFrom,
                  seekSchedulerNativeExposure, List.nil_append]
              · cases transitionFuel with
                | zero => omega
                | succ reset => rfl
  | @machine MachineResult limits limitBound actor state program fuel coherent
      onReturned forkCap safe ih =>
      intro current currentPositive answers result completed
      have terminalCompleted :
          runSchedulerNativeListTerminalFrom transitionFuel current
              (.machine limits limitBound actor state program fuel coherent
                onReturned) answers = .returned result := by
        rw [← run_scheduler_native_list_run_terminal]
        exact completed
      rw [run_scheduler_native_list_machine_factorization transitionFuel limits
        limitBound actor state program fuel coherent onReturned positive current
        answers] at terminalCompleted
      obtain ⟨returned, _executed, tailCompleted⟩ :=
        terminal_after_projected_machine_prefix_returned_elim
          transitionFuel positive current limits limitBound actor state program
          fuel coherent onReturned answers result terminalCompleted
      have factor := run_scheduler_native_list_run_from_projected_prefix
        transitionFuel positive current currentPositive limits limitBound actor
        state program fuel coherent onReturned answers returned
      have nextPositive := returned_list_terminal_implies_current_positive
        transitionFuel positive
        (machinePrefixContinuationTransitionFuel transitionFuel
          (current - 1) returned.freshQueries)
        (onReturned returned.result returned.finalState returned.finalCoherent)
        returned.remaining result tailCompleted
      obtain ⟨prior, later, selected, targetCursor, answer, tailTrace,
          forkBound, targetHolds, selectedExact⟩ :=
        ih returned.result returned.finalState returned.finalCoherent
          (machinePrefixContinuationTransitionFuel transitionFuel
            (current - 1) returned.freshQueries)
          nextPositive returned.remaining result (by
            rw [run_scheduler_native_list_run_terminal]
            exact tailCompleted)
      refine ⟨projectedMachineFreshRecords actor returned.freshQueries ++ prior,
        later, selected, targetCursor, answer, ?_, ?_, targetHolds,
          selectedExact⟩
      · rw [factor]
        simp only
        rw [tailTrace, List.append_assoc]
      · simpa using forkBound
  | forkPair frozenHistory pairRoom outputInput advanceInput template next safe
      ih =>
      intro current currentPositive answers result completed
      cases current with
      | zero => omega
      | succ current =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListRunFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons forkOutput rest =>
              cases rest with
              | nil =>
                  cases transitionFuel with
                  | zero => omega
                  | succ reset =>
                      simp [runSchedulerNativeListRunFrom,
                        terminalAtExposureEnd, seekSchedulerNativeExposure]
                        at completed
              | cons forkAdvance tail =>
                  cases transitionFuel with
                  | zero => omega
                  | succ reset =>
                      let scheduled : ScheduledForkCoins :=
                        { frozenHistory := frozenHistory
                          outputInput := outputInput
                          advanceInput := advanceInput
                          template := template
                          forkOutput := forkOutput
                          forkAdvance := forkAdvance }
                      have tailCompleted :
                          (runSchedulerNativeListRunFrom (reset + 1) (reset + 1)
                            (next scheduled.configuration) tail).terminal =
                              .returned result := by
                        simpa [runSchedulerNativeListRunFrom,
                          seekSchedulerNativeExposure, scheduled] using completed
                      obtain ⟨prior, later, selected, targetCursor, answer,
                          traceExact, forkBound, targetHolds, selectedExact⟩ :=
                        ih scheduled rfl rfl rfl rfl (reset + 1)
                          (Nat.succ_pos _) tail result tailCompleted
                      refine ⟨[.forkOutput frozenHistory outputInput advanceInput
                          template forkOutput, .forkAdvance scheduled] ++ prior,
                        later, selected, targetCursor, answer, ?_, ?_,
                        targetHolds, selectedExact⟩
                      · simp only [runSchedulerNativeListRunFrom,
                          seekSchedulerNativeExposure]
                        rw [traceExact]
                        simp only [scheduled, List.cons_append, List.nil_append]
                      · simp [forkCoordinateCount]
                        omega
  | forkAdvance frozenHistory pairRoom outputInput advanceInput template
      forkOutput next safe ih =>
      intro current currentPositive answers result completed
      cases current with
      | zero => omega
      | succ current =>
          cases answers with
          | nil =>
              simp [runSchedulerNativeListRunFrom, terminalAtExposureEnd,
                seekSchedulerNativeExposure] at completed
          | cons forkAdvance tail =>
              let scheduled : ScheduledForkCoins :=
                { frozenHistory := frozenHistory
                  outputInput := outputInput
                  advanceInput := advanceInput
                  template := template
                  forkOutput := forkOutput
                  forkAdvance := forkAdvance }
              have tailCompleted :
                  (runSchedulerNativeListRunFrom transitionFuel transitionFuel
                    (next scheduled.configuration) tail).terminal =
                      .returned result := by
                simpa [runSchedulerNativeListRunFrom,
                  seekSchedulerNativeExposure, scheduled] using completed
              obtain ⟨prior, later, selected, targetCursor, answer, traceExact,
                  forkBound, targetHolds, selectedExact⟩ :=
                ih scheduled rfl rfl rfl rfl rfl transitionFuel positive tail
                  result tailCompleted
              refine ⟨.forkAdvance scheduled :: prior, later, selected,
                targetCursor, answer, ?_, ?_, targetHolds, selectedExact⟩
              · simp only [runSchedulerNativeListRunFrom,
                  seekSchedulerNativeExposure]
                rw [traceExact]
                rfl
              · simp [forkCoordinateCount]
                omega
  | weaken safe capLe ih =>
      intro current currentPositive answers result completed
      obtain ⟨prior, later, selected, targetCursor, answer, traceExact,
          forkBound, targetHolds, selectedExact⟩ :=
        ih current currentPositive answers result completed
      exact ⟨prior, later, selected, targetCursor, answer, traceExact,
        forkBound.trans capLe, targetHolds, selectedExact⟩

#print axioms SchedulerNativeCursorMustReachWithForkCap
#print axioms scheduler_native_must_reach_of_fork_cap
#print axioms returned_run_of_fork_capped_must_reach_contains_target

end
end AspisK1.V7Tag73SchedulerNativeMustReachForkCap
