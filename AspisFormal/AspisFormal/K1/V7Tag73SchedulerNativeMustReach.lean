import AspisFormal.K1.V7Tag73SchedulerNativePrefixTraversal
import AspisFormal.K1.V7Tag73SchedulerProjectedTraceSafety

/-!
# Static must-reach certificates for the scheduler-native interpreter

`SchedulerNativeCursorAllProjectedTracedReturned` proves a property only at
ordinary terminals.  Source alignment also needs a temporal fact: every
successful continuation must pass through a particular pre-answer cursor.

The predicate below is the least proof-relevant tree with exactly that
meaning.  It follows every machine result and every fork coin pair, and it has
no returned or failed constructor.  Consequently it cannot certify a branch
which terminates before reaching the target.  Actual-run extraction from this
static tree is kept separate from its construction by the concrete client.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SchedulerNativeMustReach

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerProjectedTraceSafety
open AspisK1.V7Tag73SchedulerTraceFactorization

noncomputable section

universe u

/-- Every scheduler branch which can continue through the represented
machine/fork tree reaches a cursor satisfying `target` before an ordinary
terminal. -/
inductive SchedulerNativeCursorMustReach
    {globalOracleCalls : Nat} {Result : Type u}
    (target : SchedulerNativeCursor globalOracleCalls Result → Prop) :
    SchedulerNativeCursor globalOracleCalls Result → Prop where
  | here (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (holds : target cursor) :
      SchedulerNativeCursorMustReach target cursor
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
      (safe : ∀ (result : MachineResult) (finalState : OracleState)
        (finalCoherent : HistoryTotalCoherent finalState),
        SchedulerNativeCursorMustReach target
          (onReturned result finalState finalCoherent)) :
      SchedulerNativeCursorMustReach target
        (.machine limits limitBound actor state program fuel coherent
          onReturned)
  | forkPair
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ scheduled : ScheduledForkCoins,
        scheduled.frozenHistory = frozenHistory →
        scheduled.outputInput = outputInput →
        scheduled.advanceInput = advanceInput →
        scheduled.template = template →
        SchedulerNativeCursorMustReach target (next scheduled.configuration)) :
      SchedulerNativeCursorMustReach target
        (.forkPair frozenHistory pairRoom outputInput advanceInput template next)
  | forkAdvance
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (forkOutput : Digest256)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result)
      (safe : ∀ scheduled : ScheduledForkCoins,
        scheduled.frozenHistory = frozenHistory →
        scheduled.outputInput = outputInput →
        scheduled.advanceInput = advanceInput →
        scheduled.template = template →
        scheduled.forkOutput = forkOutput →
        SchedulerNativeCursorMustReach target (next scheduled.configuration)) :
      SchedulerNativeCursorMustReach target
        (.forkAdvance frozenHistory pairRoom outputInput advanceInput template
          forkOutput next)

/-- A stronger stopping predicate can be forgotten pointwise without changing
the operational continuation tree. -/
theorem scheduler_native_must_reach_mono
    {globalOracleCalls : Nat} {Result : Type u}
    {left right : SchedulerNativeCursor globalOracleCalls Result → Prop}
    (imp : ∀ cursor, left cursor → right cursor) :
    ∀ {cursor : SchedulerNativeCursor globalOracleCalls Result},
      SchedulerNativeCursorMustReach left cursor →
        SchedulerNativeCursorMustReach right cursor := by
  intro cursor safe
  induction safe with
  | here cursor holds => exact .here cursor (imp cursor holds)
  | machine limits limitBound actor state program fuel coherent onReturned
      safe ih =>
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

/-! ## Extraction from one literal successful run -/

/-- A successful executable run through a must-reach tree contains the
literal record emitted at the target fork.  The theorem follows the actual
machine prefix and the actual fork answers; it does not choose a synthetic
branch of the static tree.

The target-facing premise is deliberately a fork-output equation.  This is
the exact shape needed by the restored query-batch marker and rules out the
otherwise possible zero-answer terminal case at `here`. -/
theorem returned_run_of_must_reach_contains_target_fork
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
    ∀ (cursor : SchedulerNativeCursor globalOracleCalls Result),
      SchedulerNativeCursorMustReach target cursor →
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
          target targetCursor ∧
          selected = schedulerNativeRequestRecord
            (seekSchedulerNativeExposure transitionFuel targetCursor) answer := by
  intro cursor reaches
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
                answer, ?_, holds, ?_⟩
              · simp only [runSchedulerNativeListRunFrom,
                  seekSchedulerNativeExposure, List.nil_append]
              · cases transitionFuel with
                | zero => omega
                | succ reset => rfl
  | @machine MachineResult limits limitBound actor state program fuel
      coherent onReturned safe ih =>
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
          targetHolds, selectedExact⟩ :=
        ih returned.result returned.finalState returned.finalCoherent
          (machinePrefixContinuationTransitionFuel transitionFuel
            (current - 1) returned.freshQueries)
          nextPositive returned.remaining result (by
            rw [run_scheduler_native_list_run_terminal]
            exact tailCompleted)
      refine ⟨projectedMachineFreshRecords actor returned.freshQueries ++ prior,
        later, selected, targetCursor, answer, ?_, targetHolds, selectedExact⟩
      rw [factor]
      simp only
      rw [tailTrace, List.append_assoc]
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
                          traceExact, targetHolds, selectedExact⟩ :=
                        ih scheduled rfl rfl rfl rfl (reset + 1)
                          (Nat.succ_pos _) tail result tailCompleted
                      refine ⟨[.forkOutput frozenHistory outputInput advanceInput
                          template forkOutput, .forkAdvance scheduled] ++ prior,
                        later, selected, targetCursor, answer, ?_, targetHolds,
                        selectedExact⟩
                      simp only [runSchedulerNativeListRunFrom,
                        seekSchedulerNativeExposure]
                      rw [traceExact]
                      simp only [scheduled, List.cons_append, List.nil_append]
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
                  targetHolds, selectedExact⟩ :=
                ih scheduled rfl rfl rfl rfl rfl transitionFuel positive tail
                  result tailCompleted
              refine ⟨.forkAdvance scheduled :: prior, later, selected,
                targetCursor, answer, ?_, targetHolds, selectedExact⟩
              simp only [runSchedulerNativeListRunFrom,
                seekSchedulerNativeExposure]
              rw [traceExact]
              rfl

#print axioms SchedulerNativeCursorMustReach
#print axioms scheduler_native_must_reach_mono
#print axioms returned_run_of_must_reach_contains_target_fork

end
end AspisK1.V7Tag73SchedulerNativeMustReach
