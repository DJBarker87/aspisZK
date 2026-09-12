import ExtractionCollectorOperationalAlphaScheduler
import AspisFormal.K1.V7Tag73SchedulerMachineFactorization
import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73FullResultRootRuns

/-!
# One finite-tape scheduler machine segment

This leaf connects the answer suffix used by the native scheduler to the
finite-answer controller already carried by a V8 `ProjectionFacts` boundary.
The equality is deliberately restricted to histories extending that boundary;
the two total controllers need not agree on arbitrary histories.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.FSV8FiniteTapeSchedulerSegment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73FullResultRootRuns
open FSV8ProgrammedProjectionAlignment
open ExtractionCollectorOperationalAlphaScheduler

noncomputable section

universe u

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- At every chronological extension of an aligned boundary, indexing the
global finite tape is the same as indexing the boundary-relative dropped
suffix. This is not an equality of the controllers on arbitrary histories. -/
theorem finite_tape_controller_eq_projected_on_extension
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state)
    (appended : List QueryRecord) (input : ShaInput) :
    controllerFromFreshAnswerTape finiteTape (state.history ++ appended) input =
      controllerFromProjectedFreshAnswers state.history
        (remainingFreshAnswers finiteTape state)
        (state.history ++ appended) input := by
  unfold controllerFromFreshAnswerTape controllerFromProjectedFreshAnswers
    appendedFreshAnswerCount remainingFreshAnswers
  rw [fresh_answer_enumeration_append]
  simp only [List.length_append]
  have freshCount := facts.freshCount
  unfold FreshHistoryCountCoherent at freshCount
  simp only [freshCount]
  rw [List.drop_left]
  simp [List.getElem?_drop]
  split <;> simp_all

/-- `runMachine` only needs controller agreement on chronological extensions
of its entry history.  This avoids the false stronger premise that the two
controllers are equal on arbitrary histories. -/
theorem run_machine_eq_of_controller_agree_on_extensions
    {Result : Type*}
    (first second : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (initialHistory : List QueryRecord)
    (agree : ∀ appended input,
      first (initialHistory ++ appended) input =
        second (initialHistory ++ appended) input) :
    ∀ (fuel : Nat) (state : OracleState) (program : OracleMachine Result),
      (∃ appended, state.history = initialHistory ++ appended) →
      runMachine first limits actor fuel state program =
        runMachine second limits actor fuel state program := by
  intro fuel
  induction fuel with
  | zero =>
      intro state program extension
      cases program <;> rfl
  | succ fuel ih =>
      intro state program extension
      cases program with
      | pure result => rfl
      | abort reason => rfl
      | query input next =>
          rcases extension with ⟨appended, historyExact⟩
          simp only [runMachine]
          have queryEq : queryOracle first limits actor state input =
              queryOracle second limits actor state input := by
            unfold queryOracle
            rw [historyExact, agree appended input]
          rw [queryEq]
          cases success : queryOracle second limits actor state input with
          | error reason => rfl
          | ok pair =>
              rcases pair with ⟨output, nextState⟩
              simp only
              have historyCase := query_oracle_success_table_history_cases
                second limits actor state nextState input output success
              rcases historyCase with ⟨record, nextHistory, _⟩
              have tailEq := ih nextState (next output) (by
                refine ⟨appended ++ [record], ?_⟩
                rw [nextHistory, historyExact, List.append_assoc])
              rw [tailEq]

/-- The boundary-relative answer suffix executes exactly the same machine as
the global finite-tape controller.  The proof uses only reachable-history
controller agreement. -/
theorem finite_tape_run_eq_projected_remaining
    {Result : Type*} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (program : OracleMachine Result) :
    runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
        state program =
      runMachine
        (controllerFromProjectedFreshAnswers state.history
          (remainingFreshAnswers finiteTape state))
        limits actor fuel state program := by
  apply run_machine_eq_of_controller_agree_on_extensions
    (initialHistory := state.history)
  · intro appended input
    exact finite_tape_controller_eq_projected_on_extension facts appended input
  · exact ⟨[], by simp⟩

/-- A normally returned projected prefix over the dropped suffix is the exact
global finite-tape machine run.  Unused suffix answers remain unused. -/
theorem returned_prefix_is_finite_tape_run
    {Result : Type*} {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (program : OracleMachine Result)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      (remainingFreshAnswers finiteTape state)) :
    runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
        state program =
      { halt := .returned returned.result
        oracle := returned.finalState
        steps := returned.steps } := by
  let coherent : HistoryTotalCoherent state := facts.historyTotal
  calc
    runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
        state program =
      runMachine
        (controllerFromProjectedFreshAnswers state.history
          (remainingFreshAnswers finiteTape state))
        limits actor fuel state program :=
      finite_tape_run_eq_projected_remaining facts limits actor fuel program
    _ = runProjectedFreshSegment limits actor
        (remainingFreshAnswers finiteTape state) fuel state program
        coherent := by
      symm
      simpa only [List.nil_append] using
        run_projected_fresh_segment_eq_run_machine limits actor state.history
          [] (remainingFreshAnswers finiteTape state) fuel state program
          coherent
          (projected_fresh_suffix_initial state)
    _ = { halt := .returned returned.result
          oracle := returned.finalState
          steps := returned.steps } := by
      simpa only [returned.availableExact] using
        (projected_fresh_returned_trace_interpreter_exact_with_suffix
        limits actor fuel state program returned.freshQueries
        returned.remaining returned.result returned.finalState returned.steps
        coherent returned.trace)

/-- Exact one-segment bridge used by a source scheduler cursor.  It gives both
the global finite-tape machine equation and the scheduler's literal callback
continuation.  `returned` must be constructed by the executable projected
prefix consumer; no arbitrary run equation or controller equality is taken. -/
theorem finite_tape_scheduler_segment_with_continuation
    {globalOracleCalls : Nat} {Result MachineResult : Type u}
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state)
    (transitionFuel current : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor) (program : OracleMachine MachineResult) (fuel : Nat)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Result)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      (remainingFreshAnswers finiteTape state))
    (executed : consumeProjectedMachinePrefix limits actor
      (remainingFreshAnswers finiteTape state) fuel state program
      (show HistoryTotalCoherent state from facts.historyTotal) = .ok returned) :
    runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
        state program =
        { halt := .returned returned.result
          oracle := returned.finalState
          steps := returned.steps } ∧
      runSchedulerNativeListTerminalFrom transitionFuel (current + 1)
          (.machine limits limitBound actor state program fuel
            (show HistoryTotalCoherent state from facts.historyTotal)
            onReturned)
          (remainingFreshAnswers finiteTape state) =
        runSchedulerNativeListTerminalFrom transitionFuel
          (machinePrefixContinuationTransitionFuel transitionFuel current
            returned.freshQueries)
          (onReturned returned.result returned.finalState
            returned.finalCoherent)
          returned.remaining := by
  constructor
  · exact returned_prefix_is_finite_tape_run facts limits actor fuel program
      returned
  · rw [run_scheduler_native_list_machine_factorization transitionFuel
      limits limitBound actor state program fuel
      (show HistoryTotalCoherent state from facts.historyTotal) onReturned
      positive (current + 1) (remainingFreshAnswers finiteTape state)]
    unfold terminalAfterProjectedMachinePrefix
      terminalAfterCertifiedProjectedMachinePrefix
    unfold consumeProjectedMachinePrefix at executed
    rw [executed]

#print axioms finite_tape_controller_eq_projected_on_extension
#print axioms run_machine_eq_of_controller_agree_on_extensions
#print axioms finite_tape_run_eq_projected_remaining
#print axioms returned_prefix_is_finite_tape_run
#print axioms finite_tape_scheduler_segment_with_continuation

end

end AspisV8Completion.FSV8FiniteTapeSchedulerSegment
