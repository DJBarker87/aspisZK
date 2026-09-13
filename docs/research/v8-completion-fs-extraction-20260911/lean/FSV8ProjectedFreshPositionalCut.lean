import AspisFormal.K1.V7Tag73ProjectedFreshPriorQueryHistory
import AspisFormal.K1.V7Tag73ProjectedMachineNativeRequestPrefix

/-!
# Exact positional cuts in a projected fresh trace

This companion strengthens the native-request lemma with literal history cuts.
It is intentionally source-independent: a `ProjectedFreshReturnedTrace` is the
only execution certificate.  In particular, the request state selected by the
positional decomposition is also the state whose history and fresh-answer
enumeration are used in the two cuts below.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ProjectedFreshPositionalCut

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalProgrammingFreshness
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

universe u

/-- A positional projected-fresh request has exact pre- and post-request
history cuts.  The fresh enumeration of the first cut is exactly `prior`; the
enumeration of the second is exactly the selected answer followed by `later`.
No source callback, target event, or probabilistic premise occurs here. -/
theorem projected_fresh_trace_has_native_request_with_exact_cuts
    {globalOracleCalls : Nat} {Final MachineResult : Type u}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (limits : OracleLimits)
    (limitBound : limits.totalCalls ≤ globalOracleCalls)
    (actor : QueryActor)
    (onReturned : (result : MachineResult) → (state : OracleState) →
      HistoryTotalCoherent state →
        SchedulerNativeCursor globalOracleCalls Final) :
    ∀ {fuel : Nat} {entryState : OracleState}
      {program : OracleMachine MachineResult}
      {freshQueries : List (ShaInput × Digest256)}
      {result : MachineResult} {finalState : OracleState} {steps : Nat}
      (coherent : HistoryTotalCoherent entryState)
      (trace : ProjectedFreshReturnedTrace limits actor fuel entryState program
        freshQueries result finalState steps)
      (prior : List (ShaInput × Digest256)) (input : ShaInput)
      (answer : Digest256) (later : List (ShaInput × Digest256)),
      freshQueries = prior ++ (input, answer) :: later →
      ∃ (requestState : OracleState)
        (requestAppended finalAppended : List QueryRecord),
        requestState.history = entryState.history ++ requestAppended ∧
        freshAnswerEnumeration requestAppended = prior.map Prod.snd ∧
        finalState.history = requestState.history ++ finalAppended ∧
        freshAnswerEnumeration finalAppended = answer :: later.map Prod.snd ∧
        IsExactSchedulerNativeMachineFreshRequest actor requestState input
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (.machine limits limitBound actor entryState program fuel
                coherent onReturned)
              (prior.map Prod.snd))) := by
  intro fuel entryState program freshQueries result finalState steps coherent
    trace
  induction trace with
  | returned fuel state program traceCoherent result finalState steps sought =>
      intro prior input answer later decomposition
      simp at decomposition
  | fresh fuel state requestState program traceCoherent headInput nextProgram
      remainingFuel cachedSteps requestCoherent totalRoom freshRoom missing
      sought headAnswer rest result finalState tailSteps tail ih =>
      intro prior input answer later decomposition
      have coherentExact : coherent = traceCoherent := Subsingleton.elim _ _
      cases coherentExact
      have requestSuffix :=
        seek_next_fresh_request_preserves_projected_suffix limits actor
          state.history [] fuel state requestState program headInput
          nextProgram remainingFuel cachedSteps traceCoherent requestCoherent
          totalRoom freshRoom missing (projected_fresh_suffix_initial state)
          sought
      rcases requestSuffix with ⟨requestAppended, requestHistory,
        requestFresh⟩
      cases prior with
      | nil =>
          simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with ⟨⟨inputExact, answerExact⟩, laterExact⟩
          subst input
          subst answer
          subst later
          have afterRequest := projected_fresh_suffix_fresh requestState.history []
            actor requestState headInput headAnswer
            (projected_fresh_suffix_initial requestState)
          have finalSuffix := projected_fresh_returned_trace_preserves_suffix
            limits actor requestState.history [headAnswer] remainingFuel
            (freshQueryState actor requestState headInput headAnswer)
            (nextProgram headAnswer) rest result finalState tailSteps
            afterRequest tail
          rcases finalSuffix with ⟨finalAppended, finalHistory, finalFresh⟩
          cases transitionFuel with
          | zero => omega
          | succ current =>
              refine ⟨requestState, requestAppended, finalAppended,
                requestHistory, ?_, finalHistory, ?_, ?_⟩
              · simpa using requestFresh
              · simpa using finalFresh
              · simp only [List.map_nil, schedulerNativePrefixCursor]
                rw [seek_scheduler_native_exposure_machine_of_fresh current
                  limits limitBound actor fuel state requestState program
                  traceCoherent headInput nextProgram remainingFuel cachedSteps
                  requestCoherent totalRoom freshRoom missing onReturned sought]
                exact .witness limits limitBound nextProgram remainingFuel
                  requestCoherent totalRoom freshRoom missing onReturned
      | cons priorHead priorTail =>
          rcases priorHead with ⟨priorInput, priorAnswer⟩
          simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at decomposition
          rcases decomposition with ⟨⟨priorInputExact, priorAnswerExact⟩,
            tailExact⟩
          subst priorInput
          subst priorAnswer
          obtain ⟨laterRequestState, laterAppended, finalAppended,
            laterHistory, laterFresh, finalHistory, finalFresh, nextExact⟩ :=
            ih
              (fresh_query_state_preserves_history_total_coherent actor
                requestState headInput headAnswer requestCoherent)
              priorTail input answer later tailExact
          refine ⟨laterRequestState,
            requestAppended ++ [projectedFreshQueryRecord actor
              (headInput, headAnswer)] ++ laterAppended,
            finalAppended, ?_, ?_, finalHistory, finalFresh, ?_⟩
          · rw [laterHistory, freshQueryState, requestHistory]
            simp [projectedFreshQueryRecord, List.append_assoc]
          · simp only [fresh_answer_enumeration_append, requestFresh,
              laterFresh, List.map_cons]
            rfl
          · cases transitionFuel with
            | zero => omega
            | succ current =>
                simp only [List.map_cons, schedulerNativePrefixCursor]
                rw [seek_scheduler_native_exposure_machine_of_fresh current
                  limits limitBound actor fuel state requestState program
                  traceCoherent headInput nextProgram remainingFuel cachedSteps
                  requestCoherent totalRoom freshRoom missing onReturned sought]
                exact nextExact

#print axioms projected_fresh_trace_has_native_request_with_exact_cuts

end
end AspisV8Completion.FSV8ProjectedFreshPositionalCut
