import FSV8RootVerifierNativeRequest
import FSV8ProjectedFreshPositionalCut

/-!
# Exact global native request and history cuts for a V8 verifier query

This is the source-shaped companion of
`returned_v8_verifier_query_has_global_native_request`.  It transports the
literal pre-request and post-request history decomposition from the returned
verifier trace through the actual adversary-to-verifier root callback.  It
adds no target, probability, or source-alignment premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8RootVerifierNativeRequestExactCuts

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73K12BudgetedSchedulerTree
open AspisK1.V7Tag73SourceAnchoredNativeCursorFactorization
open AspisK1.V7Tag73TranscriptSchedule
open FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8V7WholeScriptUniformLaw
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8ProjectedFreshPositionalCut

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- A positional verifier fresh query has one literal request state.  Its
pre-request history starts at the actual adversary final state, and its
post-request history ends at the actual verifier final state. -/
theorem returned_v8_verifier_query_has_global_native_request_with_exact_cuts
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (transitionRoom : 2 ≤ transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (execution : ExactRootFunctionalRun configuration sample.1 sample.2
      fallback runtime)
    (prior : List (ShaInput × Digest256)) (input : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition : execution.prefixes.verifier.freshQueries =
      prior ++ (input, answer) :: later) :
    ∃ (requestState : OracleState)
      (requestAppended finalAppended : List QueryRecord),
      requestState.history = execution.prefixes.adversary.finalState.history ++
        requestAppended ∧
      freshAnswerEnumeration requestAppended = prior.map Prod.snd ∧
      execution.prefixes.verifier.finalState.history = requestState.history ++
        finalAppended ∧
      freshAnswerEnumeration finalAppended = answer :: later.map Prod.snd ∧
      IsExactSchedulerNativeMachineFreshRequest .verifier requestState input
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (rootCursor configuration sample.1)
            ((execution.prefixes.adversary.freshQueries ++ prior).map
              Prod.snd))) := by
  let verifierReturned :
      (output : Except FSAuthenticatedInterleavedPrefixMiddle.Error
        (Record execution.prefixes.adversary.result configuration.z) × Block) →
      (verifierFinalOracle : OracleState) →
      HistoryTotalCoherent verifierFinalOracle →
        SchedulerNativeCursor (globalFull256OracleCallCap parameters)
          (Runtime TapeIdentity configuration.z) := fun
      (output : Except FSAuthenticatedInterleavedPrefixMiddle.Error
        (Record execution.prefixes.adversary.result configuration.z) × Block)
      (verifierFinalOracle : OracleState)
      (_ : HistoryTotalCoherent verifierFinalOracle) =>
    SchedulerNativeCursor.returned
      (Runtime.mk (configuration.tapeIdentity sample.1)
        execution.prefixes.adversary.result
        execution.prefixes.adversary.finalState verifierFinalOracle output)
  let verifierCursor : SchedulerNativeCursor
      (globalFull256OracleCallCap parameters)
      (Runtime TapeIdentity configuration.z) :=
    .machine configuration.verifierLimits configuration.verifierLimitBound
      .verifier execution.prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        execution.prefixes.adversary.result configuration.initialDigest))
      (stagedBudget n m) execution.prefixes.adversary.finalCoherent
      verifierReturned
  have verifierNonempty : execution.prefixes.verifier.freshQueries ≠ [] := by
    rw [decomposition]
    simp
  have positive : 0 < transitionFuel := by omega
  have adversaryBoundary :
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (rootCursor configuration sample.1)
            (execution.prefixes.adversary.freshQueries.map Prod.snd)) =
        seekSchedulerNativeExposure transitionFuel verifierCursor := by
    let adversaryReturned :
        (body : List UInt8) → (proverFinalOracle : OracleState) →
        HistoryTotalCoherent proverFinalOracle →
        SchedulerNativeCursor (globalFull256OracleCallCap parameters)
          (Runtime TapeIdentity configuration.z) := fun
        (body : List UInt8) (proverFinalOracle : OracleState)
        (proverCoherent : HistoryTotalCoherent proverFinalOracle) =>
      SchedulerNativeCursor.machine configuration.verifierLimits
        configuration.verifierLimitBound .verifier proverFinalOracle
        (compileScript (wholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts body
          configuration.initialDigest))
        (stagedBudget n m) proverCoherent
        (fun output verifierFinalOracle _ =>
          .returned
            (Runtime.mk (configuration.tapeIdentity sample.1) body
              proverFinalOracle verifierFinalOracle output))
    have reaches :=
      projected_machine_prefix_reaches_returned_native_predecessor_for_k12
        transitionFuel positive configuration.adversaryLimits
        configuration.adversaryLimitBound .adversary
        configuration.adversaryFuel emptyOracle
        (configuration.blackBox.start sample.1 configuration.observation)
        empty_oracle_history_total_coherent adversaryReturned
        (freshAnswerTapeToList sample.2) execution.prefixes.adversary
    have predecessor :=
      projected_nonempty_fresh_prefix_seek_predecessor_eq_for_k12
        transitionFuel transitionRoom configuration.verifierLimits
        configuration.verifierLimitBound .verifier (stagedBudget n m)
        execution.prefixes.adversary.finalState
        (compileScript (wholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          execution.prefixes.adversary.result configuration.initialDigest))
        execution.prefixes.adversary.finalCoherent verifierReturned
        execution.prefixes.verifier.trace verifierNonempty
    change seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (.machine configuration.adversaryLimits
            configuration.adversaryLimitBound .adversary emptyOracle
            (configuration.blackBox.start sample.1 configuration.observation)
            configuration.adversaryFuel empty_oracle_history_total_coherent
            adversaryReturned)
          (execution.prefixes.adversary.freshQueries.map Prod.snd)) = _
    exact reaches.trans (by
      simpa only [adversaryReturned, verifierCursor, verifierReturned] using
        predecessor)
  obtain ⟨requestState, requestAppended, finalAppended, requestHistory,
    requestFresh, finalHistory, finalFresh, localExact⟩ :=
    projected_fresh_trace_has_native_request_with_exact_cuts
      transitionFuel positive configuration.verifierLimits
      configuration.verifierLimitBound .verifier verifierReturned
      execution.prefixes.adversary.finalCoherent
      execution.prefixes.verifier.trace prior input answer later decomposition
  refine ⟨requestState, requestAppended, finalAppended, requestHistory,
    requestFresh, finalHistory, finalFresh, ?_⟩
  rw [List.map_append, scheduler_native_prefix_cursor_append]
  cases prior with
  | nil =>
      simp only [List.map_nil, schedulerNativePrefixCursor] at localExact ⊢
      rw [adversaryBoundary]
      simpa only [verifierCursor, List.map_cons] using localExact
  | cons head rest =>
      rcases head with ⟨headInput, headAnswer⟩
      simp only [List.map_cons]
      rw [scheduler_native_prefix_cursor_cons_congr_of_seek_eq transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (rootCursor configuration sample.1)
          (execution.prefixes.adversary.freshQueries.map Prod.snd))
        verifierCursor headAnswer (rest.map Prod.snd) adversaryBoundary]
      simpa only [verifierCursor, List.map_cons] using localExact

#print axioms returned_v8_verifier_query_has_global_native_request_with_exact_cuts

end
end AspisV8Completion.FSV8RootVerifierNativeRequestExactCuts
