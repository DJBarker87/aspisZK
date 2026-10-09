import FSV8ExactRootFunctionalRun
import AspisFormal.K1.V7Tag73SchedulerTraceFactorization

/-!
# Fresh-record prefix of a returned V8 root trace

This is deterministic trace bookkeeping only.  The two returned projected
machine prefixes supplied by the exact-root inversion are expanded with the
trace-preserving scheduler factorization, so their machine-fresh records occur
in order at the front of the actual erased root trace.  Any later fork,
padding, or continuation records remain in the suffix.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8ReturnedRootFreshTracePrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73SchedulerTraceFactorization
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes

noncomputable section

theorem returned_exact_root_trace_has_fresh_machine_prefix
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (continuationPositive : 1 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : FSBoundedTranscript.Block)
    (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration sample.1 sample.2
      fallback runtime) :
    projectedMachineFreshRecords .adversary prefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier prefixes.verifier.freshQueries <+:
      (runExactRoot parameters configuration transitionFuel sample).trace := by
  have listEq := run_scheduler_native_eq_list_run transitionFuel
    (exactCompilerTargetCaps parameters).length
    (rootCursor configuration sample.1) sample.2
  have traceEq :
      (runExactRoot parameters configuration transitionFuel sample).trace =
        (runSchedulerNativeListRun transitionFuel
          (rootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2)).trace := by
    unfold runExactRoot
    exact congrArg SchedulerNativeRun.trace listEq
  rw [traceEq]
  unfold runSchedulerNativeListRun
  unfold rootCursor
  rw [run_scheduler_native_list_run_from_projected_prefix
    (Result := Runtime TapeIdentity configuration.z) transitionFuel
    positive transitionFuel positive configuration.adversaryLimits
    configuration.adversaryLimitBound .adversary emptyOracle
    (configuration.blackBox.start sample.1 configuration.observation)
    configuration.adversaryFuel empty_oracle_history_total_coherent
    (fun body proverFinalOracle proverCoherent =>
      .machine configuration.verifierLimits configuration.verifierLimitBound
        .verifier proverFinalOracle
        (compileScript (wholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts body
          configuration.initialDigest))
        (stagedBudget n m) proverCoherent
        (fun output verifierFinalOracle _ =>
          .returned
            { tapeIdentity := configuration.tapeIdentity sample.1
              body := body
              proverFinalOracle := proverFinalOracle
              verifierFinalOracle := verifierFinalOracle
              output := output }))
    (freshAnswerTapeToList sample.2) prefixes.adversary]
  rw [run_scheduler_native_list_run_from_projected_prefix
    (Result := Runtime TapeIdentity configuration.z) transitionFuel
    positive
    (machinePrefixContinuationTransitionFuel transitionFuel
      (transitionFuel - 1) prefixes.adversary.freshQueries)
    (by
      unfold machinePrefixContinuationTransitionFuel
      split <;> omega)
    configuration.verifierLimits configuration.verifierLimitBound .verifier
    prefixes.adversary.finalState
    (compileScript (wholeStagedScript configuration.firstWork
      configuration.secondWork configuration.z configuration.cuts
      prefixes.adversary.result configuration.initialDigest))
    (stagedBudget n m) prefixes.adversary.finalCoherent
    (fun output verifierFinalOracle _ =>
      .returned
        { tapeIdentity := configuration.tapeIdentity sample.1
          body := prefixes.adversary.result
          proverFinalOracle := prefixes.adversary.finalState
          verifierFinalOracle := verifierFinalOracle
          output := output })
    prefixes.adversary.remaining prefixes.verifier]
  dsimp only
  rw [← List.append_assoc]
  exact List.prefix_append _ _

/-- Every query in the returned verifier prefix has an exact chronological
coordinate in the actual erased root trace.  Later fork and padding records
are retained in the existential suffix. -/
theorem returned_verifier_fresh_member_decomposes_actual_root_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (continuationPositive : 1 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : FSBoundedTranscript.Block)
    (runtime : Runtime TapeIdentity configuration.z)
    (prefixes : SuccessfulRootMachinePrefixes configuration sample.1 sample.2
      fallback runtime)
    (query : ShaInput × Digest256)
    (member : query ∈ prefixes.verifier.freshQueries) :
    ∃ prior later,
      (runExactRoot parameters configuration transitionFuel sample).trace =
        prior ++ .machineFresh .verifier query.1 query.2 :: later := by
  have tracePrefix := returned_exact_root_trace_has_fresh_machine_prefix
    parameters configuration transitionFuel positive continuationPositive
      sample fallback runtime prefixes
  obtain ⟨verifierPrior, verifierLater, verifierSplit⟩ :=
    (List.mem_iff_append).mp member
  rcases tracePrefix with ⟨suffix, traceExact⟩
  refine ⟨projectedMachineFreshRecords .adversary
      prefixes.adversary.freshQueries ++
        projectedMachineFreshRecords .verifier verifierPrior,
    projectedMachineFreshRecords .verifier verifierLater ++ suffix, ?_⟩
  rw [verifierSplit] at traceExact
  rw [← traceExact]
  simp only [projected_machine_fresh_records_append,
    projectedMachineFreshRecords, List.cons_append, List.append_assoc]

#print axioms returned_exact_root_trace_has_fresh_machine_prefix
#print axioms returned_verifier_fresh_member_decomposes_actual_root_trace

end
end AspisV8Completion.FSV8ReturnedRootFreshTracePrefix
