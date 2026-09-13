import FSV8FreshRequestTargetEvent
import FSV8ReturnedRootFreshTracePrefix
import FSV8RootVerifierNativeRequest

/-!
# A returned verifier fresh target hit is charged to the exact root event

This leaf joins three independently checked source facts for one returned V8
execution: the chronological verifier fresh-query list, its exact global
scheduler request, and its position in the actual root trace.  The remaining
`targetAtRequest` premise is deliberately local: a caller must prove that the
answer is in the operational target set of the request state constructed by
the source run.  It is not an accepted-only probability premise.

Cached calls are not covered.  They have no `machineFresh` record and require
first-producer provenance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ReturnedVerifierFreshTargetEvent

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ProjectedMachineNativeRequestPrefix
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8FreshRequestTargetEvent
open FSV8ReturnedRootFreshTracePrefix
open FSV8RootVerifierNativeRequest

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- A literal target hit at one chronologically decomposed verifier fresh
request of a returned exact-root run belongs to the already budgeted root
target event.  The native request and trace position are constructed here. -/
theorem returned_verifier_fresh_target_hit_mem_exact_root_event
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
      prior ++ (input, answer) :: later)
    (targetAtRequest : ∀ sourceState : OracleState,
      IsExactSchedulerNativeMachineFreshRequest .verifier sourceState input
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (rootCursor configuration sample.1)
              ((execution.prefixes.adversary.freshQueries ++ prior).map
                Prod.snd))) →
        answer ∈ operationalRequestTargets ∅ sourceState.history input) :
    sample ∈ targetEvent parameters configuration transitionFuel := by
  obtain ⟨sourceState, _historyPrefix, _priorHistory, sourceRequest⟩ :=
    returned_v8_verifier_query_has_global_native_request parameters
      configuration transitionFuel transitionRoom sample fallback runtime
      execution prior input answer later decomposition
  have tracePrefix := returned_exact_root_trace_has_fresh_machine_prefix
    parameters configuration transitionFuel (by omega) (by omega) sample
      fallback runtime execution.prefixes
  rcases tracePrefix with ⟨suffix, traceExact⟩
  let priorRecords :=
    projectedMachineFreshRecords .adversary
        execution.prefixes.adversary.freshQueries ++
      projectedMachineFreshRecords .verifier prior
  let laterRecords :=
    projectedMachineFreshRecords .verifier later ++ suffix
  have traceDecomposition :
      (runExactRoot parameters configuration transitionFuel sample).trace =
        priorRecords ++ .machineFresh .verifier input answer :: laterRecords := by
    rw [decomposition] at traceExact
    rw [← traceExact]
    simp only [priorRecords, laterRecords,
      projected_machine_fresh_records_append, projectedMachineFreshRecords,
      List.cons_append, List.append_assoc]
  have priorAnswers : priorRecords.map UnifiedExposureRecord.answer =
      (execution.prefixes.adversary.freshQueries ++ prior).map Prod.snd := by
    simp only [priorRecords, List.map_append,
      projected_machine_fresh_record_answers]
  apply actual_v8_fresh_request_target_hit_mem_target_event parameters
    configuration transitionFuel sample priorRecords laterRecords .verifier
      sourceState input answer traceDecomposition
  · simpa only [priorAnswers] using sourceRequest
  · exact targetAtRequest sourceState sourceRequest

#print axioms returned_verifier_fresh_target_hit_mem_exact_root_event

end
end AspisV8Completion.FSV8ReturnedVerifierFreshTargetEvent
