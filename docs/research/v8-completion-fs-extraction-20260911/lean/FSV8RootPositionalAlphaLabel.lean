import FSV8AlphaPrefixErasureBridge
import FSV8AlphaLabeledPrefixDecomposition
import FSV8RootVerifierNativeRequestExactCuts
import FSV8AlphaExactRequestLabel
import FSV8ReturnedRootFreshTracePrefix

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8RootPositionalAlphaLabel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73ProjectedFreshPriorQueryHistory
open AspisK1.V7Tag73TranscriptSchedule
open FSV8ExactRootCursor FSV8ExactRootFunctionalRun
open FSV8V7OracleMachineBridge
open FSV8AlphaRootLabeledTraceConstructor
open FSV8AlphaPrefixErasureBridge FSV8AlphaLabeledPrefixDecomposition
open FSV8RootVerifierNativeRequestExactCuts FSV8AlphaExactRequestLabel
open FSV8ReturnedRootFreshTracePrefix
noncomputable section

theorem projected_records_answers
    (actor : QueryActor) (queries : List (ShaInput × Digest256)) :
    (projectedMachineFreshRecords actor queries).map
        UnifiedExposureRecord.answer = queries.map Prod.snd := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, ih, UnifiedExposureRecord.answer]

theorem returned_root_positional_query_has_exact_alpha_label
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (transitionRoom : 2 ≤ transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : FSBoundedTranscript.Block)
    (runtime : Runtime TapeIdentity configuration.z)
    (execution : ExactRootFunctionalRun configuration sample.1 sample.2
      fallback runtime)
    (prior : List (ShaInput × Digest256)) (input : ShaInput)
    (answer : Digest256) (later : List (ShaInput × Digest256))
    (decomposition : execution.prefixes.verifier.freshQueries =
      prior ++ (input, answer) :: later) :
    let rootPrior :=
      projectedMachineFreshRecords .adversary
        execution.prefixes.adversary.freshQueries ++
      projectedMachineFreshRecords .verifier prior
    ∃ (requestState : OracleState)
      (requestAppended finalAppended : List QueryRecord)
      (rootLater : List UnifiedExposureRecord),
      requestState.history = execution.prefixes.adversary.finalState.history ++
        requestAppended ∧
      freshAnswerEnumeration requestAppended = prior.map Prod.snd ∧
      execution.prefixes.verifier.finalState.history =
        requestState.history ++ finalAppended ∧
      freshAnswerEnumeration finalAppended = answer :: later.map Prod.snd ∧
      (runExactRoot parameters configuration transitionFuel sample).trace =
        rootPrior ++ UnifiedExposureRecord.machineFresh .verifier input answer :: rootLater ∧
      alpha0RootLabeledRecords configuration transitionFuel sample.1
          (rootPrior ++ [.machineFresh .verifier input answer]) =
        alpha0RootLabeledRecords configuration transitionFuel sample.1
          rootPrior ++
        [(relationAlphaPreferredSlotFromHistory 0 requestState.history input,
          answer)] := by
  dsimp only
  let rootPrior :=
    projectedMachineFreshRecords .adversary
      execution.prefixes.adversary.freshQueries ++
    projectedMachineFreshRecords .verifier prior
  obtain ⟨requestState, requestAppended, finalAppended, requestHistory,
      requestFresh, finalHistory, finalFresh, nativeRequest⟩ :=
    returned_v8_verifier_query_has_global_native_request_with_exact_cuts
      parameters configuration transitionFuel transitionRoom sample fallback
      runtime execution prior input answer later decomposition
  have priorAnswers :
      rootPrior.map UnifiedExposureRecord.answer =
        ((execution.prefixes.adversary.freshQueries ++ prior).map Prod.snd) := by
    simp only [rootPrior, List.map_append, projected_records_answers]
  have reached :
      seekUnifiedExposure transitionFuel
        (machineStateAfterAnswers (relationAlphaSlotMachine 0 transitionFuel)
          (exposureCursor configuration sample.1)
          (rootPrior.map UnifiedExposureRecord.answer)) =
      (seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel
          (rootCursor configuration sample.1)
          ((execution.prefixes.adversary.freshQueries ++ prior).map
            Prod.snd))).erase := by
    rw [priorAnswers]
    exact alpha_seek_after_answers_eq_erased_native_request
      0 transitionFuel (rootCursor configuration sample.1)
      ((execution.prefixes.adversary.freshQueries ++ prior).map Prod.snd)
  have labelExact :=
    scheduler_relation_alpha_label_of_exact_verifier_fresh_request
      0 transitionFuel
      (machineStateAfterAnswers (relationAlphaSlotMachine 0 transitionFuel)
        (exposureCursor configuration sample.1)
        (rootPrior.map UnifiedExposureRecord.answer))
      requestState input _ reached nativeRequest
  have tracePrefix := returned_exact_root_trace_has_fresh_machine_prefix
    parameters configuration transitionFuel (by omega) (by omega)
    sample fallback runtime execution.prefixes
  rcases tracePrefix with ⟨suffix, traceExact⟩
  refine ⟨requestState, requestAppended, finalAppended,
    projectedMachineFreshRecords .verifier later ++ suffix,
    requestHistory, requestFresh, finalHistory, finalFresh, ?_, ?_⟩
  · rw [decomposition] at traceExact
    rw [← traceExact]
    simp only [projected_machine_fresh_records_append,
      projectedMachineFreshRecords, List.cons_append, List.append_assoc]
  · change machineLabeledAnswers (relationAlphaSlotMachine 0 transitionFuel)
        (exposureCursor configuration sample.1)
        ((rootPrior ++ [UnifiedExposureRecord.machineFresh .verifier input answer]).map
          UnifiedExposureRecord.answer) = _
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [machine_labeled_answers_at_cut]
    simp only [machineLabeledAnswers]
    change _ ++ [(schedulerRelationAlphaLabel 0 transitionFuel
      (machineStateAfterAnswers (relationAlphaSlotMachine 0 transitionFuel)
        (exposureCursor configuration sample.1)
        (rootPrior.map UnifiedExposureRecord.answer)), answer)] = _
    rw [labelExact]
    rfl

#print axioms projected_records_answers
#print axioms returned_root_positional_query_has_exact_alpha_label
end
end AspisV8Completion.FSV8RootPositionalAlphaLabel
