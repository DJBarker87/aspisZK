import FSV8ReturnedVerifierFreshTargetEvent

/-!
# Fresh-marker target reduction at the actual verifier request

The marker's request-level target proof is relative to the source marker
state.  This leaf transports current-input targets immediately and transports
prior-history targets whenever their concrete creator record is present in
the exact global request state.  The sole remaining alternative is an
explicit prior marker-history record missing from that state.

No state equality, target hit at a substituted state, or cached-query
first-exposure claim is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8MarkerFreshTargetReduction

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8RootVerifierNativeRequest
open FSV8ReturnedVerifierFreshTargetEvent

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- An actual fresh marker target is already in the exact-root target event,
unless one can exhibit a literal-prefix creator record present in the marker
state but absent from the exact global request state at that same fresh-query
coordinate. -/
theorem returned_fresh_marker_target_event_or_missing_prior_record
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
    (markerState : OracleState) (markerInput : ShaInput)
    (markerAnswer : Digest256)
    (markerMember : (markerInput, markerAnswer) ∈
      execution.prefixes.verifier.freshQueries)
    (markerTarget : markerAnswer ∈
      operationalRequestTargets ∅ markerState.history markerInput) :
    sample ∈ targetEvent parameters configuration transitionFuel ∨
      ∃ (prior later : List (ShaInput × Digest256))
        (requestState : OracleState) (record : QueryRecord),
        execution.prefixes.verifier.freshQueries =
            prior ++ (markerInput, markerAnswer) :: later ∧
        IsExactSchedulerNativeMachineFreshRequest .verifier requestState
          markerInput
          (seekSchedulerNativeExposure transitionFuel
            (schedulerNativePrefixCursor transitionFuel
              (rootCursor configuration sample.1)
              ((execution.prefixes.adversary.freshQueries ++ prior).map
                Prod.snd))) ∧
        record ∈ markerState.history ∧
        HasLiteralStatePrefix markerAnswer record.input ∧
        record ∉ requestState.history := by
  obtain ⟨prior, later, decomposition⟩ := (List.mem_iff_append).mp markerMember
  obtain ⟨requestState, _entryPrefix, _priorHistory, sourceRequest⟩ :=
    returned_v8_verifier_query_has_global_native_request parameters
      configuration transitionFuel transitionRoom sample fallback runtime
      execution prior markerInput markerAnswer later decomposition
  rcases (operational_request_target_hit_iff_mem ∅ markerState.history
      markerInput markerAnswer).mpr markerTarget with
    ⟨priorFull⟩ | ⟨record, recordMember, prefixProof⟩ | ⟨prefixProof⟩
  · simpa using priorFull
  · by_cases transported : record ∈ requestState.history
    · left
      apply returned_verifier_fresh_target_hit_mem_exact_root_event parameters
        configuration transitionFuel transitionRoom sample fallback runtime
          execution prior markerInput markerAnswer later decomposition
      intro otherState otherRequest
      have stateExact : otherState = requestState :=
        exact_native_machine_request_state_unique otherRequest sourceRequest
      subst otherState
      exact (operational_request_target_hit_iff_mem ∅ requestState.history
        markerInput markerAnswer).mp
          (.priorLiteralPrefix record transported prefixProof)
    · right
      exact ⟨prior, later, requestState, record, decomposition, sourceRequest,
        recordMember, prefixProof, transported⟩
  · left
    apply returned_verifier_fresh_target_hit_mem_exact_root_event parameters
      configuration transitionFuel transitionRoom sample fallback runtime
        execution prior markerInput markerAnswer later decomposition
    intro requestState _sourceRequest
    exact (operational_request_target_hit_iff_mem ∅ requestState.history
      markerInput markerAnswer).mp (.currentLiteralPrefix prefixProof)

#print axioms returned_fresh_marker_target_event_or_missing_prior_record

end
end AspisV8Completion.FSV8MarkerFreshTargetReduction
