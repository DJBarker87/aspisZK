import FSV8MarkerFreshEnumerationSplit
import FSV8ReturnedVerifierFreshTargetEvent

/-!
# Fresh marker creator is charged to the exact V8 root target event

This source-shaped endpoint retains the concrete earlier creator record.
When that record is a fresh verifier record before the marker, the exact
chronological split and global native request retain it at the marker request.
Its literal-prefix relation therefore gives the target hit consumed by the
existing exact-root probability event.

Cached or programmed creator records are not promoted by this theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8MarkerFreshCreatorTargetEvent

open FSOracleExecution
open FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8MarkerFreshVerifierQueryBridge
open FSV8MarkerFreshEnumerationSplit
open FSV8RootVerifierNativeRequest
open FSV8ReturnedVerifierFreshTargetEvent

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- A fresh verifier creator occurring before an actual fresh marker gives a
literal target hit at the exact global request state, hence belongs to the
already-budgeted root target event. -/
theorem returned_fresh_marker_prior_fresh_creator_mem_root_target_event
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
    (markerState markerNext : OracleState)
    (markerInput : ShaInput) (markerAnswer : Digest256)
    (entryPrefix : execution.prefixes.adversary.finalState.history <+:
      markerState.history)
    (markerHistory : markerNext.history = markerState.history ++
      [markerFreshRecord .verifier markerInput markerAnswer])
    (finalPrefix : markerNext.history <+:
      execution.prefixes.verifier.finalState.history)
    (creator : QueryRecord) (creatorMember : creator ∈ markerState.history)
    (creatorActor : creator.actor = .verifier)
    (creatorFresh : creator.origin = .fresh)
    (literalPrefix : HasLiteralStatePrefix markerAnswer creator.input) :
    sample ∈ targetEvent parameters configuration transitionFuel := by
  let prior := freshQueryEnumeration
    (historySince execution.prefixes.adversary.finalState markerState)
  obtain ⟨later, localSplit⟩ := markerFresh_exact_fresh_enumeration_split
    execution.prefixes.adversary.finalState markerState markerNext
    execution.prefixes.verifier.finalState .verifier markerInput markerAnswer
    entryPrefix markerHistory finalPrefix
  have enumerationExact :=
    projected_fresh_returned_trace_fresh_query_enumeration_exact
      configuration.verifierLimits .verifier (stagedBudget n m)
      execution.prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        execution.prefixes.adversary.result configuration.initialDigest))
      execution.prefixes.verifier.freshQueries
      execution.prefixes.verifier.result execution.prefixes.verifier.finalState
      execution.prefixes.verifier.steps execution.prefixes.verifier.trace
  have decomposition : execution.prefixes.verifier.freshQueries =
      prior ++ (markerInput, markerAnswer) :: later := by
    rw [← enumerationExact]
    simpa only [prior, List.append_assoc, List.singleton_append] using localSplit
  obtain ⟨requestState, requestEntryPrefix, priorHistory, sourceRequest⟩ :=
    returned_v8_verifier_query_has_global_native_request parameters
      configuration transitionFuel transitionRoom sample fallback runtime
      execution prior markerInput markerAnswer later decomposition
  have creatorAtRequest : creator ∈ requestState.history :=
    fresh_verifier_record_before_marker_mem_request
      execution.prefixes.adversary.finalState markerState requestState creator
      entryPrefix requestEntryPrefix priorHistory creatorMember creatorActor
      creatorFresh
  apply returned_verifier_fresh_target_hit_mem_exact_root_event parameters
    configuration transitionFuel transitionRoom sample fallback runtime
      execution prior markerInput markerAnswer later decomposition
  intro otherState otherRequest
  have stateExact : otherState = requestState :=
    exact_native_machine_request_state_unique otherRequest sourceRequest
  subst otherState
  exact (operational_request_target_hit_iff_mem ∅ requestState.history
    markerInput markerAnswer).mp
      (.priorLiteralPrefix creator creatorAtRequest literalPrefix)

#print axioms returned_fresh_marker_prior_fresh_creator_mem_root_target_event

end
end AspisV8Completion.FSV8MarkerFreshCreatorTargetEvent
