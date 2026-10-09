import FSV8OutsideTargetTraceClean
import AspisFormal.K1.V7Tag73SchedulerCausalStateAlignment

/-!
# A target hit at an actual fresh V8 root request is in the root target event

This leaf is the source-to-target bridge at one exact machine-fresh trace
coordinate.  The request state is not reconstructed from a query pair: it is
identified with the dependent target-clean certificate's state using the
native scheduler request at the same chronological record prefix.

Cached queries are deliberately outside the statement.  They emit no
`machineFresh` record and therefore require first-producer provenance rather
than this theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8FreshRequestTargetEvent

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerTargetClean
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open FSV8ExactRootCursor
open FSV8OutsideTargetTraceClean

noncomputable section

/-- If an actual machine-fresh query in the exact V8 root trace returns an
answer in the operational target set determined by its literal pre-query
state, then the sampled execution belongs to the already-budgeted exact-root
target event.

The `sourceRequest` premise is an operational source fact at the same record
prefix, not an independently chosen state-alignment premise: native request
uniqueness forces it to equal the target-clean certificate state. -/
theorem actual_v8_fresh_request_target_hit_mem_target_event
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (sourceState : OracleState)
    (input : ShaInput) (answer : Digest256)
    (traceDecomposition :
      (runExactRoot parameters configuration transitionFuel sample).trace =
        prior ++ .machineFresh actor input answer :: later)
    (sourceRequest :
      IsExactSchedulerNativeMachineFreshRequest actor sourceState input
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (rootCursor configuration sample.1)
            (prior.map UnifiedExposureRecord.answer))))
    (target : answer ∈
      operationalRequestTargets ∅ sourceState.history input) :
    sample ∈ targetEvent parameters configuration transitionFuel := by
  by_contra outside
  have clean : ExactCompilerTargetClean parameters transitionFuel
      (rootCursor configuration sample.1) sample.2 := by
    unfold ExactCompilerTargetClean
    simpa [targetEvent, exactCompilerTargetEvent,
      hiddenDependentCausalHitEvent, exposureCursor] using outside
  let certificate :=
    exact_compiler_target_clean_constructs_operational_certificate
      parameters transitionFuel (rootCursor configuration sample.1) sample.2
        clean
  have certificateTrace :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (rootCursor configuration sample.1).erase
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2)) =
        prior ++ .machineFresh actor input answer :: later := by
    change exactCompilerUnifiedExposureTrace parameters transitionFuel
      (rootCursor configuration sample.1) sample.2 = _
    exact (exact_compiler_trace_is_actual_v8_root_trace parameters
      configuration transitionFuel sample).trans traceDecomposition
  obtain ⟨certificateState, atPrefix⟩ :=
    certified_operational_machine_at_prefix_of_trace_decomposition certificate
      prior later actor input answer certificateTrace
  have certificateRequest :=
    certified_machine_exposure_has_exact_native_request
      (nativeCursor := rootCursor configuration sample.1) (rootExact := rfl)
        atPrefix
  have stateExact : sourceState = certificateState :=
    exact_native_machine_request_state_unique sourceRequest certificateRequest
  rcases atPrefix with ⟨snapshotSeen, avoids, priorSnapshots, laterSnapshots,
    snapshotTrace, requestCursor, reached, exactRequest, priorExact,
      laterExact⟩
  subst certificateState
  rcases (operational_request_target_hit_iff_mem ∅ sourceState.history input
      answer).mpr target with ⟨member⟩ | ⟨record, member, prefixProof⟩ |
        ⟨prefixProof⟩
  · simpa using member
  · exact avoids ((operational_request_target_hit_iff_mem snapshotSeen
      sourceState.history input answer).mp
        (.priorLiteralPrefix record member prefixProof))
  · exact avoids ((operational_request_target_hit_iff_mem snapshotSeen
      sourceState.history input answer).mp
        (.currentLiteralPrefix prefixProof))

/-- Source-shaped event that some actual machine-fresh record in the V8 root
trace hits the targets of its exact native pre-query state.  This existential
does not include cached calls: a cache hit emits no `machineFresh` record. -/
def actualFreshRequestTargetEvent
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) : Set (ExactCompilerSample HiddenTape parameters) :=
  { sample | ∃ (prior later : List UnifiedExposureRecord)
      (actor : QueryActor) (sourceState : OracleState)
      (input : ShaInput) (answer : Digest256),
      (runExactRoot parameters configuration transitionFuel sample).trace =
          prior ++ .machineFresh actor input answer :: later ∧
      IsExactSchedulerNativeMachineFreshRequest actor sourceState input
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (rootCursor configuration sample.1)
            (prior.map UnifiedExposureRecord.answer))) ∧
      answer ∈ operationalRequestTargets ∅ sourceState.history input }

theorem actual_fresh_request_target_event_subset_root_target_event
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) :
    actualFreshRequestTargetEvent parameters configuration transitionFuel ⊆
      targetEvent parameters configuration transitionFuel := by
  intro sample member
  rcases member with ⟨prior, later, actor, sourceState, input, answer,
    traceDecomposition, sourceRequest, target⟩
  exact actual_v8_fresh_request_target_hit_mem_target_event parameters
    configuration transitionFuel sample prior later actor sourceState input
      answer traceDecomposition sourceRequest target

/-- The actual fresh-request target event uses the exact root target charge;
there is no per-query union and no grinding/work term. -/
theorem actual_fresh_request_target_probability_le_exact_count
    {HiddenTape TapeIdentity Observation : Type} [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (actualFreshRequestTargetEvent parameters configuration
          transitionFuel) ≤
      exactCompilerExactCountError parameters := by
  exact ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
    (actual_fresh_request_target_event_subset_root_target_event parameters
      configuration transitionFuel)).trans
        (target_probability_le_exact_count hiddenLaw parameters configuration
          transitionFuel)

#print axioms actual_v8_fresh_request_target_hit_mem_target_event
#print axioms actual_fresh_request_target_event_subset_root_target_event
#print axioms actual_fresh_request_target_probability_le_exact_count

end
end AspisV8Completion.FSV8FreshRequestTargetEvent
