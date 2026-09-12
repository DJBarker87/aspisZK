import AspisFormal.K1.V7Tag73ExactPlainRomTraceResourceCaps
import AspisFormal.K1.V7Tag73GammaRestoredK14Scope

/-!
# Exact numeric reserve for the scoped restored-gamma K1.4 prefix

The accepted verifier's block-zero gamma transition occurs before the exact
1444-step canonical driver cap.  A production root sweep reserves 1513
restoration requests.  Consequently the root plus every complete request up
to that transition still leaves substantially more than the 24 coordinates
required by the variable-prefix gamma factorization.

This file proves only that arithmetic reserve.  A separate trace lemma must
show that the literal prefix consumes no more than the stated per-request
machine/fork caps.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73GammaRestoredK14PrefixCapacity

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-! ## Active prefixes contain no terminal padding -/

/-- The three scheduler requests that consume genuine full-256 coordinates.
Terminal and transition-limit requests emit only padding. -/
def SchedulerNativeRequestIsActive
    {globalOracleCalls : Nat} {Result : Type}
    (request : SchedulerNativeRequest globalOracleCalls Result) : Prop :=
  match request with
  | .machineFresh .. | .forkOutput .. | .forkAdvance .. => True
  | .returned _ | .failed _ | .transitionLimit => False

@[simp] theorem scheduler_native_prefix_cursor_returned
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (result : Result) (answers : List Digest256) :
    schedulerNativePrefixCursor transitionFuel
        (.returned result : SchedulerNativeCursor globalOracleCalls Result)
        answers = .returned result := by
  cases transitionFuel with
  | zero => omega
  | succ transitionFuel =>
    clear positive
    induction answers with
    | nil => rfl
    | cons answer rest ih =>
        simpa [schedulerNativePrefixCursor, seekSchedulerNativeExposure,
          schedulerNativeRequestNext] using ih

@[simp] theorem scheduler_native_prefix_cursor_failed
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (reason : SchedulerNativeFailure)
    (answers : List Digest256) :
    schedulerNativePrefixCursor transitionFuel
        (.failed reason : SchedulerNativeCursor globalOracleCalls Result)
        answers = .failed reason := by
  cases transitionFuel with
  | zero => omega
  | succ transitionFuel =>
    clear positive
    induction answers with
    | nil => rfl
    | cons answer rest ih =>
        simpa [schedulerNativePrefixCursor, seekSchedulerNativeExposure,
          schedulerNativeRequestNext] using ih

/-- Any answer prefix ending at an active request contains no terminal
padding.  This generic form covers a verifier fork as well as an earlier
adversary exposure of the same immutable SHA coordinate. -/
theorem scheduler_native_prefix_records_padding_free_of_reached_active
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel) :
    ∀ (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256),
      SchedulerNativeRequestIsActive
        (seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor answers)) →
      paddingCoordinateCount
        (schedulerNativePrefixRecords transitionFuel cursor answers) = 0 := by
  intro cursor answers
  induction answers generalizing cursor with
  | nil =>
      intro _active
      rfl
  | cons answer rest ih =>
      intro active
      generalize requestExact :
          seekSchedulerNativeExposure transitionFuel cursor = request
      cases request with
      | returned result =>
          cases transitionFuel with
          | zero => omega
          | succ fuel =>
              simp [schedulerNativePrefixCursor, requestExact,
                schedulerNativeRequestNext,
                SchedulerNativeRequestIsActive] at active
      | failed reason =>
          cases transitionFuel with
          | zero => omega
          | succ fuel =>
              simp [schedulerNativePrefixCursor, requestExact,
                schedulerNativeRequestNext, seekSchedulerNativeExposure,
                SchedulerNativeRequestIsActive] at active
      | transitionLimit =>
          cases transitionFuel with
          | zero => omega
          | succ fuel =>
              simp [schedulerNativePrefixCursor, requestExact,
                schedulerNativeRequestNext, seekSchedulerNativeExposure,
                SchedulerNativeRequestIsActive] at active
      | machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          have tailActive : SchedulerNativeRequestIsActive
              (seekSchedulerNativeExposure transitionFuel
                (schedulerNativePrefixCursor transitionFuel
                  (schedulerNativeRequestNext
                    (.machineFresh limits limitBound actor state input
                      nextProgram remainingFuel coherent totalRoom freshRoom
                      missing onReturned) answer) rest)) := by
            simpa [schedulerNativePrefixCursor, requestExact] using active
          have tailFree := ih
            (schedulerNativeRequestNext
              (.machineFresh limits limitBound actor state input nextProgram
                remainingFuel coherent totalRoom freshRoom missing onReturned)
              answer) tailActive
          rw [schedulerNativePrefixRecords, requestExact]
          simpa [schedulerNativeRequestRecord, paddingCoordinateCount] using
            tailFree

      | forkOutput frozen pairRoom output advance template next =>
          have tailActive : SchedulerNativeRequestIsActive
              (seekSchedulerNativeExposure transitionFuel
                (schedulerNativePrefixCursor transitionFuel
                  (schedulerNativeRequestNext
                    (.forkOutput frozen pairRoom output advance template next)
                    answer) rest)) := by
            simpa [schedulerNativePrefixCursor, requestExact] using active
          have tailFree := ih
            (schedulerNativeRequestNext
              (.forkOutput frozen pairRoom output advance template next) answer)
            tailActive
          rw [schedulerNativePrefixRecords, requestExact]
          simpa [schedulerNativeRequestRecord, paddingCoordinateCount] using
            tailFree

      | forkAdvance frozen pairRoom output advance template forkOutput next =>
          have tailActive : SchedulerNativeRequestIsActive
              (seekSchedulerNativeExposure transitionFuel
                (schedulerNativePrefixCursor transitionFuel
                  (schedulerNativeRequestNext
                    (.forkAdvance frozen pairRoom output advance template
                      forkOutput next) answer) rest)) := by
            simpa [schedulerNativePrefixCursor, requestExact] using active
          have tailFree := ih
            (schedulerNativeRequestNext
              (.forkAdvance frozen pairRoom output advance template forkOutput
                next) answer) tailActive
          rw [schedulerNativePrefixRecords, requestExact]
          simpa [schedulerNativeRequestRecord, paddingCoordinateCount] using
            tailFree

/-- An observed chronological prefix whose next native request is still active
contains no padding records. -/
theorem run_trace_prefix_padding_free_of_reached_active
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (prior later : List UnifiedExposureRecord)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        prior ++ later)
    (active : SchedulerNativeRequestIsActive
      (seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel cursor
          (prior.map UnifiedExposureRecord.answer)))) :
    paddingCoordinateCount prior = 0 := by
  have recordsExact := scheduler_native_prefix_records_eq_of_run_trace_prefix
    transitionFuel cursor answers prior later traceExact
  rw [← recordsExact]
  exact scheduler_native_prefix_records_padding_free_of_reached_active
    transitionFuel positive cursor (prior.map UnifiedExposureRecord.answer)
      active

/-- Before any still-active request, chronological length is exactly the sum
of the two real full-256 resource classes. -/
theorem run_trace_prefix_length_eq_machine_plus_fork_of_reached_active
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (prior later : List UnifiedExposureRecord)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        prior ++ later)
    (active : SchedulerNativeRequestIsActive
      (seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel cursor
          (prior.map UnifiedExposureRecord.answer)))) :
    prior.length = machineFreshCoordinateCount prior +
      forkCoordinateCount prior := by
  have paddingFree := run_trace_prefix_padding_free_of_reached_active
    transitionFuel positive cursor answers prior later traceExact active
  have partition := trace_coordinate_partition prior
  omega

/-- If the next literal record is a fork output, the deterministic native
prefix must end at an active request.  This extracts the request shape from
the trace rather than assuming cursor identity. -/
theorem run_trace_prefix_reaches_active_of_selected_fork_output
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (prior later : List UnifiedExposureRecord)
    (frozenHistory : List QueryRecord)
    (outputInput advanceInput : ShaInput)
    (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
    (answer : Digest256)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        prior ++
          (.forkOutput frozenHistory outputInput advanceInput template answer :
            UnifiedExposureRecord) :: later) :
    SchedulerNativeRequestIsActive
      (seekSchedulerNativeExposure transitionFuel
        (schedulerNativePrefixCursor transitionFuel cursor
          (prior.map UnifiedExposureRecord.answer))) := by
  let selected : UnifiedExposureRecord :=
    .forkOutput frozenHistory outputInput advanceInput template answer
  have priorExact := scheduler_native_prefix_records_eq_of_run_trace_prefix
    transitionFuel cursor answers prior (selected :: later) (by
      simpa only [selected] using traceExact)
  have throughExact := scheduler_native_prefix_records_eq_of_run_trace_prefix
    transitionFuel cursor answers (prior ++ [selected]) later (by
      simpa [selected, List.append_assoc] using traceExact)
  rw [List.map_append, scheduler_native_prefix_records_append, priorExact] at throughExact
  have oneStep :
      schedulerNativePrefixRecords transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor
            (prior.map UnifiedExposureRecord.answer)) [answer] = [selected] := by
    have cancelled := (List.append_right_inj prior).mp throughExact
    have selectedAnswer : selected.answer = answer := by rfl
    rw [List.map_singleton, selectedAnswer] at cancelled
    exact cancelled
  generalize requestExact : seekSchedulerNativeExposure transitionFuel
      (schedulerNativePrefixCursor transitionFuel cursor
        (prior.map UnifiedExposureRecord.answer)) = request
  cases request <;> simp [schedulerNativePrefixRecords, requestExact, selected,
    schedulerNativeRequestRecord, SchedulerNativeRequestIsActive] at oneStep ⊢

/-- Padding is emitted only after the scheduler has halted.  Therefore a
literal answer prefix whose reached cursor still exposes a fork output
contains only machine-fresh and fork coordinates. -/
theorem scheduler_native_prefix_records_padding_free_of_reached_fork
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel) :
    ∀ (cursor : SchedulerNativeCursor globalOracleCalls Result)
      (answers : List Digest256)
      (frozenHistory : List QueryRecord)
      (pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls)
      (outputInput advanceInput : ShaInput)
      (template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration)
      (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
        SchedulerNativeCursor globalOracleCalls Result),
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor answers) =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template next →
      paddingCoordinateCount
          (schedulerNativePrefixRecords transitionFuel cursor answers) = 0 := by
  intro cursor answers
  induction answers generalizing cursor with
  | nil =>
      intro frozenHistory pairRoom outputInput advanceInput template next reached
      rfl
  | cons answer rest ih =>
      intro frozenHistory pairRoom outputInput advanceInput template next reached
      generalize requestExact :
          seekSchedulerNativeExposure transitionFuel cursor = request
      cases request with
      | returned result =>
          cases transitionFuel with
          | zero => omega
          | succ fuel =>
              simp [schedulerNativePrefixCursor, requestExact,
                schedulerNativeRequestNext] at reached
      | failed reason =>
          cases transitionFuel with
          | zero => omega
          | succ fuel =>
              simp [schedulerNativePrefixCursor, requestExact,
                schedulerNativeRequestNext, seekSchedulerNativeExposure] at reached
      | transitionLimit =>
          cases transitionFuel with
          | zero => omega
          | succ fuel =>
              simp [schedulerNativePrefixCursor, requestExact,
                schedulerNativeRequestNext, seekSchedulerNativeExposure] at reached
      | machineFresh limits limitBound actor state input nextProgram
          remainingFuel coherent totalRoom freshRoom missing onReturned =>
          have tailReached :
              seekSchedulerNativeExposure transitionFuel
                  (schedulerNativePrefixCursor transitionFuel
                    (schedulerNativeRequestNext
                      (.machineFresh limits limitBound actor state input
                        nextProgram remainingFuel coherent totalRoom freshRoom
                        missing onReturned)
                      answer)
                    rest) =
                .forkOutput frozenHistory pairRoom outputInput advanceInput
                  template next := by
            simpa [schedulerNativePrefixCursor, requestExact,
              schedulerNativeRequestNext] using reached
          have tailFree := ih
            (schedulerNativeRequestNext
              (.machineFresh limits limitBound actor state input nextProgram
                remainingFuel coherent totalRoom freshRoom missing onReturned)
              answer)
            frozenHistory pairRoom outputInput advanceInput template next
            tailReached
          rw [schedulerNativePrefixRecords, requestExact]
          simpa [schedulerNativeRequestRecord, paddingCoordinateCount] using tailFree
      | forkOutput frozen pairRoom' output advance template' next' =>
          have tailReached :
              seekSchedulerNativeExposure transitionFuel
                  (schedulerNativePrefixCursor transitionFuel
                    (schedulerNativeRequestNext
                      (.forkOutput frozen pairRoom' output advance template' next')
                      answer) rest) =
                .forkOutput frozenHistory pairRoom outputInput advanceInput
                  template next := by
            simpa [schedulerNativePrefixCursor, requestExact,
              schedulerNativeRequestNext] using reached
          have tailFree := ih
            (schedulerNativeRequestNext
              (.forkOutput frozen pairRoom' output advance template' next') answer)
            frozenHistory pairRoom outputInput advanceInput template next
            tailReached
          rw [schedulerNativePrefixRecords, requestExact]
          simpa [schedulerNativeRequestRecord, paddingCoordinateCount] using tailFree
      | forkAdvance frozen pairRoom' output advance template' forkOutput next' =>
          have tailReached :
              seekSchedulerNativeExposure transitionFuel
                  (schedulerNativePrefixCursor transitionFuel
                    (schedulerNativeRequestNext
                      (.forkAdvance frozen pairRoom' output advance template'
                        forkOutput next') answer) rest) =
                .forkOutput frozenHistory pairRoom outputInput advanceInput
                  template next := by
            simpa [schedulerNativePrefixCursor, requestExact,
              schedulerNativeRequestNext] using reached
          have tailFree := ih
            (schedulerNativeRequestNext
              (.forkAdvance frozen pairRoom' output advance template' forkOutput
                next') answer)
            frozenHistory pairRoom outputInput advanceInput template next
            tailReached
          rw [schedulerNativePrefixRecords, requestExact]
          simpa [schedulerNativeRequestRecord, paddingCoordinateCount] using tailFree

/-- An observed chronological prefix of a literal returned run inherits the
padding-free property from its reached live fork cursor. -/
theorem run_trace_prefix_padding_free_of_reached_fork
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (prior later : List UnifiedExposureRecord)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        prior ++ later)
    {frozenHistory : List QueryRecord}
    {pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls}
    {outputInput advanceInput : ShaInput}
    {template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration}
    {next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
      SchedulerNativeCursor globalOracleCalls Result}
    (reached :
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor
            (prior.map UnifiedExposureRecord.answer)) =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next) :
    paddingCoordinateCount prior = 0 := by
  have recordsExact := scheduler_native_prefix_records_eq_of_run_trace_prefix
    transitionFuel cursor answers prior later traceExact
  rw [← recordsExact]
  exact scheduler_native_prefix_records_padding_free_of_reached_fork
    transitionFuel positive cursor (prior.map UnifiedExposureRecord.answer)
      frozenHistory pairRoom outputInput advanceInput template next reached

/-- Before a live fork, chronological length is exactly the sum of the two
real full-256 resource classes: machine-fresh and fork coordinates. -/
theorem run_trace_prefix_length_eq_machine_plus_fork_of_reached_fork
    {globalOracleCalls : Nat} {Result : Type}
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (cursor : SchedulerNativeCursor globalOracleCalls Result)
    (answers : List Digest256)
    (prior later : List UnifiedExposureRecord)
    (traceExact :
      (runSchedulerNativeListRun transitionFuel cursor answers).trace =
        prior ++ later)
    {frozenHistory : List QueryRecord}
    {pairRoom : frozenHistory.length + 2 ≤ globalOracleCalls}
    {outputInput advanceInput : ShaInput}
    {template : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration}
    {next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
      SchedulerNativeCursor globalOracleCalls Result}
    (reached :
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel cursor
            (prior.map UnifiedExposureRecord.answer)) =
        .forkOutput frozenHistory pairRoom outputInput advanceInput template
          next) :
    prior.length = machineFreshCoordinateCount prior +
      forkCoordinateCount prior := by
  have paddingFree := run_trace_prefix_padding_free_of_reached_fork
    transitionFuel positive cursor answers prior later traceExact reached
  have partition := trace_coordinate_partition prior
  omega

/-- Machine-fresh allowance through the selected root-sweep request: the
original root plus every request up to and including the selected one. -/
def exactGammaRestoredPrefixMachineCap
    (parameters : ExactCompilerResourceParameters) (transitionIndex : Nat) : Nat :=
  parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
    (transitionIndex + 1) *
      (parameters.q1ShaCallCap + deployedFull256VerifierCallCap)

/-- Fork-coordinate allowance through the selected request.  Counting its
whole pair is conservative because routing stops at the pair output. -/
def exactGammaRestoredPrefixForkCap (transitionIndex : Nat) : Nat :=
  2 * (transitionIndex + 1)

/-- The 69-request gap between the canonical 1444-step verifier and the
1513-position sweep pays for the complete 24-coordinate gamma tape, even
after charging every earlier request at its full worst-case cost. -/
theorem exact_gamma_restored_prefix_numeric_capacity
    (parameters : ExactCompilerResourceParameters)
    (transitionIndex : Nat)
    (indexWithinCanonical : transitionIndex < tag73CanonicalDriverFuelCap)
    (sweepReserved : 1513 ≤ parameters.forkRequestCap) :
    exactGammaRestoredPrefixMachineCap parameters transitionIndex +
        exactGammaRestoredPrefixForkCap transitionIndex ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  rw [exact_compiler_target_caps_length]
  apply Nat.le_sub_of_add_le
  have requestsWithPadding : transitionIndex + 1 + 12 ≤
      parameters.forkRequestCap := by
    unfold tag73CanonicalDriverFuelCap at indexWithinCanonical
    omega
  have requestCountLe : transitionIndex + 1 ≤
      parameters.forkRequestCap := by
    omega
  have machineLe := Nat.mul_le_mul_right
    (parameters.q1ShaCallCap + deployedFull256VerifierCallCap) requestCountLe
  have forkLe : 2 * (transitionIndex + 1) + 24 ≤
      2 * parameters.forkRequestCap := by
    omega
  unfold exactGammaRestoredPrefixMachineCap exactGammaRestoredPrefixForkCap
    unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
  omega

/-- A sharper proof obligation for the operational trace needs no local
machine estimate.  Even if every machine-fresh coordinate allowed by the
complete compiler has already appeared, the 69-request gap between the
canonical driver and the 1513-request sweep leaves far more than twelve
unused fork pairs, hence at least 24 suffix coordinates. -/
theorem full_machine_cap_plus_gamma_prefix_forks_has_capacity
    (parameters : ExactCompilerResourceParameters)
    (transitionIndex : Nat)
    (indexWithinCanonical : transitionIndex < tag73CanonicalDriverFuelCap)
    (sweepReserved : 1513 ≤ parameters.forkRequestCap) :
    full256MachineFreshCap parameters +
        exactGammaRestoredPrefixForkCap transitionIndex ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  rw [exact_compiler_target_caps_length]
  apply Nat.le_sub_of_add_le
  unfold exactGammaRestoredPrefixForkCap unifiedFull256ExposureCap
    sameTapeStartCap
  unfold tag73CanonicalDriverFuelCap at indexWithinCanonical
  omega

/-- Operational specialization for the canonical request selected from an
accepted source root. -/
theorem exact_operational_root_gamma_prefix_numeric_capacity
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (sweepReserved : 1513 ≤ parameters.forkRequestCap) :
    exactGammaRestoredPrefixMachineCap parameters
          (exactOperationalRootGammaRestorationRequest input).verifierTransitionIndex +
        exactGammaRestoredPrefixForkCap
          (exactOperationalRootGammaRestorationRequest input).verifierTransitionIndex ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  exact exact_gamma_restored_prefix_numeric_capacity parameters
    (exactOperationalRootGammaRestorationRequest input).verifierTransitionIndex
    (exact_operational_root_gamma_restoration_request_within_canonical_cap input)
    sweepReserved

#print axioms exact_gamma_restored_prefix_numeric_capacity
#print axioms full_machine_cap_plus_gamma_prefix_forks_has_capacity
#print axioms exact_operational_root_gamma_prefix_numeric_capacity
#print axioms scheduler_native_prefix_records_padding_free_of_reached_active
#print axioms run_trace_prefix_padding_free_of_reached_active
#print axioms run_trace_prefix_length_eq_machine_plus_fork_of_reached_active
#print axioms run_trace_prefix_reaches_active_of_selected_fork_output
#print axioms scheduler_native_prefix_records_padding_free_of_reached_fork
#print axioms run_trace_prefix_padding_free_of_reached_fork
#print axioms run_trace_prefix_length_eq_machine_plus_fork_of_reached_fork

end
end AspisK1.V7Tag73GammaRestoredK14PrefixCapacity
