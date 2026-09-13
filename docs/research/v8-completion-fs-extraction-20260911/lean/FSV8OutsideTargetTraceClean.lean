import FSV8ExactRootCursor
import AspisFormal.K1.V7Tag73ExactProbabilityCoverageAudit

/-!
# V8 exact-root chronological cleanliness outside its literal target event

This is the V8 specialization of the exact compiler's operational target
certificate.  It concerns the actual erased trace of `runExactRoot`, rather
than a separately supplied trace.  It is deterministic: probability enters
only when `FSV8ExactRootCursor.targetEvent` is measured.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8OutsideTargetTraceClean

open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerTargetClean
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open FSV8ExactRootCursor

noncomputable section

/-- The exact compiler's operational reindexing preserves the literal V8
root trace.  This is the generic plain-ROM calculation specialized to the
same `rootCursor`; it does not use success or acceptance. -/
theorem exact_compiler_trace_is_actual_v8_root_trace
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters) :
    exactCompilerUnifiedExposureTrace parameters transitionFuel
        (rootCursor configuration sample.1) sample.2 =
      (runExactRoot parameters configuration transitionFuel sample).trace := by
  calc
    exactCompilerUnifiedExposureTrace parameters transitionFuel
        (rootCursor configuration sample.1) sample.2 =
      runUnifiedExposureTrace transitionFuel
        (unifiedFull256ExposureCap parameters)
        (rootCursor configuration sample.1).erase
        (operationalTapeCoordinates
          (globalFull256OracleCallCap parameters) 1
          (unifiedFull256ExposureCap parameters)
          (exactCompilerOperationalIndexedTape parameters sample.2)) := rfl
    _ = runUnifiedExposureTrace transitionFuel
        (operationalCapsFrom 1 (unifiedFull256ExposureCap parameters)
          (globalFull256OracleCallCap parameters)).length
        (rootCursor configuration sample.1).erase
        (exactCompilerOperationalIndexedTape parameters sample.2) := by
      have indexed :=
        (run_unified_exposure_trace_operational_indexed_tape
          transitionFuel 1 (unifiedFull256ExposureCap parameters)
          (rootCursor configuration sample.1).erase
          (operationalTapeCoordinates
            (globalFull256OracleCallCap parameters) 1
            (unifiedFull256ExposureCap parameters)
            (exactCompilerOperationalIndexedTape parameters sample.2))).symm
      simpa only [operational_indexed_tape_coordinates_roundtrip] using indexed
    _ = runUnifiedExposureTrace transitionFuel
        (exactCompilerTargetCaps parameters).length
        (rootCursor configuration sample.1).erase sample.2 := by
      rfl
    _ = (runExactRoot parameters configuration transitionFuel sample).trace := by
      exact (run_exact_root_trace_is_erased_exposure_trace parameters
        configuration transitionFuel sample).symm

/-- Outside the exact V8 root's own target event, every non-padding exposure
in the actual scheduler trace is chronologically clean.  In particular, a
fresh machine answer cannot equal an earlier sampled answer or occur as a
literal state prefix in its own request input.

This theorem does not classify cached calls and does not by itself identify
the alpha marker's exact coordinate in this trace. -/
theorem outside_target_actual_root_trace_chronologically_clean
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat)
    (sample : ExactCompilerSample HiddenTape parameters)
    (outside : sample ∉ targetEvent parameters configuration transitionFuel) :
    EveryNonpaddingExposureChronologicallyClean {zeroDigest256}
      (runExactRoot parameters configuration transitionFuel sample).trace := by
  rw [← exact_compiler_trace_is_actual_v8_root_trace]
  have targetClean : ExactCompilerTargetClean parameters transitionFuel
      (rootCursor configuration sample.1) sample.2 := by
    unfold ExactCompilerTargetClean
    simpa [targetEvent, exactCompilerTargetEvent,
      hiddenDependentCausalHitEvent, exposureCursor] using outside
  have compilerClean :=
    exact_compiler_target_clean_implies_every_nonpadding_exposure_clean
      parameters transitionFuel (rootCursor configuration sample.1) sample.2
      targetClean
  exact compilerClean

#print axioms exact_compiler_trace_is_actual_v8_root_trace
#print axioms outside_target_actual_root_trace_chronologically_clean

end
end AspisV8Completion.FSV8OutsideTargetTraceClean
