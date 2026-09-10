import AspisFormal.K1.V7Tag73ExactRestoredGammaActualTrace
import AspisFormal.K1.V7Tag73ExactRestoredGammaFullRouting

/-!
# Earliest production activation of the restored-gamma router

The root sweep exhibits a typed verifier-origin gamma fork.  The probability
router must nevertheless start at the first exposure of the same immutable
oracle coordinate, which may be an adversary prequery.  This leaf connects
those two views and routes the earliest exposure as gamma block-zero output.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredGammaActivation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredGammaActualTrace
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A completed production root sweep activates the restored-gamma router at
the earliest exposure equivalent to its typed gamma fork.  The selected
coordinate is therefore pre-answer and adversary-prequery safe. -/
theorem exact_root_sweep_routes_first_restored_gamma_output
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (rounds : Nat)
    (roundsPositive : 0 < rounds)
    (extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base rounds extractor
          withinForkCap))
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      projection fixedInstance sample)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredGammaFullLabels transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample)).length = 24) :
    ∃ (firstPrior firstLater : List UnifiedExposureRecord)
        (firstRecord : UnifiedExposureRecord),
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample).trace =
          firstPrior ++ firstRecord :: firstLater ∧
        WaitingControllerPrefixUnmarked transitionFuel
          (typedRestoredChallengeExposureStartsHere
            (Result := ExactPlainRomWitnessExtractor Statement
              Tag73K12ParsedProof Payload Witness)
            transitionFuel (.challenge .gamma)
            (base.machine.blackBox.start sample.1 base.machine.observation)
            base.machine.environment base.restorationConfiguration)
          (exactRestoredGammaInitialState transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap) sample.1)
          firstPrior ∧
        causalRoutedAnswer? (⟨0, by decide⟩, false)
          (exactRestoredGammaRouter transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap) sample.1)
          (exactGammaPrefixRouterInputTape parameters sample.2) =
            some firstRecord.answer := by
  let configuration :=
    exactRootSweepWitnessConfiguration base rounds extractor withinForkCap
  let startsHere : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters) → Bool :=
    typedRestoredChallengeExposureStartsHere
      (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
        Payload Witness)
      transitionFuel (.challenge .gamma)
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration
  let controller := exactRestoredGammaController transitionFuel configuration
    sample.1
  let initial := exactRestoredGammaInitialState transitionFuel configuration
    sample.1
  obtain ⟨prior, later, selected, targetCursor, answer, _request, traceExact,
      targetMarked, _exactRequest, _requestTyped, _requestCanonical,
      selectedExact⟩ :=
    exact_root_sweep_full_trace_contains_typed_gamma_fork base rounds
      roundsPositive extractor withinForkCap adequate projection fixedInstance
      sample input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have erasedTrace :
      runUnifiedExposureTrace transitionFuel
          (exactCompilerTargetCaps parameters).length initial.cursor sample.2 =
        prior ++ selected :: later := by
    have exact := exact_plain_rom_trace_is_erased_exposure_trace transitionFuel
      configuration sample
    simpa only [configuration, initial, exactRestoredGammaInitialState,
      exactPlainRomExposureCursor] using exact.symm.trans traceExact
  have selectedAligned :
      unifiedRecordAtAnswer transitionFuel reached.cursor selected.answer =
        selected :=
    trace_prefix_aligns_indexed_state transitionFuel controller prior later
      selected (exactCompilerTargetCaps parameters).length initial sample.2
      erasedTrace
  have answerExact : selected.answer = answer := by
    rw [selectedExact]
    exact scheduler_native_request_record_answer
      (seekSchedulerNativeExposure transitionFuel targetCursor) answer
  have selectedAlignedAtAnswer :
      unifiedRecordAtAnswer transitionFuel reached.cursor answer = selected := by
    simpa only [answerExact] using selectedAligned
  have targetRecord :
      schedulerNativeRequestRecord
          (seekSchedulerNativeExposure transitionFuel targetCursor) answer =
        unifiedRecordAtAnswer transitionFuel targetCursor.erase answer :=
    scheduler_native_record_eq_unified_record_at_answer transitionFuel
      targetCursor answer
  have recordExact :
      unifiedRecordAtAnswer transitionFuel reached.cursor answer =
        unifiedRecordAtAnswer transitionFuel targetCursor.erase answer :=
    selectedAlignedAtAnswer.trans (selectedExact.trans targetRecord)
  have positive : 0 < transitionFuel := by
    have reserve := adequate.schedulerTransitionFuel
    unfold exactCompilerSufficientTransitionFuel at reserve
    omega
  have eventuallyMarked : startsHere reached.cursor = true := by
    exact typed_challenge_exposure_marked_of_record_eq positive
      (.challenge .gamma)
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration reached.cursor
      targetCursor.erase answer (by
        simpa only [typedRestoredGammaForkStartsHere] using targetMarked)
      recordExact
  have routed :=
    exact_restored_gamma_router_routes_first_marked_full_answer transitionFuel
      configuration sample prior later selected traceExact (by
        simpa only [reached, controller, initial, startsHere, configuration,
          exactRootSweepWitnessConfiguration] using eventuallyMarked)
      namedComplete
  simpa only [configuration, startsHere, initial,
    exactRootSweepWitnessConfiguration] using routed

#print axioms exact_root_sweep_routes_first_restored_gamma_output

end
end AspisK1.V7Tag73ExactRestoredGammaActivation
