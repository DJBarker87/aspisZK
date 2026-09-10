import AspisFormal.K1.V7Tag73ExactRestoredGammaFullRouting
import AspisFormal.K1.V7Tag73ExactRestoredQueryBatchActualTrace
import AspisFormal.K1.V7Tag73ExactRestoredQueryBatchFullRouting

/-!
# Earliest production activation of the restored query-batch router

The root sweep exhibits a typed verifier-origin query-batch fork.  The
probability router must use the first exposure of that same prepared fork,
which is selected before either programmed answer is read.  This leaf joins
the production occurrence theorem to the waiting causal router and exposes
the block-zero output as the public restoration-native coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredQueryBatchActivation

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
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactRestoredQueryBatchActualTrace
open AspisK1.V7Tag73ExactRestoredQueryBatchFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73RestoredJointBatchActualLawClosure
open AspisK1.V7Tag73RestoredQueryBatchCausalMarker
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A completed production root sweep activates the query-batch waiting
router at the first exposure equivalent to its typed block-zero fork. -/
theorem exact_root_sweep_routes_first_restored_query_batch_output
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
        (exactRestoredQueryBatchFullLabels transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample)).length = 24) :
    ∃ (firstPrior firstLater : List UnifiedExposureRecord)
        (firstRecord : UnifiedExposureRecord),
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample).trace =
          firstPrior ++ firstRecord :: firstLater ∧
        WaitingControllerPrefixUnmarked transitionFuel
          (typedRestoredQueryBatchExposureStartsHere
            (Result := ExactPlainRomWitnessExtractor Statement
              Tag73K12ParsedProof Payload Witness)
            transitionFuel
            (base.machine.blackBox.start sample.1 base.machine.observation)
            base.machine.environment base.restorationConfiguration)
          (exactRestoredQueryBatchInitialState transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap) sample.1)
          firstPrior ∧
        causalRoutedAnswer? (⟨0, by decide⟩, false)
          (exactRestoredQueryBatchRouter transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap) sample.1)
          (V7Tag73ExactRestoredQueryBatchFullRouting.exactGammaPrefixRouterInputTape
            parameters sample.2) =
            some firstRecord.answer := by
  let configuration :=
    exactRootSweepWitnessConfiguration base rounds extractor withinForkCap
  let startsHere : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters) → Bool :=
    typedRestoredQueryBatchExposureStartsHere
      (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
        Payload Witness)
      transitionFuel
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration
  let controller := exactRestoredQueryBatchController transitionFuel
    configuration sample.1
  let initial := exactRestoredQueryBatchInitialState transitionFuel
    configuration sample.1
  obtain ⟨prior, later, selected, targetCursor, answer, traceExact,
      targetMarked, selectedExact⟩ :=
    exact_root_sweep_full_trace_contains_typed_query_batch_fork base rounds
      roundsPositive extractor withinForkCap adequate projection fixedInstance
      sample input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have erasedTrace :
      runUnifiedExposureTrace transitionFuel
          (exactCompilerTargetCaps parameters).length initial.cursor sample.2 =
        prior ++ selected :: later := by
    have exact := exact_plain_rom_trace_is_erased_exposure_trace transitionFuel
      configuration sample
    simpa only [configuration, initial,
      exactRestoredQueryBatchInitialState, exactPlainRomExposureCursor] using
      exact.symm.trans traceExact
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
    exact typed_query_batch_exposure_marked_of_record_eq positive
      (base.machine.blackBox.start sample.1 base.machine.observation)
      base.machine.environment base.restorationConfiguration reached.cursor
      targetCursor.erase answer targetMarked recordExact
  obtain ⟨firstPrior, firstRecord, firstLater, firstSplit, firstUnmarked,
      firstMarked⟩ :=
    waiting_controller_eventually_marked_has_first_marked_record transitionFuel
      startsHere initial prior selected later eventuallyMarked
  have firstDecomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        firstPrior ++ firstRecord :: firstLater :=
    traceExact.trans firstSplit
  have firstPreferred :=
    waiting_controller_prefix_unmarked_then_marked_routes_first_output
      transitionFuel startsHere initial firstPrior rfl firstUnmarked firstMarked
  have routed :=
    exact_restored_query_batch_router_routes_selected_full_answer_of_named_complete
      transitionFuel configuration sample firstPrior firstLater firstRecord
      (⟨0, by decide⟩, false) firstDecomposition (by
        simpa only [controller, initial, startsHere, configuration,
          exactRestoredQueryBatchController,
          exactRootSweepWitnessConfiguration] using firstPreferred) namedComplete
  refine ⟨firstPrior, firstLater, firstRecord, ?_, ?_, ?_⟩
  · simpa only [configuration] using firstDecomposition
  · simpa only [startsHere, initial, configuration,
      exactRootSweepWitnessConfiguration] using firstUnmarked
  · simpa only [configuration] using routed

/-- Public-coordinate form: the earliest typed query-batch answer is exactly
block zero of the output half of the restoration-native gamma-prefix tape. -/
theorem exact_root_sweep_first_restored_query_batch_coordinate_exact
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
        (exactRestoredQueryBatchFullLabels transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample)).length = 24) :
    ∃ (firstPrior firstLater : List UnifiedExposureRecord)
        (firstRecord : UnifiedExposureRecord),
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample).trace =
          firstPrior ++ firstRecord :: firstLater ∧
        WaitingControllerPrefixUnmarked transitionFuel
          (typedRestoredQueryBatchExposureStartsHere
            (Result := ExactPlainRomWitnessExtractor Statement
              Tag73K12ParsedProof Payload Witness)
            transitionFuel
            (base.machine.blackBox.start sample.1 base.machine.observation)
            base.machine.environment base.restorationConfiguration)
          (exactRestoredQueryBatchInitialState transitionFuel
            (exactRootSweepWitnessConfiguration base rounds extractor
              withinForkCap) sample.1)
          firstPrior ∧
        (exactCompilerRestoredQueryBatchCoordinates transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) sample.1 sample.2).2.1 ⟨0, by decide⟩ =
          firstRecord.answer := by
  obtain ⟨firstPrior, firstLater, firstRecord, traceExact, prefixUnmarked,
      routed⟩ :=
    exact_root_sweep_routes_first_restored_query_batch_output base rounds
      roundsPositive extractor withinForkCap adequate projection fixedInstance
      sample input namedComplete
  refine ⟨firstPrior, firstLater, firstRecord, traceExact, prefixUnmarked, ?_⟩
  exact exact_restored_query_batch_output_coordinate_eq_of_routed_lookup
    transitionFuel
    (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
    sample.1 sample.2 ⟨0, by decide⟩ firstRecord.answer routed

#print axioms exact_root_sweep_routes_first_restored_query_batch_output
#print axioms exact_root_sweep_first_restored_query_batch_coordinate_exact

end
end AspisK1.V7Tag73ExactRestoredQueryBatchActivation
