import AspisFormal.K1.V7Tag73CausalResidualCoordinatePrefix
import AspisFormal.K1.V7Tag73ExactRestoredGammaActualTrace
import AspisFormal.K1.V7Tag73ExactRestoredGammaFullRouting

/-!
# Residual-coordinate control before restored-gamma activation

The restoration-native gamma router starts at the earliest exposure equivalent
to the typed gamma fork.  That exposure may be an adversary prequery.  Before
it, the waiting controller assigns no gamma coordinate, so every chronological
answer belongs to the residual coordinate.  Equality of that residual therefore
forces the complete literal pre-activation answer prefix on a second tape.

This is the causal cut needed by the K1.4 initial-lane source bridge.  It makes
no claim about any answer at or after gamma activation.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredGammaPreActivationPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
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
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73RestoredQueryBatchForkController
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- An unmarked prefix replayed from the waiting phase contains no named gamma
slot.  This is stronger than merely preserving the phase: it identifies every
answer in the prefix as a residual-coordinate answer. -/
theorem waiting_prefix_unmarked_has_no_named_slots
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool) :
    ∀ (state : IndexedUnifiedExposureState globalOracleCalls
        WaitingRestoredQueryBatchMemory)
      (records : List UnifiedExposureRecord),
      state.memory = .waiting →
      WaitingControllerPrefixUnmarked transitionFuel startsHere state records →
      namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel
            (waitingRestoredQueryBatchForkController transitionFuel startsHere)
            state records) = [] := by
  intro state records
  induction records generalizing state with
  | nil =>
      intro _waiting _unmarked
      rfl
  | cons record records ih =>
      intro waiting unmarked
      obtain ⟨markedFalse, tailUnmarked⟩ := unmarked
      let controller :=
        waitingRestoredQueryBatchForkController transitionFuel startsHere
      let next := controller.afterAnswer transitionFuel state record.answer
      have preferred : controller.preferredSlot state = none := by
        rcases state with ⟨exposureIndex, cursor, memory⟩
        simp only at waiting markedFalse ⊢
        subst memory
        simp [controller, waitingRestoredQueryBatchForkController,
          markedFalse]
      have nextWaiting : next.memory = .waiting := by
        rcases state with ⟨exposureIndex, cursor, memory⟩
        simp only at waiting markedFalse ⊢
        subst memory
        simp [next, controller, waitingRestoredQueryBatchForkController,
          IndexedUnifiedExposureController.afterAnswer, markedFalse]
      rw [indexed_controller_labeled_records_cons, preferred]
      simpa [namedTraceSlots, controller, next] using
        ih next nextWaiting tailUnmarked

/-- On one literal accepted execution, equality of the restored-gamma residual
coordinate forces the same complete chronological answer prefix before the
earliest gamma activation on a second tape. -/
theorem restored_gamma_residual_forces_pre_activation_answer_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (decomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        prior ++ record :: later)
    (unmarked : WaitingControllerPrefixUnmarked transitionFuel
      (typedRestoredChallengeExposureStartsHere transitionFuel
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
          Payload Witness) (.challenge .gamma)
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment
        configuration.restorationConfiguration)
      (exactRestoredGammaInitialState transitionFuel configuration sample.1)
      prior)
    (residualEnough :
      residualTraceSteps
          (indexedControllerLabeledRecords transitionFuel
            (exactRestoredGammaController transitionFuel configuration sample.1)
            (exactRestoredGammaInitialState transitionFuel configuration sample.1)
            prior) ≤
        (exactCompilerTargetCaps parameters).length - 24)
    (residualExact :
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration
          sample.1 sample.2).1 =
        (exactCompilerRestoredGammaCoordinates transitionFuel configuration
          sample.1 right).1) :
    ∃ rightRemaining,
      freshAnswerTapeToList right =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let controller := exactRestoredGammaController transitionFuel configuration
    sample.1
  let initial := exactRestoredGammaInitialState transitionFuel configuration
    sample.1
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  have prefixTrace : MachineLabeledTrace
      (controller.machine transitionFuel) initial prefixLabels
      (indexedStateAfterRecords transitionFuel controller prior initial) :=
    indexed_controller_labeled_records_form_trace transitionFuel controller
      initial prior
  have allResidual : namedTraceSlots prefixLabels = [] := by
    exact waiting_prefix_unmarked_has_no_named_slots transitionFuel
      (typedRestoredChallengeExposureStartsHere transitionFuel
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
          Payload Witness) (.challenge .gamma)
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment
        configuration.restorationConfiguration)
      initial prior rfl (by simpa only [initial] using unmarked)
  have leftPrefix : freshAnswerTapeToList
      (exactGammaPrefixRouterInputTape parameters sample.2) =
        prefixLabels.map Prod.snd ++
          ((record :: later).map UnifiedExposureRecord.answer) := by
    calc
      freshAnswerTapeToList
          (exactGammaPrefixRouterInputTape parameters sample.2) =
          freshAnswerTapeToList sample.2 :=
        exact_gamma_prefix_router_input_tape_preserves_list parameters sample.2
      _ = (runExactPlainRom transitionFuel configuration sample).trace.map
          UnifiedExposureRecord.answer :=
        (exact_plain_rom_trace_answers_are_master_tape transitionFuel
          configuration sample).symm
      _ = (prior ++ record :: later).map UnifiedExposureRecord.answer := by
        rw [decomposition]
      _ = prior.map UnifiedExposureRecord.answer ++
          (record :: later).map UnifiedExposureRecord.answer := by
        rw [List.map_append]
      _ = prefixLabels.map Prod.snd ++
          (record :: later).map UnifiedExposureRecord.answer := by
        rw [indexed_controller_labeled_records_answers]
  have leftTraceExact : freshAnswerTapeToList
      (exactGammaPrefixRouterInputTape parameters sample.2) =
        prefixLabels.map Prod.snd ++
          (freshAnswerTapeToList
            (exactGammaPrefixRouterInputTape parameters sample.2)).drop
              prefixLabels.length := by
    rw [leftPrefix]
    have prefixLength : (prefixLabels.map Prod.snd).length =
        prefixLabels.length := by simp
    rw [← prefixLength, List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  have routerResidualExact :
      (((controller.machine transitionFuel).fullRouter
        ((exactCompilerTargetCaps parameters).length - 24) initial).coordinateEquiv
          (exactGammaPrefixRouterInputTape parameters sample.2)).2 =
      (((controller.machine transitionFuel).fullRouter
        ((exactCompilerTargetCaps parameters).length - 24) initial).coordinateEquiv
          (exactGammaPrefixRouterInputTape parameters right)).2 := by
    change
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration
          sample.1 sample.2).1 =
        (exactCompilerRestoredGammaCoordinates transitionFuel configuration
          sample.1 right).1 at residualExact
    exact residualExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    all_residual_trace_forces_right_prefix prefixTrace allResidual
      (by simpa only [prefixLabels] using residualEnough)
      (exactGammaPrefixRouterInputTape parameters sample.2)
      (exactGammaPrefixRouterInputTape parameters right) leftTraceExact
      routerResidualExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer :=
    indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  rw [prefixAnswers,
    exact_gamma_prefix_router_input_tape_preserves_list] at rightPrefix
  exact ⟨rightRemaining, rightPrefix⟩

/-- Lightweight activation lemma for this causal cut.  Unlike the aggregate
activation module, this imports only the literal root-sweep occurrence and the
already-established full router. -/
theorem root_sweep_routes_first_restored_gamma_output_for_prefix
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

/-- Root-sweep specialization: for two tapes in one restored-gamma residual
fibre, the complete answer history before the earliest gamma exposure is
identical.  The activation point is obtained from the real typed root sweep;
it is not selected by inspecting a raw SHA input after the fact. -/
theorem root_sweep_gamma_fibre_has_common_pre_activation_prefix
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
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (input : ExactK12OperationalInput transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      projection fixedInstance (hidden, left))
    (namedComplete :
      (namedTraceSlots
        (exactRestoredGammaFullLabels transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) (hidden, left))).length = 24)
    (residualExact :
      (exactCompilerRestoredGammaCoordinates transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) hidden left).1 =
        (exactCompilerRestoredGammaCoordinates transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) hidden right).1) :
    ∃ (firstPrior firstLater : List UnifiedExposureRecord)
        (firstRecord : UnifiedExposureRecord) (rightRemaining : List Digest256),
      (runExactPlainRom transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) (hidden, left)).trace =
          firstPrior ++ firstRecord :: firstLater ∧
      WaitingControllerPrefixUnmarked transitionFuel
        (typedRestoredChallengeExposureStartsHere transitionFuel
          (globalOracleCalls := globalFull256OracleCallCap parameters)
          (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness) (.challenge .gamma)
          (base.machine.blackBox.start hidden base.machine.observation)
          base.machine.environment base.restorationConfiguration)
        (exactRestoredGammaInitialState transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) hidden)
        firstPrior ∧
      freshAnswerTapeToList right =
        firstPrior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let configuration :=
    exactRootSweepWitnessConfiguration base rounds extractor withinForkCap
  obtain ⟨firstPrior, firstLater, firstRecord, decomposition, unmarked,
      _routed⟩ :=
    root_sweep_routes_first_restored_gamma_output_for_prefix base rounds
      roundsPositive extractor withinForkCap adequate projection fixedInstance
      (hidden, left) input namedComplete
  let controller := exactRestoredGammaController transitionFuel configuration
    hidden
  let initial := exactRestoredGammaInitialState transitionFuel configuration
    hidden
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial firstPrior
  let selectedLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller firstPrior initial)
    [firstRecord]
  have throughSelectedEnough :=
    exact_restored_gamma_prefix_residual_enough_of_named_complete
      transitionFuel configuration (hidden, left) firstPrior firstLater
      firstRecord decomposition namedComplete
  have labelsAppend : indexedControllerLabeledRecords transitionFuel controller
      initial (firstPrior ++ [firstRecord]) =
        priorLabels ++ selectedLabels := by
    exact indexed_controller_labeled_records_append transitionFuel controller
      initial firstPrior [firstRecord]
  have priorEnough : residualTraceSteps priorLabels ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
    rw [labelsAppend, residual_trace_steps_append] at throughSelectedEnough
    exact (Nat.le_add_right _ _).trans throughSelectedEnough
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    restored_gamma_residual_forces_pre_activation_answer_prefix transitionFuel
      configuration (hidden, left) right firstPrior firstLater firstRecord
      decomposition (by
        simpa only [configuration, exactRootSweepWitnessConfiguration] using
          unmarked)
      (by simpa only [controller, initial, priorLabels] using priorEnough)
      (by simpa only [configuration] using residualExact)
  refine ⟨firstPrior, firstLater, firstRecord, rightRemaining, decomposition,
    ?_, rightPrefix⟩
  simpa only [configuration, exactRootSweepWitnessConfiguration] using unmarked

#print axioms waiting_prefix_unmarked_has_no_named_slots
#print axioms restored_gamma_residual_forces_pre_activation_answer_prefix
#print axioms root_sweep_routes_first_restored_gamma_output_for_prefix
#print axioms root_sweep_gamma_fibre_has_common_pre_activation_prefix

end
end AspisK1.V7Tag73ExactRestoredGammaPreActivationPrefix
