import AspisFormal.K1.V7Tag73CausalSlotRouterLookup
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73RestoredJointBatchActualLawClosure
import AspisFormal.K1.V7Tag73RestoredQueryBatchLabelsNodup

/-!
# Exact full-run routing for the restored query-batch sampler

The restoration-native probability coordinates are compiled from a waiting
pre-answer controller on the complete `runExactPlainRom` cursor.  This file
connects that controller to the literal complete exposure trace and master
tape.  It remains deterministic: no random-oracle freshness, independence,
or probability premise is used.

The source-specific layer still has to identify the root-sweep record at
which the typed query-batch fork is dispatched.  Once it supplies the exact
trace decomposition and pre-answer label, the theorems below recover that
record's answer as the corresponding output/advance probability coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredQueryBatchFullRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73RestoredJointBatchActualLawClosure
open AspisK1.V7Tag73RestoredQueryBatchCausalMarker
open AspisK1.V7Tag73RestoredQueryBatchForkController
open AspisK1.V7Tag73RestoredQueryBatchLabelsNodup
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactRestoredQueryBatchController
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  waitingRestoredQueryBatchForkController transitionFuel
    (typedRestoredQueryBatchExposureStartsHere transitionFuel
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (Result := Result)
      (configuration.machine.blackBox.start hidden
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration)

def exactRestoredQueryBatchInitialState
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      WaitingRestoredQueryBatchMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration hidden).erase
    memory := .waiting }

def exactRestoredQueryBatchFullLabels
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    List (Option GammaPrefixDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (exactRestoredQueryBatchController transitionFuel configuration sample.1)
    (exactRestoredQueryBatchInitialState transitionFuel configuration sample.1)
    (runExactPlainRom transitionFuel configuration sample).trace

def exactRestoredQueryBatchRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) : ExactCompilerCausalGammaPrefixRouter parameters :=
  exactCompilerIndexedGammaPrefixRouter parameters transitionFuel
    (exactRestoredQueryBatchController transitionFuel configuration hidden)
    WaitingRestoredQueryBatchMemory.waiting
    (exactPlainRomCursor configuration hidden).erase

/-! ## The exact casted tape seen by the generic router -/

def exactGammaPrefixRouterInputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset GammaPrefixDigestSlot).card +
        ((exactCompilerTargetCaps parameters).length - 24)) := by
  let total := (exactCompilerTargetCaps parameters).length
  have enough : 24 ≤ total :=
    exact_compiler_tape_has_gamma_prefix_capacity parameters
  have totalEq : total = 24 + (total - 24) := by omega
  have slotCard : Fintype.card GammaPrefixDigestSlot = 24 :=
    gamma_prefix_digest_slot_card
  have univCard : (Finset.univ : Finset GammaPrefixDigestSlot).card = 24 := by
    simpa using slotCard
  exact castFreshAnswerTape
    (congrArg (fun count => count + (total - 24)) univCard).symm
    (castFreshAnswerTape totalEq tape)

theorem exact_gamma_prefix_router_input_tape_preserves_list
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    freshAnswerTapeToList (exactGammaPrefixRouterInputTape parameters tape) =
      freshAnswerTapeToList tape := by
  unfold exactGammaPrefixRouterInputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]

/-! ## Complete trace labels and resource accounting -/

theorem exact_restored_query_batch_full_labels_form_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    MachineLabeledTrace
      ((exactRestoredQueryBatchController transitionFuel configuration
        sample.1).machine transitionFuel)
      (exactRestoredQueryBatchInitialState transitionFuel configuration sample.1)
      (exactRestoredQueryBatchFullLabels transitionFuel configuration sample)
      (indexedStateAfterRecords transitionFuel
        (exactRestoredQueryBatchController transitionFuel configuration sample.1)
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestoredQueryBatchInitialState transitionFuel configuration
          sample.1)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (exactRestoredQueryBatchController transitionFuel configuration sample.1)
    (exactRestoredQueryBatchInitialState transitionFuel configuration sample.1)
    (runExactPlainRom transitionFuel configuration sample).trace

theorem exact_restored_query_batch_full_named_slots_nodup
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (namedTraceSlots
      (exactRestoredQueryBatchFullLabels transitionFuel configuration sample)).Nodup := by
  change
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (waitingRestoredQueryBatchForkController transitionFuel
          (typedRestoredQueryBatchExposureStartsHere transitionFuel
            (globalOracleCalls := globalFull256OracleCallCap parameters)
            (Result := Result)
            (configuration.machine.blackBox.start sample.1
              configuration.machine.observation)
            configuration.machine.environment
            configuration.restorationConfiguration))
        { exposureIndex := 0
          cursor := (exactPlainRomCursor configuration sample.1).erase
          memory := WaitingRestoredQueryBatchMemory.waiting }
        (runExactPlainRom transitionFuel configuration sample).trace)).Nodup
  exact waiting_restored_query_batch_labeled_records_named_slots_nodup
    transitionFuel
    (typedRestoredQueryBatchExposureStartsHere transitionFuel
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (Result := Result)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration)
    (runExactPlainRom transitionFuel configuration sample).trace
    (exactPlainRomCursor configuration sample.1).erase

theorem exact_restored_query_batch_full_labels_tape_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    freshAnswerTapeToList (exactGammaPrefixRouterInputTape parameters sample.2) =
      (exactRestoredQueryBatchFullLabels transitionFuel configuration
        sample).map Prod.snd ++ [] := by
  rw [exact_gamma_prefix_router_input_tape_preserves_list,
    show exactRestoredQueryBatchFullLabels transitionFuel configuration sample =
        indexedControllerLabeledRecords transitionFuel
          (exactRestoredQueryBatchController transitionFuel configuration
            sample.1)
          (exactRestoredQueryBatchInitialState transitionFuel configuration
            sample.1)
          (runExactPlainRom transitionFuel configuration sample).trace by rfl,
    indexed_controller_labeled_records_answers,
    exact_plain_rom_trace_answers_are_master_tape]
  simp

/-- The complete trace has exactly the residual capacity reserved by the
router once the deployed restored sampler has supplied all twenty-four named
duplex coordinates.  The completeness premise is intentionally explicit:
an early restoration failure may leave some named slots unused, in which case
the corresponding full-trace statement is false. -/
theorem exact_restored_query_batch_full_residual_exact_of_named_complete
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredQueryBatchFullLabels transitionFuel configuration
          sample)).length = 24) :
    residualTraceSteps
        (exactRestoredQueryBatchFullLabels transitionFuel configuration sample) =
      (exactCompilerTargetCaps parameters).length - 24 := by
  let labels := exactRestoredQueryBatchFullLabels transitionFuel configuration
    sample
  have enough : 24 ≤ (exactCompilerTargetCaps parameters).length :=
    exact_compiler_tape_has_gamma_prefix_capacity parameters
  have labelsLength : labels.length =
      (exactCompilerTargetCaps parameters).length := by
    have tapeExact := exact_restored_query_batch_full_labels_tape_exact
      transitionFuel configuration sample
    have lengths := congrArg List.length tapeExact
    have raw : 24 + ((exactCompilerTargetCaps parameters).length - 24) =
        labels.length := by
      simpa [labels] using lengths
    omega
  have split := labeled_trace_length_split labels
  change residualTraceSteps labels =
    (exactCompilerTargetCaps parameters).length - 24
  change (namedTraceSlots labels).length = 24 at namedComplete
  omega

/-- Every chronological prefix through a selected record fits the residual
component whenever the complete deployed run supplies all twenty-four named
query-batch coordinates.  This replaces a brittle manual prefix count by the
exact full-tape partition theorem. -/
theorem exact_restored_query_batch_prefix_residual_enough_of_named_complete
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (decomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        prior ++ record :: later)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredQueryBatchFullLabels transitionFuel configuration
          sample)).length = 24) :
    residualTraceSteps
        (indexedControllerLabeledRecords transitionFuel
          (exactRestoredQueryBatchController transitionFuel configuration
            sample.1)
          (exactRestoredQueryBatchInitialState transitionFuel configuration
            sample.1)
          (prior ++ [record])) ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  let controller := exactRestoredQueryBatchController transitionFuel
    configuration sample.1
  let initial := exactRestoredQueryBatchInitialState transitionFuel
    configuration sample.1
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial (prior ++ [record])
  let suffixLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller (prior ++ [record])
      initial) later
  have labelsExact :
      exactRestoredQueryBatchFullLabels transitionFuel configuration sample =
        prefixLabels ++ suffixLabels := by
    have traceSplit :
        (runExactPlainRom transitionFuel configuration sample).trace =
          (prior ++ [record]) ++ later := by
      simpa [List.append_assoc] using decomposition
    unfold exactRestoredQueryBatchFullLabels
    rw [traceSplit]
    rw [indexed_controller_labeled_records_append]
  have fullExact :=
    exact_restored_query_batch_full_residual_exact_of_named_complete
      transitionFuel configuration sample namedComplete
  rw [labelsExact, residual_trace_steps_append] at fullExact
  have prefixLe : residualTraceSteps prefixLabels ≤
      residualTraceSteps prefixLabels + residualTraceSteps suffixLabels := by
    omega
  simpa only [controller, initial, prefixLabels, suffixLabels] using
    prefixLe.trans_eq fullExact

/-! ## Routing a selected literal full-run record -/

theorem exact_restored_query_batch_router_routes_selected_full_answer
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (target : GammaPrefixDigestSlot)
    (decomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        prior ++ record :: later)
    (preferred :
      (exactRestoredQueryBatchController transitionFuel configuration
        sample.1).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactRestoredQueryBatchController transitionFuel configuration
            sample.1)
          prior
          (exactRestoredQueryBatchInitialState transitionFuel configuration
            sample.1)) = some target)
    (residualEnough :
      residualTraceSteps
          (indexedControllerLabeledRecords transitionFuel
            (exactRestoredQueryBatchController transitionFuel configuration
              sample.1)
            (exactRestoredQueryBatchInitialState transitionFuel configuration
              sample.1)
            (prior ++ [record])) ≤
        (exactCompilerTargetCaps parameters).length - 24) :
    causalRoutedAnswer? target
        (exactRestoredQueryBatchRouter transitionFuel configuration sample.1)
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      some record.answer := by
  let controller := exactRestoredQueryBatchController transitionFuel
    configuration sample.1
  let initial := exactRestoredQueryBatchInitialState transitionFuel
    configuration sample.1
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let prefixRecords := prior ++ [record]
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prefixRecords
  have prefixTrace : MachineLabeledTrace (controller.machine transitionFuel)
      initial prefixLabels
      (indexedStateAfterRecords transitionFuel controller prefixRecords
        initial) := by
    exact indexed_controller_labeled_records_form_trace transitionFuel
      controller initial prefixRecords
  have prefixNodup : (namedTraceSlots prefixLabels).Nodup := by
    change
      (namedTraceSlots
        (indexedControllerLabeledRecords transitionFuel
          (waitingRestoredQueryBatchForkController transitionFuel
            (typedRestoredQueryBatchExposureStartsHere transitionFuel
              (globalOracleCalls := globalFull256OracleCallCap parameters)
              (Result := Result)
              (configuration.machine.blackBox.start sample.1
                configuration.machine.observation)
              configuration.machine.environment
              configuration.restorationConfiguration))
          { exposureIndex := 0
            cursor := (exactPlainRomCursor configuration sample.1).erase
            memory := WaitingRestoredQueryBatchMemory.waiting }
          prefixRecords)).Nodup
    exact waiting_restored_query_batch_labeled_records_named_slots_nodup
      transitionFuel
      (typedRestoredQueryBatchExposureStartsHere transitionFuel
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (Result := Result)
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment
        configuration.restorationConfiguration)
      prefixRecords (exactPlainRomCursor configuration sample.1).erase
  have tapeExact : freshAnswerTapeToList
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      prefixLabels.map Prod.snd ++ later.map UnifiedExposureRecord.answer := by
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
      _ = prefixRecords.map UnifiedExposureRecord.answer ++
          later.map UnifiedExposureRecord.answer := by
        simp [prefixRecords, List.map_append]
      _ = prefixLabels.map Prod.snd ++
          later.map UnifiedExposureRecord.answer := by
        rw [indexed_controller_labeled_records_answers]
  have labelsDecomposition :
      prefixLabels = priorLabels ++ (some target, record.answer) :: [] := by
    simp only [prefixLabels, prefixRecords,
      indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords, controller, initial, reached,
      priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    prefixTrace prefixNodup
    (fun slot _member => Finset.mem_univ slot)
    (by simpa [prefixLabels, prefixRecords, controller, initial] using
      residualEnough)
    (exactGammaPrefixRouterInputTape parameters sample.2)
    (later.map UnifiedExposureRecord.answer) tapeExact
    priorLabels [] target record.answer labelsDecomposition

/-- Source-facing routing form: a selected pre-answer label and completion of
all twenty-four deployed duplex slots are sufficient.  The residual-capacity
side condition is derived, not exposed to the source adapter. -/
theorem exact_restored_query_batch_router_routes_selected_full_answer_of_named_complete
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (target : GammaPrefixDigestSlot)
    (decomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        prior ++ record :: later)
    (preferred :
      (exactRestoredQueryBatchController transitionFuel configuration
        sample.1).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactRestoredQueryBatchController transitionFuel configuration
            sample.1)
          prior
          (exactRestoredQueryBatchInitialState transitionFuel configuration
            sample.1)) = some target)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredQueryBatchFullLabels transitionFuel configuration
          sample)).length = 24) :
    causalRoutedAnswer? target
        (exactRestoredQueryBatchRouter transitionFuel configuration sample.1)
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      some record.answer := by
  apply exact_restored_query_batch_router_routes_selected_full_answer
    transitionFuel configuration sample prior later record target decomposition
      preferred
  exact exact_restored_query_batch_prefix_residual_enough_of_named_complete
    transitionFuel configuration sample prior later record decomposition
      namedComplete

/-! ## Named lookup to the public restoration-native coordinates -/

theorem exact_restored_query_batch_output_coordinate_eq_of_routed_lookup
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 12) (answer : Digest256)
    (routed : causalRoutedAnswer? (block, false)
        (exactRestoredQueryBatchRouter transitionFuel configuration hidden)
        (exactGammaPrefixRouterInputTape parameters tape) = some answer) :
    (exactCompilerRestoredQueryBatchCoordinates transitionFuel configuration
      hidden tape).2.1 block = answer := by
  change
    (CausalSlotRouter.coordinateEquiv
      (exactRestoredQueryBatchRouter transitionFuel configuration hidden)
      (exactGammaPrefixRouterInputTape parameters tape)).1
        ⟨(block, false), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (exactRestoredQueryBatchRouter transitionFuel configuration hidden)
    (exactGammaPrefixRouterInputTape parameters tape)
    (block, false) (Finset.mem_univ _) answer routed

theorem exact_restored_query_batch_advance_coordinate_eq_of_routed_lookup
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 12) (answer : Digest256)
    (routed : causalRoutedAnswer? (block, true)
        (exactRestoredQueryBatchRouter transitionFuel configuration hidden)
        (exactGammaPrefixRouterInputTape parameters tape) = some answer) :
    (exactCompilerRestoredQueryBatchCoordinates transitionFuel configuration
      hidden tape).2.2 block = answer := by
  change
    (CausalSlotRouter.coordinateEquiv
      (exactRestoredQueryBatchRouter transitionFuel configuration hidden)
      (exactGammaPrefixRouterInputTape parameters tape)).1
        ⟨(block, true), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (exactRestoredQueryBatchRouter transitionFuel configuration hidden)
    (exactGammaPrefixRouterInputTape parameters tape)
    (block, true) (Finset.mem_univ _) answer routed

#print axioms exactRestoredQueryBatchFullLabels
#print axioms exact_gamma_prefix_router_input_tape_preserves_list
#print axioms exact_restored_query_batch_full_labels_form_trace
#print axioms exact_restored_query_batch_full_named_slots_nodup
#print axioms exact_restored_query_batch_full_labels_tape_exact
#print axioms exact_restored_query_batch_full_residual_exact_of_named_complete
#print axioms exact_restored_query_batch_prefix_residual_enough_of_named_complete
#print axioms exact_restored_query_batch_router_routes_selected_full_answer
#print axioms exact_restored_query_batch_router_routes_selected_full_answer_of_named_complete
#print axioms exact_restored_query_batch_output_coordinate_eq_of_routed_lookup
#print axioms exact_restored_query_batch_advance_coordinate_eq_of_routed_lookup

end
end AspisK1.V7Tag73ExactRestoredQueryBatchFullRouting
