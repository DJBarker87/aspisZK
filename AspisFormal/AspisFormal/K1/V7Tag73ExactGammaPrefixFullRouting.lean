import AspisFormal.K1.V7Tag73CausalSlotRouterLookup
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73ExactFixedFullRunFactorization
import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73ExactPlainRomTraceResourceCaps
import AspisFormal.K1.V7Tag73FullCursorClientLineageLift
import AspisFormal.K1.V7Tag73GammaPrefixLabeledRecordsNodup

/-! # Exact full-run routing for the gamma-prefix controller -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactGammaPrefixFullRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73GammaPrefixLabeledRecordsNodup
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactGammaPrefixInitialState
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      GammaPrefixControllerMemory :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration hidden).erase
    memory := inactiveGammaPrefixMemory }

def exactGammaPrefixFullLabels
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    List (Option GammaPrefixDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (gammaPrefixCausalController transitionFuel)
    (exactGammaPrefixInitialState configuration sample.1)
    (runExactPlainRom transitionFuel configuration sample).trace

/-- The casted tape fed to the generic full router preserves the chronological
master-answer list. -/
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

theorem exact_gamma_prefix_full_labels_form_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    MachineLabeledTrace
      ((gammaPrefixCausalController transitionFuel).machine transitionFuel)
      (exactGammaPrefixInitialState configuration sample.1)
      (exactGammaPrefixFullLabels transitionFuel configuration sample)
      (indexedStateAfterRecords transitionFuel
        (gammaPrefixCausalController transitionFuel)
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactGammaPrefixInitialState configuration sample.1)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (gammaPrefixCausalController transitionFuel)
    (exactGammaPrefixInitialState configuration sample.1)
    (runExactPlainRom transitionFuel configuration sample).trace

theorem exact_gamma_prefix_full_named_slots_nodup
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (namedTraceSlots
      (exactGammaPrefixFullLabels transitionFuel configuration sample)).Nodup := by
  exact gamma_prefix_labeled_records_named_slots_nodup transitionFuel
    (runExactPlainRom transitionFuel configuration sample).trace
    (exactGammaPrefixInitialState configuration sample.1)

theorem exact_gamma_prefix_full_labels_tape_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    freshAnswerTapeToList (exactGammaPrefixRouterInputTape parameters sample.2) =
      (exactGammaPrefixFullLabels transitionFuel configuration sample).map
        Prod.snd ++ [] := by
  rw [exact_gamma_prefix_router_input_tape_preserves_list]
  unfold exactGammaPrefixFullLabels
  rw [indexed_controller_labeled_records_answers,
    exact_plain_rom_trace_answers_are_master_tape]
  simp

/-- Root-only labels for the literal first execution.  Keeping this separate
from `exactGammaPrefixFullLabels` matters: the later restoration-client trace
contains fork coordinates, whereas the root is entirely machine-fresh. -/
def exactGammaPrefixRootLabels
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    List (Option GammaPrefixDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (gammaPrefixCausalController transitionFuel)
    (exactGammaPrefixInitialState configuration sample.1)
    (exactFixedRootRecords input.package.root)

/-- The literal root prefix fits below the residual portion reserved for the
complete twelve-block gamma duplex tape.  This is pure `M + 2R` accounting:
the root itself contains only machine-fresh coordinates, while the reserved
twenty-four output/advance positions are paid from the programmed-pair
allowance. -/
theorem exact_gamma_prefix_root_residual_enough_of_programmed_cover
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (programmedCover : 24 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps (exactGammaPrefixRootLabels input) ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  let records := exactFixedRootRecords input.package.root
  let labels := exactGammaPrefixRootLabels input
  have labelsLength : labels.length = records.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (gammaPrefixCausalController transitionFuel)
        (exactGammaPrefixInitialState configuration sample.1) records)
    simpa [labels, exactGammaPrefixRootLabels] using answers
  have residualLe : residualTraceSteps labels ≤ labels.length := by
    have split := labeled_trace_length_split labels
    omega
  have projectedLength (actor : QueryActor) :
      ∀ queries : List (ShaInput × Digest256),
        (projectedMachineFreshRecords actor queries).length = queries.length := by
    intro queries
    induction queries with
    | nil => rfl
    | cons query queries ih =>
        rcases query with ⟨queryInput, queryAnswer⟩
        simp [projectedMachineFreshRecords, ih]
  have recordsCount : records.length = machineFreshCoordinateCount records := by
    unfold records exactFixedRootRecords fullProjectedRootRecords
    simp [projectedLength]
  have recordsMachineLe : records.length ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [recordsCount,
      exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
        configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [records]
  have recordsLengthLe : records.length ≤ full256MachineFreshCap parameters :=
    recordsMachineLe.trans input.package.root.traceCaps.1
  have capLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLe.trans
    (labelsLength.le.trans (recordsLengthLe.trans capLe))

/-- A literal selected record is routed to its pre-answer gamma label whenever
the prefix fits the router's reserved residual component. -/
theorem exact_gamma_prefix_router_routes_selected_full_answer
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
      (gammaPrefixCausalController transitionFuel).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (gammaPrefixCausalController transitionFuel) prior
          (exactGammaPrefixInitialState configuration sample.1)) = some target)
    (residualEnough :
      residualTraceSteps
          (indexedControllerLabeledRecords transitionFuel
            (gammaPrefixCausalController transitionFuel)
            (exactGammaPrefixInitialState configuration sample.1)
            (prior ++ [record])) ≤
        (exactCompilerTargetCaps parameters).length - 24) :
    causalRoutedAnswer? target
        (exactCompilerGammaPrefixRouter parameters transitionFuel
          (exactPlainRomCursor configuration sample.1).erase)
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      some record.answer := by
  let controller := gammaPrefixCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters) transitionFuel
  let initial := exactGammaPrefixInitialState configuration sample.1
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let prefixRecords := prior ++ [record]
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prefixRecords
  have prefixTrace : MachineLabeledTrace (controller.machine transitionFuel)
      initial prefixLabels
      (indexedStateAfterRecords transitionFuel controller prefixRecords
        initial) :=
    indexed_controller_labeled_records_form_trace transitionFuel controller
      initial prefixRecords
  have prefixNodup : (namedTraceSlots prefixLabels).Nodup := by
    exact gamma_prefix_labeled_records_named_slots_nodup transitionFuel
      prefixRecords initial
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
    simpa only [indexedControllerLabeledRecords, controller, initial,
      priorLabels, preferred]
  change causalRoutedAnswer? target
      ((controller.machine transitionFuel).router Finset.univ
        ((exactCompilerTargetCaps parameters).length - 24) initial)
      (exactGammaPrefixRouterInputTape parameters sample.2) =
    some record.answer
  exact machine_labeled_trace_routes_named_answer prefixTrace prefixNodup
    (fun slot _member => Finset.mem_univ slot)
    (by simpa [prefixLabels, prefixRecords, controller, initial] using
      residualEnough)
    (exactGammaPrefixRouterInputTape parameters sample.2)
    (later.map UnifiedExposureRecord.answer) tapeExact
    priorLabels [] target record.answer labelsDecomposition

/-- A selected literal root answer is read from its gamma-prefix coordinate.
Unlike the full-trace theorem above, the residual obligation is discharged
from the root's exact machine-fresh cap, so no later restoration-client
activity and no unused sampler retry is silently counted as observed. -/
theorem exact_gamma_prefix_root_router_routes_selected_answer
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (target : GammaPrefixDigestSlot)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ record :: later)
    (preferred :
      (gammaPrefixCausalController transitionFuel).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (gammaPrefixCausalController transitionFuel) prior
          (exactGammaPrefixInitialState configuration sample.1)) = some target)
    (programmedCover : 24 ≤ 2 * parameters.forkRequestCap) :
    causalRoutedAnswer? target
        (exactCompilerGammaPrefixRouter parameters transitionFuel
          (exactPlainRomCursor configuration sample.1).erase)
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      some record.answer := by
  let controller := gammaPrefixCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters) transitionFuel
  let initial := exactGammaPrefixInitialState configuration sample.1
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial (prior ++ [record])
  let suffixLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller (prior ++ [record])
      initial) later
  have rootLabelsExact : exactGammaPrefixRootLabels input =
      prefixLabels ++ suffixLabels := by
    unfold exactGammaPrefixRootLabels
    rw [rootExact]
    have grouped : prior ++ record :: later = (prior ++ [record]) ++ later := by
      simp [List.append_assoc]
    rw [grouped, indexed_controller_labeled_records_append]
  have rootEnough :=
    exact_gamma_prefix_root_residual_enough_of_programmed_cover input
      programmedCover
  rw [rootLabelsExact, residual_trace_steps_append] at rootEnough
  have prefixLe : residualTraceSteps prefixLabels ≤
      residualTraceSteps prefixLabels + residualTraceSteps suffixLabels := by
    omega
  have prefixEnough : residualTraceSteps prefixLabels ≤
      (exactCompilerTargetCaps parameters).length - 24 :=
    prefixLe.trans rootEnough
  let tail := (exactFixedComputedClientTailRun transitionFuel configuration
    sample input.package.root).trace
  have fullDecomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        prior ++ record :: (later ++ tail) := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    simp [exactFixedOperationalStateMapTrace, rootExact, tail,
      List.append_assoc]
  apply exact_gamma_prefix_router_routes_selected_full_answer transitionFuel
    configuration sample prior (later ++ tail) record target fullDecomposition
  · simpa only [controller, initial] using preferred
  · simpa only [controller, initial, prefixLabels] using prefixEnough

theorem exact_gamma_prefix_output_coordinate_eq_of_routed_lookup
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters))
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 12) (answer : Digest256)
    (routed : causalRoutedAnswer? (block, false)
        (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)
        (exactGammaPrefixRouterInputTape parameters tape) = some answer) :
    (exactCompilerGammaPrefixCoordinates parameters transitionFuel cursor
      tape).2.1 block = answer := by
  change
    (CausalSlotRouter.coordinateEquiv
      (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)
      (exactGammaPrefixRouterInputTape parameters tape)).1
        ⟨(block, false), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)
    (exactGammaPrefixRouterInputTape parameters tape)
    (block, false) (Finset.mem_univ _) answer routed

theorem exact_gamma_prefix_advance_coordinate_eq_of_routed_lookup
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters))
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 12) (answer : Digest256)
    (routed : causalRoutedAnswer? (block, true)
        (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)
        (exactGammaPrefixRouterInputTape parameters tape) = some answer) :
    (exactCompilerGammaPrefixCoordinates parameters transitionFuel cursor
      tape).2.2 block = answer := by
  change
    (CausalSlotRouter.coordinateEquiv
      (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)
      (exactGammaPrefixRouterInputTape parameters tape)).1
        ⟨(block, true), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (exactCompilerGammaPrefixRouter parameters transitionFuel cursor)
    (exactGammaPrefixRouterInputTape parameters tape)
    (block, true) (Finset.mem_univ _) answer routed

#print axioms exactGammaPrefixFullLabels
#print axioms exact_gamma_prefix_router_input_tape_preserves_list
#print axioms exact_gamma_prefix_full_labels_form_trace
#print axioms exact_gamma_prefix_full_named_slots_nodup
#print axioms exact_gamma_prefix_full_labels_tape_exact
#print axioms exact_gamma_prefix_root_residual_enough_of_programmed_cover
#print axioms exact_gamma_prefix_root_router_routes_selected_answer
#print axioms exact_gamma_prefix_router_routes_selected_full_answer
#print axioms exact_gamma_prefix_output_coordinate_eq_of_routed_lookup
#print axioms exact_gamma_prefix_advance_coordinate_eq_of_routed_lookup

end
end AspisK1.V7Tag73ExactGammaPrefixFullRouting
