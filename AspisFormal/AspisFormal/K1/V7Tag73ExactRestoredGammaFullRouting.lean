import AspisFormal.K1.V7Tag73CausalSlotRouterLookup
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73ExactPlainRomRun
import AspisFormal.K1.V7Tag73RestoredChallengeCausalMarker
import AspisFormal.K1.V7Tag73RestoredJointBatchActualLawClosure
import AspisFormal.K1.V7Tag73RestoredQueryBatchLabelsNodup

/-!
# Exact full-run routing for the restored gamma sampler

The restoration-native probability coordinates are compiled from a waiting
pre-answer controller on the complete `runExactPlainRom` cursor.  This file
connects that controller to the literal complete exposure trace and master
tape.  It remains deterministic: no random-oracle freshness, independence,
or probability premise is used.

The source-specific layer still has to identify the root-sweep record at
which the typed gamma fork is dispatched.  Once it supplies the exact
trace decomposition and pre-answer label, the theorems below recover that
record's answer as the corresponding output/advance probability coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRestoredGammaFullRouting

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
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73RestoredQueryBatchForkController
open AspisK1.V7Tag73RestoredQueryBatchLabelsNodup
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler

noncomputable section

/-- Equality of the emitted record at one answer fixes every pre-answer field,
and therefore fixes the emitted record at every answer.  This lets a literal
trace record transport a causal marker without inspecting the fresh digest. -/
theorem unified_record_at_answer_extensional_of_eq
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (source target : UnifiedExposureCursor globalOracleCalls)
    (witness : Digest256)
    (exact : unifiedRecordAtAnswer transitionFuel source witness =
      unifiedRecordAtAnswer transitionFuel target witness) :
    ∀ answer, unifiedRecordAtAnswer transitionFuel source answer =
      unifiedRecordAtAnswer transitionFuel target answer := by
  intro answer
  unfold unifiedRecordAtAnswer at exact ⊢
  generalize sourceExact : seekUnifiedExposure transitionFuel source =
    sourceRequest at exact ⊢
  generalize targetExact : seekUnifiedExposure transitionFuel target =
    targetRequest at exact ⊢
  cases sourceRequest <;> cases targetRequest <;> simp_all

/-- Literal full-run coordinates at the first prepared block-zero gamma
restoration fork. -/
def exactCompilerRestoredGammaCoordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape) :
    FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
      ExactCompilerGammaPrefixResidual parameters × TotalGammaDuplexTape :=
  exactCompilerTypedRestoredGammaCoordinates
    (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    parameters transitionFuel
    (configuration.machine.blackBox.start hidden
      configuration.machine.observation)
    configuration.machine.environment
    configuration.restorationConfiguration
    (exactPlainRomCursor configuration hidden).erase

def exactRestoredGammaController
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) :=
  waitingRestoredQueryBatchForkController transitionFuel
    (typedRestoredChallengeExposureStartsHere transitionFuel (.challenge .gamma)
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (Result := Result)
      (configuration.machine.blackBox.start hidden
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration)

def exactRestoredGammaInitialState
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

/-- A chronological record prefix contains no activation point for a waiting
controller.  The predicate is intentionally recursive on the actual replay
state: it cannot be discharged by inspecting completed answers or by a raw
SHA-coordinate classifier. -/
def WaitingControllerPrefixUnmarked
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool) :
    IndexedUnifiedExposureState globalOracleCalls
        WaitingRestoredQueryBatchMemory →
      List UnifiedExposureRecord → Prop
  | _state, [] => True
  | state, record :: records =>
      startsHere state.cursor = false ∧
        WaitingControllerPrefixUnmarked transitionFuel startsHere
          ((waitingRestoredQueryBatchForkController transitionFuel startsHere).afterAnswer
            transitionFuel state record.answer)
          records

/-- Replaying an unmarked prefix from the waiting phase leaves the controller
waiting.  This is the generic chronological half of the canonical-gamma
bridge; the root-sweep source layer only has to prove that its earlier
requests satisfy `WaitingControllerPrefixUnmarked`. -/
theorem waiting_controller_prefix_unmarked_preserves_waiting
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool) :
    ∀ (state : IndexedUnifiedExposureState globalOracleCalls
        WaitingRestoredQueryBatchMemory)
      (records : List UnifiedExposureRecord),
      state.memory = .waiting →
      WaitingControllerPrefixUnmarked transitionFuel startsHere state records →
      (indexedStateAfterRecords transitionFuel
        (waitingRestoredQueryBatchForkController transitionFuel startsHere)
        records state).memory = .waiting := by
  intro state records
  induction records generalizing state with
  | nil =>
      intro waiting _unmarked
      simpa using waiting
  | cons record records ih =>
      intro waiting unmarked
      obtain ⟨markedFalse, tailUnmarked⟩ := unmarked
      rw [indexed_state_after_records_cons]
      apply ih _ ?_ tailUnmarked
      rcases state with ⟨exposureIndex, cursor, memory⟩
      simp only at waiting
      subst memory
      simp [waitingRestoredQueryBatchForkController, markedFalse,
        IndexedUnifiedExposureController.afterAnswer]

/-- Once an unmarked chronological prefix has been replayed, the first marked
cursor is routed to the block-zero output slot.  This packages the two facts
needed by the source adapter without assuming that the marked exposure was
verifier-origin: an adversary-first exposure of the same immutable oracle
coordinate is handled by choosing that earlier exposure as the stopping
point. -/
theorem waiting_controller_prefix_unmarked_then_marked_routes_first_output
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (state : IndexedUnifiedExposureState globalOracleCalls
      WaitingRestoredQueryBatchMemory)
    (records : List UnifiedExposureRecord)
    (waiting : state.memory = .waiting)
    (unmarked : WaitingControllerPrefixUnmarked transitionFuel startsHere
      state records)
    (marked : startsHere
      (indexedStateAfterRecords transitionFuel
        (waitingRestoredQueryBatchForkController transitionFuel startsHere)
        records state).cursor = true) :
    (waitingRestoredQueryBatchForkController transitionFuel startsHere).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (waitingRestoredQueryBatchForkController transitionFuel startsHere)
          records state) =
      some (⟨0, by decide⟩, false) := by
  let reached := indexedStateAfterRecords transitionFuel
    (waitingRestoredQueryBatchForkController transitionFuel startsHere)
    records state
  have stillWaiting : reached.memory = .waiting :=
    waiting_controller_prefix_unmarked_preserves_waiting
    transitionFuel startsHere state records waiting unmarked
  change
    (waitingRestoredQueryBatchForkController transitionFuel startsHere).preferredSlot
        reached = some (⟨0, by decide⟩, false)
  change startsHere reached.cursor = true at marked
  rcases reached with ⟨exposureIndex, cursor, memory⟩
  simp only at stillWaiting marked ⊢
  subst memory
  exact waiting_controller_marks_block_zero_output transitionFuel exposureIndex
    startsHere cursor marked

/-- Any known marked point in a chronological trace has an earliest marked
record.  The returned prefix is certified unmarked by construction, so it is
safe even when an adversary queried the eventual verifier coordinate before
the verifier-origin restoration fork. -/
theorem waiting_controller_eventually_marked_has_first_marked_record
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool) :
    ∀ (state : IndexedUnifiedExposureState globalOracleCalls
        WaitingRestoredQueryBatchMemory)
      (prior : List UnifiedExposureRecord)
      (record : UnifiedExposureRecord)
      (later : List UnifiedExposureRecord),
      startsHere
          (indexedStateAfterRecords transitionFuel
            (waitingRestoredQueryBatchForkController transitionFuel startsHere)
            prior state).cursor = true →
      ∃ (firstPrior : List UnifiedExposureRecord)
          (firstRecord : UnifiedExposureRecord)
          (firstLater : List UnifiedExposureRecord),
        prior ++ record :: later =
          firstPrior ++ firstRecord :: firstLater ∧
        WaitingControllerPrefixUnmarked transitionFuel startsHere state
          firstPrior ∧
        startsHere
            (indexedStateAfterRecords transitionFuel
              (waitingRestoredQueryBatchForkController transitionFuel startsHere)
              firstPrior state).cursor = true := by
  intro state prior
  induction prior generalizing state with
  | nil =>
      intro record later marked
      exact ⟨[], record, later, rfl, trivial, marked⟩
  | cons head tail ih =>
      intro record later marked
      cases markedNow : startsHere state.cursor with
      | true =>
          exact ⟨[], head, tail ++ record :: later, by simp, trivial,
            markedNow⟩
      | false =>
          let controller :=
            waitingRestoredQueryBatchForkController transitionFuel startsHere
          let next := controller.afterAnswer transitionFuel state head.answer
          have markedAfterTail : startsHere
              (indexedStateAfterRecords transitionFuel controller tail next).cursor =
                true := by
            simpa only [controller, next, indexed_state_after_records_cons] using
              marked
          obtain ⟨firstPrior, firstRecord, firstLater, splitExact,
              prefixUnmarked, firstMarked⟩ :=
            ih next record later markedAfterTail
          refine ⟨head :: firstPrior, firstRecord, firstLater, ?_, ?_, ?_⟩
          · simp only [List.cons_append]
            rw [splitExact]
          · exact ⟨markedNow, prefixUnmarked⟩
          · simpa only [controller, next, indexed_state_after_records_cons]
              using firstMarked

def exactRestoredGammaFullLabels
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    List (Option GammaPrefixDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (exactRestoredGammaController transitionFuel configuration sample.1)
    (exactRestoredGammaInitialState transitionFuel configuration sample.1)
    (runExactPlainRom transitionFuel configuration sample).trace

def exactRestoredGammaRouter
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (hidden : HiddenTape) : ExactCompilerCausalGammaPrefixRouter parameters :=
  exactCompilerIndexedGammaPrefixRouter parameters transitionFuel
    (exactRestoredGammaController transitionFuel configuration hidden)
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

theorem exact_restored_gamma_full_labels_form_trace
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    MachineLabeledTrace
      ((exactRestoredGammaController transitionFuel configuration
        sample.1).machine transitionFuel)
      (exactRestoredGammaInitialState transitionFuel configuration sample.1)
      (exactRestoredGammaFullLabels transitionFuel configuration sample)
      (indexedStateAfterRecords transitionFuel
        (exactRestoredGammaController transitionFuel configuration sample.1)
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestoredGammaInitialState transitionFuel configuration
          sample.1)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (exactRestoredGammaController transitionFuel configuration sample.1)
    (exactRestoredGammaInitialState transitionFuel configuration sample.1)
    (runExactPlainRom transitionFuel configuration sample).trace

theorem exact_restored_gamma_full_named_slots_nodup
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    (namedTraceSlots
      (exactRestoredGammaFullLabels transitionFuel configuration sample)).Nodup := by
  change
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (waitingRestoredQueryBatchForkController transitionFuel
          (typedRestoredChallengeExposureStartsHere transitionFuel (.challenge .gamma)
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
    (typedRestoredChallengeExposureStartsHere transitionFuel (.challenge .gamma)
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      (Result := Result)
      (configuration.machine.blackBox.start sample.1
        configuration.machine.observation)
      configuration.machine.environment
      configuration.restorationConfiguration)
    (runExactPlainRom transitionFuel configuration sample).trace
    (exactPlainRomCursor configuration sample.1).erase

theorem exact_restored_gamma_full_labels_tape_exact
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters) :
    freshAnswerTapeToList (exactGammaPrefixRouterInputTape parameters sample.2) =
      (exactRestoredGammaFullLabels transitionFuel configuration
        sample).map Prod.snd ++ [] := by
  rw [exact_gamma_prefix_router_input_tape_preserves_list,
    show exactRestoredGammaFullLabels transitionFuel configuration sample =
        indexedControllerLabeledRecords transitionFuel
          (exactRestoredGammaController transitionFuel configuration
            sample.1)
          (exactRestoredGammaInitialState transitionFuel configuration
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
theorem exact_restored_gamma_full_residual_exact_of_named_complete
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredGammaFullLabels transitionFuel configuration
          sample)).length = 24) :
    residualTraceSteps
        (exactRestoredGammaFullLabels transitionFuel configuration sample) =
      (exactCompilerTargetCaps parameters).length - 24 := by
  let labels := exactRestoredGammaFullLabels transitionFuel configuration
    sample
  have enough : 24 ≤ (exactCompilerTargetCaps parameters).length :=
    exact_compiler_tape_has_gamma_prefix_capacity parameters
  have labelsLength : labels.length =
      (exactCompilerTargetCaps parameters).length := by
    have tapeExact := exact_restored_gamma_full_labels_tape_exact
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
theorem exact_restored_gamma_prefix_residual_enough_of_named_complete
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
        (exactRestoredGammaFullLabels transitionFuel configuration
          sample)).length = 24) :
    residualTraceSteps
        (indexedControllerLabeledRecords transitionFuel
          (exactRestoredGammaController transitionFuel configuration
            sample.1)
          (exactRestoredGammaInitialState transitionFuel configuration
            sample.1)
          (prior ++ [record])) ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  let controller := exactRestoredGammaController transitionFuel
    configuration sample.1
  let initial := exactRestoredGammaInitialState transitionFuel
    configuration sample.1
  let prefixLabels := indexedControllerLabeledRecords transitionFuel controller
    initial (prior ++ [record])
  let suffixLabels := indexedControllerLabeledRecords transitionFuel controller
    (indexedStateAfterRecords transitionFuel controller (prior ++ [record])
      initial) later
  have labelsExact :
      exactRestoredGammaFullLabels transitionFuel configuration sample =
        prefixLabels ++ suffixLabels := by
    have traceSplit :
        (runExactPlainRom transitionFuel configuration sample).trace =
          (prior ++ [record]) ++ later := by
      simpa [List.append_assoc] using decomposition
    unfold exactRestoredGammaFullLabels
    rw [traceSplit]
    rw [indexed_controller_labeled_records_append]
  have fullExact :=
    exact_restored_gamma_full_residual_exact_of_named_complete
      transitionFuel configuration sample namedComplete
  rw [labelsExact, residual_trace_steps_append] at fullExact
  have prefixLe : residualTraceSteps prefixLabels ≤
      residualTraceSteps prefixLabels + residualTraceSteps suffixLabels := by
    omega
  simpa only [controller, initial, prefixLabels, suffixLabels] using
    prefixLe.trans_eq fullExact

/-! ## Routing a selected literal full-run record -/

theorem exact_restored_gamma_router_routes_selected_full_answer
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
      (exactRestoredGammaController transitionFuel configuration
        sample.1).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactRestoredGammaController transitionFuel configuration
            sample.1)
          prior
          (exactRestoredGammaInitialState transitionFuel configuration
            sample.1)) = some target)
    (residualEnough :
      residualTraceSteps
          (indexedControllerLabeledRecords transitionFuel
            (exactRestoredGammaController transitionFuel configuration
              sample.1)
            (exactRestoredGammaInitialState transitionFuel configuration
              sample.1)
            (prior ++ [record])) ≤
        (exactCompilerTargetCaps parameters).length - 24) :
    causalRoutedAnswer? target
        (exactRestoredGammaRouter transitionFuel configuration sample.1)
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      some record.answer := by
  let controller := exactRestoredGammaController transitionFuel
    configuration sample.1
  let initial := exactRestoredGammaInitialState transitionFuel
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
            (typedRestoredChallengeExposureStartsHere transitionFuel (.challenge .gamma)
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
      (typedRestoredChallengeExposureStartsHere transitionFuel (.challenge .gamma)
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
theorem exact_restored_gamma_router_routes_selected_full_answer_of_named_complete
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
      (exactRestoredGammaController transitionFuel configuration
        sample.1).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactRestoredGammaController transitionFuel configuration
            sample.1)
          prior
          (exactRestoredGammaInitialState transitionFuel configuration
            sample.1)) = some target)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredGammaFullLabels transitionFuel configuration
          sample)).length = 24) :
    causalRoutedAnswer? target
        (exactRestoredGammaRouter transitionFuel configuration sample.1)
        (exactGammaPrefixRouterInputTape parameters sample.2) =
      some record.answer := by
  apply exact_restored_gamma_router_routes_selected_full_answer
    transitionFuel configuration sample prior later record target decomposition
      preferred
  exact exact_restored_gamma_prefix_residual_enough_of_named_complete
    transitionFuel configuration sample prior later record decomposition
      namedComplete

/-- Route the earliest exposure equivalent to a known restored-gamma fork.
This is the source-facing adversary-prequery-safe form: callers may exhibit a
later marked verifier occurrence, while the theorem selects and routes the
first marked record in the literal complete trace. -/
theorem exact_restored_gamma_router_routes_first_marked_full_answer
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (sample : ExactCompilerSample HiddenTape parameters)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (decomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        prior ++ record :: later)
    (eventuallyMarked :
      let reached := indexedStateAfterRecords transitionFuel
        (exactRestoredGammaController transitionFuel configuration sample.1)
        prior
        (exactRestoredGammaInitialState transitionFuel configuration sample.1)
      typedRestoredChallengeExposureStartsHere
          (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness)
          transitionFuel (.challenge .gamma)
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)
          configuration.machine.environment
          configuration.restorationConfiguration reached.cursor = true)
    (namedComplete :
      (namedTraceSlots
        (exactRestoredGammaFullLabels transitionFuel configuration
          sample)).length = 24) :
    ∃ (firstPrior firstLater : List UnifiedExposureRecord)
        (firstRecord : UnifiedExposureRecord),
      (runExactPlainRom transitionFuel configuration sample).trace =
          firstPrior ++ firstRecord :: firstLater ∧
        WaitingControllerPrefixUnmarked transitionFuel
          (typedRestoredChallengeExposureStartsHere
            (Result := ExactPlainRomWitnessExtractor Statement
              Tag73K12ParsedProof Payload Witness)
            transitionFuel (.challenge .gamma)
            (configuration.machine.blackBox.start sample.1
              configuration.machine.observation)
            configuration.machine.environment
            configuration.restorationConfiguration)
          (exactRestoredGammaInitialState transitionFuel configuration sample.1)
          firstPrior ∧
        causalRoutedAnswer? (⟨0, by decide⟩, false)
          (exactRestoredGammaRouter transitionFuel configuration sample.1)
          (exactGammaPrefixRouterInputTape parameters sample.2) =
            some firstRecord.answer := by
  let startsHere : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters) → Bool :=
    typedRestoredChallengeExposureStartsHere
    (Result := ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness)
    transitionFuel (.challenge .gamma)
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.machine.environment configuration.restorationConfiguration
  let controller := exactRestoredGammaController transitionFuel configuration
    sample.1
  let initial := exactRestoredGammaInitialState transitionFuel configuration
    sample.1
  have eventuallyMarked' : startsHere
      (indexedStateAfterRecords transitionFuel controller prior initial).cursor =
        true := by
    simpa only [startsHere, controller, initial] using eventuallyMarked
  obtain ⟨firstPrior, firstRecord, firstLater, firstSplit, firstUnmarked,
      firstMarked⟩ :=
    waiting_controller_eventually_marked_has_first_marked_record transitionFuel
      startsHere initial prior record later eventuallyMarked'
  have firstDecomposition :
      (runExactPlainRom transitionFuel configuration sample).trace =
        firstPrior ++ firstRecord :: firstLater :=
    decomposition.trans firstSplit
  have firstPreferred :=
    waiting_controller_prefix_unmarked_then_marked_routes_first_output
      transitionFuel startsHere initial firstPrior rfl firstUnmarked firstMarked
  have routed :=
    exact_restored_gamma_router_routes_selected_full_answer_of_named_complete
      transitionFuel configuration sample firstPrior firstLater firstRecord
      (⟨0, by decide⟩, false) firstDecomposition (by
        simpa only [controller, initial, startsHere,
          exactRestoredGammaController] using firstPreferred) namedComplete
  refine ⟨firstPrior, firstLater, firstRecord, firstDecomposition, ?_, routed⟩
  simpa only [startsHere, initial] using firstUnmarked

/-! ## Named lookup to the public restoration-native coordinates -/

theorem exact_restored_gamma_output_coordinate_eq_of_routed_lookup
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
        (exactRestoredGammaRouter transitionFuel configuration hidden)
        (exactGammaPrefixRouterInputTape parameters tape) = some answer) :
    (exactCompilerRestoredGammaCoordinates transitionFuel configuration
      hidden tape).2.1 block = answer := by
  change
    (CausalSlotRouter.coordinateEquiv
      (exactRestoredGammaRouter transitionFuel configuration hidden)
      (exactGammaPrefixRouterInputTape parameters tape)).1
        ⟨(block, false), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (exactRestoredGammaRouter transitionFuel configuration hidden)
    (exactGammaPrefixRouterInputTape parameters tape)
    (block, false) (Finset.mem_univ _) answer routed

theorem exact_restored_gamma_advance_coordinate_eq_of_routed_lookup
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
        (exactRestoredGammaRouter transitionFuel configuration hidden)
        (exactGammaPrefixRouterInputTape parameters tape) = some answer) :
    (exactCompilerRestoredGammaCoordinates transitionFuel configuration
      hidden tape).2.2 block = answer := by
  change
    (CausalSlotRouter.coordinateEquiv
      (exactRestoredGammaRouter transitionFuel configuration hidden)
      (exactGammaPrefixRouterInputTape parameters tape)).1
        ⟨(block, true), Finset.mem_univ _⟩ = answer
  exact coordinate_eq_of_causalRoutedAnswer?_eq_some
    (exactRestoredGammaRouter transitionFuel configuration hidden)
    (exactGammaPrefixRouterInputTape parameters tape)
    (block, true) (Finset.mem_univ _) answer routed

#print axioms waiting_controller_prefix_unmarked_preserves_waiting
#print axioms unified_record_at_answer_extensional_of_eq
#print axioms
  waiting_controller_prefix_unmarked_then_marked_routes_first_output
#print axioms waiting_controller_eventually_marked_has_first_marked_record

#print axioms exactRestoredGammaFullLabels
#print axioms exact_gamma_prefix_router_input_tape_preserves_list
#print axioms exact_restored_gamma_full_labels_form_trace
#print axioms exact_restored_gamma_full_named_slots_nodup
#print axioms exact_restored_gamma_full_labels_tape_exact
#print axioms exact_restored_gamma_full_residual_exact_of_named_complete
#print axioms exact_restored_gamma_prefix_residual_enough_of_named_complete
#print axioms exact_restored_gamma_router_routes_selected_full_answer
#print axioms exact_restored_gamma_router_routes_selected_full_answer_of_named_complete
#print axioms exact_restored_gamma_router_routes_first_marked_full_answer
#print axioms exact_restored_gamma_output_coordinate_eq_of_routed_lookup
#print axioms exact_restored_gamma_advance_coordinate_eq_of_routed_lookup

end
end AspisK1.V7Tag73ExactRestoredGammaFullRouting
