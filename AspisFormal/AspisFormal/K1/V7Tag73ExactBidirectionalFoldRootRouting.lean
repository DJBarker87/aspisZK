import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaOneShot
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldAnchor
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73ExactCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion

/-!
# Exact root routing for the bidirectional fold/alpha controller

This module connects the controller's answer-independent five-slot inventory
to the literal exact root and compiler tape.  It deliberately remains generic
about which source record receives which slot; later source lemmas only need
to establish the pre-answer `preferredSlot` fact for their selected record.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73BidirectionalFoldAlphaOneShot
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactBidirectionalFoldController
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (trial : ExactCompilerExposureTrial parameters) :=
  bidirectionalFoldAlphaController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel trial.val

def exactBidirectionalFoldInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :=
  bidirectionalFoldAlphaInitialState
    (exactPlainRomCursor configuration sample.1).erase

def exactBidirectionalFoldRootLabels
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
    (trial : ExactCompilerExposureTrial parameters) :
    List (Option FoldOneFoldDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (exactBidirectionalFoldController transitionFuel trial)
    (exactBidirectionalFoldInitialState input)
    (exactFixedRootRecords input.package.root)

/-- The master tape cast to the controller's five named destinations plus
residual.  This is a length proof only and preserves chronological values. -/
def bidirectionalFoldNamedSlotInputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset FoldOneFoldDigestSlot).card +
        ((exactCompilerTargetCaps parameters).length - 5)) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ, fold_onefold_digest_slot_card]
    exact (Nat.add_sub_of_le
      (exact_compiler_tape_has_bidirectional_fold_onefold_capacity
        parameters)).symm) tape

theorem bidirectional_fold_named_slot_input_tape_preserves_list
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    freshAnswerTapeToList
        (bidirectionalFoldNamedSlotInputTape parameters tape) =
      freshAnswerTapeToList tape := by
  unfold bidirectionalFoldNamedSlotInputTape
  rw [fresh_answer_tape_to_list_cast]

theorem exact_bidirectional_fold_root_labels_form_trace
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
    (trial : ExactCompilerExposureTrial parameters) :
    MachineLabeledTrace
      ((exactBidirectionalFoldController transitionFuel trial).machine
        transitionFuel)
      (exactBidirectionalFoldInitialState input)
      (exactBidirectionalFoldRootLabels input trial)
      (indexedStateAfterRecords transitionFuel
        (exactBidirectionalFoldController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactBidirectionalFoldInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (exactBidirectionalFoldController transitionFuel trial)
    (exactBidirectionalFoldInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_bidirectional_fold_root_named_slots_nodup
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
    (trial : ExactCompilerExposureTrial parameters) :
    (namedTraceSlots (exactBidirectionalFoldRootLabels input trial)).Nodup := by
  exact bidirectional_labeled_records_named_slots_nodup transitionFuel trial.val
    (exactFixedRootRecords input.package.root)
    (exactBidirectionalFoldInitialState input)

theorem exact_bidirectional_fold_root_labels_tape_prefix
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
    (trial : ExactCompilerExposureTrial parameters) :
    freshAnswerTapeToList
        (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      (exactBidirectionalFoldRootLabels input trial).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold exactBidirectionalFoldRootLabels
  rw [bidirectional_fold_named_slot_input_tape_preserves_list,
    indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  exact (exactCompilerInitialGammaCursorAlignment input).answersExact

theorem exact_bidirectional_fold_root_residual_enough_of_programmed_cover
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
    (trial : ExactCompilerExposureTrial parameters)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps (exactBidirectionalFoldRootLabels input trial) ≤
      (exactCompilerTargetCaps parameters).length - 5 := by
  let rootRecords := exactFixedRootRecords input.package.root
  let labels := exactBidirectionalFoldRootLabels input trial
  have labelsLength : labels.length = rootRecords.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (exactBidirectionalFoldController transitionFuel trial)
        (exactBidirectionalFoldInitialState input) rootRecords)
    simpa [labels, exactBidirectionalFoldRootLabels, rootRecords] using answers
  have residualLeLabels : residualTraceSteps labels ≤ labels.length := by
    have split := labeled_trace_length_split labels
    omega
  have projectedLength (actor : QueryActor) :
      ∀ queries : List (ShaInput × Digest256),
        (projectedMachineFreshRecords actor queries).length = queries.length := by
    intro queries
    induction queries with
    | nil => rfl
    | cons query queries ih =>
        rcases query with ⟨queryInput, answer⟩
        simp [projectedMachineFreshRecords, ih]
  have rootCountExact : rootRecords.length =
      machineFreshCoordinateCount rootRecords := by
    unfold rootRecords exactFixedRootRecords fullProjectedRootRecords
    simp [projectedLength]
  have rootMachineLe : machineFreshCoordinateCount rootRecords ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [rootRecords]
  have rootLengthLe : rootRecords.length ≤
      full256MachineFreshCap parameters := by
    rw [rootCountExact]
    exact rootMachineLe.trans input.package.root.traceCaps.1
  have fullCapLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 5 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLeLabels.trans
    (labelsLength.le.trans (rootLengthLe.trans fullCapLe))

/-- Once a literal root record is selected by the controller, the causal
router returns exactly that record's answer from the original compiler tape. -/
theorem exact_bidirectional_fold_router_routes_selected_root_answer
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
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (target : FoldOneFoldDigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (residualEnough :
      residualTraceSteps (exactBidirectionalFoldRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 5)
    (preferred :
      (exactBidirectionalFoldController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) prior
          (exactBidirectionalFoldInitialState input)) = some target) :
    causalRoutedAnswer? target
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      some answer := by
  let controller := exactBidirectionalFoldController transitionFuel trial
  let initial := exactBidirectionalFoldInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition : exactBidirectionalFoldRootLabels input trial =
      priorLabels ++ (some target, answer) :: laterLabels := by
    unfold exactBidirectionalFoldRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_bidirectional_fold_root_labels_form_trace input trial)
    (exact_bidirectional_fold_root_named_slots_nodup input trial)
    (fun slot _member => Finset.mem_univ slot) residualEnough
    (bidirectionalFoldNamedSlotInputTape parameters sample.2)
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_bidirectional_fold_root_labels_tape_prefix input trial)
    priorLabels laterLabels target answer labelsDecomposition

end


#print axioms exact_bidirectional_fold_root_labels_form_trace
#print axioms bidirectional_fold_named_slot_input_tape_preserves_list
#print axioms exact_bidirectional_fold_root_named_slots_nodup
#print axioms exact_bidirectional_fold_root_labels_tape_prefix
#print axioms exact_bidirectional_fold_root_residual_enough_of_programmed_cover
#print axioms exact_bidirectional_fold_router_routes_selected_root_answer

end AspisK1.V7Tag73ExactBidirectionalFoldRootRouting
