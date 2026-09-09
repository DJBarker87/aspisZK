import AspisFormal.K1.V7Tag73ExactCandidateDirectedRootRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedRootRouting
import AspisFormal.K1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup

/-!
# Accepted-root routing for a fold-armed fixed q16 candidate

The older candidate router guessed the alpha boundary separately.  This
version fixes only the fold-work and final-work exposure trials.  Processing
the selected fold-work answer installs the exact future alpha input, so no
unpaid alpha-boundary union remains.  One q16 terminal slot is still fixed in
advance for the finite 512-candidate cover.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73FoldArmedCompleteLabelsNodup
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactCompilerFoldArmedCandidateQueryBatchRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex finalExposureIndex : Nat)
    (target : Q16DigestSlot)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter parameters :=
  ((foldArmedCandidateQueryBatchController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel foldExposureIndex finalExposureIndex target).machine
        transitionFuel).fullRouter
    ((exactCompilerTargetCaps parameters).length - 542)
    { exposureIndex := 0
      cursor := cursor
      memory :=
        ((false, (inactiveFoldArmedAlphaZeroMemory, inactiveDagMemory)),
          inactiveQueryBatchDagExtensionMemory) }

def exactFoldArmedCandidateQueryBatchInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      (ExtendedControllerMemory FoldArmedCompleteMemory) :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory :=
      ((false, (inactiveFoldArmedAlphaZeroMemory, inactiveDagMemory)),
        inactiveQueryBatchDagExtensionMemory) }

def exactFoldArmedCandidateRootLabels
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot) :
    List (Option FoldAlphaFinalWorkQ16QueryBatchDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
      finalTrial.val target)
    (exactFoldArmedCandidateQueryBatchInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_fold_armed_candidate_root_labels_form_trace
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot) :
    MachineLabeledTrace
      ((foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
        finalTrial.val target).machine transitionFuel)
      (exactFoldArmedCandidateQueryBatchInitialState input)
      (exactFoldArmedCandidateRootLabels input foldTrial finalTrial target)
      (indexedStateAfterRecords transitionFuel
        (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
          finalTrial.val target)
        (exactFixedRootRecords input.package.root)
        (exactFoldArmedCandidateQueryBatchInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel _ _ _

theorem exact_fold_armed_candidate_root_named_slots_nodup
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot) :
    (namedTraceSlots
      (exactFoldArmedCandidateRootLabels input foldTrial finalTrial target)
      ).Nodup := by
  apply fold_armed_candidate_labeled_records_named_slots_nodup transitionFuel
    foldTrial.val finalTrial.val target
  simp [FoldArmedOuterCoherent, baseIndexedState,
    exactFoldArmedCandidateQueryBatchInitialState]

theorem exact_fold_armed_candidate_root_labels_tape_prefix
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot) :
    freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      (exactFoldArmedCandidateRootLabels input foldTrial finalTrial target).map
          Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold foldAlphaQ16QueryBatchNamedSlotInputTape
    exactCompilerFoldAlphaQ16QueryBatchInputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]
  unfold exactFoldArmedCandidateRootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  have base := exact_causal_router_tape_has_literal_root_prefix input
  unfold finalWorkQ16NamedSlotInputTape exactCompilerFinalWorkQ16InputTape at base
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast] at base
  exact base

theorem exact_fold_armed_candidate_root_residual_enough
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
        (exactFoldArmedCandidateRootLabels input foldTrial finalTrial target) ≤
      (exactCompilerTargetCaps parameters).length - 542 := by
  let records := exactFixedRootRecords input.package.root
  let labels := exactFoldArmedCandidateRootLabels input foldTrial finalTrial
    target
  have labelsLength : labels.length = records.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
          finalTrial.val target)
        (exactFoldArmedCandidateQueryBatchInitialState input) records)
    simpa [labels, exactFoldArmedCandidateRootLabels, records] using answers
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
        rcases query with ⟨queryInput, answer⟩
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
      (exactCompilerTargetCaps parameters).length - 542 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLe.trans
    (labelsLength.le.trans (recordsLengthLe.trans capLe))

/-- Any preferred answer in the fold-armed candidate experiment is read from
its exact coordinate in the shared accepted-root tape. -/
theorem exact_fold_armed_candidate_root_answer_is_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (target : Q16DigestSlot)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (preferred :
      (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
        finalTrial.val target).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
            finalTrial.val target)
          prior (exactFoldArmedCandidateQueryBatchInitialState input)) =
        some slot) :
    causalRoutedAnswer? slot
      (exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
        foldTrial.val finalTrial.val target
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      some answer := by
  let controller := foldArmedCandidateQueryBatchController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel foldTrial.val finalTrial.val target
  let initial := exactFoldArmedCandidateQueryBatchInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition :
      exactFoldArmedCandidateRootLabels input foldTrial finalTrial target =
        priorLabels ++ (some slot, answer) :: laterLabels := by
    unfold exactFoldArmedCandidateRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  unfold exactCompilerFoldArmedCandidateQueryBatchRouter
  change causalRoutedAnswer? slot
      ((controller.machine transitionFuel).router Finset.univ
        ((exactCompilerTargetCaps parameters).length - 542) initial)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
    some answer
  exact machine_labeled_trace_routes_named_answer
    (exact_fold_armed_candidate_root_labels_form_trace input foldTrial
      finalTrial target)
    (exact_fold_armed_candidate_root_named_slots_nodup input foldTrial
      finalTrial target)
    (fun candidate _ ↦ Finset.mem_univ candidate)
    (exact_fold_armed_candidate_root_residual_enough input foldTrial finalTrial
      target programmedCover)
    (foldAlphaQ16QueryBatchNamedSlotInputTape
      (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_fold_armed_candidate_root_labels_tape_prefix input foldTrial
      finalTrial target)
    priorLabels laterLabels slot answer labelsDecomposition

#print axioms exactCompilerFoldArmedCandidateQueryBatchRouter
#print axioms exactFoldArmedCandidateQueryBatchInitialState
#print axioms exactFoldArmedCandidateRootLabels
#print axioms exact_fold_armed_candidate_root_named_slots_nodup
#print axioms exact_fold_armed_candidate_root_labels_tape_prefix
#print axioms exact_fold_armed_candidate_root_residual_enough
#print axioms exact_fold_armed_candidate_root_answer_is_routed

end
end AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
