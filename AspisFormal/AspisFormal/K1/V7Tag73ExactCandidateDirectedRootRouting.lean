import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchLabelsNodup
import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchControllerProjection
import AspisFormal.K1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting

/-!
# Accepted-root routing for one fixed q16 candidate

The candidate-directed controller has the same 542-slot tape geometry as the
selected-first controller, but arms its query-batch extension from one q16
terminal slot fixed before any answer is exposed.  This file couples its
online labels to the literal accepted-root answer prefix and supplies the
generic routed-answer theorem used by the finite 512-candidate cover.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateDirectedRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateDirectedQueryBatchLabelsNodup
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The causal router for one pre-fixed candidate hypothesis. -/
def exactCompilerCandidateDirectedQueryBatchRouter
    (parameters : ExactCompilerResourceParameters)
    (transitionFuel foldExposureIndex finalExposureIndex boundaryIndex : Nat)
    (target : Q16DigestSlot)
    (cursor : UnifiedExposureCursor
      (globalFull256OracleCallCap parameters)) :
    ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter parameters :=
  ((extendControllerThroughCandidateQueryBatch transitionFuel target
      (candidateCompleteBaseController transitionFuel foldExposureIndex
        finalExposureIndex boundaryIndex) completeFoldAlphaQ16DagMemory
    ).machine transitionFuel).fullRouter
    ((exactCompilerTargetCaps parameters).length - 542)
    { exposureIndex := 0
      cursor := cursor
      memory :=
        ((false, (inactiveAlphaZeroMemory, inactiveDagMemory)),
          inactiveQueryBatchDagExtensionMemory) }

def exactCandidateDirectedRootLabels
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
    (boundaryIndex : Nat) (target : Q16DigestSlot) :
    List (Option FoldAlphaFinalWorkQ16QueryBatchDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (extendControllerThroughCandidateQueryBatch transitionFuel target
      (candidateCompleteBaseController transitionFuel foldTrial.val
        finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
    (exactCandidateDirectedQueryBatchInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_candidate_directed_root_labels_form_trace
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
    (boundaryIndex : Nat) (target : Q16DigestSlot) :
    MachineLabeledTrace
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory).machine
            transitionFuel)
      (exactCandidateDirectedQueryBatchInitialState input)
      (exactCandidateDirectedRootLabels input foldTrial finalTrial boundaryIndex
        target)
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target
          (candidateCompleteBaseController transitionFuel foldTrial.val
            finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
        (exactFixedRootRecords input.package.root)
        (exactCandidateDirectedQueryBatchInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel _ _ _

theorem exact_candidate_directed_root_named_slots_nodup
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
    (boundaryIndex : Nat) (target : Q16DigestSlot) :
    (namedTraceSlots
      (exactCandidateDirectedRootLabels input foldTrial finalTrial boundaryIndex
        target)).Nodup := by
  exact candidate_directed_labeled_records_named_slots_nodup transitionFuel
    foldTrial.val finalTrial.val boundaryIndex target
      (exactFixedRootRecords input.package.root)
      (exactCandidateDirectedQueryBatchInitialState input)

theorem exact_candidate_directed_root_labels_tape_prefix
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
    (boundaryIndex : Nat) (target : Q16DigestSlot) :
    freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      (exactCandidateDirectedRootLabels input foldTrial finalTrial boundaryIndex
        target).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold foldAlphaQ16QueryBatchNamedSlotInputTape
    exactCompilerFoldAlphaQ16QueryBatchInputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]
  unfold exactCandidateDirectedRootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  have base := exact_causal_router_tape_has_literal_root_prefix input
  unfold finalWorkQ16NamedSlotInputTape exactCompilerFinalWorkQ16InputTape at base
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast] at base
  exact base

theorem exact_candidate_directed_root_residual_enough
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
    (boundaryIndex : Nat) (target : Q16DigestSlot)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
        (exactCandidateDirectedRootLabels input foldTrial finalTrial
          boundaryIndex target) ≤
      (exactCompilerTargetCaps parameters).length - 542 := by
  let records := exactFixedRootRecords input.package.root
  let labels := exactCandidateDirectedRootLabels input foldTrial finalTrial
    boundaryIndex target
  have labelsLength : labels.length = records.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target
          (candidateCompleteBaseController transitionFuel foldTrial.val
            finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
        (exactCandidateDirectedQueryBatchInitialState input) records)
    simpa [labels, exactCandidateDirectedRootLabels, records] using answers
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

/-- Any preferred answer in a fixed candidate experiment is read from its
exact coordinate in the shared accepted-root tape. -/
theorem exact_candidate_directed_root_answer_is_routed
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
    (boundaryIndex : Nat) (target : Q16DigestSlot)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (preferred :
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (extendControllerThroughCandidateQueryBatch transitionFuel target
            (candidateCompleteBaseController transitionFuel foldTrial.val
              finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
          prior (exactCandidateDirectedQueryBatchInitialState input)) =
        some slot) :
    causalRoutedAnswer? slot
      (exactCompilerCandidateDirectedQueryBatchRouter parameters transitionFuel
        foldTrial.val finalTrial.val boundaryIndex target
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      some answer := by
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16QueryBatchDigestSlot
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
    extendControllerThroughCandidateQueryBatch transitionFuel target
      (candidateCompleteBaseController transitionFuel foldTrial.val
        finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
  let initial := exactCandidateDirectedQueryBatchInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition :
      exactCandidateDirectedRootLabels input foldTrial finalTrial boundaryIndex
          target =
        priorLabels ++ (some slot, answer) :: laterLabels := by
    unfold exactCandidateDirectedRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  unfold exactCompilerCandidateDirectedQueryBatchRouter
  change causalRoutedAnswer? slot
      ((controller.machine transitionFuel).router Finset.univ
        ((exactCompilerTargetCaps parameters).length - 542) initial)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
    some answer
  exact machine_labeled_trace_routes_named_answer
    (exact_candidate_directed_root_labels_form_trace input foldTrial finalTrial
      boundaryIndex target)
    (exact_candidate_directed_root_named_slots_nodup input foldTrial finalTrial
      boundaryIndex target)
    (fun candidate _ => Finset.mem_univ candidate)
    (exact_candidate_directed_root_residual_enough input foldTrial finalTrial
      boundaryIndex target programmedCover)
    (foldAlphaQ16QueryBatchNamedSlotInputTape
      (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_candidate_directed_root_labels_tape_prefix input foldTrial finalTrial
      boundaryIndex target)
      priorLabels laterLabels slot answer labelsDecomposition

#print axioms exactCompilerCandidateDirectedQueryBatchRouter
#print axioms exactCandidateDirectedRootLabels
#print axioms exact_candidate_directed_root_labels_form_trace
#print axioms exact_candidate_directed_root_named_slots_nodup
#print axioms exact_candidate_directed_root_labels_tape_prefix
#print axioms exact_candidate_directed_root_residual_enough
#print axioms exact_candidate_directed_root_answer_is_routed

end
end AspisK1.V7Tag73ExactCandidateDirectedRootRouting
