import AspisFormal.K1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup

/-!
# Accepted-root routing for the complete 542-slot K1.3 controller

This extends the accepted-root tape wrapper from the established 518
fold/alpha/final-work/q16 coordinates through the exact 24-coordinate
query-batch duplex.  Every label is assigned online from the literal
production execution; no transcript role is reconstructed from raw bytes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalFinalWorkQ16UsedForest
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalQ16FinalWorkProbability
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaQ16QueryBatchLabelsNodup
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactCompilerFoldAlphaQ16QueryBatchInputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      (542 + ((exactCompilerTargetCaps parameters).length - 542)) :=
  castFreshAnswerTape (by
    have enough :=
      exact_compiler_tape_has_fold_alpha_final_work_q16_query_batch_capacity
        parameters
    omega) tape

def foldAlphaQ16QueryBatchNamedSlotInputTape
    {residual : Nat}
    (tape : FreshAnswerTape Digest256 (542 + residual)) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset
        FoldAlphaFinalWorkQ16QueryBatchDigestSlot).card + residual) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ,
      fold_alpha_final_work_q16_query_batch_digest_slot_card]) tape

/-- The fold-work component of the public 542-coordinate factor is exactly
the left-hand fold slot of the underlying causal router. -/
theorem fold_alpha_q16_query_batch_fold_coordinate_eq_named_slot
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
      parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router tape).1.2.1 =
      (router.coordinateEquiv
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters tape))).1
        ⟨Sum.inl none, Finset.mem_univ _⟩ := by
  simp only [exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates,
    exactCompilerFoldAlphaQ16QueryBatchInputTape,
    foldAlphaQ16QueryBatchNamedSlotInputTape,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply,
    foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv,
    foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup,
    foldAlphaFinalWorkQ16DigestSlotFunctionEquiv,
    alphaFinalWorkQ16DigestSlotFunctionEquiv,
    finalWorkQ16DigestSlotFunctionEquiv, univSubtypeEquiv]
  rfl

/-- The final-work component of the public 542-coordinate factor is exactly
the corresponding left-hand work slot of the causal router. -/
theorem fold_alpha_q16_query_batch_final_work_coordinate_eq_named_slot
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
      parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router tape).1.2.2.2.1 =
      (router.coordinateEquiv
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters tape))).1
        ⟨Sum.inl (some (Sum.inr none)), Finset.mem_univ _⟩ := by
  simp only [exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates,
    exactCompilerFoldAlphaQ16QueryBatchInputTape,
    foldAlphaQ16QueryBatchNamedSlotInputTape,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply,
    foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv,
    foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup,
    foldAlphaFinalWorkQ16DigestSlotFunctionEquiv,
    alphaFinalWorkQ16DigestSlotFunctionEquiv,
    finalWorkQ16DigestSlotFunctionEquiv, univSubtypeEquiv]
  rfl

/-- One public query-batch output coordinate is exactly the corresponding
right-hand named slot of the underlying 542-slot router. -/
theorem fold_alpha_q16_query_batch_output_coordinate_eq_named_slot
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
      parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 12) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router tape).2.1 block =
      (router.coordinateEquiv
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters tape))).1
        ⟨Sum.inr (block, false), Finset.mem_univ _⟩ := by
  simp only [exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates,
    exactCompilerFoldAlphaQ16QueryBatchInputTape,
    foldAlphaQ16QueryBatchNamedSlotInputTape,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply,
    foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv,
    foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup,
    foldAlphaFinalWorkQ16DigestSlotFunctionEquiv,
    gammaPrefixDigestSlotFunctionEquiv, univSubtypeEquiv]
  rfl

/-- One public query-batch advance coordinate is exactly the corresponding
right-hand named slot of the underlying 542-slot router. -/
theorem fold_alpha_q16_query_batch_advance_coordinate_eq_named_slot
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchRouter
      parameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (block : Fin 12) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router tape).2.2 block =
      (router.coordinateEquiv
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters tape))).1
        ⟨Sum.inr (block, true), Finset.mem_univ _⟩ := by
  simp only [exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates,
    exactCompilerFoldAlphaQ16QueryBatchInputTape,
    foldAlphaQ16QueryBatchNamedSlotInputTape,
    CausalSlotRouter.fullCoordinateEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply,
    foldAlphaFinalWorkQ16QueryBatchDigestSlotFunctionEquiv,
    foldAlphaFinalWorkQ16QueryBatchCoordinateRegroup,
    foldAlphaFinalWorkQ16DigestSlotFunctionEquiv,
    gammaPrefixDigestSlotFunctionEquiv, univSubtypeEquiv]
  rfl

def exactFoldAlphaQ16QueryBatchInitialState
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
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory :=
      ((false, (inactiveAlphaZeroMemory, inactiveDagMemory)),
        inactiveQueryBatchDagExtensionMemory) }

def exactFoldAlphaQ16QueryBatchRootLabels
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
    (boundaryIndex : Nat) :
    List (Option FoldAlphaFinalWorkQ16QueryBatchDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (foldAlphaQ16QueryBatchController
      (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
      finalTrial.val boundaryIndex)
    (exactFoldAlphaQ16QueryBatchInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_fold_alpha_q16_query_batch_root_labels_form_trace
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
    (boundaryIndex : Nat) :
    MachineLabeledTrace
      ((foldAlphaQ16QueryBatchController
        (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
        finalTrial.val boundaryIndex).machine transitionFuel)
      (exactFoldAlphaQ16QueryBatchInitialState input)
      (exactFoldAlphaQ16QueryBatchRootLabels input foldTrial finalTrial
        boundaryIndex)
      (indexedStateAfterRecords transitionFuel
        (foldAlphaQ16QueryBatchController
          (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
          finalTrial.val boundaryIndex)
        (exactFixedRootRecords input.package.root)
        (exactFoldAlphaQ16QueryBatchInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel _ _ _

theorem exact_fold_alpha_q16_query_batch_root_named_slots_nodup
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
    (boundaryIndex : Nat) :
    (namedTraceSlots
      (exactFoldAlphaQ16QueryBatchRootLabels input foldTrial finalTrial
        boundaryIndex)).Nodup := by
  exact fold_alpha_q16_query_batch_labeled_records_named_slots_nodup
    transitionFuel foldTrial.val finalTrial.val boundaryIndex
      (exactFixedRootRecords input.package.root)
      (exactFoldAlphaQ16QueryBatchInitialState input)

theorem exact_fold_alpha_q16_query_batch_root_labels_tape_prefix
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
    (boundaryIndex : Nat) :
    freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      (exactFoldAlphaQ16QueryBatchRootLabels input foldTrial finalTrial
        boundaryIndex).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold foldAlphaQ16QueryBatchNamedSlotInputTape
    exactCompilerFoldAlphaQ16QueryBatchInputTape
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast]
  unfold exactFoldAlphaQ16QueryBatchRootLabels
  rw [indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  have base := exact_causal_router_tape_has_literal_root_prefix input
  unfold finalWorkQ16NamedSlotInputTape exactCompilerFinalWorkQ16InputTape at base
  rw [fresh_answer_tape_to_list_cast, fresh_answer_tape_to_list_cast] at base
  exact base

theorem exact_fold_alpha_q16_query_batch_root_residual_enough
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
    (boundaryIndex : Nat)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
        (exactFoldAlphaQ16QueryBatchRootLabels input foldTrial finalTrial
          boundaryIndex) ≤
      (exactCompilerTargetCaps parameters).length - 542 := by
  let records := exactFixedRootRecords input.package.root
  let labels := exactFoldAlphaQ16QueryBatchRootLabels input foldTrial finalTrial
    boundaryIndex
  have labelsLength : labels.length = records.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (foldAlphaQ16QueryBatchController
          (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
          finalTrial.val boundaryIndex)
        (exactFoldAlphaQ16QueryBatchInitialState input) records)
    simpa [labels, exactFoldAlphaQ16QueryBatchRootLabels, records] using answers
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

/-- Every online preference at a literal accepted-root exposure is routed to
its exact coordinate in the complete 542-slot source factorization. -/
theorem exact_fold_alpha_q16_query_batch_root_answer_is_routed
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
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (slot : FoldAlphaFinalWorkQ16QueryBatchDigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (preferred :
      (foldAlphaQ16QueryBatchController
        (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
        finalTrial.val boundaryIndex).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (foldAlphaQ16QueryBatchController
            (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
            finalTrial.val boundaryIndex) prior
          (exactFoldAlphaQ16QueryBatchInitialState input)) = some slot) :
    causalRoutedAnswer? slot
      (exactCompilerFoldAlphaQ16QueryBatchRouter parameters transitionFuel
        foldTrial.val finalTrial.val boundaryIndex
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      some answer := by
  let controller := foldAlphaQ16QueryBatchController
    (globalFull256OracleCallCap parameters) transitionFuel foldTrial.val
      finalTrial.val boundaryIndex
  let initial := exactFoldAlphaQ16QueryBatchInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition :
      exactFoldAlphaQ16QueryBatchRootLabels input foldTrial finalTrial
          boundaryIndex =
        priorLabels ++ (some slot, answer) :: laterLabels := by
    unfold exactFoldAlphaQ16QueryBatchRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_fold_alpha_q16_query_batch_root_labels_form_trace input foldTrial
      finalTrial boundaryIndex)
    (exact_fold_alpha_q16_query_batch_root_named_slots_nodup input foldTrial
      finalTrial boundaryIndex)
    (fun target _ => Finset.mem_univ target)
    (exact_fold_alpha_q16_query_batch_root_residual_enough input foldTrial
      finalTrial boundaryIndex programmedCover)
    (foldAlphaQ16QueryBatchNamedSlotInputTape
      (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2))
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_fold_alpha_q16_query_batch_root_labels_tape_prefix input foldTrial
      finalTrial boundaryIndex)
    priorLabels laterLabels slot answer labelsDecomposition

#print axioms exactCompilerFoldAlphaQ16QueryBatchInputTape
#print axioms foldAlphaQ16QueryBatchNamedSlotInputTape
#print axioms fold_alpha_q16_query_batch_output_coordinate_eq_named_slot
#print axioms fold_alpha_q16_query_batch_advance_coordinate_eq_named_slot
#print axioms exactFoldAlphaQ16QueryBatchInitialState
#print axioms exactFoldAlphaQ16QueryBatchRootLabels
#print axioms exact_fold_alpha_q16_query_batch_root_labels_form_trace
#print axioms exact_fold_alpha_q16_query_batch_root_named_slots_nodup
#print axioms exact_fold_alpha_q16_query_batch_root_labels_tape_prefix
#print axioms exact_fold_alpha_q16_query_batch_root_residual_enough
#print axioms exact_fold_alpha_q16_query_batch_root_answer_is_routed

end
end AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
