import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection
import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedFinalWorkRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedQ16Routing

/-!
# Accepted work coordinates in the 542-slot production router

The query-batch extension preserves every preferred slot selected by its
518-slot fold/alpha/final-work/q16 base.  These lemmas route the two deployed
work answers through the enlarged production coordinate system.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedCandidateWorkRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting
open AspisK1.V7Tag73ExactFoldArmedQ16Routing
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73FoldArmedCompleteLabelsNodup
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem exact_fold_armed_candidate_accepted_fold_is_routed
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
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactAcceptedDagInstallation input)
    (target : Q16DigestSlot) :
    causalRoutedAnswer? (Sum.inl none)
      (exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
        fold.trial.val source.finalTrial.val target
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      some fold.answer := by
  let baseController := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val source.finalTrial.val
  let baseInitial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let baseReached := indexedStateAfterRecords transitionFuel baseController
    fold.prior baseInitial
  have coherentInitial : FoldArmedOuterCoherent fold.trial.val baseInitial := by
    simp [FoldArmedOuterCoherent, baseInitial, foldArmedInitialState]
  have coherentReached : FoldArmedOuterCoherent fold.trial.val baseReached := by
    exact fold_armed_outer_coherent_after_records transitionFuel fold.trial.val
      source.finalTrial.val fold.prior baseInitial coherentInitial
  have atFold : baseReached.exposureIndex = fold.trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      baseController fold.prior baseInitial
    simpa [baseReached, baseInitial, foldArmedInitialState, fold.trialExact]
      using count
  have unused : baseReached.memory.1 = false := by
    unfold FoldArmedOuterCoherent at coherentReached
    rw [atFold] at coherentReached
    simpa using coherentReached
  have basePreferred : baseController.preferredSlot baseReached = some none := by
    simpa [baseController] using
      fold_armed_complete_preferred_at_fold transitionFuel fold.trial.val
        source.finalTrial.val baseReached unused atFold
  let extendedController := foldArmedCandidateQueryBatchController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val source.finalTrial.val target
  let extendedInitial := exactFoldArmedCandidateQueryBatchInitialState input
  let extendedReached := indexedStateAfterRecords transitionFuel
    extendedController fold.prior extendedInitial
  have baseStateExact : baseIndexedState extendedReached = baseReached := by
    simpa [extendedController, extendedInitial, baseController, baseInitial,
      extendedReached, baseReached] using
      fold_armed_candidate_base_after_records input fold.trial
        source.finalTrial target fold.prior
  have preferred : extendedController.preferredSlot extendedReached =
      some (Sum.inl none) := by
    simp [extendedController, foldArmedCandidateQueryBatchController,
      extendControllerThroughCandidateQueryBatch, baseStateExact,
      baseController, basePreferred]
  exact exact_fold_armed_candidate_root_answer_is_routed programmedCover input
    fold.trial source.finalTrial target fold.prior fold.later fold.actor
    (bytes fold.digest ++ [domGrind] ++
      bytes (exactOperationalTape input).messages.foldGrinding.selected)
    fold.answer (Sum.inl none) fold.rootDecomposition (by
      simpa [extendedController, extendedInitial, extendedReached] using
        preferred)

theorem exact_fold_armed_candidate_final_work_is_routed
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
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactAcceptedDagInstallation input)
    (target : Q16DigestSlot) :
    causalRoutedAnswer? (Sum.inl (some (Sum.inr none)))
      (exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
        fold.trial.val source.finalTrial.val target
        (exactPlainRomCursor configuration sample.1).erase)
      (foldAlphaQ16QueryBatchNamedSlotInputTape
        (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters sample.2)) =
      some source.workAnswer := by
  obtain ⟨workPrior, workLater, workActor, workDecomposition,
      workDagPreferred⟩ := source.workLabeled
  let baseController := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val source.finalTrial.val
  let baseInitial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let baseReached := indexedStateAfterRecords transitionFuel baseController
    workPrior baseInitial
  have dagProjection : foldArmedPreFinalDagState baseReached =
      indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel source.finalTrial) workPrior
        (exactDagCandidateInitialState input) := by
    rw [show foldArmedPreFinalDagState baseReached =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
            transitionFuel source.finalTrial.val) workPrior
          (foldArmedPreFinalDagState baseInitial) by
      exact fold_armed_dag_state_after_records transitionFuel fold.trial.val
        source.finalTrial.val workPrior baseInitial]
    rw [fold_armed_initial_dag_state_eq input]
    rfl
  have dagPreferred :
      (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
        transitionFuel source.finalTrial.val).preferredSlot
        (foldArmedPreFinalDagState baseReached) = some none := by
    rw [dagProjection]
    simpa [exactDagTrialController] using workDagPreferred
  have alphaNone := fold_armed_alpha_preferred_none_at_final_work input
    fold.trial source.finalTrial workPrior workLater workActor
      (literalFinalWorkKey source.digest
        (exactOperationalTape input).messages.finalGrinding.selected)
      source.workAnswer (by simp [literalFinalWorkKey, bytes_length])
      (by simp [literalFinalWorkKey, bytes_length]) workDecomposition
  have underlyingPreferred :
      (alphaFinalWorkQ16DagController transitionFuel source.finalTrial.val
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState baseReached) = some (Sum.inr none) := by
    apply alpha_final_work_q16_preferred_of_dag
    · simpa [foldArmedAlphaZeroController, foldArmedAlphaState] using alphaNone
    · simpa [foldArmedPreFinalDagState] using dagPreferred
  have workDistinct : workPrior.length ≠ fold.trial.val := by
    symm
    exact exact_accepted_fold_trial_ne_final_work_record input fold source.digest
      source.workAnswer source.prefinal workPrior workLater workActor
        workDecomposition
  have reachedIndex : baseReached.exposureIndex = workPrior.length := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      baseController workPrior baseInitial
    simpa [baseReached, baseInitial, foldArmedInitialState] using count
  have notFold : baseReached.exposureIndex ≠ fold.trial.val := by
    simpa [reachedIndex] using workDistinct
  have basePreferred : baseController.preferredSlot baseReached =
      some (some (Sum.inr none)) := by
    simp [baseController, foldArmedCompleteController, notFold,
      underlyingPreferred]
  let extendedController := foldArmedCandidateQueryBatchController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val source.finalTrial.val target
  let extendedInitial := exactFoldArmedCandidateQueryBatchInitialState input
  let extendedReached := indexedStateAfterRecords transitionFuel
    extendedController workPrior extendedInitial
  have baseStateExact : baseIndexedState extendedReached = baseReached := by
    simpa [extendedController, extendedInitial, baseController, baseInitial,
      extendedReached, baseReached] using
      fold_armed_candidate_base_after_records input fold.trial
        source.finalTrial target workPrior
  have preferred : extendedController.preferredSlot extendedReached =
      some (Sum.inl (some (Sum.inr none))) := by
    simp [extendedController, foldArmedCandidateQueryBatchController,
      extendControllerThroughCandidateQueryBatch, baseStateExact,
      baseController, basePreferred]
  exact exact_fold_armed_candidate_root_answer_is_routed programmedCover input
    fold.trial source.finalTrial target workPrior workLater workActor
    (literalFinalWorkKey source.digest
      (exactOperationalTape input).messages.finalGrinding.selected).workInput
    source.workAnswer (Sum.inl (some (Sum.inr none))) workDecomposition (by
      simpa [extendedController, extendedInitial, extendedReached] using
        preferred)

#print axioms exact_fold_armed_candidate_accepted_fold_is_routed
#print axioms exact_fold_armed_candidate_final_work_is_routed

end
end AspisK1.V7Tag73ExactFoldArmedCandidateWorkRouting
