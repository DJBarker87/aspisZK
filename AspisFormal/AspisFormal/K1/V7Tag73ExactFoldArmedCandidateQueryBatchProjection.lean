import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchControllerProjection
import AspisFormal.K1.V7Tag73ExactCandidateAdvanceFreshness
import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
import AspisFormal.K1.V7Tag73ExactFoldArmedFinalWorkRouting
import AspisFormal.K1.V7Tag73CandidateQueryBatchArmedController
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Projection agreement for old and fold-armed candidate controllers

The dynamic fold-armed base changes only fold/alpha bookkeeping.  Its q16 DAG,
cursor, and candidate-directed query-batch observer evolve identically to the
older controller that named the alpha boundary separately.  This theorem lets
the already established selected-candidate context be reused without retaining
the old boundary index in the probability experiment.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCandidateAdvanceFreshness
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def CandidateProjectionAgreement
    {globalOracleCalls : Nat}
    (old : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (armed : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory)) : Prop :=
  old.exposureIndex = armed.exposureIndex ∧
    old.cursor = armed.cursor ∧
    old.memory.2 = armed.memory.2 ∧
    completeFoldAlphaQ16DagMemory old.memory.1 =
      foldArmedCompleteDagMemory armed.memory.1

theorem candidate_projection_agreement_after_answer
    {globalOracleCalls transitionFuel foldExposureIndex finalExposureIndex
      boundaryIndex : Nat}
    (target : Q16DigestSlot)
    (old : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
    (armed : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory FoldArmedCompleteMemory))
    (answer : Digest256)
    (agreement : CandidateProjectionAgreement old armed) :
    CandidateProjectionAgreement
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldExposureIndex
          finalExposureIndex boundaryIndex) completeFoldAlphaQ16DagMemory
        ).afterAnswer transitionFuel old answer)
      ((foldArmedCandidateQueryBatchController transitionFuel foldExposureIndex
        finalExposureIndex target).afterAnswer transitionFuel armed answer) := by
  rcases agreement with ⟨indexExact, cursorExact, extensionExact, dagExact⟩
  constructor
  · simp [indexExact]
  constructor
  · simp [cursorExact]
  constructor
  · simp only [IndexedUnifiedExposureController.afterAnswer,
      extendControllerThroughCandidateQueryBatch,
      foldArmedCandidateQueryBatchController]
    have dagExact' : completeFoldAlphaQ16DagMemory
        (baseIndexedState old).memory =
      foldArmedCompleteDagMemory (baseIndexedState armed).memory := by
      simpa [baseIndexedState] using dagExact
    rw [cursorExact, extensionExact, dagExact']
  · simp only [IndexedUnifiedExposureController.afterAnswer,
      extendControllerThroughCandidateQueryBatch,
      foldArmedCandidateQueryBatchController, candidateCompleteBaseController,
      foldArmedCompleteDagMemory, completeFoldAlphaQ16DagMemory,
      foldAlphaFinalWorkQ16Controller, foldArmedCompleteController,
      alphaFinalWorkQ16DagController]
    have stateExact :
        finalWorkQ16IndexedState
            (underlyingIndexedState (baseIndexedState old)) =
          finalWorkQ16IndexedState
            (foldArmedUnderlyingState (baseIndexedState armed)) := by
      rcases old with ⟨oldIndex, oldCursor, oldMemory⟩
      rcases armed with ⟨armedIndex, armedCursor, armedMemory⟩
      simp only [baseIndexedState, finalWorkQ16IndexedState,
        underlyingIndexedState, foldArmedUnderlyingState] at indexExact cursorExact dagExact ⊢
      subst armedIndex
      subst armedCursor
      change oldMemory.1.2.2 = armedMemory.1.2.2 at dagExact
      rw [dagExact]
    rw [stateExact]

theorem candidate_projection_agreement_after_records
    {globalOracleCalls transitionFuel foldExposureIndex finalExposureIndex
      boundaryIndex : Nat}
    (target : Q16DigestSlot) :
    ∀ (records : List UnifiedExposureRecord)
      (old : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory CompleteFoldAlphaQ16Memory))
      (armed : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory FoldArmedCompleteMemory)),
      CandidateProjectionAgreement old armed →
      CandidateProjectionAgreement
        (indexedStateAfterRecords transitionFuel
          (extendControllerThroughCandidateQueryBatch transitionFuel target
            (candidateCompleteBaseController transitionFuel foldExposureIndex
              finalExposureIndex boundaryIndex) completeFoldAlphaQ16DagMemory)
          records old)
        (indexedStateAfterRecords transitionFuel
          (foldArmedCandidateQueryBatchController transitionFuel
            foldExposureIndex finalExposureIndex target) records armed) := by
  intro records
  induction records with
  | nil => intro old armed agreement; exact agreement
  | cons record records ih =>
      intro old armed agreement
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      exact ih _ _ (candidate_projection_agreement_after_answer target old armed
        record.answer agreement)

/-- Exact accepted-source specialization from the two canonical inactive
initial states. -/
theorem exact_candidate_projection_agreement_after_records
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
    (records : List UnifiedExposureRecord) :
    CandidateProjectionAgreement
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target
          (candidateCompleteBaseController transitionFuel foldTrial.val
            finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
        records (exactCandidateDirectedQueryBatchInitialState input))
      (indexedStateAfterRecords transitionFuel
        (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
          finalTrial.val target) records
        (exactFoldArmedCandidateQueryBatchInitialState input)) := by
  apply candidate_projection_agreement_after_records target records
  simp [CandidateProjectionAgreement,
    exactCandidateDirectedQueryBatchInitialState,
    exactFoldArmedCandidateQueryBatchInitialState,
    completeFoldAlphaQ16DagMemory, foldArmedCompleteDagMemory]

/-- Base-state projection for the concrete fold-armed candidate extension. -/
theorem fold_armed_candidate_base_after_records
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
    (target : Q16DigestSlot) (records : List UnifiedExposureRecord) :
    baseIndexedState
        (indexedStateAfterRecords transitionFuel
          (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
            finalTrial.val target) records
          (exactFoldArmedCandidateQueryBatchInitialState input)) =
      indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel foldTrial.val
          finalTrial.val) records
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase) := by
  have projected := base_indexed_state_after_candidate_extended_records
    transitionFuel target
      (foldArmedCompleteController
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        transitionFuel foldTrial.val finalTrial.val)
      foldArmedCompleteDagMemory records
      (exactFoldArmedCandidateQueryBatchInitialState input)
  simpa [foldArmedCandidateQueryBatchController,
    exactFoldArmedCandidateQueryBatchInitialState, baseIndexedState,
    foldArmedInitialState] using projected

/-- The standalone armed query-batch projection is identical after the same
accepted-root prefix in the old and dynamic-base experiments. -/
theorem exact_query_batch_projection_eq_after_records
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
    (records : List UnifiedExposureRecord) :
    queryBatchIndexedState
        (indexedStateAfterRecords transitionFuel
          (extendControllerThroughCandidateQueryBatch transitionFuel target
            (candidateCompleteBaseController transitionFuel foldTrial.val
              finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
          records (exactCandidateDirectedQueryBatchInitialState input)) =
      queryBatchIndexedState
        (indexedStateAfterRecords transitionFuel
          (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
            finalTrial.val target) records
          (exactFoldArmedCandidateQueryBatchInitialState input)) := by
  have agreement := exact_candidate_projection_agreement_after_records input
    foldTrial finalTrial boundaryIndex target records
  let old := indexedStateAfterRecords transitionFuel
    (extendControllerThroughCandidateQueryBatch transitionFuel target
      (candidateCompleteBaseController transitionFuel foldTrial.val
        finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
    records (exactCandidateDirectedQueryBatchInitialState input)
  let armed := indexedStateAfterRecords transitionFuel
    (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
      finalTrial.val target) records
    (exactFoldArmedCandidateQueryBatchInitialState input)
  change CandidateProjectionAgreement old armed at agreement
  rcases agreement with ⟨indexExact, cursorExact, extensionExact, _⟩
  change queryBatchIndexedState old = queryBatchIndexedState armed
  rcases old with ⟨oldIndex, oldCursor, oldMemory⟩
  rcases armed with ⟨armedIndex, armedCursor, armedMemory⟩
  simp only [queryBatchIndexedState] at indexExact cursorExact extensionExact ⊢
  subst armedIndex
  subst armedCursor
  rw [extensionExact]

/-- The accepted root is aligned for the dynamic fold-armed candidate
controller, obtained by transporting the established alignment along exact
cursor agreement. -/
theorem exact_root_records_aligned_for_fold_armed_candidate_controller
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
    IndexedRecordsAligned transitionFuel
      (foldArmedCandidateQueryBatchController transitionFuel foldTrial.val
        finalTrial.val target)
      (exactFoldArmedCandidateQueryBatchInitialState input)
      (exactFixedRootRecords input.package.root) := by
  have oldAligned :=
    exact_root_records_aligned_for_candidate_directed_controller input
      foldTrial finalTrial boundaryIndex target
  intro prior selected later decomposition
  have selectedOld := oldAligned prior selected later decomposition
  have agreement := exact_candidate_projection_agreement_after_records input
    foldTrial finalTrial boundaryIndex target prior
  rw [← agreement.2.1]
  exact selectedOld

#print axioms candidate_projection_agreement_after_answer
#print axioms candidate_projection_agreement_after_records
#print axioms exact_candidate_projection_agreement_after_records
#print axioms fold_armed_candidate_base_after_records
#print axioms exact_query_batch_projection_eq_after_records
#print axioms exact_root_records_aligned_for_fold_armed_candidate_controller

end
end AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchProjection
