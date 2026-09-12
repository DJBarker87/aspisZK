import AspisFormal.K1.V7Tag73CandidateQueryBatchPreBoundaryLabels
import AspisFormal.K1.V7Tag73K13CandidateWitnessBaseCoordinates
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Candidate-witness replay to the query-batch boundary

The exact selected candidate identities let the generic 542-coordinate replay
theorem reach the literal accepted-source prefix immediately before the
query-batch domain answer.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CandidateBoundaryPrefixReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateQueryBatchPreAnswerPrefix
open AspisK1.V7Tag73CandidateQueryBatchPreBoundaryLabels
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactCandidateAdvanceFreshness
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16QueryBatchRootRouting
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedCandidateQueryBatchLabelsNodup
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CandidateWitnessBaseCoordinates
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Aligned prefixes emitted from the same scheduler state are determined by
their chronological answer lists.  This generic form is used below for the
542-slot candidate controller. -/
theorem indexed_records_aligned_eq_of_answer_maps_eq_generic
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (controller : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (state : IndexedUnifiedExposureState globalOracleCalls Memory) :
    ∀ left right,
      IndexedRecordsAligned transitionFuel controller state left →
      IndexedRecordsAligned transitionFuel controller state right →
      left.map UnifiedExposureRecord.answer =
        right.map UnifiedExposureRecord.answer →
      left = right := by
  intro left
  induction left generalizing state with
  | nil =>
      intro right _leftAligned _rightAligned answersExact
      cases right with
      | nil => rfl
      | cons head tail => simp at answersExact
  | cons leftHead leftTail ih =>
      intro right leftAligned rightAligned answersExact
      cases right with
      | nil => simp at answersExact
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at answersExact
          have leftHeadExact := leftAligned [] leftHead leftTail (by simp)
          have rightHeadExact := rightAligned [] rightHead rightTail (by simp)
          simp only [indexed_state_after_records_nil] at leftHeadExact
          simp only [indexed_state_after_records_nil] at rightHeadExact
          have headExact : leftHead = rightHead := by
            rw [answersExact.1] at leftHeadExact
            exact leftHeadExact.symm.trans rightHeadExact
          subst rightHead
          have leftTailAligned : IndexedRecordsAligned transitionFuel controller
              (controller.afterAnswer transitionFuel state leftHead.answer)
              leftTail := by
            simpa only [indexed_state_after_records_cons,
              indexed_state_after_records_nil] using
              indexed_records_aligned_segment transitionFuel controller state
                (leftHead :: leftTail) [leftHead] leftTail [] leftAligned (by
                  simp)
          have rightTailAligned : IndexedRecordsAligned transitionFuel controller
              (controller.afterAnswer transitionFuel state leftHead.answer)
              rightTail := by
            simpa only [indexed_state_after_records_cons,
              indexed_state_after_records_nil] using
              indexed_records_aligned_segment transitionFuel controller state
                (leftHead :: rightTail) [leftHead] rightTail [] rightAligned (by
                  simp)
          have tailExact := ih
            (controller.afterAnswer transitionFuel state leftHead.answer)
            rightTail leftTailAligned rightTailAligned answersExact.2
          rw [tailExact]

/-- A candidate boundary-ready prefix cannot be a strict prefix of another
boundary-unseen replay on the same answer tape.  Consuming the next answer
arms the unique query-batch boundary, and arming persists thereafter. -/
theorem candidate_boundary_ready_prefix_not_shorter
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (initial : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (left right : List UnifiedExposureRecord)
    (tape leftRemaining rightRemaining : List Digest256)
    (continuation : Digest256)
    (leftPrefix : tape =
      left.map UnifiedExposureRecord.answer ++ leftRemaining)
    (rightPrefix : tape =
      right.map UnifiedExposureRecord.answer ++ rightRemaining)
    (leftAligned : IndexedRecordsAligned transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) initial left)
    (rightAligned : IndexedRecordsAligned transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) initial right)
    (leftInput : unifiedInputBeforeAnswer? transitionFuel
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) left initial).cursor =
        some (bytes continuation ++ [domAbsorb, queryBatchChallengeLabel]))
    (leftAdvance : (indexedStateAfterRecords transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) left initial).memory.2.q16.advances target = some continuation)
    (leftUnseen : (indexedStateAfterRecords transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) left initial).memory.2.queryBatch.boundarySeen = false)
    (leftEmpty : (indexedStateAfterRecords transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) left initial).memory.2.queryBatch.producers = [])
    (rightUnseen : (indexedStateAfterRecords transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) right initial).memory.2.queryBatch.boundarySeen = false) :
    right.length ≤ left.length := by
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    target base dagOf
  by_contra notLe
  have shorter : left.length < right.length := by omega
  have leftAnswerPrefix :
      left.map UnifiedExposureRecord.answer <+: tape :=
    ⟨leftRemaining, leftPrefix.symm⟩
  have rightAnswerPrefix :
      right.map UnifiedExposureRecord.answer <+: tape :=
    ⟨rightRemaining, rightPrefix.symm⟩
  have answerPrefix : left.map UnifiedExposureRecord.answer <+:
      right.map UnifiedExposureRecord.answer :=
    List.prefix_of_prefix_length_le leftAnswerPrefix rightAnswerPrefix (by
      simpa using Nat.le_of_lt shorter)
  have takeAnswers :
      (right.take left.length).map UnifiedExposureRecord.answer =
        left.map UnifiedExposureRecord.answer := by
    rw [List.map_take]
    simpa using (List.prefix_iff_eq_take.mp answerPrefix).symm
  have leftTakeAligned : IndexedRecordsAligned transitionFuel controller initial
      (right.take left.length) := by
    apply indexed_records_aligned_segment transitionFuel controller initial
      right [] (right.take left.length) (right.drop left.length)
    · simpa [controller] using rightAligned
    · simpa using (List.take_append_drop left.length right).symm
  have leftExact : left = right.take left.length :=
    indexed_records_aligned_eq_of_answer_maps_eq_generic transitionFuel
      controller initial left (right.take left.length)
        (by simpa [controller] using leftAligned) leftTakeAligned
        takeAnswers.symm
  have dropNonempty : right.drop left.length ≠ [] := by
    intro empty
    have lengthLe : right.length ≤ left.length := by
      have droppedLength : (right.drop left.length).length = 0 := by
        simp [empty]
      simp only [List.length_drop] at droppedLength
      omega
    omega
  obtain ⟨nextAnswerRecord, tailRecords, dropExact⟩ :=
    List.exists_cons_of_ne_nil dropNonempty
  have rightExact : right = left ++ nextAnswerRecord :: tailRecords := by
    calc
      right = right.take left.length ++ right.drop left.length :=
        (List.take_append_drop left.length right).symm
      _ = left ++ nextAnswerRecord :: tailRecords := by
        rw [← leftExact, dropExact]
  let before := indexedStateAfterRecords transitionFuel controller left initial
  have afterSeen :
      (controller.afterAnswer transitionFuel before nextAnswerRecord.answer
        ).memory.2.queryBatch.boundarySeen = true := by
    have armed := exact_candidate_boundary_arms_query_batch target
      (dagOf before.memory.1) before.memory.2
      (bytes continuation ++ [domAbsorb, queryBatchChallengeLabel])
      nextAnswerRecord.answer continuation leftUnseen leftEmpty leftAdvance rfl
    have seen := congrArg (fun memory => memory.boundarySeen) armed
    simp only [controller, IndexedUnifiedExposureController.afterAnswer,
      extendControllerThroughCandidateQueryBatch]
    rw [leftInput]
    exact seen
  have finalSeen := candidate_boundary_seen_persists_over_records
    transitionFuel target base dagOf tailRecords
      (controller.afterAnswer transitionFuel before nextAnswerRecord.answer)
      afterSeen
  have rightSeen : (indexedStateAfterRecords transitionFuel controller right
      initial).memory.2.queryBatch.boundarySeen = true := by
    rw [rightExact, indexed_state_after_records_append,
      indexed_state_after_records_cons]
    simpa [controller, before] using finalSeen
  have : false = true := rightUnseen.symm.trans (by
    simpa [controller] using rightSeen)
  contradiction

/-- The right compiler tape replays the complete left accepted-root prefix up
to (but not including) the selected query-batch answer. -/
theorem candidate_witness_boundary_prefix_replays
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (blockAdvance queryBatchDigest : Digest256)
        (prior later : List UnifiedExposureRecord) (actor : QueryActor)
        (leftRemaining rightRemaining : List Digest256),
      exactFixedRootRecords left.input.package.root =
        prior ++
          (.machineFresh actor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: later ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              right.answers)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              left.answers)) =
        prior.map UnifiedExposureRecord.answer ++ leftRemaining ∧
      (let base : IndexedUnifiedExposureController
          (globalFull256OracleCallCap parameters) Digest256
          FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
        candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val 0
       let controller := extendControllerThroughCandidateQueryBatch
          transitionFuel candidate base completeFoldAlphaQ16DagMemory
       let initial := exactCandidateDirectedQueryBatchInitialState left.input
       let beforeBoundary := indexedStateAfterRecords transitionFuel controller
          prior initial
       beforeBoundary.memory.2.q16.advances candidate = some blockAdvance ∧
         beforeBoundary.memory.2.queryBatch.boundarySeen = false ∧
         beforeBoundary.memory.2.queryBatch.producers = []) ∧
      (let base : IndexedUnifiedExposureController
          (globalFull256OracleCallCap parameters) Digest256
          FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
        candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val 0
       let controller := extendControllerThroughCandidateQueryBatch
          transitionFuel candidate base completeFoldAlphaQ16DagMemory
       let initial := exactCandidateDirectedQueryBatchInitialState left.input
       unifiedInputBeforeAnswer? transitionFuel
          (indexedStateAfterRecords transitionFuel controller prior
            initial).cursor =
        some (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])) := by
  obtain ⟨selectedRoom, selectedFinal⟩ := left.selected.2.1
  obtain ⟨boundaryFinal, target, blockAdvance, queryBatchDigest, prior, later,
      actor, rootExact, boundaryFinalExact, targetCounter, targetBlock,
      onlyBase, boundaryReady⟩ :=
    exact_selected_candidate_boundary_prior_has_only_base_labels
      transitionRoom left.input foldTrial 0
  have targetExact : target = candidate :=
    selected_terminal_slot_eq_witness_candidate left targetCounter targetBlock
  subst target
  have finalExact : boundaryFinal = finalTrial := by
    exact boundaryFinalExact.trans selectedFinal.symm
  subst boundaryFinal
  have baseExact := candidate_witnesses_have_equal_base_coordinates left right
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    exact_candidate_coordinates_force_pre_query_batch_prefix left.input
      foldTrial finalTrial candidate prior
      ((.machineFresh actor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) :: later)
      (by simpa only [List.cons_append] using rootExact) programmedCover
      right.answers baseExact (by simpa only [finalExact] using onlyBase)
  obtain ⟨leftRemaining, leftPrefix⟩ :=
    exact_candidate_coordinates_force_pre_query_batch_prefix left.input
      foldTrial finalTrial candidate prior
      ((.machineFresh actor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) :: later)
      (by simpa only [List.cons_append] using rootExact) programmedCover
      left.answers rfl (by simpa only [finalExact] using onlyBase)
  let base : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    candidateCompleteBaseController transitionFuel foldTrial.val finalTrial.val 0
  let controller := extendControllerThroughCandidateQueryBatch
    transitionFuel candidate base completeFoldAlphaQ16DagMemory
  let initial := exactCandidateDirectedQueryBatchInitialState left.input
  have alignedRaw :=
    exact_root_records_aligned_for_candidate_directed_controller left.input
      foldTrial finalTrial 0 candidate
  have aligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords left.input.package.root) := by
    simpa [controller, base, initial] using alignedRaw
  have selectedAligned := aligned prior
    (.machineFresh actor
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest)
    later rootExact
  have requestExact := aligned_machine_record_has_exact_input transitionFuel
    (indexedStateAfterRecords transitionFuel controller prior initial).cursor
    actor (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
    queryBatchDigest selectedAligned
  exact ⟨blockAdvance, queryBatchDigest, prior, later, actor, leftRemaining,
    rightRemaining, rootExact, rightPrefix, leftPrefix, by
      simpa [finalExact] using boundaryReady, by
      simpa only [UnifiedExposureRecord.answer] using requestExact⟩

/-- Two witnesses in the same candidate-directed fibre replay each other's
complete literal accepted-root prefix before the selected query-batch answer.
This symmetric form is the deterministic input needed by the subsequent
first-exposure alignment argument: it retains both concrete boundary
decompositions while making no equality claim about the two challenge
answers. -/
theorem candidate_witness_boundary_prefixes_mutually_replay
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (leftBlockAdvance leftQueryBatchDigest rightBlockAdvance
        rightQueryBatchDigest : Digest256)
        (leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord)
        (leftActor rightActor : QueryActor)
        (leftRemaining rightRemaining : List Digest256),
      exactFixedRootRecords left.input.package.root =
        leftPrior ++
          (.machineFresh leftActor
            (bytes leftBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            leftQueryBatchDigest : UnifiedExposureRecord) :: leftLater ∧
      exactFixedRootRecords right.input.package.root =
        rightPrior ++
          (.machineFresh rightActor
            (bytes rightBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            rightQueryBatchDigest : UnifiedExposureRecord) :: rightLater ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              right.answers)) =
        leftPrior.map UnifiedExposureRecord.answer ++ rightRemaining ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              left.answers)) =
        rightPrior.map UnifiedExposureRecord.answer ++ leftRemaining := by
  obtain ⟨leftBlockAdvance, leftQueryBatchDigest, leftPrior, leftLater,
      leftActor, _leftOwnRemaining, rightRemaining, leftRoot, rightReplaysLeft,
      _leftOwnPrefix, _leftUnseen, _leftRequest⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      left right
  obtain ⟨rightBlockAdvance, rightQueryBatchDigest, rightPrior, rightLater,
      rightActor, _rightOwnRemaining, leftRemaining, rightRoot, leftReplaysRight,
      _rightOwnPrefix, _rightUnseen, _rightRequest⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      right left
  exact ⟨leftBlockAdvance, leftQueryBatchDigest, rightBlockAdvance,
    rightQueryBatchDigest, leftPrior, leftLater, rightPrior, rightLater,
    leftActor, rightActor, leftRemaining, rightRemaining, leftRoot, rightRoot,
    rightReplaysLeft, leftReplaysRight⟩

/-- Two accepted witnesses in one candidate-directed fibre reach the selected
query-batch request after exactly the same literal source-record prefix.  This
is the adversary-first-safe replacement for assigning a logical role to a raw
SHA coordinate: equality follows from deterministic replay and the unique
boundary transition. -/
theorem candidate_witness_boundary_priors_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (leftBlockAdvance leftQueryBatchDigest rightBlockAdvance
        rightQueryBatchDigest : Digest256)
        (leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord)
        (leftActor rightActor : QueryActor),
      exactFixedRootRecords left.input.package.root =
        leftPrior ++
          (.machineFresh leftActor
            (bytes leftBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            leftQueryBatchDigest : UnifiedExposureRecord) :: leftLater ∧
      exactFixedRootRecords right.input.package.root =
        rightPrior ++
          (.machineFresh rightActor
            (bytes rightBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            rightQueryBatchDigest : UnifiedExposureRecord) :: rightLater ∧
      leftPrior = rightPrior ∧
      leftBlockAdvance = rightBlockAdvance := by
  obtain ⟨leftBlockAdvance, leftQueryBatchDigest, leftPrior, leftLater,
      leftActor, leftOwnRemaining, rightRemaining, leftRoot, rightReplaysLeft,
      leftOwnPrefix, leftReadyRaw, leftRequestRaw⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      left right
  obtain ⟨rightBlockAdvance, rightQueryBatchDigest, rightPrior, rightLater,
      rightActor, rightOwnRemaining, leftRemaining, rightRoot, leftReplaysRight,
      rightOwnPrefix, rightReadyRaw, rightRequestRaw⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      right left
  let base : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    candidateCompleteBaseController transitionFuel foldTrial.val finalTrial.val 0
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    candidate base completeFoldAlphaQ16DagMemory
  let initial := exactCandidateDirectedQueryBatchInitialState left.input
  have leftAlignedFullRaw :=
    exact_root_records_aligned_for_candidate_directed_controller left.input
      foldTrial finalTrial 0 candidate
  have leftAlignedFull : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords left.input.package.root) := by
    simpa [controller, base, initial] using leftAlignedFullRaw
  have rightAlignedFullRaw :=
    exact_root_records_aligned_for_candidate_directed_controller right.input
      foldTrial finalTrial 0 candidate
  have rightAlignedFull : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords right.input.package.root) := by
    simpa [controller, base, initial,
      exactCandidateDirectedQueryBatchInitialState] using rightAlignedFullRaw
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      leftPrior :=
    indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords left.input.package.root) [] leftPrior
      ((.machineFresh leftActor
        (bytes leftBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        leftQueryBatchDigest : UnifiedExposureRecord) :: leftLater)
      leftAlignedFull (by simpa only [List.nil_append] using leftRoot)
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      rightPrior :=
    indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords right.input.package.root) [] rightPrior
      ((.machineFresh rightActor
        (bytes rightBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        rightQueryBatchDigest : UnifiedExposureRecord) :: rightLater)
      rightAlignedFull (by simpa only [List.nil_append] using rightRoot)
  obtain ⟨leftAdvance, leftUnseen, leftEmpty⟩ :
      (indexedStateAfterRecords transitionFuel controller leftPrior initial
        ).memory.2.q16.advances candidate = some leftBlockAdvance ∧
      (indexedStateAfterRecords transitionFuel controller leftPrior initial
        ).memory.2.queryBatch.boundarySeen = false ∧
      (indexedStateAfterRecords transitionFuel controller leftPrior initial
        ).memory.2.queryBatch.producers = [] := by
    simpa [controller, base, initial] using leftReadyRaw
  obtain ⟨rightAdvance, rightUnseen, rightEmpty⟩ :
      (indexedStateAfterRecords transitionFuel controller rightPrior initial
        ).memory.2.q16.advances candidate = some rightBlockAdvance ∧
      (indexedStateAfterRecords transitionFuel controller rightPrior initial
        ).memory.2.queryBatch.boundarySeen = false ∧
      (indexedStateAfterRecords transitionFuel controller rightPrior initial
        ).memory.2.queryBatch.producers = [] := by
    simpa [controller, base, initial,
      exactCandidateDirectedQueryBatchInitialState] using rightReadyRaw
  have leftRequest : unifiedInputBeforeAnswer? transitionFuel
      (indexedStateAfterRecords transitionFuel controller leftPrior initial
        ).cursor =
      some (bytes leftBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel]) := by
    simpa [controller, base, initial] using leftRequestRaw
  have rightRequest : unifiedInputBeforeAnswer? transitionFuel
      (indexedStateAfterRecords transitionFuel controller rightPrior initial
        ).cursor =
      some (bytes rightBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel]) := by
    simpa [controller, base, initial,
      exactCandidateDirectedQueryBatchInitialState] using rightRequestRaw
  have rightLeLeft : rightPrior.length ≤ leftPrior.length :=
    candidate_boundary_ready_prefix_not_shorter transitionFuel candidate base
      completeFoldAlphaQ16DagMemory initial leftPrior rightPrior
      (freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters right.answers)))
      rightRemaining rightOwnRemaining leftBlockAdvance
      rightReplaysLeft rightOwnPrefix leftAligned rightAligned
      leftRequest leftAdvance leftUnseen leftEmpty rightUnseen
  have leftLeRight : leftPrior.length ≤ rightPrior.length :=
    candidate_boundary_ready_prefix_not_shorter transitionFuel candidate base
      completeFoldAlphaQ16DagMemory initial rightPrior leftPrior
      (freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters left.answers)))
      leftRemaining leftOwnRemaining rightBlockAdvance
      leftReplaysRight leftOwnPrefix rightAligned leftAligned
      rightRequest rightAdvance rightUnseen rightEmpty leftUnseen
  have lengthExact : leftPrior.length = rightPrior.length :=
    Nat.le_antisymm leftLeRight rightLeLeft
  have leftAnswersTake : List.take leftPrior.length
      (freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters right.answers))) =
      leftPrior.map UnifiedExposureRecord.answer := by
    rw [rightReplaysLeft]
    simp
  have rightAnswersTake : List.take rightPrior.length
      (freshAnswerTapeToList
        (foldAlphaQ16QueryBatchNamedSlotInputTape
          (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters right.answers))) =
      rightPrior.map UnifiedExposureRecord.answer := by
    rw [rightOwnPrefix]
    simp
  have answersExact : leftPrior.map UnifiedExposureRecord.answer =
      rightPrior.map UnifiedExposureRecord.answer := by
    rw [← leftAnswersTake, lengthExact, rightAnswersTake]
  have priorExact : leftPrior = rightPrior :=
    indexed_records_aligned_eq_of_answer_maps_eq_generic transitionFuel
      controller initial leftPrior rightPrior leftAligned rightAligned answersExact
  have requestPayloadExact :
      bytes leftBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel] =
        bytes rightBlockAdvance ++ [domAbsorb, queryBatchChallengeLabel] := by
    apply Option.some.inj
    rw [priorExact] at leftRequest
    exact leftRequest.symm.trans rightRequest
  have blockAdvanceExact : leftBlockAdvance = rightBlockAdvance := by
    apply digest_bytes_injective
    exact List.append_cancel_right requestPayloadExact
  exact ⟨leftBlockAdvance, leftQueryBatchDigest, rightBlockAdvance,
    rightQueryBatchDigest, leftPrior, leftLater, rightPrior, rightLater,
    leftActor, rightActor, leftRoot, rightRoot, priorExact, blockAdvanceExact⟩

/-- Replaying the left boundary prefix on the right tape reaches the literal
left query-batch request before consuming its answer.  The request is
recovered from the scheduler cursor, rather than inferred from a logical
role attached after the hash lookup. -/
theorem candidate_witness_boundary_request_replays
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    ∃ (blockAdvance queryBatchDigest : Digest256)
        (prior later : List UnifiedExposureRecord) (actor : QueryActor)
        (rightRemaining : List Digest256),
      exactFixedRootRecords left.input.package.root =
        prior ++
          (.machineFresh actor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: later ∧
      freshAnswerTapeToList
          (foldAlphaQ16QueryBatchNamedSlotInputTape
            (exactCompilerFoldAlphaQ16QueryBatchInputTape parameters
              right.answers)) =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining ∧
      let base : IndexedUnifiedExposureController
          (globalFull256OracleCallCap parameters) Digest256
          FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
        candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val 0
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel candidate base completeFoldAlphaQ16DagMemory
      let initial := exactCandidateDirectedQueryBatchInitialState left.input
      unifiedInputBeforeAnswer? transitionFuel
          (indexedStateAfterRecords transitionFuel controller prior
            initial).cursor =
        some (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel]) := by
  obtain ⟨blockAdvance, queryBatchDigest, prior, later, actor,
      _leftRemaining, rightRemaining, rootExact, rightPrefix, _leftPrefix,
      _boundaryUnseen,
      requestExact⟩ :=
    candidate_witness_boundary_prefix_replays transitionRoom programmedCover
      left right
  exact ⟨blockAdvance, queryBatchDigest, prior, later, actor, rightRemaining,
    rootExact, rightPrefix, requestExact⟩

#print axioms candidate_witness_boundary_prefix_replays
#print axioms candidate_witness_boundary_prefixes_mutually_replay
#print axioms candidate_witness_boundary_priors_eq
#print axioms candidate_witness_boundary_request_replays

end
end AspisK1.V7Tag73K13CandidateBoundaryPrefixReplay
