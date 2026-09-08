import AspisFormal.K1.V7Tag73ExactBidirectionalFoldPreAnchorResidualPrefix
import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
import AspisFormal.K1.V7Tag73ExactPairCoordinateProfileInvariant

/-!
# Clean bidirectional fold pair-prior invariant

Equality of the five-slot controller's residual coordinate fixes the literal
accepted-root prefix before the selected fold/boundary pair anchor.  This is
the pre-alpha source invariant needed by the corrected one-fold argument; it
does not assert that the later pre-q16 transcript remains fixed while alpha
changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldPairPriorInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldPreAnchorResidualPrefix
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPairCoordinateProfileInvariant
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equal residual coordinates give equal literal record prefixes at the
selected fold/boundary pair anchor.  The selected member and its actor may
differ; only the preceding source history is fixed. -/
theorem exact_clean_bidirectional_pair_anchor_priors_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1) :
    ∃ leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord,
      ∃ leftActor rightActor : QueryActor,
      ∃ leftTarget rightTarget : ShaInput,
      ∃ leftAnswer rightAnswer : Digest256,
        exactFixedRootRecords leftWitness.input.package.root =
            leftPrior ++ (.machineFresh leftActor leftTarget leftAnswer :
              UnifiedExposureRecord) :: leftLater ∧
        exactFixedRootRecords rightWitness.input.package.root =
            rightPrior ++ (.machineFresh rightActor rightTarget rightAnswer :
              UnifiedExposureRecord) :: rightLater ∧
        trial.val = leftPrior.length ∧
        trial.val = rightPrior.length ∧
        ((leftTarget = selectedFoldWorkInput leftWitness.input
              leftWitness.fold ∧ leftAnswer = leftWitness.fold.answer) ∨
          (leftTarget = selectedFoldBoundaryInput leftWitness.input
              leftWitness.fold ∧
            leftAnswer = leftWitness.fold.boundaryAnswer)) ∧
        ((rightTarget = selectedFoldWorkInput rightWitness.input
              rightWitness.fold ∧ rightAnswer = rightWitness.fold.answer) ∨
          (rightTarget = selectedFoldBoundaryInput rightWitness.input
              rightWitness.fold ∧
            rightAnswer = rightWitness.fold.boundaryAnswer)) ∧
        leftPrior = rightPrior := by
  have leftLabeled : ExactAcceptedFoldPairLabeled leftWitness.input
      leftWitness.fold trial := by
    have labeled := exactAcceptedFoldPairTrial_labeled leftWitness.input
      leftWitness.fold
    rwa [leftWitness.trialExact] at labeled
  have rightLabeled : ExactAcceptedFoldPairLabeled rightWitness.input
      rightWitness.fold trial := by
    have labeled := exactAcceptedFoldPairTrial_labeled rightWitness.input
      rightWitness.fold
    rwa [rightWitness.trialExact] at labeled
  obtain ⟨leftPrior, leftLater, leftActor, leftTarget, leftAnswer,
      leftRootExact, leftTrialExact, leftRole⟩ :=
    exact_accepted_fold_pair_labeled_anchor_decomposition leftWitness.input
      leftWitness.fold trial leftLabeled
  obtain ⟨rightPrior, rightLater, rightActor, rightTarget, rightAnswer,
      rightRootExact, rightTrialExact, rightRole⟩ :=
    exact_accepted_fold_pair_labeled_anchor_decomposition rightWitness.input
      rightWitness.fold trial rightLabeled
  have rightTapeFromLeft : ∃ remaining,
      freshAnswerTapeToList right =
        leftPrior.map UnifiedExposureRecord.answer ++ remaining := by
    apply exact_bidirectional_residual_coordinate_forces_pre_anchor_tape_prefix
      leftWitness.input trial leftPrior
        ((.machineFresh leftActor leftTarget leftAnswer :
          UnifiedExposureRecord) :: leftLater)
    · simpa only [List.cons_append] using leftRootExact
    · exact leftTrialExact
    · exact programmedCover
    · exact residualExact
  have priorExact : leftPrior = rightPrior :=
    exact_fixed_k13_selected_root_priors_eq_of_right_tape_prefix trial hidden
      left right leftWitness.input rightWitness.input leftPrior leftLater
      rightPrior rightLater leftActor rightActor leftTarget rightTarget
      leftAnswer rightAnswer leftRootExact rightRootExact leftTrialExact
      rightTrialExact rightTapeFromLeft
  exact ⟨leftPrior, leftLater, rightPrior, rightLater, leftActor, rightActor,
    leftTarget, rightTarget, leftAnswer, rightAnswer, leftRootExact,
    rightRootExact, leftTrialExact, rightTrialExact, leftRole, rightRole,
    priorExact⟩

/-- At the common pre-alpha controller state, the selected member of the
fold-work/boundary pair has the same literal SHA input.  Hence the two fibres
cannot silently choose different members of the pair at the same trial. -/
theorem exact_clean_bidirectional_pair_anchor_selected_inputs_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1) :
    ∃ leftPrior leftLater rightPrior rightLater : List UnifiedExposureRecord,
      ∃ leftActor rightActor : QueryActor,
      ∃ leftTarget rightTarget : ShaInput,
      ∃ leftAnswer rightAnswer : Digest256,
        exactFixedRootRecords leftWitness.input.package.root =
            leftPrior ++ (.machineFresh leftActor leftTarget leftAnswer :
              UnifiedExposureRecord) :: leftLater ∧
        exactFixedRootRecords rightWitness.input.package.root =
            rightPrior ++ (.machineFresh rightActor rightTarget rightAnswer :
              UnifiedExposureRecord) :: rightLater ∧
        trial.val = leftPrior.length ∧
        trial.val = rightPrior.length ∧
        (leftTarget = selectedFoldWorkInput leftWitness.input leftWitness.fold ∨
          leftTarget = selectedFoldBoundaryInput leftWitness.input
            leftWitness.fold) ∧
        (rightTarget = selectedFoldWorkInput rightWitness.input
            rightWitness.fold ∨
          rightTarget = selectedFoldBoundaryInput rightWitness.input
            rightWitness.fold) ∧
        leftPrior = rightPrior ∧ leftTarget = rightTarget := by
  obtain ⟨leftPrior, leftLater, rightPrior, rightLater, leftActor, rightActor,
      leftTarget, rightTarget, leftAnswer, rightAnswer, leftRootExact,
      rightRootExact, leftTrialExact, rightTrialExact, leftRole, rightRole,
      priorExact⟩ :=
    exact_clean_bidirectional_pair_anchor_priors_eq trial hidden left right
      leftWitness rightWitness programmedCover residualExact
  have commonPrior := priorExact
  subst rightPrior
  let controller := bidirectionalFoldAlphaController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel trial.val
  let initial := bidirectionalFoldAlphaInitialState
    (exactPlainRomCursor configuration hidden).erase
  have leftAlignedRaw :=
    exact_root_records_aligned_for_bidirectional_fold_controller
      leftWitness.input trial
  have rightAlignedRaw :=
    exact_root_records_aligned_for_bidirectional_fold_controller
      rightWitness.input trial
  have leftAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords leftWitness.input.package.root) := by
    simpa [controller, initial] using leftAlignedRaw
  have rightAligned : IndexedRecordsAligned transitionFuel controller initial
      (exactFixedRootRecords rightWitness.input.package.root) := by
    simpa [controller, initial] using rightAlignedRaw
  have leftSelectedAligned := leftAligned leftPrior
    (.machineFresh leftActor leftTarget leftAnswer) leftLater leftRootExact
  have rightSelectedAligned := rightAligned leftPrior
    (.machineFresh rightActor rightTarget rightAnswer) rightLater rightRootExact
  have leftInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    leftActor leftTarget leftAnswer leftSelectedAligned
  have rightInputAtCursor := aligned_machine_record_has_exact_input
    transitionFuel
    (indexedStateAfterRecords transitionFuel controller leftPrior initial).cursor
    rightActor rightTarget rightAnswer rightSelectedAligned
  have selectedInputExact : leftTarget = rightTarget :=
    Option.some.inj (leftInputAtCursor.symm.trans rightInputAtCursor)
  have leftSimple :
      leftTarget = selectedFoldWorkInput leftWitness.input leftWitness.fold ∨
        leftTarget = selectedFoldBoundaryInput leftWitness.input
          leftWitness.fold := leftRole.elim (fun work => Or.inl work.1)
            (fun boundary => Or.inr boundary.1)
  have rightSimple :
      rightTarget = selectedFoldWorkInput rightWitness.input
          rightWitness.fold ∨
        rightTarget = selectedFoldBoundaryInput rightWitness.input
          rightWitness.fold := rightRole.elim (fun work => Or.inl work.1)
            (fun boundary => Or.inr boundary.1)
  exact ⟨leftPrior, leftLater, leftPrior, rightLater, leftActor, rightActor,
    leftTarget, rightTarget, leftAnswer, rightAnswer, leftRootExact,
    rightRootExact, leftTrialExact, rightTrialExact, leftSimple, rightSimple, rfl,
    selectedInputExact⟩

/-- Equal residual coordinates fix the relation-round digest carried by both
members of the selected pair.  The mixed work/boundary cases are impossible
because their deployed SHA inputs have lengths 41 and 42 respectively. -/
theorem exact_clean_bidirectional_pair_anchor_fold_digest_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (trial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1) :
    leftWitness.fold.digest = rightWitness.fold.digest := by
  obtain ⟨_leftPrior, _leftLater, _rightPrior, _rightLater, _leftActor,
      _rightActor, leftTarget, rightTarget, _leftAnswer, _rightAnswer,
      _leftRootExact, _rightRootExact, _leftTrialExact, _rightTrialExact,
      leftRole, rightRole, _priorExact, targetExact⟩ :=
    exact_clean_bidirectional_pair_anchor_selected_inputs_eq trial hidden left
      right leftWitness rightWitness programmedCover residualExact
  rcases leftRole with leftWork | leftBoundary <;>
    rcases rightRole with rightWork | rightBoundary
  · rw [leftWork, rightWork] at targetExact
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) targetExact
    simpa [selectedFoldWorkInput, bytes_length] using prefixExact
  · rw [leftWork, rightBoundary] at targetExact
    have lengthExact := congrArg List.length targetExact
    simp [selectedFoldWorkInput, selectedFoldBoundaryInput, bytes_length] at lengthExact
  · rw [leftBoundary, rightWork] at targetExact
    have lengthExact := congrArg List.length targetExact
    simp [selectedFoldWorkInput, selectedFoldBoundaryInput, bytes_length] at lengthExact
  · rw [leftBoundary, rightBoundary] at targetExact
    apply digest_bytes_injective
    have prefixExact := congrArg (List.take 32) targetExact
    simpa [selectedFoldBoundaryInput, bytes_length] using prefixExact

#print axioms exact_clean_bidirectional_pair_anchor_priors_eq
#print axioms exact_clean_bidirectional_pair_anchor_selected_inputs_eq
#print axioms exact_clean_bidirectional_pair_anchor_fold_digest_eq

end

end AspisK1.V7Tag73ExactCleanBidirectionalFoldPairPriorInvariant
