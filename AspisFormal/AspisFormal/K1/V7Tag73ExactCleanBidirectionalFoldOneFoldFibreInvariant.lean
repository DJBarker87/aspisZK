import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreTarget
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorFinalProfile
import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldRootInvariant
import AspisFormal.K1.V7Tag73PreQ16PrefixWordStability

/-!
# Corrected clean one-fold fibre invariant

This file names the exact deterministic source theorem still required after
the chronological replay refactor, and proves that theorem is sufficient for
all three component facts consumed by the bidirectional work-times-degree-three
probability bound.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldComponents
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreTarget
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactCleanBidirectionalFoldPairPriorInvariant
open AspisK1.V7Tag73ExactCleanBidirectionalFoldRootInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldOneFoldComponentMembership
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TargetInventory
open AspisK1.V7Tag73PreQ16PrefixWordStability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

private theorem inverse_entry_unique
    (multiplier : QM31Exact) (left right : M31Exact)
    (leftExact : multiplier * algebraMap M31Exact QM31Exact left = 1)
    (rightExact : multiplier * algebraMap M31Exact QM31Exact right = 1) :
    left = right := by
  apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
  have multiplierNonzero : multiplier ≠ 0 := by
    intro zero
    rw [zero] at leftExact
    norm_num at leftExact
  apply mul_left_cancel₀ multiplierNonzero
  exact leftExact.trans rightExact.symm

/-- Lightweight fieldwise uniqueness used here instead of importing the
concrete canonical-schedule aggregate. -/
private theorem exact_one_fold_schedule_unique_from_tables
    (left right : ExactSchedule)
    (alphaExact : left.alpha = right.alpha)
    (leftTables : ExactOneFoldInverseTables left)
    (rightTables : ExactOneFoldInverseTables right) :
    left = right := by
  cases left with
  | mk leftAlpha leftX leftY =>
      cases right with
      | mk rightAlpha rightX rightY =>
          dsimp only at alphaExact leftTables rightTables ⊢
          have xExact : leftX = rightX := by
            funext index
            exact inverse_entry_unique (2 * exactCircleX index)
              (leftX index) (rightX index) (leftTables.1 index)
              (rightTables.1 index)
          have yExact : leftY = rightY := by
            funext index
            exact inverse_entry_unique (2 * exactCircleY index)
              (leftY index) (rightY index) (leftTables.2 index)
              (rightTables.2 index)
          cases alphaExact
          cases xExact
          cases yExact
          rfl

/-- Exact semantic data which is fixed on one clean residual/fold fibre.
These are precisely the fields read before or at alpha by the one-fold
algebraic reduction; no q16 coordinate or completed-transcript word occurs. -/
def ExactCleanBidirectionalK13OneFoldFibreInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    (let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).1) →
    (let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).2.1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).2.1) →
    leftWitness.failure.words = rightWitness.failure.words ∧
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma ∧
      (exactK13ParsedProof rightWitness.input).schedule =
        scheduleAtAlpha (exactK13ParsedProof leftWitness.input).schedule
          (exactOperationalChallenge rightWitness.input (.alpha 0))

/-- The source-checked inverse tables make the non-alpha schedule fields
canonical.  Therefore changing only alpha in the left schedule yields exactly
the right schedule, without any transcript or probability premise. -/
theorem exact_scheduleAtAlpha_eq_of_source_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    {leftDecoded rightDecoded : Fin 641 → QM31Exact}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftBinding : ExactParsedProofSourceBinding left leftDecoded)
    (rightBinding : ExactParsedProofSourceBinding right rightDecoded) :
    (exactK13ParsedProof right).schedule =
      scheduleAtAlpha (exactK13ParsedProof left).schedule
        (exactOperationalChallenge right (.alpha 0)) := by
  apply exact_one_fold_schedule_unique_from_tables
  · exact rightBinding.alphaZeroExact
  · exact rightBinding.inverseTablesExact
  · exact ⟨leftBinding.inverseTablesExact.1,
      leftBinding.inverseTablesExact.2⟩

/-- After canonical schedule functionality, the genuinely causal remainder is
only the chronological word and gamma. -/
def ExactCleanBidirectionalK13OneFoldWordsGammaInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    (let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).1) →
    (let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).2.1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).2.1) →
    leftWitness.failure.words = rightWitness.failure.words ∧
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma

/-- The broad causal Merkle-target complement fixes the entire completed word
between either proof-relevant anchor and the full root trace.  Both traces can
therefore be compared through their common fold-pair prefix, where residual
equality also fixes the authenticated roots. -/
theorem exact_clean_bidirectional_pair_words_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1) :
    leftWitness.failure.words = rightWitness.failure.words := by
  obtain ⟨leftPrior, leftLater, rightPrior, rightLater, leftActor,
      rightActor, leftTarget, rightTarget, leftAnswer, rightAnswer,
      leftRootExact, rightRootExact, _leftTrialExact, _rightTrialExact,
      leftRole, rightRole, priorExact⟩ :=
    exact_clean_bidirectional_pair_anchor_priors_eq trial hidden left right
      leftWitness rightWitness programmedCover residualExact
  subst rightPrior
  have rootsExact := exact_clean_bidirectional_pair_k12_roots_eq transitionRoom
    trial hidden left right leftWitness rightWitness programmedCover
      residualExact
  have leftPairRoots := exact_accepted_fold_anchor_k12_roots_mem
    transitionRoom leftWitness.input leftWitness.fold leftPrior leftLater
      leftActor leftTarget leftAnswer leftRootExact leftRole
  have rightPairRoots := exact_accepted_fold_anchor_k12_roots_mem
    transitionRoom rightWitness.input rightWitness.fold leftPrior rightLater
      rightActor rightTarget rightAnswer rightRootExact rightRole
  have leftFinalRoots := exact_actual_trial_k12_roots_mem transitionRoom
    leftWitness.input leftWitness.failure.anchor.trial
      leftWitness.failure.anchor.actual leftWitness.failure.anchor.prior
      leftWitness.failure.anchor.later leftWitness.failure.anchor.pivotActor
      leftWitness.failure.anchor.pivotInput
      leftWitness.failure.anchor.pivotAnswer
      leftWitness.failure.anchor.rootExact
      leftWitness.failure.anchor.trialExact
  have rightFinalRoots := exact_actual_trial_k12_roots_mem transitionRoom
    rightWitness.input rightWitness.failure.anchor.trial
      rightWitness.failure.anchor.actual rightWitness.failure.anchor.prior
      rightWitness.failure.anchor.later rightWitness.failure.anchor.pivotActor
      rightWitness.failure.anchor.pivotInput
      rightWitness.failure.anchor.pivotAnswer
      rightWitness.failure.anchor.rootExact
      rightWitness.failure.anchor.trialExact
  have leftPairStable := exact_preQ16PrefixWords_append_eq_of_no_target
    leftWitness.input leftPrior
      ((.machineFresh leftActor leftTarget leftAnswer :
        UnifiedExposureRecord) :: leftLater)
      (by simpa only [List.cons_append] using leftRootExact)
      (exactK12Roots leftWitness.input) leftPairRoots.1 leftPairRoots.2
      leftWitness.noMerkleTarget
  have rightPairStable := exact_preQ16PrefixWords_append_eq_of_no_target
    rightWitness.input leftPrior
      ((.machineFresh rightActor rightTarget rightAnswer :
        UnifiedExposureRecord) :: rightLater)
      (by simpa only [List.cons_append] using rightRootExact)
      (exactK12Roots rightWitness.input) rightPairRoots.1 rightPairRoots.2
      rightWitness.noMerkleTarget
  have leftFinalStable := exact_preQ16PrefixWords_append_eq_of_no_target
    leftWitness.input leftWitness.failure.anchor.prior
      ((.machineFresh leftWitness.failure.anchor.pivotActor
          leftWitness.failure.anchor.pivotInput
          leftWitness.failure.anchor.pivotAnswer : UnifiedExposureRecord) ::
        leftWitness.failure.anchor.later)
      (by simpa only [List.cons_append] using
        leftWitness.failure.anchor.rootExact)
      (exactK12Roots leftWitness.input) leftFinalRoots.1 leftFinalRoots.2
      leftWitness.noMerkleTarget
  have rightFinalStable := exact_preQ16PrefixWords_append_eq_of_no_target
    rightWitness.input rightWitness.failure.anchor.prior
      ((.machineFresh rightWitness.failure.anchor.pivotActor
          rightWitness.failure.anchor.pivotInput
          rightWitness.failure.anchor.pivotAnswer : UnifiedExposureRecord) ::
        rightWitness.failure.anchor.later)
      (by simpa only [List.cons_append] using
        rightWitness.failure.anchor.rootExact)
      (exactK12Roots rightWitness.input) rightFinalRoots.1 rightFinalRoots.2
      rightWitness.noMerkleTarget
  rw [← leftRootExact] at leftPairStable
  rw [← rightRootExact] at rightPairStable
  rw [← leftWitness.failure.anchor.rootExact] at leftFinalStable
  rw [← rightWitness.failure.anchor.rootExact] at rightFinalStable
  calc
    leftWitness.failure.words =
        preQ16PrefixWords leftWitness.failure.anchor.prior
          (exactK12Roots leftWitness.input) := leftWitness.failure.wordsExact
    _ = preQ16PrefixWords
          (exactFixedRootRecords leftWitness.input.package.root)
          (exactK12Roots leftWitness.input) := leftFinalStable.symm
    _ = preQ16PrefixWords leftPrior
          (exactK12Roots leftWitness.input) := leftPairStable
    _ = preQ16PrefixWords leftPrior
          (exactK12Roots rightWitness.input) := by rw [rootsExact]
    _ = preQ16PrefixWords
          (exactFixedRootRecords rightWitness.input.package.root)
          (exactK12Roots rightWitness.input) := rightPairStable.symm
    _ = preQ16PrefixWords rightWitness.failure.anchor.prior
          (exactK12Roots rightWitness.input) := rightFinalStable
    _ = rightWitness.failure.words := rightWitness.failure.wordsExact.symm

/-- The chronological word theorem and the retained literal gamma binding
give the complete causal invariant required by the one-fold reduction.  The
production source provider is used only to identify the parsed gamma with the
operationally decoded gamma on each accepting run. -/
theorem exact_clean_onefold_words_gamma_invariant_of_source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance) :
    ExactCleanBidirectionalK13OneFoldWordsGammaInvariant transitionFuel
      configuration projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact _foldExact
  have wordsExact := exact_clean_bidirectional_pair_words_eq transitionRoom
    programmedCover trial hidden left right leftWitness rightWitness
      residualExact
  obtain ⟨leftDecoded, _leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.input
  obtain ⟨rightDecoded, _rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.input
  have operationalGammaExact :=
    exact_clean_bidirectional_pair_operational_gamma_eq transitionRoom trial
      hidden left right leftWitness rightWitness programmedCover residualExact
  exact ⟨wordsExact,
    leftBinding.gammaExact.trans
      (operationalGammaExact.trans rightBinding.gammaExact.symm)⟩

/-- The already-required production source provider discharges schedule
functionality, so the word/gamma causal invariant implies the full fibre
invariant consumed by target transport. -/
theorem exact_clean_onefold_fibre_invariant_of_words_gamma
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (causal : ExactCleanBidirectionalK13OneFoldWordsGammaInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactCleanBidirectionalK13OneFoldFibreInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro trial hidden left right leftWitness rightWitness residualExact foldExact
  obtain ⟨wordsExact, gammaExact⟩ := causal trial hidden left right leftWitness
    rightWitness residualExact foldExact
  obtain ⟨leftDecoded, _leftDecode, leftBinding⟩ :=
    source (hidden, left) leftWitness.input
  obtain ⟨rightDecoded, _rightDecode, rightBinding⟩ :=
    source (hidden, right) rightWitness.input
  exact ⟨wordsExact, gammaExact,
    exact_scheduleAtAlpha_eq_of_source_bindings leftWitness.input
      rightWitness.input leftBinding rightBinding⟩

/-- Canonical representative context selected from the already-required
production decoded/source provider.  Keeping this choice behind one definition
prevents the probability layer from re-elaborating the dependent existential. -/
noncomputable def exactCleanBidirectionalOneFoldContextOfSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (sample : ExactCompilerSample HiddenTape parameters)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (words : ExtractedWords)
    (skeleton : Tag73OrdinarySamplerSkeleton) :
    ExactCausalOneFoldSamplerContext :=
  let supplied := source sample input
  let decoded := Classical.choose supplied
  let binding : ExactParsedProofSourceBinding input decoded :=
    (Classical.choose_spec supplied).2
  exactAcceptedFoldOneFoldContext decoder initialEncoderExact finalEncoderExact
    words input fold binding skeleton

#print axioms ExactCleanBidirectionalK13OneFoldFibreInvariant
#print axioms exact_scheduleAtAlpha_eq_of_source_bindings
#print axioms ExactCleanBidirectionalK13OneFoldWordsGammaInvariant
#print axioms exact_clean_bidirectional_pair_words_eq
#print axioms exact_clean_onefold_words_gamma_invariant_of_source
#print axioms exact_clean_onefold_fibre_invariant_of_words_gamma
#print axioms exactCleanBidirectionalOneFoldContextOfSource

end

end AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreInvariant
