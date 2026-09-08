import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreInvariant

/-! # Fibre invariant to exact one-fold target membership -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldInvariantTarget

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreInvariant
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreTarget
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldComponents
open AspisK1.V7Tag73ExactCleanBidirectionalFoldRootInvariant
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73FoldOneFoldComponentMembership
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One application of the complete fibre invariant supplies the exact three
equalities required by the executable target-transport theorem. -/
theorem exact_clean_onefold_target_member_of_invariant
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
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (leftDecoded : Fin 641 → QM31Exact)
    (leftSource : ExactParsedProofSourceBinding leftWitness.input leftDecoded)
    (rightDecoded : Fin 641 → QM31Exact)
    (rightSource : ExactParsedProofSourceBinding rightWitness.input rightDecoded)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).2.1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).2.1) :
    successfulOrdinaryExactValue
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
          rightWitness.input rightWitness.fold) ∈
      exactRawOneFoldTarget
        (exactAcceptedFoldOneFoldContext decoder initialEncoderExact
          finalEncoderExact leftWitness.failure.words leftWitness.input
          leftWitness.fold leftSource)
        (successfulOrdinaryExactFactorization
          (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
            rightWitness.input rightWitness.fold)).1 := by
  have wordsExact := exact_clean_bidirectional_pair_words_eq transitionRoom
    programmedCover trial hidden left right leftWitness rightWitness
      residualExact
  have operationalGammaExact :=
    exact_clean_bidirectional_pair_operational_gamma_eq transitionRoom trial
      hidden left right leftWitness rightWitness programmedCover residualExact
  have gammaExact := leftSource.gammaExact.trans
    (operationalGammaExact.trans rightSource.gammaExact.symm)
  have scheduleExact := exact_scheduleAtAlpha_eq_of_source_bindings
    leftWitness.input rightWitness.input leftSource rightSource
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover rightWitness.input rightWitness.fold
  let oracle := exactAcceptedFoldReplayOracle leftWitness.failure.words
    leftWitness.input leftWitness.fold
  have proofExact : oracle.proof? actual =
      some (exactK13ParsedProof rightWitness.input) :=
    exactBidirectionalFoldOneFoldReplayOracle_crossProof_inputs transitionRoom
      programmedCover leftWitness.failure.words leftWitness.input
        rightWitness.input leftWitness.fold rightWitness.fold
          leftWitness.trialExact rightWitness.trialExact residualExact foldExact
            gammaExact scheduleExact
  have failure := rightWitness.failure.failure
  rw [← wordsExact] at failure
  have bad := actual_oneFold_failure_is_counterfactual_bad_response decoder
    (exactOneFoldAlgebraBinding (exactK13ParsedProof leftWitness.input).schedule
      (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
      leftSource.inverseTablesExact)
    oracle actual (exactK13ParsedProof rightWitness.input) proofExact failure
  rw [exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext]
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad

/-- Package target transport together with the literal successful-alpha and
31-bit-work facts into the compact component predicate consumed by the
probability layer. -/
theorem exact_clean_onefold_component_facts_of_pair
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
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (source : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).1)
    (foldExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).2.1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).2.1) :
    let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    FoldOneFoldComponentFacts
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right)
      (exactCleanBidirectionalOneFoldContextOfSource source initialEncoderExact
        finalEncoderExact (hidden, left) leftWitness.input leftWitness.fold
        leftWitness.failure.words) := by
  dsimp only
  let leftSupplied := source (hidden, left) leftWitness.input
  let leftDecoded := Classical.choose leftSupplied
  let leftSource : ExactParsedProofSourceBinding leftWitness.input leftDecoded :=
    (Classical.choose_spec leftSupplied).2
  let rightSupplied := source (hidden, right) rightWitness.input
  let rightDecoded := Classical.choose rightSupplied
  let rightSource : ExactParsedProofSourceBinding rightWitness.input
      rightDecoded := (Classical.choose_spec rightSupplied).2
  have succeeds := exact_clean_preQ16_onefold_alpha_succeeds transitionRoom
    programmedCover rightWitness
  have workAccepted := exact_clean_preQ16_onefold_work_accepted programmedCover
    rightWitness
  have coordinateExact :=
    exact_clean_preQ16_onefold_coordinate_eq_accepted rightWitness
  refine ⟨succeeds, workAccepted, ?_⟩
  let coordinateRaw : SuccessfulTag73RawStream :=
    ⟨fourGammaBlocksRawEquiv
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration hidden).erase)
        right).2.2, succeeds⟩
  have rawExact : coordinateRaw =
      exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
        rightWitness.input rightWitness.fold := by
    apply Subtype.ext
    change fourGammaBlocksRawEquiv
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
          (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
            trial.val (exactPlainRomCursor configuration hidden).erase)
          right).2.2 =
      fourGammaBlocksRawEquiv
        (exactAcceptedFoldBidirectionalCoordinates rightWitness.input
          rightWitness.fold).2.2
    rw [coordinateExact]
  change successfulOrdinaryExactValue coordinateRaw ∈
    exactRawOneFoldTarget
      (exactAcceptedFoldOneFoldContext decoder initialEncoderExact
        finalEncoderExact leftWitness.failure.words leftWitness.input
        leftWitness.fold leftSource)
      (successfulOrdinaryExactFactorization coordinateRaw).1
  rw [rawExact]
  have wordsExact := exact_clean_bidirectional_pair_words_eq transitionRoom
    programmedCover trial hidden left right leftWitness rightWitness
      residualExact
  have operationalGammaExact :=
    exact_clean_bidirectional_pair_operational_gamma_eq transitionRoom trial
      hidden left right leftWitness rightWitness programmedCover residualExact
  have gammaExact := leftSource.gammaExact.trans
    (operationalGammaExact.trans rightSource.gammaExact.symm)
  have scheduleExact := exact_scheduleAtAlpha_eq_of_source_bindings
    leftWitness.input rightWitness.input leftSource rightSource
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover rightWitness.input rightWitness.fold
  let oracle := exactAcceptedFoldReplayOracle leftWitness.failure.words
    leftWitness.input leftWitness.fold
  have proofExact : oracle.proof? actual =
      some (exactK13ParsedProof rightWitness.input) :=
    exactBidirectionalFoldOneFoldReplayOracle_crossProof_inputs transitionRoom
      programmedCover leftWitness.failure.words leftWitness.input
        rightWitness.input leftWitness.fold rightWitness.fold
          leftWitness.trialExact rightWitness.trialExact residualExact foldExact
            gammaExact scheduleExact
  have failure := rightWitness.failure.failure
  rw [← wordsExact] at failure
  have bad := actual_oneFold_failure_is_counterfactual_bad_response decoder
    (exactOneFoldAlgebraBinding (exactK13ParsedProof leftWitness.input).schedule
      (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
      leftSource.inverseTablesExact)
    oracle actual (exactK13ParsedProof rightWitness.input) proofExact failure
  rw [exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext]
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad

#print axioms exact_clean_onefold_target_member_of_invariant
#print axioms exact_clean_onefold_component_facts_of_pair

end


end AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldInvariantTarget
