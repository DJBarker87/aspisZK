import AspisFormal.K1.V7Tag73ExactInternalCurveProbability
import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldProbability
import AspisFormal.K1.V7Tag73K13BoundChallengeClosure
import AspisFormal.K1.V7Tag73K13JointBatchCausalSource
import AspisFormal.K1.V7Tag73K13RestrictedJointBatchActualLawClosure
import AspisFormal.K1.V7Tag73K13RestrictedLaterAlphaActualLawClosure
import AspisFormal.K1.V7Tag73PreQ16OperationalMeasuredComposition
import AspisFormal.K1.V7Tag73SuccessfulOneFoldConditioningBridge
import AspisFormal.K1.V7Tag73VariablePrefixK14Probability

/-!
# Actual-law bounds for corrected pre-q16 K1.3 and K1.4

The q16, query-batch, later-alpha, and causal-target bounds reuse their exact
deployed-coordinate theorems.  The one-fold and width-29 adapters below differ
only in the event being transported: it is the chronological pre-q16 word
rather than the later completed-transcript word.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16OperationalActualLawBounds

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldProbability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K13BoundChallengeClosure
open AspisK1.V7Tag73K13JointBatchCausalSource
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73K13RestrictedLaterAlphaActualLawClosure
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73PreQ16OperationalMeasuredComposition
open AspisK1.V7Tag73PreQ16OperationalStageAssembly
open AspisK1.V7Tag73PreQ16OperationalStageEvents
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisK1.V7Tag73SuccessfulOneFoldConditioningBridge
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisK1.V7Tag73VariablePrefixK14MeasureTransport
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Exact pre-alpha causal source for the chronological one-fold event. -/
structure ExactTag73RestrictedPreQ16OneFoldSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  context : HiddenTape → FreshAnswerTape Digest256
      (relationAlphaRouterResidual parameters) →
    Tag73CompleteOrdinarySamplerSkeleton → ExactCausalOneFoldSamplerContext
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactPreQ16K13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder) hidden ⊆
      (exactPlainRomAlphaZeroSamplerCoordinates transitionFuel configuration
          hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent Tag73DuplexOrdinarySucceeds
          (fun residual ↦ successfulTag73DuplexOrdinaryCoordinates ⁻¹'
            duplexOrdinaryDependentEvent
              (causalOneFoldSamplerTarget fun skeleton ↦
                (context hidden residual skeleton).toGeneric))

/-- Exact compiler-law bound for the chronological one-fold event. -/
theorem exact_tag73_restricted_preQ16_onefold_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (source : ExactTag73RestrictedPreQ16OneFoldSource transitionFuel
      configuration projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactPreQ16K13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder) ≤ exactOneFoldIdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩ exactPreQ16K13OneFoldEvent transitionFuel configuration
          projection fixedInstance decoder) ≤
      (foldChallengeCap : ENNReal) / ((P ^ 4 : Nat) : ENNReal)
  exact exact_compiler_dependent_onefold_event_probability_le
    (F := M31Exact) hiddenLaw (exactCompilerTargetCaps parameters).length
    Tag73DuplexOrdinarySucceeds
    (fun hidden ↦ exactPlainRomAlphaZeroSamplerCoordinates transitionFuel
      configuration hidden)
    successfulTag73DuplexOrdinaryCoordinates
    (fun hidden residual skeleton ↦
      (source.context hidden residual skeleton).toGeneric)
    (clean ∩ exactPreQ16K13OneFoldEvent transitionFuel configuration
      projection fixedInstance decoder)
    source.covered

/-- Exact causal-gamma source for the width-29 failure on the pre-q16 word. -/
structure ExactTag73RestrictedPreQ16K14Source
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  words : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    AspisPool.V7MerkleQueryExtractor.ExtractedWords
  provider : ∀ hidden residual,
    VariablePrefixK14Provider decoder (words hidden residual)
  covered : ∀ hidden,
    jointEventSlice
        (clean ∩ exactPreQ16K14Width29Event transitionFuel configuration
          projection fixedInstance decoder) hidden ⊆
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
          (exactPlainRomCursor configuration hidden).erase) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
            (variablePrefixK14FailureGammaTarget (provider hidden residual)))

/-- The kernel-proved V7 width-29 theorem bounds the corrected event. -/
theorem exact_tag73_restricted_preQ16_k14_probability_le
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (source : ExactTag73RestrictedPreQ16K14Source transitionFuel configuration
      projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactPreQ16K14Width29Event transitionFuel configuration
          projection fixedInstance decoder) ≤ exactK14IdealRawError := by
  change
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactPreQ16K14Width29Event transitionFuel configuration
          projection fixedInstance decoder) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)
  apply hidden_tape_variable_prefix_k14_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length
    (fun hidden ↦ exactCompilerGammaPrefixCoordinates parameters
      transitionFuel (exactPlainRomCursor configuration hidden).erase)
    (fun hidden residual ↦
      variablePrefixK14FailureGammaTarget (source.provider hidden residual))
    initialBatchChallengeCap
  · intro hidden residual skeleton
    exact variable_prefix_k14_failure_target_card_le initialEncoderExact
      AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7InitialPublishedWidth29CurveDecodability
      (source.provider hidden residual) skeleton
  · exact source.covered

/-- Release-facing actual-law K1.3 bound for the corrected stage package. -/
theorem exact_tag73_preQ16_operational_k13_clean_probability_le
    {HiddenTape TapeIdentity Observation Payload : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation V5PublicStatement Tag73K12ParsedProof Payload
      DecodedSpendWitness parameters)
    (projection : AcceptedTapeProjection V5PublicStatement Tag73K12ParsedProof
      Payload)
    (fixedInstance : PublicInstance V5PublicStatement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (decoderBinding : InitialProjectionBinding decoder)
    (basis : Basis (Fin 4) F QM31Exact) (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (environment : ExactPreQ16OperationalStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (jointBatchSource : ExactTag73K13JointBatchCausalSource transitionFuel
      configuration projection fixedInstance decoder relationSource
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (laterAlphaSource : ExactTag73RestrictedK13LaterAlphaSource transitionFuel
      configuration projection fixedInstance decoder
      (relationSource.toK13SourceObligations transitionFuel configuration
        projection fixedInstance decoder)
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              transitionRoom (by omega) initialEncoderExact environment)) ≤
      exactPreQ16OperationalK13RawError parameters := by
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  let source := relationSource.toK13SourceObligations transitionFuel
    configuration projection fixedInstance decoder
  have q16Bound :=
    exact_clean_preQ16_trial_union_probability_le_one_forest_of_bindings
      (decoder := decoder) hiddenLaw environment.toDecodedParsedSourceProvider
      transitionRoom programmedCover
      (fun sample input schedule ↦
        (environment.k13Source sample input).frontierExact schedule)
      reference traceExists foldExposureCap finalExposureCap
  have oneFoldBound :=
    exact_clean_bidirectional_preQ16_onefold_probability_le hiddenLaw
      transitionRoom (by omega) initialEncoderExact finalEncoderExact
      environment.toDecodedParsedSourceProvider foldExposureCap
  have jointBound := exact_tag73_restricted_k13_joint_batch_probability_le
    hiddenLaw relationSource clean jointBatchSource.toRestrictedSource
  have laterBound := exact_tag73_restricted_k13_later_alpha_probability_le
    hiddenLaw source clean laterAlphaSource
  have lateBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactK13PreQ16MerkleTargetHitEvent configuration
            transitionFuel) ≤ exactPreQ16LateTargetRawError parameters :=
    ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      Set.inter_subset_right).trans
        (exact_k13_preQ16_merkle_target_hit_probability_le hiddenLaw
          configuration transitionFuel)
  exact exact_preQ16_operational_k13_clean_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance decoder decoderBinding
    basis rc poseidon transitionRoom (by omega) initialEncoderExact environment
    source q16Bound oneFoldBound jointBound laterBound lateBound

#print axioms exact_tag73_restricted_preQ16_onefold_probability_le
#print axioms exact_tag73_restricted_preQ16_k14_probability_le
#print axioms exact_tag73_preQ16_operational_k13_clean_probability_le

end

end AspisK1.V7Tag73PreQ16OperationalActualLawBounds
