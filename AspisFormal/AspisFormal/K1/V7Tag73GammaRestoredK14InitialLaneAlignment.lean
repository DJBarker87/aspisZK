import AspisFormal.K1.V7Tag73GammaRestoredK14InitialLaneProvider
import AspisFormal.K1.V7Tag73GammaRestoredK14Scope
import AspisFormal.K1.V7Tag73K14K15IdealErrorLedger
import AspisFormal.K1.V7Tag73RestoredGammaFibreK14Membership
import AspisFormal.K1.V7Tag73SamplerDecoder
import AspisFormal.K1.V7Tag73SecureCircleMap
import AspisFormal.K1.V7Tag73VariablePrefixK14MeasureTransport

/-!
# Restored-gamma K1.4 alignment at the fixed initial-lane boundary

This is the release-facing K1.4 reduction.  The source supplies only:

* byte-exact replay of the bounded gamma sampler; and
* equality of the 29 pre-gamma initial lanes with a function of the hidden
  tape and the non-gamma coordinate residual.

No complete Merkle word, post-gamma transcript, decoder list, or bad-challenge
set is required to be invariant across the gamma fibre.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14InitialLaneAlignment

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14InitialLaneProvider
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredGammaFibreK14Membership
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14MeasureTransport
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisK1.V7ExactCorrelatedAgreementTerminal
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- The exact remaining production facts for K1.4.  `lanes` is fixed before
the successful gamma component is exposed. -/
structure ExactTag73GammaRestoredK14InitialLaneAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  lanes : HiddenTape → ExactCompilerGammaPrefixResidual parameters →
    Width29InitialLanes
  defaultResponse : InitialMessage QM31Exact
  exactAt : ∀ (hidden : HiddenTape)
      (answers : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (_cleanMember : (hidden, answers) ∈ clean)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance (hidden, answers))
      (k13 : ExactGammaRestoredOperationalK13Certificate decoder input)
      (_failure : Width29DecompositionFailure decoder
        k13.certificate.classified.k12.words
        (restoredOperationalK13View k13.certificate.data).gamma
        (restoredOperationalK13View k13.certificate.data).disclosedFinal
        (restoredOperationalK13View k13.certificate.data).schedule),
    let coordinates := exactCompilerRestoredGammaCoordinates transitionFuel
      configuration hidden answers
    ∃ decoded : OrdinaryPrefixDecode,
      runGammaPrefix coordinates.2 = some decoded ∧
      extractedWidth29InitialWords k13.certificate.classified.k12.words =
        lanes hidden coordinates.1 ∧
      decoded.value = k13.certificate.data.gammaBytes

/-- Every clean literal K1.4 failure is covered by the fixed-lane bad-gamma
event.  All response selection and curve membership are constructed in Lean. -/
theorem initial_lane_alignment_covers_restored_k14_event
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14InitialLaneAlignment transitionFuel
      configuration projection fixedInstance decoder clean)
    (hidden : HiddenTape) :
    jointEventSlice
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder)
        hidden ⊆
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration
          hidden) ⁻¹'
        dependentSuccessfulSubtypeEvent GammaPrefixSucceeds
          (fun residual ↦ successfulGammaPrefixSkeletonDependentEventK14
            (restoredGammaInitialLaneFailureTarget decoder
              (source.lanes hidden residual) source.defaultResponse)) := by
  intro answers member
  rcases member with ⟨cleanMember, input, k13, failure⟩
  obtain ⟨decoded, run, lanesExact, bytesExact⟩ :=
    source.exactAt hidden answers cleanMember input k13 failure
  let coordinates := exactCompilerRestoredGammaCoordinates transitionFuel
    configuration hidden answers
  have success : GammaPrefixSucceeds coordinates.2 := by
    unfold GammaPrefixSucceeds
    rw [run]
    rfl
  let flat : SuccessfulGammaPrefixTape := ⟨coordinates.2, success⟩
  let factored := successfulGammaPrefixFactorization flat
  have routedValue : decodeTagQM31ExactLE decoded.value =
      some factored.2.1 := by
    simpa only [factored, successfulGammaPrefixFactorization_value] using
      flatRoutingEquiv_returned_exact_value flat decoded run
  have recordedValue : decodeTagQM31ExactLE decoded.value =
      some k13.certificate.data.gamma := by
    simpa only [bytesExact] using k13.certificate.data.gammaDecoded
  have gammaExact : k13.certificate.data.gamma = factored.2.1 :=
    Option.some.inj (recordedValue.symm.trans routedValue)
  have viewGammaExact :
      (restoredOperationalK13View k13.certificate.data).gamma = factored.2.1 :=
    gammaExact
  have factoredFailure : Width29DecompositionFailure decoder
      k13.certificate.classified.k12.words factored.2.1
      (restoredOperationalK13View k13.certificate.data).disclosedFinal
      (restoredOperationalK13View k13.certificate.data).schedule := by
    rw [viewGammaExact] at failure
    exact failure
  let lanes := source.lanes hidden coordinates.1
  have lanesExact' :
      extractedWidth29InitialWords k13.certificate.classified.k12.words =
        lanes := lanesExact
  have available : ∃ response,
      InitialLaneBadResponseRealized decoder lanes factored.2.1 response :=
    initialLaneBadResponseRealizedOfFailure decoder
    k13.certificate.classified.k12.words
    lanes factored.2.1
    (restoredOperationalK13View k13.certificate.data).disclosedFinal
    (restoredOperationalK13View k13.certificate.data).schedule lanesExact'
    factored.2.2 factoredFailure
  apply mem_preimage_dependent_k14_of_factored
    (exactCompilerRestoredGammaCoordinates transitionFuel configuration hidden)
    answers
    (fun residual skeleton ↦
      restoredGammaInitialLaneFailureTarget decoder
        (source.lanes hidden residual) source.defaultResponse skeleton)
    success
  change factored.2.1 ∈
    restoredGammaInitialLaneFailureTarget decoder lanes source.defaultResponse
      factored.1
  apply realized_bad_response_mem_initial_lane_failure_target decoder lanes
    source.defaultResponse factored.1 factored.2.1
  exact available

/-- Exact scoped K1.4 probability bound from only byte replay and pre-gamma
initial-lane alignment. -/
theorem exact_gamma_restored_k14_probability_le_of_initial_lane_alignment
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
    (source : ExactTag73GammaRestoredK14InitialLaneAlignment transitionFuel
      configuration projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder) ≤
      exactK14IdealRawError := by
  change
    (hiddenTapeUniformFreshJointLaw hiddenLaw
      (exactCompilerTargetCaps parameters).length).toOuterMeasure
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder) ≤
      (initialBatchChallengeCap : ENNReal) /
        ((P ^ 4 - 1 : Nat) : ENNReal)
  apply hidden_tape_variable_prefix_k14_event_probability_le hiddenLaw
    (exactCompilerTargetCaps parameters).length
    (fun hidden ↦ exactCompilerRestoredGammaCoordinates transitionFuel
      configuration hidden)
    (fun hidden residual ↦
      restoredGammaInitialLaneFailureTarget decoder
        (source.lanes hidden residual) source.defaultResponse)
    initialBatchChallengeCap
  · intro hidden residual skeleton
    exact restored_gamma_initial_lane_failure_target_card_le decoder
      initialEncoderExact exactV7InitialPublishedWidth29CurveDecodability
      (source.lanes hidden residual)
      source.defaultResponse skeleton
  · exact initial_lane_alignment_covers_restored_k14_event source

#print axioms ExactTag73GammaRestoredK14InitialLaneAlignment
#print axioms initial_lane_alignment_covers_restored_k14_event
#print axioms exact_gamma_restored_k14_probability_le_of_initial_lane_alignment

end
end AspisK1.V7Tag73GammaRestoredK14InitialLaneAlignment
