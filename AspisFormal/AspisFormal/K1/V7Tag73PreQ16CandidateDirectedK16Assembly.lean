import AspisFormal.K1.V7Tag73PreQ16RestoredK16Assembly

/-!
# K1.2--K1.5 actual-law composition using the candidate-directed K1.3 source

Integration draft against main 37e1f04b8790f4dc092a38e5ad08d27b00801e0b.
NOT kernel checked in the authoring environment.

This replaces the older jointBatchSource entry point in the restored K1.6
assembly with the maintained prefix-factorization entry point and propagates
the honest candidateDirectedPreQ16OperationalK13RawError all the way into the
K1.6 conclusion. It also instantiates the already-proved width-29 theorem.

This is deliberately a theorem *of source obligations*. It does not construct
the production prefix factorization, the K1.3 later-alpha source, the K1.4
source, or the remaining K1.5 source certificates. They remain explicit below.
An axiom-free replay would validate this conditional composition, not discharge
these quantified premises. No release-completion claim follows from this file.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16CandidateDirectedK16Assembly

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactConcreteK16Assembly
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15RestrictedMeasureLedger
open AspisK1.V7Tag73K15SemanticActualLawClosure
open AspisK1.V7Tag73PreQ16OperationalMeasuredComposition
open AspisK1.V7Tag73PreQ16OperationalActualLawBounds
open AspisK1.V7Tag73PreQ16OperationalStageAssembly
open AspisK1.V7Tag73PreQ16K15RestrictedBoundGammaClosure
open AspisK1.V7Tag73PreQ16K15RemainingFixedActualLawClosure
open AspisK1.V7Tag73PreQ16K15RestrictedRelationAlphaActualLawClosure
open AspisK1.V7Tag73PreQ16K15RestrictedSemanticActualLawClosure
open AspisK1.V7Tag73RelationTailSourceComposition
open AspisK1.V7Tag73K13CandidateDirectedOperationalClosure
open AspisK1.V7Tag73K13ViewPrefixFactorization
open AspisK1.V7Tag73K13RestrictedLaterAlphaActualLawClosure
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73PreQ16RestoredK15Events
open AspisK1.V7Tag73PreQ16RestoredK15MeasuredAssembly
open AspisK1.V7Tag73PreQ16RestoredStageAssembly
open AspisK1.V7Tag73PreQ16RestoredK16Assembly
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RestoredCausalErrorLedger
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- Candidate-directed restored K1.6 composition. Every actual-law stage
inequality is obtained from the existing stage theorem, not supplied as a new
probability hypothesis. The source certificates remain visible parameters. -/
theorem exact_tag73_preQ16_candidate_directed_k16_aok_raw_of_prefix_source
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
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (environment : ExactPreQ16RestoredStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (k12Source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance)
    (relationSource : ExactTag73RelationSourceEnvironment transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (factorization : ExactCandidateDirectedK13ViewPrefixFactorization
      transitionFuel configuration projection fixedInstance decoder
      (relationSource.toK13SourceObligations transitionFuel configuration
        projection fixedInstance decoder))
    (laterAlphaSource : ExactTag73RestrictedK13LaterAlphaSource transitionFuel
      configuration projection fixedInstance decoder
      (relationSource.toK13SourceObligations transitionFuel configuration
        projection fixedInstance decoder)
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (k14Source : ExactTag73RestrictedPreQ16K14Source transitionFuel configuration
      projection fixedInstance decoder
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (remainingFixedK15Sources :
      ExactTag73RestrictedPreQ16RemainingFixedSources transitionFuel
        configuration projection fixedInstance decoder decoderBinding basis rc
        poseidon environment.restoredK15
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance))
    (semanticLanes : ExactTag73SemanticLanes HiddenTape parameters)
    (semanticTerminal : ExactTag73SemanticTerminal HiddenTape parameters decoder
      semanticLanes)
    (semanticSumcheck : ExactTag73SemanticSumcheck HiddenTape parameters decoder
      semanticLanes)
    (semanticCovered : ExactTag73RestrictedPreQ16SemanticCover
      environment.restoredK15
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance)
      semanticLanes semanticTerminal semanticSumcheck)
    (relationAlphaSource : ExactTag73RestrictedPreQ16K15RelationAlphaSource
      transitionFuel configuration projection fixedInstance decoder
      decoderBinding basis rc poseidon environment.restoredK15
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (restoredK15Source :
      ExactTag73RestrictedPreQ16K15BoundGammaSource transitionFuel configuration
        projection fixedInstance decoder decoderBinding basis rc poseidon
        environment.restoredK15
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw transitionFuel
          configuration fixedInstance
          (exactTag73SpendRelation (deployedOwner := deployedOwner)
            (deployedNote := deployedNote)
            (deployedNullifier := deployedNullifier)
            (deployedNode := deployedNode)) +
        exactFixedClosedK16RawError
          (exactTag73ConcreteUpstreamTerms configuration
            (candidateDirectedPreQ16OperationalK13RawError parameters)
            exactK14IdealRawError exactK15RestoredCausalRawError) parameters := by
  let room2 : 2 ≤ transitionFuel := le_trans (by decide : 2 ≤ 3) transitionRoom
  have cover513 : 513 ≤ 2 * parameters.forkRequestCap := by omega

  have operationalK12 := exact_preQ16_operational_k12_error_measure_bound hiddenLaw
    transitionFuel configuration projection fixedInstance decoder decoderBinding
    basis rc poseidon room2 cover513 initialEncoderExact
    environment.operationalStages k12Source
  have k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw
      (exactTag73PreQ16RestoredStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon room2 cover513
        initialEncoderExact environment)
      (exactTag73K12ErrorBound configuration) := by
    change K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw
      (exactTag73PreQ16OperationalStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon room2 cover513
        initialEncoderExact environment.operationalStages)
      (exactTag73K12ErrorBound configuration)
    exact operationalK12

  have operationalK13 :=
    exact_tag73_preQ16_operational_k13_candidate_directed_probability_le_of_prefix_factorization
      hiddenLaw transitionFuel configuration projection fixedInstance decoder
      decoderBinding basis rc poseidon environment.operationalStages relationSource
      room2 programmedCover initialEncoderExact finalEncoderExact reference
      traceExists foldExposureCap finalExposureCap factorization laterAlphaSource
  have k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k13CircleListDecodeErrorEvent
              (exactTag73PreQ16RestoredStages transitionFuel configuration
                projection fixedInstance decoder decoderBinding basis rc poseidon
                room2 cover513 initialEncoderExact environment)) ≤
        candidateDirectedPreQ16OperationalK13RawError parameters := by
    change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              room2 cover513 initialEncoderExact environment.operationalStages)) ≤
      candidateDirectedPreQ16OperationalK13RawError parameters
    exact operationalK13

  have width29Bound := exact_tag73_restricted_preQ16_k14_probability_le hiddenLaw
    (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
      fixedInstance) initialEncoderExact k14Source
  have operationalK14 := exact_preQ16_operational_k14_clean_error_measure_bound
    hiddenLaw transitionFuel configuration projection fixedInstance decoder
    decoderBinding basis rc poseidon room2 cover513 initialEncoderExact
    environment.operationalStages width29Bound
  have k14Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k14CoherentChainErrorEvent
              (exactTag73PreQ16RestoredStages transitionFuel configuration
                projection fixedInstance decoder decoderBinding basis rc poseidon
                room2 cover513 initialEncoderExact environment)) ≤
        exactK14IdealRawError := by
    change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k14CoherentChainErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              room2 cover513 initialEncoderExact environment.operationalStages)) ≤
      exactK14IdealRawError
    exact operationalK14

  -- This exact internal theorem was already used by the maintained K1.4 bound.
  -- Do not replace it with a new published-curve assumption on elaboration failure.
  have width29 : PublishedInitialWidth29CurveDecodability exactInitialEncoder :=
    AspisK1.V7ExactCorrelatedAgreementTerminal.exactV7InitialPublishedWidth29CurveDecodability
  have restoredK15Bound :=
    exact_tag73_restricted_preQ16_restored_k15_residual_probability_le hiddenLaw
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance) width29 restoredK15Source
  have remainingFixedK15Bounds :=
    remaining_preQ16_fixed_k15_event_bounds_of_sources hiddenLaw
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance) remainingFixedK15Sources
  have fixedK15Bounds :=
    restricted_preQ16_fixed_k15_event_bounds_of_semantic_relation_sources
      hiddenLaw
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance)
      remainingFixedK15Bounds semanticLanes semanticTerminal semanticSumcheck
      semanticCovered relationAlphaSource

  exact exact_tag73_preQ16_restored_k16_aok_raw_of_bounds hiddenLaw transitionFuel
    configuration projection fixedInstance decoder decoderBinding basis rc
    poseidon transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap
    cover513 initialEncoderExact environment
    (candidateDirectedPreQ16OperationalK13RawError parameters)
    k12Bound k13Bound k14Bound fixedK15Bounds restoredK15Bound

#print axioms
  exact_tag73_preQ16_candidate_directed_k16_aok_raw_of_prefix_source

end
end AspisK1.V7Tag73PreQ16CandidateDirectedK16Assembly
