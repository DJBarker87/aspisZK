import AspisFormal.K1.V7Tag73ExactConcreteK16Assembly
import AspisFormal.K1.V7Tag73ExactFixedK16Closure
import AspisFormal.K1.V7Tag73PreQ16OperationalMeasuredComposition
import AspisFormal.K1.V7Tag73PreQ16OperationalActualLawBounds
import AspisFormal.K1.V7Tag73PreQ16K15RestrictedBoundGammaClosure
import AspisFormal.K1.V7Tag73PreQ16K15RemainingFixedActualLawClosure
import AspisFormal.K1.V7Tag73PreQ16K15RestrictedSemanticActualLawClosure
import AspisFormal.K1.V7Tag73PreQ16RestoredK15MeasuredAssembly

/-! # Exact corrected pre-q16 K1.1--K1.6 assembly -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16RestoredK16Assembly

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
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73K13RestrictedLaterAlphaActualLawClosure
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73PreQ16RestoredK15Events
open AspisK1.V7Tag73PreQ16RestoredK15MeasuredAssembly
open AspisK1.V7Tag73PreQ16RestoredStageAssembly
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

/-- Concrete corrected K1.1--K1.6 closure from literal stage bounds.  K1.5's
deterministic cover and exact error arithmetic are discharged internally. -/
theorem exact_tag73_preQ16_restored_k16_aok_raw_of_bounds
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
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16RestoredStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw
      (exactTag73PreQ16RestoredStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon
        (le_trans (by decide : 2 ≤ 3) transitionRoom) programmedCover
        initialEncoderExact environment)
      (exactTag73K12ErrorBound configuration))
    (k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k13CircleListDecodeErrorEvent
              (exactTag73PreQ16RestoredStages transitionFuel configuration
                projection fixedInstance decoder decoderBinding basis rc poseidon
                (le_trans (by decide : 2 ≤ 3) transitionRoom) programmedCover
                initialEncoderExact environment)) ≤
        exactPreQ16OperationalK13RawError parameters)
    (k14Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k14CoherentChainErrorEvent
              (exactTag73PreQ16RestoredStages transitionFuel configuration
                projection fixedInstance decoder decoderBinding basis rc poseidon
                (le_trans (by decide : 2 ≤ 3) transitionRoom) programmedCover
                initialEncoderExact environment)) ≤ exactK14IdealRawError)
    (fixedK15Bounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance)
        (exactPreQ16RestoredFixedK15Events environment.restoredK15)))
    (restoredK15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactPreQ16RestoredK15ResidualEvent environment.restoredK15) ≤
        exactK14IdealRawError) :
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
            (exactPreQ16OperationalK13RawError parameters) exactK14IdealRawError
            exactK15RestoredCausalRawError) parameters := by
  let room2 : 2 ≤ transitionFuel := le_trans (by decide : 2 ≤ 3) transitionRoom
  let stages := exactTag73PreQ16RestoredStages transitionFuel configuration
    projection fixedInstance decoder decoderBinding basis rc poseidon room2
    programmedCover initialEncoderExact environment
  let relation := exactTag73SpendRelation (deployedOwner := deployedOwner)
    (deployedNote := deployedNote) (deployedNullifier := deployedNullifier)
    (deployedNode := deployedNode)
  let terms := exactTag73ConcreteUpstreamTerms configuration
    (exactPreQ16OperationalK13RawError parameters) exactK14IdealRawError
    exactK15RestoredCausalRawError
  have k15Bound := exact_restricted_preQ16_restored_k15_error_measure_bound
    hiddenLaw transitionFuel configuration projection fixedInstance decoder
    decoderBinding basis rc poseidon room2 programmedCover initialEncoderExact
    environment
    (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
      fixedInstance) fixedK15Bounds restoredK15Bound
  exact exact_fixed_tag73_k16_classical_rom_aok_raw_restricted_stages hiddenLaw
    transitionFuel configuration projection fixedInstance relation transitionRoom
    driverCoversProtocol runtimeReserves cutoffBeyondCap stages terms
    (((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      Set.inter_subset_right).trans k12Bound)
    k13Bound k14Bound k15Bound

/-- Source-facing closure of corrected K1.2--K1.4.  The restoration-aware stage
differs from the operational stage only at K1.5, so the already-proved actual-law
bounds transport definitionally.  Only the exact K1.5 component bounds remain
arguments. -/
theorem exact_tag73_preQ16_restored_k16_aok_raw_after_k14
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
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
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
    (oneFoldSource : ExactTag73RestrictedPreQ16OneFoldSource transitionFuel
      configuration projection fixedInstance decoder
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
          projection fixedInstance \
        exactK13PreQ16LateTargetEvent transitionFuel configuration projection
          fixedInstance))
    (jointBatchSource : ExactTag73RestrictedK13JointBatchSource transitionFuel
      configuration projection fixedInstance decoder relationSource
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (laterAlphaSource : ExactTag73RestrictedK13LaterAlphaSource transitionFuel
      configuration projection fixedInstance decoder relationSource
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
    (publishedInitialWidth29 :
      PublishedInitialWidth29CurveDecodability exactInitialEncoder)
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
            (exactPreQ16OperationalK13RawError parameters) exactK14IdealRawError
            exactK15RestoredCausalRawError) parameters := by
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
    exact_tag73_preQ16_operational_k13_clean_probability_le hiddenLaw
      transitionFuel configuration projection fixedInstance decoder decoderBinding
      basis rc poseidon environment.operationalStages relationSource room2
      programmedCover initialEncoderExact reference traceExists foldExposureCap
      finalExposureCap oneFoldSource jointBatchSource laterAlphaSource
  have k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            k13CircleListDecodeErrorEvent
              (exactTag73PreQ16RestoredStages transitionFuel configuration
                projection fixedInstance decoder decoderBinding basis rc poseidon
                room2 cover513 initialEncoderExact environment)) ≤
        exactPreQ16OperationalK13RawError parameters := by
    change (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          k13CircleListDecodeErrorEvent
            (exactTag73PreQ16OperationalStages transitionFuel configuration
              projection fixedInstance decoder decoderBinding basis rc poseidon
              room2 cover513 initialEncoderExact
              environment.operationalStages)) ≤
      exactPreQ16OperationalK13RawError parameters
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
              room2 cover513 initialEncoderExact
              environment.operationalStages)) ≤ exactK14IdealRawError
    exact operationalK14
  have restoredK15Bound :=
    exact_tag73_restricted_preQ16_restored_k15_residual_probability_le hiddenLaw
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
        fixedInstance) publishedInitialWidth29 restoredK15Source
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
    cover513 initialEncoderExact environment k12Bound k13Bound k14Bound
    fixedK15Bounds restoredK15Bound

#print axioms exact_tag73_preQ16_restored_k16_aok_raw_of_bounds
#print axioms exact_tag73_preQ16_restored_k16_aok_raw_after_k14

end

end AspisK1.V7Tag73PreQ16RestoredK16Assembly
