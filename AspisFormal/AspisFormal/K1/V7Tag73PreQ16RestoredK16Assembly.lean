import AspisFormal.K1.V7Tag73ExactConcreteK16Assembly
import AspisFormal.K1.V7Tag73ExactFixedK16Closure
import AspisFormal.K1.V7Tag73PreQ16OperationalMeasuredComposition
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
open AspisK1.V7Tag73PreQ16OperationalMeasuredComposition
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

#print axioms exact_tag73_preQ16_restored_k16_aok_raw_of_bounds

end

end AspisK1.V7Tag73PreQ16RestoredK16Assembly
