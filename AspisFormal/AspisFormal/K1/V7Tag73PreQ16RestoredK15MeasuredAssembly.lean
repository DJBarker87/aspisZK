import AspisFormal.K1.V7Tag73PreQ16RestoredK15Events
import AspisFormal.K1.V7Tag73RestoredK15EventComposition
import AspisFormal.K1.V7Tag73RestrictedK15EventComposition

/-! # Measured corrected pre-q16 restoration-aware K1.5 -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16RestoredK15MeasuredAssembly

open Module
open MeasureTheory
open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactOperationalK15Stage
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisK1.V7Tag73K15RestrictedMeasureLedger
open AspisK1.V7Tag73PreQ16RestoredK15Events
open AspisK1.V7Tag73PreQ16RestoredStageAssembly
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73RestoredCausalErrorLedger
open AspisK1.V7Tag73RestoredK15EventComposition
open AspisK1.V7Tag73RestrictedK15EventComposition
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7DeterministicSpendWitness
open AspisV5AcceptedSpendRelation
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact full-law K1.5 bound from the eight fixed event bounds and one
restored residual bound. -/
theorem exact_preQ16_restored_k15_error_measure_bound
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16RestoredStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (fixedBounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (exactPreQ16RestoredFixedK15Events environment.restoredK15))
    (restoredBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactPreQ16RestoredK15ResidualEvent environment.restoredK15) ≤
        exactK14IdealRawError) :
    K15SpendWitnessErrorMeasureBound hiddenLaw
      (exactTag73PreQ16RestoredStages transitionFuel configuration projection
        fixedInstance decoder decoderBinding basis rc poseidon transitionRoom
        programmedCover initialEncoderExact environment)
      exactK15RestoredCausalRawError := by
  exact restored_k15_error_measure_bound_of_cover hiddenLaw
    (exactTag73PreQ16RestoredStages transitionFuel configuration projection
      fixedInstance decoder decoderBinding basis rc poseidon transitionRoom
      programmedCover initialEncoderExact environment)
    (exactPreQ16RestoredFixedK15Events environment.restoredK15)
    (exactPreQ16RestoredK15ResidualEvent environment.restoredK15)
    (exact_preQ16_restored_k15_error_event_subset_fixed_union_residual
      transitionRoom programmedCover initialEncoderExact environment)
    fixedBounds restoredBound

/-- Exact clean-slice K1.5 bound consumed by K1.6. -/
theorem exact_restricted_preQ16_restored_k15_error_measure_bound
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
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 513 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (environment : ExactPreQ16RestoredStageEnvironment transitionFuel
      configuration projection fixedInstance decoder decoderBinding basis rc
      poseidon)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (fixedBounds : FixedK15EventBounds
      (exactCompilerJointLaw hiddenLaw parameters)
      (restrictFixedK15Events clean
        (exactPreQ16RestoredFixedK15Events environment.restoredK15)))
    (restoredBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactPreQ16RestoredK15ResidualEvent environment.restoredK15) ≤
        exactK14IdealRawError) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ k15SpendWitnessErrorEvent
          (exactTag73PreQ16RestoredStages transitionFuel configuration projection
            fixedInstance decoder decoderBinding basis rc poseidon transitionRoom
            programmedCover initialEncoderExact environment)) ≤
      exactK15RestoredCausalRawError := by
  exact restricted_restored_k15_error_measure_bound_of_cover hiddenLaw
    (exactTag73PreQ16RestoredStages transitionFuel configuration projection
      fixedInstance decoder decoderBinding basis rc poseidon transitionRoom
      programmedCover initialEncoderExact environment)
    clean (exactPreQ16RestoredFixedK15Events environment.restoredK15)
    (exactPreQ16RestoredK15ResidualEvent environment.restoredK15)
    (exact_preQ16_restored_k15_error_event_subset_fixed_union_residual
      transitionRoom programmedCover initialEncoderExact environment)
    fixedBounds restoredBound

#print axioms exact_preQ16_restored_k15_error_measure_bound
#print axioms exact_restricted_preQ16_restored_k15_error_measure_bound

end

end AspisK1.V7Tag73PreQ16RestoredK15MeasuredAssembly
