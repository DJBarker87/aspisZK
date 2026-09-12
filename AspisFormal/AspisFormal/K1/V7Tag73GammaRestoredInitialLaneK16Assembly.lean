import AspisFormal.K1.V7Tag73GammaRestoredK14InitialLaneAlignment
import AspisFormal.K1.V7Tag73GammaRestoredOperationalK16Assembly

/-!
# K1.6 assembly using the minimal restored-gamma K1.4 source

This capstone is identical to the canonical gamma-restored assembly except
that K1.4 consumes byte replay and fixed 29-lane alignment.  It no longer asks
for a complete extracted word or a counterfactual decoder-list provider.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73GammaRestoredInitialLaneK16Assembly

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredInitialLaneK16Assembly
open AspisK1.V7Tag73GammaRestoredK14InitialLaneAlignment
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73GammaRestoredOperationalK14Stage
open AspisK1.V7Tag73GammaRestoredOperationalK16Assembly
open AspisK1.V7Tag73GammaRestoredOperationalStages
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Clean-restricted classical-ROM AoK closure with the minimal K1.4 source. -/
theorem exact_tag73_gamma_restored_initial_lane_k16_aok_raw
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (k15 : ExactGammaRestoredOperationalK15Classifier transitionFuel
      configuration projection fixedInstance relation decoder binding)
    (k13Error k15Error : ENNReal)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (k13Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73GammaRestoredOperationalK13FailureEvent transitionFuel
              configuration projection fixedInstance decoder) ≤ k13Error)
    (k14Source : ExactTag73GammaRestoredK14InitialLaneAlignment transitionFuel
      configuration projection fixedInstance decoder
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (k15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73GammaRestoredOperationalK15FailureEvent k15) ≤ k15Error) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError
          (exactGammaRestoredOperationalUpstreamTerms k13Error k15Error)
          parameters := by
  let stages := exactTag73GammaRestoredOperationalStages transitionFuel
    configuration projection fixedInstance relation decoder binding k15
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  have k12Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) ≤ 0 := by
    rw [exact_gamma_restored_stages_k12_error_event_eq_empty k15]
    simp
  have k13Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k13CircleListDecodeErrorEvent stages) ≤ k13Error := by
    rw [exact_gamma_restored_stages_k13_error_event_eq k15]
    exact k13Bound
  have k14Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k14CoherentChainErrorEvent stages) ≤
        exactK14IdealRawError := by
    rw [exact_gamma_restored_stages_k14_error_event_eq k15,
      exact_gamma_restored_operational_k14_failure_event_eq_width29]
    exact exact_gamma_restored_k14_probability_le_of_initial_lane_alignment
      hiddenLaw clean initialEncoderExact k14Source
  have k15Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k15SpendWitnessErrorEvent stages) ≤ k15Error := by
    rw [exact_gamma_restored_stages_k15_error_event_eq k15]
    exact k15Bound
  exact exact_fixed_tag73_k16_classical_rom_aok_raw_restricted_stages
    hiddenLaw transitionFuel configuration projection fixedInstance relation
      transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap stages
      (exactGammaRestoredOperationalUpstreamTerms k13Error k15Error)
      k12Clean k13Clean k14Clean k15Clean

#print axioms exact_tag73_gamma_restored_initial_lane_k16_aok_raw

end
end AspisK1.V7Tag73GammaRestoredInitialLaneK16Assembly
