import AspisFormal.K1.V7Tag73GammaRestoredK14Probability
import AspisFormal.K1.V7Tag73GammaRestoredOperationalStages

/-!
# K1.6 assembly for the canonical gamma-restored child

This is the first K1.6 stage assembly whose K1.4 numerical theorem and K1.4
classifier are definitionally scoped to the same canonical root-gamma child.
The prior restoration-wide assembly selected an arbitrary successful K1.3
node, so its broad K1.4 event could not soundly be discharged by the narrower
gamma-fork probability law.

The remaining numerical inputs are now explicit and honest: failure to obtain
the scoped K1.3 certificate, and failure of the final scoped K1.5 handoff.
K1.4 is discharged internally from its deterministic source adapter and the
kernel-checked width-29 theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73GammaRestoredOperationalK16Assembly

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
open AspisK1.V7Tag73GammaRestoredK14Probability
open AspisK1.V7Tag73GammaRestoredOperationalK14Stage
open AspisK1.V7Tag73GammaRestoredOperationalStages
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

def exactGammaRestoredOperationalUpstreamTerms
    (k13 k15 : ENNReal) : ConcreteUpstreamErrorTerms where
  k12TwoTreeMerkle208 := 0
  k13CircleListDecoding := k13
  k14CoherentChainSelection := exactK14IdealRawError
  k15SpendWitnessRecovery := k15

/-- Clean-restricted classical-ROM AoK closure with K1.4 bound on exactly the
canonical gamma-restored child selected by the stage package. -/
theorem exact_tag73_gamma_restored_operational_k16_aok_raw
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
    (k14Source : ExactTag73GammaRestoredK14Source transitionFuel configuration
      projection fixedInstance decoder
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
    exact exact_gamma_restored_operational_k14_width29_probability_le hiddenLaw
      clean initialEncoderExact k14Source
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

#print axioms exactGammaRestoredOperationalUpstreamTerms
#print axioms exact_tag73_gamma_restored_operational_k16_aok_raw

end
end AspisK1.V7Tag73GammaRestoredOperationalK16Assembly
