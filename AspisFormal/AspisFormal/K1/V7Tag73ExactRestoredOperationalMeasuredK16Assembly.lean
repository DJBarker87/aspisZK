import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13MeasuredComposition
import AspisFormal.K1.V7Tag73ExactRestoredOperationalK14Probability
import AspisFormal.K1.V7Tag73ExactRestoredOperationalK16Assembly

/-!
# Measured clean-restricted restoration-wide K1.6 assembly

This is the production-shaped K1.6 composition for the corrected
restoration-wide stage package.  It uses the compiler-clean event throughout,
charges the compiler target event exactly once, and installs the measured K1.3
q16 bound internally.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalMeasuredK16Assembly

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredOperationalK13MeasuredComposition
open AspisK1.V7Tag73ExactRestoredOperationalK13OneFoldProbability
open AspisK1.V7Tag73ExactRestoredOperationalK14Probability
open AspisK1.V7Tag73ExactRestoredOperationalK16Assembly
open AspisK1.V7Tag73ExactRestoredOperationalStages
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Final clean-restricted K1.6 theorem for the corrected restoration-wide
stage order.  The q16 probability is no longer a premise.  Remaining premises
are the literal Merkle, one-fold, relation, K1.4 and K1.5 source-law endpoints.
-/
theorem exact_tag73_restored_operational_measured_k16_aok_raw
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
    (k15 : ExactRestoredOperationalK15Classifier transitionFuel configuration
      projection fixedInstance relation decoder binding)
    (k15Error : ENNReal)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ configuration.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (semantic : ExactRestoredRootCleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (merkleBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            (exactTag73RestoredOperationalRootK12AuthenticationEvent
                transitionFuel configuration projection fixedInstance ∪
              exactTag73RestoredOperationalRootK12ExtractionEvent
                transitionFuel configuration projection fixedInstance)) ≤
        exactTag73K12ErrorBound configuration)
    (idealBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73RestoredOperationalCanonicalRootK13IdealRejectedEvent
              transitionFuel configuration projection fixedInstance decoder) ≤
        exactJointQueryBatchIdealRawError +
          exactLaterRelationAlphaIdealRawError)
    (oneFoldSource : ExactTag73RestoredCanonicalOneFoldSource transitionFuel
      configuration projection fixedInstance decoder
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (k14Source : ExactTag73RestoredOperationalK14Source transitionFuel
      configuration projection fixedInstance decoder
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance))
    (k15Bound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            exactTag73RestoredOperationalK15FailureEvent k15) ≤ k15Error) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel configuration projection
          fixedInstance) ≤
      exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel configuration fixedInstance relation +
        exactFixedClosedK16RawError
          (exactRestoredOperationalUpstreamTerms
            (exactRestoredOperationalK13RawError configuration)
              exactK14IdealRawError
              k15Error)
          parameters := by
  let stages := exactTag73RestoredOperationalStages transitionFuel configuration
    projection fixedInstance relation decoder binding k15
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  have k12Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k12TwoTreeMerkle208ErrorEvent stages) ≤ 0 := by
    rw [exact_restored_operational_stages_k12_error_event_eq_empty k15]
    simp
  have k13Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k13CircleListDecodeErrorEvent stages) ≤
        exactRestoredOperationalK13RawError configuration := by
    rw [exact_restored_stages_k13_error_event_eq k15]
    exact exact_restored_operational_k13_clean_error_measure_bound hiddenLaw
      (le_trans (by omega : 2 ≤ 3) transitionRoom) programmedCover
      frontierExact semantic reference traceExists foldExposureCap
      finalExposureCap initialEncoderExact merkleBound idealBound oneFoldSource
  have k14Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k14CoherentChainErrorEvent stages) ≤
        exactK14IdealRawError := by
    have width29Bound :=
      exact_restored_operational_k14_width29_probability_le hiddenLaw clean
        initialEncoderExact k14Source
    apply le_trans (measure_mono ?_) width29Bound
    rintro sample ⟨cleanMember, failure⟩
    exact ⟨cleanMember,
      exact_restored_stages_k14_error_subset_width29 k15 failure⟩
  have k15Clean :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ k15SpendWitnessErrorEvent stages) ≤ k15Error := by
    rw [exact_restored_stages_k15_error_event_eq k15]
    exact k15Bound
  exact exact_fixed_tag73_k16_classical_rom_aok_raw_restricted_stages
    hiddenLaw transitionFuel configuration projection fixedInstance relation
      transitionRoom driverCoversProtocol runtimeReserves cutoffBeyondCap stages
      (exactRestoredOperationalUpstreamTerms
        (exactRestoredOperationalK13RawError configuration)
          exactK14IdealRawError k15Error)
      k12Clean k13Clean k14Clean k15Clean

end

#print axioms exact_tag73_restored_operational_measured_k16_aok_raw

end AspisK1.V7Tag73ExactRestoredOperationalMeasuredK16Assembly
