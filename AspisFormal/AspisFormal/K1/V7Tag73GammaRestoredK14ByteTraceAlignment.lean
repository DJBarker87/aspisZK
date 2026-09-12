import AspisFormal.K1.V7Tag73GammaRestoredK14CausalClosure

/-!
# Byte-level production trace boundary for restored-gamma K1.4

The production/source bridge should expose the bounded gamma decoder exactly as
it executes on the routed raw SHA blocks.  It should not separately assert a
QM31 equality.  This leaf derives sampler success and the field-level equality
from the raw decoder result, canonical decoding, and the verifier-owned gamma
record retained by the restored K1.3 certificate.

Consequently the remaining source facts are byte-level gamma replay and
authenticated-word invariance.  The width-29 provider, field conversion, and
probability statement remain entirely kernel checked.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14ByteTraceAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14FibreAlignment
open AspisK1.V7Tag73GammaRestoredK14CausalClosure
open AspisK1.V7Tag73GammaRestoredK14CausalSource
open AspisK1.V7Tag73GammaRestoredK14Probability
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73K14K15IdealErrorLedger
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Literal source facts at the selected restored gamma child.  The gamma
claim is expressed only in terms of the deployed bounded decoder's output
bytes and the verifier-owned recorded bytes. -/
structure ExactTag73GammaRestoredK14ByteTraceAlignment
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
  defaultResponse : InitialMessage QM31Exact
  defaultDisclosedFinal : FinalMessage QM31Exact
  defaultSchedule : ExactSchedule
  defaultSelected : ExactCandidatePair
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
      k13.certificate.classified.k12.words = words hidden coordinates.1 ∧
      decoded.value = k13.certificate.data.gammaBytes

/-- Byte-exact replay is sufficient for the complete pointwise fibre
alignment.  In particular, the QM31 equality follows by functionality of
canonical decoding and is not trusted at the source boundary. -/
noncomputable def ExactTag73GammaRestoredK14ByteTraceAlignment.toFibreAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14ByteTraceAlignment transitionFuel
      configuration projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14FibreAlignment transitionFuel configuration
      projection fixedInstance decoder clean where
  words := source.words
  defaultResponse := source.defaultResponse
  defaultDisclosedFinal := source.defaultDisclosedFinal
  defaultSchedule := source.defaultSchedule
  defaultSelected := source.defaultSelected
  exactAt := by
    intro hidden answers cleanMember input k13 failure
    obtain ⟨decoded, run, wordsExact, bytesExact⟩ :=
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
    have gammaExact : k13.certificate.data.gamma = factored.2.1 := by
      exact Option.some.inj (recordedValue.symm.trans routedValue)
    exact ⟨success, wordsExact, gammaExact⟩

/-- Direct adapter consumed by the existing scoped K1.4 probability theorem. -/
noncomputable def ExactTag73GammaRestoredK14ByteTraceAlignment.toProbabilitySource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14ByteTraceAlignment transitionFuel
      configuration projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14Source transitionFuel configuration projection
      fixedInstance decoder clean :=
  AspisK1.V7Tag73GammaRestoredK14CausalClosure.ExactTag73GammaRestoredK14CausalSource.toProbabilitySource
    source.toFibreAlignment.toCausalSource

/-- Scoped K1.4 bound from byte-level production facts only. -/
theorem exact_gamma_restored_operational_k14_width29_probability_le_of_byte_trace
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
    (source : ExactTag73GammaRestoredK14ByteTraceAlignment transitionFuel
      configuration projection fixedInstance decoder clean) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73GammaRestoredOperationalK14Width29Event
          transitionFuel configuration projection fixedInstance decoder) ≤
      exactK14IdealRawError :=
  exact_gamma_restored_operational_k14_width29_probability_le hiddenLaw clean
    initialEncoderExact source.toProbabilitySource

#print axioms ExactTag73GammaRestoredK14ByteTraceAlignment
#print axioms ExactTag73GammaRestoredK14ByteTraceAlignment.toFibreAlignment
#print axioms ExactTag73GammaRestoredK14ByteTraceAlignment.toProbabilitySource
#print axioms
  exact_gamma_restored_operational_k14_width29_probability_le_of_byte_trace

end
end AspisK1.V7Tag73GammaRestoredK14ByteTraceAlignment
