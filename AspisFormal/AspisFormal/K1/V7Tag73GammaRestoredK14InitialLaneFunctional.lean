import AspisFormal.K1.V7Tag73GammaRestoredK14InitialLaneAlignment

/-!
# Pairwise pre-gamma lane functionality for restored-gamma K1.4

This replaces the old requirement that complete extracted Merkle words agree
throughout a gamma fibre.  Only the 29 lanes committed before gamma must agree.
Lean chooses those lanes once per hidden/non-gamma residual and constructs the
minimal probability source proved in the preceding module.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14InitialLaneFunctional

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14InitialLaneAlignment
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One clean failing execution indexed by its non-gamma coordinate residual.
Only its initial lanes and bounded-decoder replay are used below. -/
structure GammaRestoredK14InitialLaneFibreWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters) : Type where
  answers : FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length
  cleanMember : (hidden, answers) ∈ clean
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance (hidden, answers)
  k13 : ExactGammaRestoredOperationalK13Certificate decoder input
  failure : Width29DecompositionFailure decoder
    k13.certificate.classified.k12.words
    (restoredOperationalK13View k13.certificate.data).gamma
    (restoredOperationalK13View k13.certificate.data).disclosedFinal
    (restoredOperationalK13View k13.certificate.data).schedule
  decoded : OrdinaryPrefixDecode
  run : runGammaPrefix
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration hidden
        answers).2 = some decoded
  residualExact :
    (exactCompilerRestoredGammaCoordinates transitionFuel configuration hidden
      answers).1 = residual
  bytesExact : decoded.value = k13.certificate.data.gammaBytes

/-- Exact source boundary: byte replay plus pairwise equality of the 29
pre-gamma lanes.  Values outside those lanes may differ arbitrarily. -/
structure ExactTag73GammaRestoredK14InitialLaneFunctional
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (clean : Set (ExactCompilerSample HiddenTape parameters)) where
  defaultLanes : Width29InitialLanes
  defaultResponse : InitialMessage QM31Exact
  decoderAt : ∀ (hidden : HiddenTape)
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
    ∃ decoded : OrdinaryPrefixDecode,
      runGammaPrefix
          (exactCompilerRestoredGammaCoordinates transitionFuel configuration
            hidden answers).2 = some decoded ∧
      decoded.value = k13.certificate.data.gammaBytes
  sameInitialLanes : ∀ (hidden : HiddenTape)
      (residual : ExactCompilerGammaPrefixResidual parameters)
      (left right : GammaRestoredK14InitialLaneFibreWitness transitionFuel
        configuration projection fixedInstance decoder clean hidden residual),
    extractedWidth29InitialWords left.k13.certificate.classified.k12.words =
      extractedWidth29InitialWords right.k13.certificate.classified.k12.words

/-- Canonical 29-lane value attached to a hidden/non-gamma residual fibre. -/
noncomputable def ExactTag73GammaRestoredK14InitialLaneFunctional.fibreLanes
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14InitialLaneFunctional transitionFuel
      configuration projection fixedInstance decoder clean)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters) :
    Width29InitialLanes := by
  classical
  exact if existsWitness : Nonempty (GammaRestoredK14InitialLaneFibreWitness
      transitionFuel configuration projection fixedInstance decoder clean
        hidden residual) then
    extractedWidth29InitialWords
      (Classical.choice existsWitness).k13.certificate.classified.k12.words
  else source.defaultLanes

/-- Pairwise lane functionality constructs the minimal byte/lane alignment. -/
noncomputable def
    ExactTag73GammaRestoredK14InitialLaneFunctional.toInitialLaneAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (source : ExactTag73GammaRestoredK14InitialLaneFunctional transitionFuel
      configuration projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14InitialLaneAlignment transitionFuel configuration
      projection fixedInstance decoder clean where
  lanes := source.fibreLanes
  defaultResponse := source.defaultResponse
  exactAt := by
    intro hidden answers cleanMember input k13 failure
    obtain ⟨decoded, run, bytesExact⟩ :=
      source.decoderAt hidden answers cleanMember input k13 failure
    let coordinates := exactCompilerRestoredGammaCoordinates transitionFuel
      configuration hidden answers
    let actual : GammaRestoredK14InitialLaneFibreWitness transitionFuel configuration
        projection fixedInstance decoder clean hidden coordinates.1 :=
      { answers := answers
        cleanMember := cleanMember
        input := input
        k13 := k13
        failure := failure
        decoded := decoded
        run := run
        residualExact := rfl
        bytesExact := bytesExact }
    have existsWitness : Nonempty (GammaRestoredK14InitialLaneFibreWitness
        transitionFuel configuration projection fixedInstance decoder clean
          hidden coordinates.1) := ⟨actual⟩
    refine ⟨decoded, run, ?_, bytesExact⟩
    change extractedWidth29InitialWords k13.certificate.classified.k12.words =
      source.fibreLanes hidden coordinates.1
    rw [ExactTag73GammaRestoredK14InitialLaneFunctional.fibreLanes,
      dif_pos existsWitness]
    exact source.sameInitialLanes hidden coordinates.1 actual
      (Classical.choice existsWitness)

#print axioms GammaRestoredK14InitialLaneFibreWitness
#print axioms ExactTag73GammaRestoredK14InitialLaneFunctional
#print axioms ExactTag73GammaRestoredK14InitialLaneFunctional.fibreLanes
#print axioms
  ExactTag73GammaRestoredK14InitialLaneFunctional.toInitialLaneAlignment

end
end AspisK1.V7Tag73GammaRestoredK14InitialLaneFunctional
