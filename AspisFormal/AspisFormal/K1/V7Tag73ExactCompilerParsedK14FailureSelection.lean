import AspisFormal.K1.V7Tag73ExactCompilerK14FailureSelection
import AspisFormal.K1.V7Tag73ParsedK13ClassifierSuccess
import AspisFormal.K1.V7Tag73ParsedK14BranchFailureSelection

/-! # Exact compiler parser-level K1.4 failure selection -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactCompilerParsedK14FailureSelection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerGammaSelectedProofClosure
open AspisK1.V7Tag73ExactCompilerK14FailureSelection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ParsedK13ClassifierSuccess
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73ParsedK14BranchFailureSelection
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The exact scheduler family selects the canonical candidate exhibited by
a width-29 failure on any parser-certified word. -/
theorem exact_compiler_actual_gamma_family_selects_parsed_width29_failure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ParsedK13Certificate decoder words (exactK13ParsedProof input))
    (failure : Width29DecompositionFailure decoder words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule)
    {decoded : Fin 641 → QM31Exact}
    (source : ExactParsedProofSourceBinding input decoded)
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (response : SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result)),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample ∧
      let routed := successfulGammaPrefixFlatRoutingEquiv flat
      let provider : RestoredSelectedBranchProvider decoder words :=
        exactCompilerK14Provider defaultResponse defaultDisclosedFinal
          defaultSchedule defaultSelected input initialDigest
            (routedSuccessfulGammaFactorization routed).1
      let family := restoredSelectedChainFamilyOfK13Provider provider
      family.available (routedSuccessfulGammaValue routed).1 ∧
        family.selected (routedSuccessfulGammaValue routed).1 =
          Classical.choose failure := by
  obtain ⟨initialDigest, flat, response, gammaExact, replayExact, runExact,
      proofExact⟩ :=
    exact_compiler_actual_gamma_selected_proof_closure input source
      coordinateStep
  obtain ⟨returned, classifierExact⟩ :=
    classify_parsed_k13_succeeds_of_certificate k13
  obtain ⟨branch, branchExact, finalExact, scheduleExact⟩ :=
    actual_routed_counterfactual_branch_source_exact defaultResponse
      defaultDisclosedFinal defaultSchedule defaultSelected
      (exactCompilerRoutedParsedOracle input initialDigest)
      (successfulGammaPrefixFlatRoutingEquiv flat) (exactK13ParsedProof input)
      proofExact returned classifierExact
  let routed := successfulGammaPrefixFlatRoutingEquiv flat
  let provider : RestoredSelectedBranchProvider decoder words :=
    exactCompilerK14Provider defaultResponse defaultDisclosedFinal
      defaultSchedule defaultSelected input initialDigest
        (routedSuccessfulGammaFactorization routed).1
  let family := restoredSelectedChainFamilyOfK13Provider provider
  have branchExact' :
      provider.branch (routedSuccessfulGammaValue routed).1 = some branch := by
    simpa only [provider, routed, exactCompilerK14Provider,
      exactCompilerRestoredSelectedProvider] using branchExact
  have familyFacts := k13_family_selected_of_branch provider
    (routedSuccessfulGammaValue routed).1 branch branchExact'
  have proofGammaExact :
      (exactK13ParsedProof input).gamma =
        (routedSuccessfulGammaValue routed).1 :=
    source.gammaExact.trans gammaExact
  have selectedExact : branch.selected = Classical.choose failure :=
    parsed_branch_selected_eq_choose_width29_failure branch proofGammaExact
      finalExact scheduleExact failure
  refine ⟨initialDigest, flat, response, gammaExact, replayExact, runExact, ?_⟩
  dsimp only [routed, provider, family]
  exact ⟨familyFacts.1, familyFacts.2.trans selectedExact⟩

#print axioms
  exact_compiler_actual_gamma_family_selects_parsed_width29_failure

end
end AspisK1.V7Tag73ExactCompilerParsedK14FailureSelection
