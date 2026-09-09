import AspisFormal.K1.V7Tag73ExactCompilerParsedK14FailureSelection
import AspisFormal.K1.V7Tag73ExactAdversaryAnchorFinalProfile
import AspisFormal.K1.V7Tag73K13PreQ16JointEventHandoff

/-! # Corrected pre-q16 exact-compiler K1.4 failure selection -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactCompilerPreQ16K14FailureSelection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73ExactAdversaryAnchorFinalProfile
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerActualGammaReplayClosure
open AspisK1.V7Tag73ExactCompilerK14FailureSelection
open AspisK1.V7Tag73ExactCompilerParsedK14FailureSelection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
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

/-- Release-facing corrected-word specialization.  The K1.3 certificate fixes
the literal pre-q16 word; the deployed decoded-source provider and transition
reserve discharge the two scheduler/source premises. -/
theorem exact_compiler_actual_gamma_family_selects_preQ16_width29_failure
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (decodedSource : ExactFixedK13DecodedParsedSourceProvider transitionFuel
      configuration projection fixedInstance)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (failure : Width29DecompositionFailure decoder k13.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair) :
    ∃ (initialDigest : Digest256) (flat : SuccessfulGammaPrefixTape)
      (response : SchedulerNativeGammaResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))),
      exactOperationalChallenge input .gamma =
          (routedSuccessfulGammaValue
            (successfulGammaPrefixFlatRoutingEquiv flat)).1 ∧
      exactCompilerRoutedGammaReplay input initialDigest
          (successfulGammaPrefixFlatRoutingEquiv flat) = .ok response ∧
      response.run = runExactPlainRom transitionFuel configuration sample ∧
      let routed := successfulGammaPrefixFlatRoutingEquiv flat
      let provider : RestoredSelectedBranchProvider decoder k13.words :=
        exactCompilerK14Provider defaultResponse defaultDisclosedFinal
          defaultSchedule defaultSelected input initialDigest
            (routedSuccessfulGammaFactorization routed).1
      let family := restoredSelectedChainFamilyOfK13Provider provider
      family.available (routedSuccessfulGammaValue routed).1 ∧
        family.selected (routedSuccessfulGammaValue routed).1 =
          Classical.choose failure := by
  obtain ⟨decoded, _decodeExact, source⟩ := decodedSource sample input
  exact exact_compiler_actual_gamma_family_selects_parsed_width29_failure
    input k13.parsed failure source
    (exact_compiler_actual_gamma_coordinate_step transitionRoom input)
    defaultResponse defaultDisclosedFinal defaultSchedule defaultSelected

#print axioms
  exact_compiler_actual_gamma_family_selects_preQ16_width29_failure

end
end AspisK1.V7Tag73ExactCompilerPreQ16K14FailureSelection
