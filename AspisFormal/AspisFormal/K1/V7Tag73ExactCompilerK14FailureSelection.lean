import AspisFormal.K1.V7Tag73ExactCompilerGammaSelectedProofClosure
import AspisFormal.K1.V7Tag73K14FamilyFailureMembership
import AspisFormal.K1.V7Tag73VariablePrefixK14Probability

/-!
# Exact compiler K1.4 failure-family selection

This leaf stops before constructing the large width-29 target.  It proves only
that the one pre-fixed scheduler replay family is available at the actual gamma
and selects the canonical candidate exhibited by an actual decomposition
failure.  The algebraic target membership is supplied independently by
`V7Tag73K14FamilyFailureMembership`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactCompilerK14FailureSelection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerGammaSelectedProofClosure
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Lift one exact compiler replay oracle to the complete skeleton-indexed
K1.4 provider expected by the variable-prefix probability theorem.  Naming
this definition prevents downstream leaves from repeatedly unfolding the
dependent scheduler state. -/
noncomputable def exactCompilerK14Provider
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
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (initialDigest : Digest256) :
    VariablePrefixK14Provider decoder words :=
  fun skeleton =>
    exactCompilerRestoredSelectedProvider defaultResponse
      defaultDisclosedFinal defaultSchedule defaultSelected input initialDigest
      skeleton

/-- At the actual gamma, the pre-fixed exact-compiler family selects the
canonical candidate carried by a width-29 failure.  No K1.4 success
certificate, target membership, probability statement, or post-gamma family
premise occurs here. -/
theorem exact_compiler_actual_gamma_family_selects_width29_failure
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (k13 : ExactK13Certificate decoder input k12)
    (failure : Width29DecompositionFailure decoder k12.words
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
      let provider : RestoredSelectedBranchProvider decoder k12.words :=
        exactCompilerK14Provider defaultResponse defaultDisclosedFinal
          defaultSchedule defaultSelected input initialDigest
            (routedSuccessfulGammaFactorization routed).1
      let family := restoredSelectedChainFamilyOfK13Provider provider
      family.available (routedSuccessfulGammaValue routed).1 ∧
        family.selected (routedSuccessfulGammaValue routed).1 =
          Classical.choose failure := by
  obtain ⟨initialDigest, flat, response, gammaExact, replayExact, runExact,
      parsed, classifierExact, branch, branchExact, finalExact, scheduleExact⟩ :=
    exact_compiler_actual_gamma_provider_branch_closure input k12 k13 source
      coordinateStep defaultResponse defaultDisclosedFinal defaultSchedule
      defaultSelected
  let routed := successfulGammaPrefixFlatRoutingEquiv flat
  let provider : RestoredSelectedBranchProvider decoder k12.words :=
    exactCompilerK14Provider defaultResponse defaultDisclosedFinal
      defaultSchedule defaultSelected input initialDigest
        (routedSuccessfulGammaFactorization routed).1
  let family := restoredSelectedChainFamilyOfK13Provider provider
  have branchExact' :
      provider.branch (routedSuccessfulGammaValue routed).1 = some branch := by
    simpa only [provider, routed, exactCompilerK14Provider] using branchExact
  have familyFacts := k13_family_selected_of_branch provider
    (routedSuccessfulGammaValue routed).1 branch branchExact'
  have proofGammaExact :
      (exactK13ParsedProof input).gamma =
        (routedSuccessfulGammaValue routed).1 :=
    source.gammaExact.trans gammaExact
  have branchSelectedOnProof :
      selectCandidateChain
          (decoder.decodeBoth
            (exactK13Transcript input k12).initial
            (foldedReceived (exactK13ParsedProof input).schedule
              (exactK13Transcript input k12)))
        (exactK13ParsedProof input).schedule
        (exactK13ParsedProof input).disclosedFinal = some branch.selected := by
    simpa [exactK13Transcript, proofGammaExact, finalExact, scheduleExact] using
      branch.selectedExact
  have failureSelectedOnProof :
      selectCandidateChain
          (decoder.decodeBoth
            (exactK13Transcript input k12).initial
            (foldedReceived (exactK13ParsedProof input).schedule
              (exactK13Transcript input k12)))
        (exactK13ParsedProof input).schedule
        (exactK13ParsedProof input).disclosedFinal =
          some (Classical.choose failure) := by
    simpa [exactK13Transcript] using (Classical.choose_spec failure).1
  have selectedExact : branch.selected = Classical.choose failure := by
    apply Option.some.inj
    exact branchSelectedOnProof.symm.trans failureSelectedOnProof
  refine ⟨initialDigest, flat, response, gammaExact, replayExact, runExact, ?_⟩
  dsimp only [routed, provider, family]
  exact ⟨familyFacts.1, familyFacts.2.trans selectedExact⟩

#print axioms exact_compiler_actual_gamma_family_selects_width29_failure
#print axioms exactCompilerK14Provider

end
end AspisK1.V7Tag73ExactCompilerK14FailureSelection
