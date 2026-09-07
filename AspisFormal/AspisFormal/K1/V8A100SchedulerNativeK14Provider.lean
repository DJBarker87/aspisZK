import AspisFormal.K1.V8A100PreGammaTupleBinding
import AspisFormal.K1.V7Tag73CounterfactualReplayProofFilter

/-!
# Scheduler-native partial K1.4 provider for V8

The V7 scheduler replay already fixes one parsed-proof oracle over every
nonzero gamma for a nuisance skeleton.  This module runs the existing total
K1.3/K1.4 classifiers on each returned proof and exposes precisely the
partial K1.4 provider required by V8.  No fallback extraction and no
caller-supplied cross-gamma coherence premise is used.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V8A100SchedulerNativeK14Provider

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73CounterfactualReplayProofFilter
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73SchedulerNativePreGammaFamily
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V8A100PreGammaTupleBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Classify one replayed proof through K1.4.  The same routed skeleton is
used for all nonzero gamma values; malformed, rejected, K1.3-failing and
K1.4-failing branches are unavailable. -/
noncomputable def routedCounterfactualParsedK14Branch?
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : QM31Exact) :
    Option (RestoredK14Branch decoder binding words gamma) := by
  classical
  by_cases nonzero : gamma ≠ 0
  · let value : NonzeroQM31Exact := ⟨gamma, nonzero⟩
    let sample := routedForSkeletonValue skeleton value
    match proofEq : oracle.proof? sample with
    | none => exact none
    | some proof =>
        have gammaExact : proof.gamma = gamma := by
          calc
            proof.gamma = (routedSuccessfulGammaValue sample).1 :=
              oracle.proofGammaExact sample proof proofEq
            _ = gamma := by
              rw [show sample = routedForSkeletonValue skeleton value by rfl,
                routedForSkeletonValue_returns_value]
        match classifyParsedK13 decoder words proof with
        | .inr _error => exact none
        | .inl k13 =>
            match classifyParsedK14 decoder binding words proof k13 with
            | .inr _error => exact none
            | .inl k14 =>
                exact some
                  (gammaExact ▸ restoredK14BranchOfParsedCertificate k14)
  · exact none

/-- The complete partial K1.4 family is fixed once the replay oracle and
nuisance skeleton are fixed. -/
noncomputable def routedCounterfactualK14PartialProvider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton) :
    PartialRestoredK14BranchProvider decoder binding words :=
  ⟨routedCounterfactualParsedK14Branch? oracle skeleton⟩

@[simp] theorem routed_k14_partial_provider_zero_unavailable
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton) :
    (@routedCounterfactualK14PartialProvider decoder binding words oracle
      skeleton).branch 0 = none := by
  simp [routedCounterfactualK14PartialProvider,
    routedCounterfactualParsedK14Branch?]

/-- A coherent extraction's selected pair is the same canonical pair chosen
by the K1.3 branch made from the certificate used to classify it. -/
theorem parsed_k13_selected_eq_k14_combined
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {proof : Tag73K12ParsedProof}
    (k13 : ParsedK13Certificate decoder words proof)
    (k14 : ParsedK14Certificate decoder binding words proof) :
    (restoredSelectedBranchOfParsedK13 k13).selected =
      k14.extraction.combined := by
  apply Option.some.inj
  exact (restoredSelectedBranchOfParsedK13 k13).selectedExact.symm.trans
    k14.extraction.combinedSelected

/-- Forget a coherent extraction down to its canonical K1.3 selected branch.
The equality field is not chosen independently: it is the extraction's own
`combinedSelected` certificate. -/
def restoredSelectedBranchOfK14
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact}
    (branch : RestoredK14Branch decoder binding words gamma) :
    RestoredSelectedBranch decoder words gamma where
  disclosedFinal := branch.disclosedFinal
  schedule := branch.schedule
  selected := branch.extraction.combined
  selectedExact := branch.extraction.combinedSelected

/-- K1.3 view of precisely the branches that pass the replayed K1.4
classifier.  This is a source-derived subprovider, not a separately chosen
response family. -/
noncomputable def routedK14DerivedK13Provider
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredSelectedBranchProvider decoder words where
  defaultResponse := defaultResponse
  defaultDisclosedFinal := defaultDisclosedFinal
  defaultSchedule := defaultSchedule
  defaultSelected := defaultSelected
  branch := fun gamma =>
    (routedCounterfactualParsedK14Branch?
      (binding := binding) oracle skeleton gamma).map restoredSelectedBranchOfK14

/-- The K1.3 subprovider and partial K1.4 provider are definitionally
refined branch by branch. -/
theorem routed_k14_partial_provider_refines_derived_k13
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (oracle : RoutedCounterfactualParsedK13Oracle)
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredK14ProviderRefinesK13Provider
      (routedK14DerivedK13Provider (binding := binding) (words := words)
        defaultResponse defaultDisclosedFinal defaultSchedule defaultSelected
        oracle skeleton)
      (routedCounterfactualK14PartialProvider
        (binding := binding) (words := words) oracle skeleton) := by
  constructor
  intro gamma later laterExact
  refine ⟨restoredSelectedBranchOfK14 later, ?_, rfl⟩
  change Option.map restoredSelectedBranchOfK14
      (routedCounterfactualParsedK14Branch? oracle skeleton gamma) =
    some (restoredSelectedBranchOfK14 later)
  change routedCounterfactualParsedK14Branch? oracle skeleton gamma =
    some later at laterExact
  rw [laterExact]
  rfl

/-- Exact-compiler specialization: both providers are definitionally built
from the same whole replay oracle and fixed nuisance skeleton. -/
noncomputable def exactCompilerPartialK14Provider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    PartialRestoredK14BranchProvider decoder binding words :=
  routedCounterfactualK14PartialProvider
    (exactCompilerRoutedParsedOracle input initialDigest) skeleton

/-- The exact compiler replay also determines the K1.3 view of every K1.4
successful branch, with no cross-gamma premise. -/
noncomputable def exactCompilerK14DerivedK13Provider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredSelectedBranchProvider decoder words :=
  routedK14DerivedK13Provider (binding := binding) defaultResponse
    defaultDisclosedFinal defaultSchedule defaultSelected
    (exactCompilerRoutedParsedOracle input initialDigest) skeleton

theorem exact_compiler_partial_k14_refines_derived_selected_provider
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton) :
    RestoredK14ProviderRefinesK13Provider
      (exactCompilerK14DerivedK13Provider (binding := binding) defaultResponse
        defaultDisclosedFinal defaultSchedule defaultSelected input initialDigest
        skeleton)
      (exactCompilerPartialK14Provider
        (binding := binding) (words := words) input initialDigest skeleton) := by
  exact routed_k14_partial_provider_refines_derived_k13 defaultResponse
    defaultDisclosedFinal defaultSchedule defaultSelected
    (exactCompilerRoutedParsedOracle input initialDigest) skeleton

/-- After the executable replay/classifier construction above, the remaining
field for this *strong* obligation is the byte-parser/transcript theorem saying
that every available branch used the full two component vectors carried by the
prefix.  The actual no-new-tree verifier checks only their gamma dots, so the
release path uses the separate scalar-fingerprint bad-gamma theorem rather
than claiming that parsing alone establishes this stronger field. -/
def exactCompilerPreGammaTupleObligationOfPrefixReplay
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {compilerSample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance compilerSample)
    (initialDigest : Digest256)
    (skeleton : VariableGammaCompleteSkeleton)
    (componentPrefix : V8TwoPointComponentPrefix)
    (prefixReplay : RestoredK14ProviderMatchesTwoPointPrefix
      (exactCompilerPartialK14Provider
        (binding := binding) (words := words) input initialDigest skeleton)
      componentPrefix) :
    ExactCompilerPreGammaTupleObligation (binding := binding) (words := words)
      (exactCompilerK14DerivedK13Provider (binding := binding) (words := words)
        defaultResponse defaultDisclosedFinal defaultSchedule defaultSelected
        input initialDigest skeleton) componentPrefix where
  k14Family := exactCompilerPartialK14Provider
    (binding := binding) (words := words) input initialDigest skeleton
  sourceRefinement :=
    exact_compiler_partial_k14_refines_derived_selected_provider
      defaultResponse defaultDisclosedFinal defaultSchedule defaultSelected
      input initialDigest skeleton
  prefixReplay := prefixReplay

#print axioms routedCounterfactualParsedK14Branch?
#print axioms routed_k14_partial_provider_zero_unavailable
#print axioms parsed_k13_selected_eq_k14_combined
#print axioms restoredSelectedBranchOfK14
#print axioms routed_k14_partial_provider_refines_derived_k13
#print axioms exactCompilerPartialK14Provider
#print axioms exactCompilerK14DerivedK13Provider
#print axioms
  exact_compiler_partial_k14_refines_derived_selected_provider
#print axioms exactCompilerPreGammaTupleObligationOfPrefixReplay

end

end AspisK1.V8A100SchedulerNativeK14Provider
