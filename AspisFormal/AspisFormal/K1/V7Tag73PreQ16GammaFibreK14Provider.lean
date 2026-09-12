import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73GammaPrefixCausalController
import AspisFormal.K1.V7Tag73K13PreQ16JointEventHandoff
import AspisFormal.K1.V7Tag73VariablePrefixK14Probability

/-!
# K1.4 provider generated from one chronological pre-q16 gamma fibre

At fixed hidden tape and non-gamma residual, the exact causal coordinate
equivalence reconstructs one literal compiler sample for every successful
gamma tape.  We retain a branch exactly when that reconstructed execution
has a corrected pre-q16 K1.3 certificate and a width-29 failure on the fixed
word.  Consequently the complete challenge-indexed provider is constructed
before the returned gamma; it is not a source premise and does not inspect a
post-gamma choice of strategy.

The remaining source layer is reduced to two deterministic equalities: the
corrected word must be constant on the gamma fibre, and the parsed proof's
gamma must equal the value decoded from its routed successful tape.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73PreQ16GammaFibreK14Provider

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaPrefixCausalController
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Reconstruct the exact compiler sample at one point of the deployed
causal gamma-coordinate fibre. -/
def exactPreQ16GammaFibreSample
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters)
    (flat : SuccessfulGammaPrefixTape) :
    ExactCompilerSample HiddenTape parameters :=
  (hidden,
    (exactCompilerGammaPrefixCoordinates parameters transitionFuel
      (exactPlainRomCursor configuration hidden).erase).symm
        (residual, flat.1))

/-- Successful chronological tape with the requested nuisance skeleton and
nonzero gamma value. -/
def successfulPreQ16GammaTape
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact) : SuccessfulGammaPrefixTape :=
  successfulGammaPrefixFactorization.symm (skeleton, gamma)

@[simp] theorem successful_preQ16_gamma_tape_factorization
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact) :
    successfulGammaPrefixFactorization
        (successfulPreQ16GammaTape skeleton gamma) =
      (skeleton, gamma) := by
  exact successfulGammaPrefixFactorization.apply_symm_apply (skeleton, gamma)

/-- Reconstructing the fibre point of an actual sample returns that sample
byte-for-byte. -/
theorem exact_preQ16_gamma_fibre_sample_roundtrip
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (success : GammaPrefixSucceeds
      (exactCompilerGammaPrefixCoordinates parameters transitionFuel
        (exactPlainRomCursor configuration hidden).erase tape).2) :
    let coordinates := exactCompilerGammaPrefixCoordinates parameters
      transitionFuel (exactPlainRomCursor configuration hidden).erase tape
    let flat : SuccessfulGammaPrefixTape := ⟨coordinates.2, success⟩
    let factored := successfulGammaPrefixFactorization flat
    exactPreQ16GammaFibreSample transitionFuel configuration hidden
        coordinates.1
        (successfulPreQ16GammaTape factored.1 factored.2) =
      (hidden, tape) := by
  dsimp only [exactPreQ16GammaFibreSample]
  apply Prod.ext
  · rfl
  · apply (exactCompilerGammaPrefixCoordinates parameters transitionFuel
      (exactPlainRomCursor configuration hidden).erase).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact Subtype.ext_iff.mp
        (successfulGammaPrefixFactorization.symm_apply_apply
          ⟨(exactCompilerGammaPrefixCoordinates parameters transitionFuel
            (exactPlainRomCursor configuration hidden).erase tape).2, success⟩)

/-- One literal counterfactual execution in the fibre with a width-29
failure on the fixed corrected word. -/
structure PreQ16GammaFibreK14FailureWitness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters)
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : QM31Exact) : Type where
  nonzero : gamma ≠ 0
  input : ExactK12OperationalInput transitionFuel configuration projection
    fixedInstance
      (exactPreQ16GammaFibreSample transitionFuel configuration hidden residual
        (successfulPreQ16GammaTape skeleton ⟨gamma, nonzero⟩))
  k13 : ExactPreQ16K13StageCertificate decoder input
  wordsExact : k13.words = words
  gammaExact : (exactK13ParsedProof input).gamma = gamma
  failure : Width29DecompositionFailure decoder k13.words
    (exactK13ParsedProof input).gamma
    (exactK13ParsedProof input).disclosedFinal
    (exactK13ParsedProof input).schedule
  fixedBranch : RestoredSelectedBranch decoder words gamma
  fixedFailure : Width29DecompositionFailure decoder words gamma
    fixedBranch.disclosedFinal fixedBranch.schedule
  fixedSelectedExact : fixedBranch.selected = Classical.choose fixedFailure

/-- Package an actual fibre failure after transporting its word and gamma to
the fixed fibre indices. -/
noncomputable def preQ16GammaFibreK14FailureWitnessOfActual
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {hidden : HiddenTape}
    {residual : ExactCompilerGammaPrefixResidual parameters}
    {skeleton : VariableGammaCompleteSkeleton}
    {gamma : QM31Exact}
    (nonzero : gamma ≠ 0)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance
        (exactPreQ16GammaFibreSample transitionFuel configuration hidden
          residual (successfulPreQ16GammaTape skeleton ⟨gamma, nonzero⟩)))
    (k13 : ExactPreQ16K13StageCertificate decoder input)
    (wordsExact : k13.words = words)
    (gammaExact : (exactK13ParsedProof input).gamma = gamma)
    (failure : Width29DecompositionFailure decoder k13.words
      (exactK13ParsedProof input).gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule) :
    PreQ16GammaFibreK14FailureWitness transitionFuel configuration projection
      fixedInstance decoder words hidden residual skeleton gamma := by
  have fixedFailure : Width29DecompositionFailure decoder words gamma
      (exactK13ParsedProof input).disclosedFinal
      (exactK13ParsedProof input).schedule := by
    simpa only [← wordsExact, ← gammaExact] using failure
  let fixedBranch : RestoredSelectedBranch decoder words gamma :=
    { disclosedFinal := (exactK13ParsedProof input).disclosedFinal
      schedule := (exactK13ParsedProof input).schedule
      selected := Classical.choose fixedFailure
      selectedExact := (Classical.choose_spec fixedFailure).1 }
  exact
    { nonzero := nonzero
      input := input
      k13 := k13
      wordsExact := wordsExact
      gammaExact := gammaExact
      failure := failure
      fixedBranch := fixedBranch
      fixedFailure := fixedFailure
      fixedSelectedExact := rfl }

noncomputable def PreQ16GammaFibreK14FailureWitness.branch
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {hidden : HiddenTape}
    {residual : ExactCompilerGammaPrefixResidual parameters}
    {skeleton : VariableGammaCompleteSkeleton}
    {gamma : QM31Exact}
    (witness : PreQ16GammaFibreK14FailureWitness transitionFuel configuration
      projection fixedInstance decoder words hidden residual skeleton gamma) :
    RestoredSelectedBranch decoder words gamma :=
  witness.fixedBranch

/-- Small algebraic carrier retained by the executable provider.  The large
compiler execution proving provenance remains in `Prop` below and is not
duplicated when the width-29 target theorem inspects this carrier. -/
structure PreQ16GammaFibreK14TargetWitness
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) : Type where
  nonzero : gamma ≠ 0
  branch : RestoredSelectedBranch decoder words gamma
  failure : Width29DecompositionFailure decoder words gamma
    branch.disclosedFinal branch.schedule
  selectedExact : branch.selected = Classical.choose failure

/-- Erase the compiler-heavy fields while retaining exactly the algebraic
certificate consumed by target membership. -/
noncomputable def PreQ16GammaFibreK14FailureWitness.target
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {hidden : HiddenTape}
    {residual : ExactCompilerGammaPrefixResidual parameters}
    {skeleton : VariableGammaCompleteSkeleton}
    {gamma : QM31Exact}
    (witness : PreQ16GammaFibreK14FailureWitness transitionFuel configuration
      projection fixedInstance decoder words hidden residual skeleton gamma) :
    PreQ16GammaFibreK14TargetWitness decoder words gamma :=
  { nonzero := witness.nonzero
    branch := witness.fixedBranch
    failure := witness.fixedFailure
    selectedExact := witness.fixedSelectedExact }

/-- A small target witness is admissible only when a literal reconstructed
compiler execution produces it.  This proposition is the provenance seal on
the provider; it contains no additional source assumption. -/
def PreQ16GammaFibreK14TargetRealized
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters)
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : QM31Exact)
    (target : PreQ16GammaFibreK14TargetWitness decoder words gamma) : Prop :=
  Nonempty {witness : PreQ16GammaFibreK14FailureWitness transitionFuel
    configuration projection fixedInstance decoder words hidden residual
      skeleton gamma // witness.target = target}

/-- Complete provider induced by the exact chronological coordinate fibre.
Unavailable and zero-gamma branches have empty support. -/
noncomputable def preQ16GammaFibreK14Provider
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters)
    (skeleton : VariableGammaCompleteSkeleton)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair) :
    RestoredSelectedBranchProvider decoder words := by
  classical
  exact
    { defaultResponse := defaultResponse
      defaultDisclosedFinal := defaultDisclosedFinal
      defaultSchedule := defaultSchedule
      defaultSelected := defaultSelected
      branch := fun gamma =>
        let Candidate := PreQ16GammaFibreK14TargetWitness decoder words gamma
        let Realized := PreQ16GammaFibreK14TargetRealized transitionFuel
          configuration projection fixedInstance decoder words hidden residual
            skeleton gamma
        if existsCandidate : ∃ target : Candidate, Realized target then
          some (Classical.choose existsCandidate).branch
        else none }

/-- Skeleton-indexed form consumed by the variable-prefix K1.4 probability
theorem. -/
noncomputable def preQ16GammaFibreVariableK14Provider
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (hidden : HiddenTape)
    (residual : ExactCompilerGammaPrefixResidual parameters)
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair) :
    VariablePrefixK14Provider decoder words :=
  fun skeleton =>
    preQ16GammaFibreK14Provider transitionFuel configuration projection
      fixedInstance decoder words hidden residual skeleton defaultResponse
        defaultDisclosedFinal defaultSchedule defaultSelected

/-- Every concrete fibre witness is retained by the pre-fixed provider. -/
theorem preQ16_gamma_fibre_provider_branch_of_witness
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {hidden : HiddenTape}
    {residual : ExactCompilerGammaPrefixResidual parameters}
    {skeleton : VariableGammaCompleteSkeleton}
    {gamma : QM31Exact}
    (defaultResponse : InitialMessage QM31Exact)
    (defaultDisclosedFinal : FinalMessage QM31Exact)
    (defaultSchedule : ExactSchedule)
    (defaultSelected : ExactCandidatePair)
    (witness : PreQ16GammaFibreK14FailureWitness transitionFuel configuration
      projection fixedInstance decoder words hidden residual skeleton gamma) :
    ∃ selectedTarget : PreQ16GammaFibreK14TargetWitness decoder words gamma,
      (preQ16GammaFibreK14Provider transitionFuel configuration projection
        fixedInstance decoder words hidden residual skeleton defaultResponse
          defaultDisclosedFinal defaultSchedule defaultSelected).branch gamma =
        some selectedTarget.branch := by
  classical
  let Candidate := PreQ16GammaFibreK14TargetWitness decoder words gamma
  let Realized := PreQ16GammaFibreK14TargetRealized transitionFuel configuration
    projection fixedInstance decoder words hidden residual skeleton gamma
  have actualRealized : Realized witness.target :=
    ⟨⟨witness, rfl⟩⟩
  have existsCandidate : ∃ target : Candidate, Realized target :=
    ⟨witness.target, actualRealized⟩
  let selectedTarget : Candidate := Classical.choose existsCandidate
  refine ⟨selectedTarget, ?_⟩
  unfold preQ16GammaFibreK14Provider
  dsimp only
  rw [dif_pos existsCandidate]

#print axioms exactPreQ16GammaFibreSample
#print axioms successfulPreQ16GammaTape
#print axioms successful_preQ16_gamma_tape_factorization
#print axioms exact_preQ16_gamma_fibre_sample_roundtrip
#print axioms preQ16GammaFibreK14FailureWitnessOfActual
#print axioms PreQ16GammaFibreK14FailureWitness.branch
#print axioms PreQ16GammaFibreK14TargetWitness
#print axioms PreQ16GammaFibreK14FailureWitness.target
#print axioms PreQ16GammaFibreK14TargetRealized
#print axioms preQ16GammaFibreK14Provider
#print axioms preQ16GammaFibreVariableK14Provider
#print axioms preQ16_gamma_fibre_provider_branch_of_witness

end
end AspisK1.V7Tag73PreQ16GammaFibreK14Provider
