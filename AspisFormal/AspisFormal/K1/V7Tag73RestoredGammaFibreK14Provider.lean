import AspisFormal.K1.V7Tag73ExactRestoredGammaFullRouting
import AspisFormal.K1.V7Tag73ExactRestoredOperationalStages
import AspisFormal.K1.V7Tag73VariablePrefixGammaFlatRouting

/-!
# K1.4 provider generated from one restored-gamma coordinate fibre

The width-29 response family is not a source assumption.  At a fixed hidden
tape, residual coordinate and successful sampler skeleton, run the literal
compiler at every nonzero gamma coordinate and retain a restored K1.3 branch
exactly when that execution exhibits a width-29 failure on the fixed
authenticated words.  This produces the complete challenge-indexed provider
required by the published degree bound.

The remaining source layer only has to show that an actual clean failure has
the fixed fibre words and that its verifier-derived gamma is the value decoded
from the routed restored-gamma tape.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73RestoredGammaFibreK14Provider

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalRestoredFamily
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredOperationalStages
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CandidateChainExtraction
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Reconstruct the exact compiler sample at one point of a fixed
restored-gamma coordinate fibre. -/
def exactRestoredGammaFibreSample
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
    (exactCompilerRestoredGammaCoordinates transitionFuel configuration hidden).symm
      (residual, flat.1))

/-- The successful tape with exactly the requested nuisance skeleton and
nonzero gamma value. -/
def successfulRestoredGammaTape
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact) : SuccessfulGammaPrefixTape :=
  successfulGammaPrefixFactorization.symm (skeleton, gamma)

@[simp] theorem successful_restored_gamma_tape_factorization
    (skeleton : VariableGammaCompleteSkeleton)
    (gamma : NonzeroQM31Exact) :
    successfulGammaPrefixFactorization
        (successfulRestoredGammaTape skeleton gamma) =
      (skeleton, gamma) := by
  exact successfulGammaPrefixFactorization.apply_symm_apply (skeleton, gamma)

/-- Reconstructing a sample from its actual residual and successful
gamma-factorization coordinates returns the byte-for-byte original compiler
sample. -/
theorem exact_restored_gamma_fibre_sample_roundtrip
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (success : GammaPrefixSucceeds
      (exactCompilerRestoredGammaCoordinates transitionFuel configuration
        hidden tape).2) :
    let coordinates := exactCompilerRestoredGammaCoordinates transitionFuel
      configuration hidden tape
    let flat : SuccessfulGammaPrefixTape := ⟨coordinates.2, success⟩
    let factored := successfulGammaPrefixFactorization flat
    exactRestoredGammaFibreSample transitionFuel configuration hidden
        coordinates.1
        (successfulRestoredGammaTape factored.1 factored.2) =
      (hidden, tape) := by
  dsimp only [exactRestoredGammaFibreSample]
  apply Prod.ext
  · rfl
  · apply (exactCompilerRestoredGammaCoordinates transitionFuel configuration
      hidden).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · exact Subtype.ext_iff.mp
        (successfulGammaPrefixFactorization.symm_apply_apply
          ⟨(exactCompilerRestoredGammaCoordinates transitionFuel configuration
            hidden tape).2, success⟩)

/-- One literal counterfactual execution in the fibre that supplies a
width-29 failing restored branch on the fixed authenticated word vector. -/
structure RestoredGammaFibreK14FailureWitness
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
      (exactRestoredGammaFibreSample transitionFuel configuration hidden residual
        (successfulRestoredGammaTape skeleton ⟨gamma, nonzero⟩))
  k13 : ExactRestoredOperationalK13Certificate decoder input
  wordsExact : k13.classified.k12.words = words
  gammaExact : (restoredOperationalK13View k13.data).gamma = gamma
  failure : Width29DecompositionFailure decoder k13.classified.k12.words
    (restoredOperationalK13View k13.data).gamma
    (restoredOperationalK13View k13.data).disclosedFinal
    (restoredOperationalK13View k13.data).schedule
  fixedBranch : RestoredSelectedBranch decoder words gamma
  fixedFailure : Width29DecompositionFailure decoder words gamma
    fixedBranch.disclosedFinal fixedBranch.schedule
  fixedSelectedExact : fixedBranch.selected = Classical.choose fixedFailure

/-- Transport one literal compiler failure onto the fixed word/gamma indices
of its coordinate fibre.  All dependent rewriting is isolated here so the
provider and probability leaves remain small. -/
noncomputable def restoredGammaFibreK14FailureWitnessOfActual
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
        (exactRestoredGammaFibreSample transitionFuel configuration hidden
          residual (successfulRestoredGammaTape skeleton ⟨gamma, nonzero⟩)))
    (k13 : ExactRestoredOperationalK13Certificate decoder input)
    (wordsExact : k13.classified.k12.words = words)
    (gammaExact : (restoredOperationalK13View k13.data).gamma = gamma)
    (failure : Width29DecompositionFailure decoder k13.classified.k12.words
      (restoredOperationalK13View k13.data).gamma
      (restoredOperationalK13View k13.data).disclosedFinal
      (restoredOperationalK13View k13.data).schedule) :
    RestoredGammaFibreK14FailureWitness transitionFuel configuration projection
      fixedInstance decoder words hidden residual skeleton gamma := by
  have fixedFailure : Width29DecompositionFailure decoder words gamma
      (restoredOperationalK13View k13.data).disclosedFinal
      (restoredOperationalK13View k13.data).schedule := by
    simpa only [← wordsExact, ← gammaExact] using failure
  let fixedBranch : RestoredSelectedBranch decoder words gamma :=
    { disclosedFinal := (restoredOperationalK13View k13.data).disclosedFinal
      schedule := (restoredOperationalK13View k13.data).schedule
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

/-- Forget the witness packaging while retaining the exact failing response.
The canonical selected pair is taken directly from the width-29 failure, so
no proof-irrelevance or choice-alignment premise is needed. -/
noncomputable def RestoredGammaFibreK14FailureWitness.branch
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
    (witness : RestoredGammaFibreK14FailureWitness transitionFuel configuration
      projection fixedInstance decoder words hidden residual skeleton gamma) :
    RestoredSelectedBranch decoder words gamma :=
  witness.fixedBranch

/-- The complete response provider induced by a literal coordinate fibre.
For zero gamma, or when the counterfactual compiler has no failing restored
branch, the provider is unavailable and its defaults have empty support. -/
noncomputable def restoredGammaFibreK14Provider
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
        let Candidate := RestoredGammaFibreK14FailureWitness transitionFuel
          configuration projection fixedInstance decoder words hidden residual
            skeleton gamma
        if existsCandidate : Nonempty Candidate then
          some (RestoredGammaFibreK14FailureWitness.branch
            (Classical.choice existsCandidate))
        else none }

/-- A concrete fibre witness is retained by the generated provider.  This
small routing fact is kept separate from the width-29 algebraic membership
proof so source-heavy consumers do not force Lean to normalize both layers at
once. -/
theorem restored_gamma_fibre_provider_branch_of_witness
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
    (witness : RestoredGammaFibreK14FailureWitness transitionFuel configuration
      projection fixedInstance decoder words hidden residual skeleton gamma) :
    ∃ selectedWitness : RestoredGammaFibreK14FailureWitness transitionFuel
        configuration projection fixedInstance decoder words hidden residual
          skeleton gamma,
      (restoredGammaFibreK14Provider transitionFuel configuration projection
        fixedInstance decoder words hidden residual skeleton defaultResponse
          defaultDisclosedFinal defaultSchedule defaultSelected).branch gamma =
        some selectedWitness.branch := by
  classical
  let Candidate := RestoredGammaFibreK14FailureWitness transitionFuel
    configuration projection fixedInstance decoder words hidden residual
      skeleton gamma
  have existsCandidate : Nonempty Candidate := ⟨witness⟩
  let selectedWitness : Candidate := Classical.choice existsCandidate
  refine ⟨selectedWitness, ?_⟩
  unfold restoredGammaFibreK14Provider
  dsimp only
  rw [dif_pos existsCandidate]

#print axioms exactRestoredGammaFibreSample
#print axioms successfulRestoredGammaTape
#print axioms successful_restored_gamma_tape_factorization
#print axioms exact_restored_gamma_fibre_sample_roundtrip
#print axioms restoredGammaFibreK14FailureWitnessOfActual
#print axioms RestoredGammaFibreK14FailureWitness.branch
#print axioms restoredGammaFibreK14Provider
#print axioms restored_gamma_fibre_provider_branch_of_witness

end
end AspisK1.V7Tag73RestoredGammaFibreK14Provider
