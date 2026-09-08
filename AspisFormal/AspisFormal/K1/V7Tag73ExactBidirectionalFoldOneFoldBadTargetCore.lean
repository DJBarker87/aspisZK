import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
import AspisFormal.K1.V7Tag73ExactInternalCurveProbability

/-! # Lightweight exact one-fold context from an executable replay family -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact degree-three context obtained from the literal counterfactual replay
family of one accepted seed execution. -/
def exactAcceptedFoldOneFoldContext
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoded : Fin 641 → QM31Exact}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (words : ExtractedWords)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactParsedProofSourceBinding input decoded)
    (skeleton : Tag73OrdinarySamplerSkeleton) :
    ExactCausalOneFoldSamplerContext where
  schedule := (exactK13ParsedProof input).schedule
  encoders := exactK13Encoders decoder
  initialEncoderExact := initialEncoderExact
  finalEncoderExact := finalEncoderExact
  inverseTablesExact := source.inverseTablesExact
  base := counterfactualOneFoldBase
    (exactAcceptedFoldReplayOracle words input fold)
  strategy := counterfactualOneFoldStrategy decoder
    (exactAcceptedFoldReplayOracle words input fold)
    (skeleton, fun _ => fold.answer)

/-- Pointwise target membership with the exact context kept abstract.  This is
the small kernel step from a causal bad response to the finite degree-three
target; operational replay normalization is deliberately outside this lemma. -/
theorem mem_exactRawOneFoldTarget_of_badResponse
    (context : Tag73OrdinarySamplerSkeleton →
      ExactCausalOneFoldSamplerContext)
    (skeleton : Tag73OrdinarySamplerSkeleton)
    (alpha : QM31Exact)
    (bad : CausalOneFoldBadResponse (context skeleton).schedule
      (context skeleton).encoders
      (exactOneFoldAlgebraBinding (context skeleton).schedule
        (context skeleton).encoders
        (context skeleton).initialEncoderExact
        (context skeleton).finalEncoderExact
        (context skeleton).inverseTablesExact)
      (context skeleton).base (context skeleton).strategy alpha) :
    alpha ∈ exactRawOneFoldTarget context skeleton := by
  change alpha ∈ causalOneFoldFailureTarget (context skeleton).schedule
    (context skeleton).encoders
    (exactOneFoldAlgebraBinding (context skeleton).schedule
      (context skeleton).encoders
      (context skeleton).initialEncoderExact
      (context skeleton).finalEncoderExact
      (context skeleton).inverseTablesExact)
    (context skeleton).base (context skeleton).strategy
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad

/-- Definitional exposure of the exact fixed bad target.  Keeping this as a
small leaf avoids asking the final source theorem to normalize the complete
operational replay term in one step. -/
theorem exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoded : Fin 641 → QM31Exact}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (words : ExtractedWords)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactParsedProofSourceBinding input decoded)
    (skeleton : Tag73OrdinarySamplerSkeleton) :
    exactRawOneFoldTarget
        (exactAcceptedFoldOneFoldContext decoder initialEncoderExact
          finalEncoderExact words input fold source) skeleton =
      causalOneFoldFailureTarget (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder)
        (exactOneFoldAlgebraBinding (exactK13ParsedProof input).schedule
          (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
          source.inverseTablesExact)
        (counterfactualOneFoldBase
          (exactAcceptedFoldReplayOracle words input fold))
        (counterfactualOneFoldStrategy decoder
          (exactAcceptedFoldReplayOracle words input fold)
          (skeleton, fun _ => fold.answer)) := by
  rfl

#print axioms exactAcceptedFoldOneFoldContext
#print axioms mem_exactRawOneFoldTarget_of_badResponse
#print axioms exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext

end
end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
