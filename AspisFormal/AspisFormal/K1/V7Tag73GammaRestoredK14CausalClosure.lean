import AspisFormal.K1.V7Tag73GammaRestoredK14CausalSource

/-! # Probability-source closure from exact restored-gamma alignment -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option linter.constructorNameAsVariable false

namespace AspisK1.V7Tag73GammaRestoredK14CausalClosure

open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredGammaFullRouting
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14CausalSource
open AspisK1.V7Tag73GammaRestoredK14Probability
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73RestoredGammaFibreK14Membership
open AspisK1.V7Tag73RestoredGammaFibreK14Target
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixK14Probability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact causal alignment derives the event inclusion consumed by the
width-29 probability theorem. -/
noncomputable def ExactTag73GammaRestoredK14CausalSource.toProbabilitySource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : AspisK1.V7FsAokExperiment.PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {clean : Set (ExactCompilerSample HiddenTape parameters)}
    (causal : ExactTag73GammaRestoredK14CausalSource transitionFuel
      configuration projection fixedInstance decoder clean) :
    ExactTag73GammaRestoredK14Source transitionFuel configuration projection
      fixedInstance decoder clean where
  words := causal.words
  provider := fun hidden residual =>
    exactGammaRestoredK14CausalProvider transitionFuel configuration projection
      fixedInstance decoder causal.words causal.defaultResponse
        causal.defaultDisclosedFinal causal.defaultSchedule
          causal.defaultSelected hidden residual
  covered := by
    intro hidden answers member
    rcases member with ⟨cleanMember, input, k13, failure⟩
    exact causal.alignedAt hidden answers cleanMember input k13 failure

#print axioms ExactTag73GammaRestoredK14CausalSource.toProbabilitySource

end
end AspisK1.V7Tag73GammaRestoredK14CausalClosure
