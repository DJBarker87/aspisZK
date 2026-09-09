import AspisFormal.K1.V7Tag73K13CandidateDirectedViewAlignedAt

/-!
# Candidate-directed K1.3 view alignment record

The pointwise theorem is compiled separately; this module only packages it in
the source-alignment interface consumed by the probability closure.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K13CandidateDirectedViewAlignment

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedSourceBridge
open AspisK1.V7Tag73K13CandidateDirectedViewAlignedAt
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A functional coordinate fibre constructs the exact source alignment
consumed by the candidate-directed probability theorem. -/
noncomputable def ExactCandidateDirectedK13ViewFunctional.toViewAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    (functional : ExactCandidateDirectedK13ViewFunctional transitionFuel
      configuration projection fixedInstance decoder source) :
    ExactCandidateDirectedK13ViewAlignment transitionFuel configuration
      projection fixedInstance decoder source where
  view := exactCandidateDirectedFunctionalView source
  alignedAt := exactCandidateDirectedFunctionalView_alignedAt functional

#print axioms ExactCandidateDirectedK13ViewFunctional.toViewAlignment

end
end AspisK1.V7Tag73K13CandidateDirectedViewAlignment
