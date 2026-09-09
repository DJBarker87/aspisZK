import AspisFormal.K1.V7Tag73K13CleanViewFunctional

/-! # Activity of a represented compiler-clean K1.3 fibre -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanViewActive

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CleanViewFunctional
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

theorem exactCleanCandidateDirectedFunctionalView_active
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
    (functional : ExactCleanCandidateDirectedK13ViewFunctional transitionFuel
      configuration projection fixedInstance decoder source)
    {candidate foldTrial finalTrial hidden context fold work skeleton}
    (witness : ExactCleanCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    (exactCleanCandidateDirectedFunctionalView source candidate foldTrial
      finalTrial hidden context fold work skeleton).active = true := by
  rw [exactCleanCandidateDirectedFunctionalView_eq functional witness]
  exact witness.base.viewActive

#print axioms exactCleanCandidateDirectedFunctionalView_active

end
end AspisK1.V7Tag73K13CleanViewActive
