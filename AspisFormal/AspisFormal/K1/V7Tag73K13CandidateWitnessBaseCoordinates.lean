import AspisFormal.K1.V7Tag73K13CandidateFibreBaseCoordinates
import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFunctional

/-!
# Candidate-witness base-coordinate equality

The candidate-directed witness stores the context, fold-work and final-work
coordinates separately.  Equality of those fields reconstructs the complete
542-coordinate prefix consumed by the causal replay theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CandidateWitnessBaseCoordinates

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
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CandidateFibreBaseCoordinates
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Two witnesses in one candidate-directed fibre have identical base
coordinates before the query-batch answer. -/
theorem candidate_witnesses_have_equal_base_coordinates
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
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {context : ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)}
    {fold work : Digest256}
    {skeleton : VariableGammaCompleteSkeleton}
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      (exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
        foldTrial.val finalTrial.val candidate
        (exactPlainRomCursor configuration hidden).erase) left.answers).1 =
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      (exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
        foldTrial.val finalTrial.val candidate
        (exactPlainRomCursor configuration hidden).erase) right.answers).1 := by
  apply candidate_context_fold_work_eq_implies_base_coordinates_eq
  · exact left.contextExact.trans right.contextExact.symm
  · exact left.foldExact.trans right.foldExact.symm
  · exact left.workExact.trans right.workExact.symm

#print axioms candidate_witnesses_have_equal_base_coordinates

end
end AspisK1.V7Tag73K13CandidateWitnessBaseCoordinates
