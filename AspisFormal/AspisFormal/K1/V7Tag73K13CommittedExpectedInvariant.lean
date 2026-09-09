import AspisFormal.K1.V7Tag73K13CommittedExpectedExact
import AspisFormal.K1.V7Tag73K13CommittedInputInvariant

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CommittedExpectedInvariant

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
open AspisK1.V7Tag73K13CandidateDirectedViewFunctional
open AspisK1.V7Tag73K13CommittedExpectedExact
open AspisK1.V7Tag73K13CommittedInputInvariant
open AspisK1.V7Tag73K13CommittedPreChallengeData
open AspisK1.V7Tag73K13CommittedPreChallengeInput
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

theorem ExactCandidateDirectedK13CommittedInputInvariant.expectedExact
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
    (invariant : ExactCandidateDirectedK13CommittedInputInvariant
      transitionFuel configuration projection fixedInstance decoder source)
    {candidate foldTrial finalTrial hidden context fold work skeleton}
    (left right : ExactCandidateDirectedK13ViewWitness source candidate
      foldTrial finalTrial hidden context fold work skeleton) :
    exactTag73K13ExpectedQueryVector decoder left.input left.k12 =
      exactTag73K13ExpectedQueryVector decoder right.input right.k12 := by
  let leftInput := exactK13CommittedPreChallengeInput source left.input left.k12
  let rightInput := exactK13CommittedPreChallengeInput source right.input right.k12
  have inputExact : leftInput = rightInput :=
    invariant candidate foldTrial finalTrial hidden context fold work skeleton
      left right
  rw [← committedInput_expected_exact source left.input left.k12,
    ← committedInput_expected_exact source right.input right.k12]
  exact congrArg (ExactK13CommittedPreChallengeInput.expected decoder) inputExact

#print axioms ExactCandidateDirectedK13CommittedInputInvariant.expectedExact

end AspisK1.V7Tag73K13CommittedExpectedInvariant
