import AspisFormal.K1.V7Tag73K13CommittedInputInvariant
import AspisFormal.K1.V7Tag73K13CommittedSnapshotExact

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CommittedSnapshotInvariant

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
open AspisK1.V7Tag73K13CommittedInputInvariant
open AspisK1.V7Tag73K13CommittedPreChallengeData
open AspisK1.V7Tag73K13CommittedPreChallengeInput
open AspisK1.V7Tag73K13CommittedSnapshotExact
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

theorem ExactCandidateDirectedK13CommittedInputInvariant.snapshotExact
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
    exactK13PreQueryExecutionSnapshot
        (source.execution (hidden, left.answers) left.input) =
      exactK13PreQueryExecutionSnapshot
        (source.execution (hidden, right.answers) right.input) := by
  let leftInput := exactK13CommittedPreChallengeInput source left.input left.k12
  let rightInput := exactK13CommittedPreChallengeInput source right.input right.k12
  have inputExact : leftInput = rightInput :=
    invariant candidate foldTrial finalTrial hidden context fold work skeleton
      left right
  rw [← committedInput_snapshot_exact source left.input left.k12,
    ← committedInput_snapshot_exact source right.input right.k12]
  exact congrArg ExactK13CommittedPreChallengeInput.snapshot inputExact

#print axioms ExactCandidateDirectedK13CommittedInputInvariant.snapshotExact

end AspisK1.V7Tag73K13CommittedSnapshotInvariant
