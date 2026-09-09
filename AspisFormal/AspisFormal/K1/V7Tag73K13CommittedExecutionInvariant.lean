import AspisFormal.K1.V7Tag73K13CommittedAuthenticatedInvariant
import AspisFormal.K1.V7Tag73K13CommittedExpectedInvariant
import AspisFormal.K1.V7Tag73K13CommittedSnapshotInvariant

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CommittedExecutionInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedSourceFactorization
open AspisK1.V7Tag73K13CommittedAuthenticatedInvariant
open AspisK1.V7Tag73K13CommittedExpectedInvariant
open AspisK1.V7Tag73K13CommittedInputInvariant
open AspisK1.V7Tag73K13CommittedSnapshotInvariant
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

theorem ExactCandidateDirectedK13CommittedInputInvariant.toExecutionInvariant
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
      transitionFuel configuration projection fixedInstance decoder source) :
    ExactCandidateDirectedK13CommittedExecutionInvariant transitionFuel
      configuration projection fixedInstance decoder source := by
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  exact ⟨
    AspisK1.V7Tag73K13CommittedSnapshotInvariant.ExactCandidateDirectedK13CommittedInputInvariant.snapshotExact
      invariant left right,
    AspisK1.V7Tag73K13CommittedExpectedInvariant.ExactCandidateDirectedK13CommittedInputInvariant.expectedExact
      invariant left right,
    AspisK1.V7Tag73K13CommittedAuthenticatedInvariant.ExactCandidateDirectedK13CommittedInputInvariant.authenticatedExact
      invariant left right⟩

#print axioms
  ExactCandidateDirectedK13CommittedInputInvariant.toExecutionInvariant

end AspisK1.V7Tag73K13CommittedExecutionInvariant
