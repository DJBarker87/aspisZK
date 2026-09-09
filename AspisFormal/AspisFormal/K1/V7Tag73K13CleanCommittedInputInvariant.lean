import AspisFormal.K1.V7Tag73K13CleanViewFunctional
import AspisFormal.K1.V7Tag73K13CandidateDirectedSourceFactorization
import AspisFormal.K1.V7Tag73K13CommittedAuthenticatedExact
import AspisFormal.K1.V7Tag73K13CommittedExpectedExact
import AspisFormal.K1.V7Tag73K13CommittedSnapshotExact
import AspisFormal.K1.V7Tag73K13PreChallengeSemanticCongruence

/-!
# Compiler-clean uniqueness of the literal K1.3 committed input

The source noninterference obligation is required only between executions in
the fixed compiler-clean event.  Equality of the three algebraic view
components is derived from equality of the literal committed input.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanCommittedInputInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CandidateDirectedSourceFactorization
open AspisK1.V7Tag73K13CleanViewFunctional
open AspisK1.V7Tag73K13CommittedAuthenticatedExact
open AspisK1.V7Tag73K13CommittedExpectedExact
open AspisK1.V7Tag73K13CommittedPreChallengeData
open AspisK1.V7Tag73K13CommittedPreChallengeInput
open AspisK1.V7Tag73K13CommittedSnapshotExact
open AspisK1.V7Tag73K13PreChallengeSemanticCongruence
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One fixed candidate-directed coordinate fibre determines one literal
committed pre-query input among compiler-clean executions. -/
def ExactCleanCandidateDirectedK13CommittedInputInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) : Prop :=
  ∀ candidate foldTrial finalTrial hidden context fold work skeleton
      (left right : ExactCleanCandidateDirectedK13ViewWitness source candidate
        foldTrial finalTrial hidden context fold work skeleton),
    exactK13CommittedPreChallengeInput source left.base.input left.base.k12 =
      exactK13CommittedPreChallengeInput source right.base.input right.base.k12

/-- Literal committed-input uniqueness on clean fibres fixes the complete
pre-challenge view used by the finite-field collision argument. -/
theorem ExactCleanCandidateDirectedK13CommittedInputInvariant.toViewFunctional
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
    (invariant : ExactCleanCandidateDirectedK13CommittedInputInvariant
      transitionFuel configuration projection fixedInstance decoder source) :
    ExactCleanCandidateDirectedK13ViewFunctional transitionFuel configuration
      projection fixedInstance decoder source := by
  intro candidate foldTrial finalTrial hidden context fold work skeleton
    left right
  let leftInput := exactK13CommittedPreChallengeInput source left.base.input
    left.base.k12
  let rightInput := exactK13CommittedPreChallengeInput source right.base.input
    right.base.k12
  have inputExact : leftInput = rightInput :=
    invariant candidate foldTrial finalTrial hidden context fold work skeleton
      left right
  have snapshotExact :
      exactK13PreQueryExecutionSnapshot
          (source.execution (hidden, left.base.answers) left.base.input) =
        exactK13PreQueryExecutionSnapshot
          (source.execution (hidden, right.base.answers) right.base.input) := by
    rw [← committedInput_snapshot_exact source left.base.input left.base.k12,
      ← committedInput_snapshot_exact source right.base.input right.base.k12]
    exact congrArg ExactK13CommittedPreChallengeInput.snapshot inputExact
  have expectedExact :
      exactTag73K13ExpectedQueryVector decoder left.base.input left.base.k12 =
        exactTag73K13ExpectedQueryVector decoder right.base.input
          right.base.k12 := by
    rw [← committedInput_expected_exact source left.base.input left.base.k12,
      ← committedInput_expected_exact source right.base.input right.base.k12]
    exact congrArg (ExactK13CommittedPreChallengeInput.expected decoder) inputExact
  have authenticatedExact :
      exactTag73K13AuthenticatedQueryVector decoder left.base.input
          left.base.k12 =
        exactTag73K13AuthenticatedQueryVector decoder right.base.input
          right.base.k12 := by
    rw [← committedInput_authenticated_exact source left.base.input
        left.base.k12,
      ← committedInput_authenticated_exact source right.base.input
        right.base.k12]
    exact congrArg ExactK13CommittedPreChallengeInput.authenticated inputExact
  have preExact :
      source.preQueryDiscrepancy (hidden, left.base.answers) left.base.input =
        source.preQueryDiscrepancy (hidden, right.base.answers)
          right.base.input := by
    rw [source.preQueryDiscrepancyExact, source.preQueryDiscrepancyExact]
    exact preQueryDiscrepancy_congr_of_projection_eq
      (source.execution (hidden, left.base.answers) left.base.input)
      (source.execution (hidden, right.base.answers) right.base.input)
      snapshotExact
  change left.base.view = right.base.view
  rw [left.base.viewExact, right.base.viewExact]
  exact exactJointQueryBatchPreChallengeView_eq_of_components preExact
    expectedExact authenticatedExact

#print axioms ExactCleanCandidateDirectedK13CommittedInputInvariant
#print axioms
  ExactCleanCandidateDirectedK13CommittedInputInvariant.toViewFunctional

end
end AspisK1.V7Tag73K13CleanCommittedInputInvariant
