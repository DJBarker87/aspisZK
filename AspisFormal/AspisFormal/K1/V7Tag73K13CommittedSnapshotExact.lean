import AspisFormal.K1.V7Tag73K13CommittedPreChallengeInput

set_option autoImplicit false

namespace AspisK1.V7Tag73K13CommittedSnapshotExact

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CommittedPreChallengeData
open AspisK1.V7Tag73K13CommittedPreChallengeInput
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

theorem committedInput_snapshot_exact
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input) :
    (exactK13CommittedPreChallengeInput source input k12).snapshot =
      exactK13PreQueryExecutionSnapshot (source.execution sample input) := by
  exact preQueryExecutionInput_snapshot_exact (source.execution sample input)

#print axioms committedInput_snapshot_exact

end AspisK1.V7Tag73K13CommittedSnapshotExact
