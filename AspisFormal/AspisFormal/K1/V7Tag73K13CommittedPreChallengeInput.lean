import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73K13CommittedPreChallengeData

/-!
# Literal committed input for candidate-directed K1.3

The query-batch collision target is fixed before the query-batch challenge is
returned.  This file packages the exact production values that determine that
target: the small pre-query relation state, the parsed final vector, the fold
schedule and positions, and the K1.2-extracted Merkle words.

The resulting source obligation is equality of this literal committed input on
one causal coordinate fibre.  Equality of the algebraic snapshot and both
query vectors is derived here; none is accepted as an independent premise.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CommittedPreChallengeInput

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CommittedPreChallengeData
open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Projection from one accepted operational run.  Every field is either a
maintained pre-query relation value, canonical parsed data, or canonical K1.2
output. -/
def exactK13CommittedPreChallengeInput
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
    ExactK13CommittedPreChallengeInput where
  execution := exactK13PreQueryExecutionInput (source.execution sample input)
  parsedDisclosedFinal := (exactK13ParsedProof input).disclosedFinal
  initialWord := (exactK13Transcript input k12).initial
  schedule := (exactK13ParsedProof input).schedule
  queries := (exactK13ParsedProof input).queries

end
end AspisK1.V7Tag73K13CommittedPreChallengeInput
