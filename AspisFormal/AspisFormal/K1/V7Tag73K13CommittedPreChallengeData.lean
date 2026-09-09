import AspisFormal.K1.V7Tag73ExactFixedK13K14Classifier
import AspisFormal.K1.V7Tag73K13PreQueryExecutionProjection

/-! # Pure committed pre-query data for candidate-directed K1.3 -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CommittedPreChallengeData

open AspisK1.V7Tag73K13PreQueryExecutionProjection
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5WithoutReplacementQuerySoundness
open AspisV6OneFoldCandidateExtraction

/-- All literal values that determine the pre-query K1.3 collision target.
The parsed final vector is retained separately from the relation execution's
copy so the source bridge cannot silently assume their equality. -/
structure ExactK13CommittedPreChallengeInput where
  execution : ExactK13PreQueryExecutionInput
  parsedDisclosedFinal : FinalMessage QM31Exact
  initialWord : AspisV6OneFoldCandidateExtraction.InitialWord QM31Exact
  schedule : ExactSchedule
  queries : QuerySchedule 16 262144

def ExactK13CommittedPreChallengeInput.snapshot
    (input : ExactK13CommittedPreChallengeInput) :
    ExactK13PreQueryExecutionSnapshot :=
  input.execution.snapshot

def ExactK13CommittedPreChallengeInput.expected
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK13CommittedPreChallengeInput) : Fin 16 → QM31Exact :=
  fun ordinal => decoder.finalEncoder input.parsedDisclosedFinal
    (input.queries ordinal)

def ExactK13CommittedPreChallengeInput.authenticated
    (input : ExactK13CommittedPreChallengeInput) : Fin 16 → QM31Exact :=
  fun ordinal =>
    circleFoldLayer 262144 input.schedule.alpha input.schedule.circleInv2x
      input.schedule.circleInv2y
      input.initialWord
      (input.queries ordinal)

end AspisK1.V7Tag73K13CommittedPreChallengeData
