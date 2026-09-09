import AspisFormal.K1.V7Tag73K13CandidateDirectedViewFunctional

/-!
# Semantic congruence of the K1.3 pre-challenge vectors

The expected and authenticated query vectors contain no independent source
choice.  They are determined by the parsed Tag-73 proof and the canonical
K1.2 extracted words.  This leaf isolates that fact so the remaining
candidate-directed source theorem only has to preserve those committed
values and the literal pre-query scalar.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13PreChallengeSemanticCongruence

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Equal parsed proofs and canonical K1.2 words give equal disclosed-final
evaluation vectors. -/
theorem exactTag73K13ExpectedQueryVector_congr
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftK12 : ExactPrefixK12Certificate left)
    (rightK12 : ExactPrefixK12Certificate right)
    (proofExact : exactK13ParsedProof left = exactK13ParsedProof right) :
    exactTag73K13ExpectedQueryVector decoder left leftK12 =
      exactTag73K13ExpectedQueryVector decoder right rightK12 := by
  funext ordinal
  simp only [exactTag73K13ExpectedQueryVector, exactK13Transcript,
    extractedIdealTranscript]
  rw [proofExact]

/-- The same two committed values determine the authenticated one-fold query
vector, including the selected alpha and the exact query positions. -/
theorem exactTag73K13AuthenticatedQueryVector_congr
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (leftK12 : ExactPrefixK12Certificate left)
    (rightK12 : ExactPrefixK12Certificate right)
    (proofExact : exactK13ParsedProof left = exactK13ParsedProof right)
    (wordsExact : leftK12.words = rightK12.words) :
    exactTag73K13AuthenticatedQueryVector decoder left leftK12 =
      exactTag73K13AuthenticatedQueryVector decoder right rightK12 := by
  funext ordinal
  simp only [exactTag73K13AuthenticatedQueryVector, exactK13Transcript,
    extractedIdealTranscript]
  rw [proofExact, wordsExact]

#print axioms exactTag73K13ExpectedQueryVector_congr
#print axioms exactTag73K13AuthenticatedQueryVector_congr

end
end AspisK1.V7Tag73K13PreChallengeSemanticCongruence
