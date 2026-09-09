import AspisFormal.K1.V7Tag73K13CommittedPreChallengeInput

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CommittedAuthenticatedExact

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
open AspisK1.V7Tag73K13CommittedPreChallengeInput
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

theorem committedInput_authenticated_exact
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
    (exactK13CommittedPreChallengeInput source input k12).authenticated =
      exactTag73K13AuthenticatedQueryVector decoder input k12 := by
  funext ordinal
  simp only [ExactK13CommittedPreChallengeInput.authenticated,
    exactK13CommittedPreChallengeInput,
    exactTag73K13AuthenticatedQueryVector, exactK13Transcript,
    extractedIdealTranscript]

#print axioms committedInput_authenticated_exact

end AspisK1.V7Tag73K13CommittedAuthenticatedExact
