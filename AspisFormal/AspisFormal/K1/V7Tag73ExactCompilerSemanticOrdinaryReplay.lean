import AspisFormal.K1.V7Tag73AcceptedSemanticExecution
import AspisFormal.K1.V7Tag73ExactCompilerOrdinaryEventReplay
import AspisFormal.K1.V7Tag73K15SemanticSequentialRouter

/-!
# Production replay for all 22 semantic ordinary samplers

The semantic K1.5 family consists of theta, ten zerocheck coordinates, mu,
and ten semantic sumcheck challenges.  This leaf instantiates the generic
cache-aware ordinary-event theorem at every one of those literal accepted
events.  It proves source/run/value agreement pointwise; the subsequent
probability leaf must still package the whole family into one pre-answer
coordinate equivalence.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerSemanticOrdinaryReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CausalEventReplay
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerOrdinaryEventReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeOrdinaryReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Pointwise exact production replay statement for one semantic position. -/
def ExactSemanticOrdinaryReplayAt
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (position : SemanticOrdinaryPosition) : Prop :=
  ∃ (initialDigest output : Digest256) (outputs : List Digest256)
    (advanced : Digest256) (advances : List Digest256)
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) (gammaOutputInput initialDigest))
    (decoded : DecodedSchedulerNativeOrdinaryResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result)),
    GammaTableCoordinateChain (exactOperationalTable input) initialDigest
        (output :: outputs) (advanced :: advances) ∧
    exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
      .paused firstPause ∧
    runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
        ((output, advanced) :: outputs.zip advances) = .ok decoded ∧
    decoded.response.run =
      runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) ∧
    decoded.value = exactOperationalChallenge input position.challengeId

/-- Every one of the 22 accepted semantic ordinary samplers has a cache-aware
source replay with the exact operational value and full production result. -/
theorem exact_compiler_all_semantic_ordinary_replays
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∀ position, ExactSemanticOrdinaryReplayAt input position := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  obtain ⟨segments⟩ := complete_evaluator_exposes_semantic_segments
    (exactOperationalTable input) (exactOperationalTape input)
      (exactOperationalRawTrace input) evaluator
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  have beforeEtaDecoded : StateSamplesDecodeAs
      (exactOperationalTape input).messages segments.beforeEta :=
    state_samples_decode_of_included (exactOperationalTape input).messages
      segments.beforeEta evaluator.finalState
        (semantic_beforeEta_samples_included_final
          (exactOperationalTable input) (exactOperationalTape input)
            (exactOperationalRawTrace input) evaluator segments)
          finalDecoded
  have semanticDecoded : StateSamplesDecodeAs
      (exactOperationalTape input).messages segments.afterSemantic := by
    have decoded := semantic_segments_decode_from_final_ledger
      (exactOperationalTable input) (exactOperationalTape input)
        (exactOperationalRawTrace input) evaluator segments finalDecoded
    simpa [StateSamplesDecodeAs, SamplesDecodeAs] using decoded
  intro position
  unfold ExactSemanticOrdinaryReplayAt
  cases position with
  | theta =>
      exact exact_compiler_actual_ordinary_event_replay transitionRoom input
        (beforeEtaTailEvents (exactOperationalTape input).messages)
        evaluator.afterC2 segments.beforeEta .theta
        ((exactOperationalTape input).messages.challengeUse .theta)
        (by rfl) (by simp [beforeEtaTailEvents, challengeEvent])
        segments.beforeEtaRun beforeEtaDecoded
  | zerocheckPoint coordinate =>
      apply exact_compiler_actual_ordinary_event_replay transitionRoom input
        (beforeEtaTailEvents (exactOperationalTape input).messages)
        evaluator.afterC2 segments.beforeEta (.zerocheckPoint coordinate)
        ((exactOperationalTape input).messages.challengeUse
          (.zerocheckPoint coordinate))
        (by rfl)
      · fin_cases coordinate <;> simp [beforeEtaTailEvents, challengeEvent]
      · exact segments.beforeEtaRun
      · exact beforeEtaDecoded
  | mu =>
      exact exact_compiler_actual_ordinary_event_replay transitionRoom input
        (beforeEtaTailEvents (exactOperationalTape input).messages)
        evaluator.afterC2 segments.beforeEta .mu
        ((exactOperationalTape input).messages.challengeUse .mu)
        (by rfl) (by simp [beforeEtaTailEvents, challengeEvent])
        segments.beforeEtaRun beforeEtaDecoded
  | sumcheck round =>
      exact exact_compiler_actual_ordinary_event_replay transitionRoom input
        (semanticEvents (exactOperationalTape input).messages)
        segments.afterEta segments.afterSemantic (.semantic round)
        ((exactOperationalTape input).messages.challengeUse (.semantic round))
        (by rfl)
        (production_semantic_challenge_mem
          (exactOperationalTape input).messages round)
        segments.semanticRun semanticDecoded

#print axioms ExactSemanticOrdinaryReplayAt
#print axioms exact_compiler_all_semantic_ordinary_replays

end
end AspisK1.V7Tag73ExactCompilerSemanticOrdinaryReplay
