import AspisFormal.K1.V7Tag73ExactCompilerAlphaZeroOrdinaryReplay
import AspisFormal.K1.V7Tag73ExactCompilerOrdinaryEventReplay

/-!
# Production replay for all four relation-alpha samplers

Round zero is cut from the pre-q16 accepted prefix; rounds one through three
occur in the accepted post-q16 relation tail.  All four are connected to the
same role-neutral cache-aware ordinary replay primitive.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerRelationAlphaOrdinaryReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerAlphaZeroOrdinaryReplay
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerOrdinaryEventReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeOrdinaryReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def ExactRelationAlphaOrdinaryReplayAt
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
    (round : Fin 4) : Prop :=
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
    decoded.value = exactOperationalChallenge input (.alpha round)

theorem exact_compiler_all_relation_alpha_ordinary_replays
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
    ∀ round, ExactRelationAlphaOrdinaryReplayAt input round := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  have finalDecoded := exact_operational_input_final_samples_decode input
    evaluator
  intro round
  fin_cases round
  · exact exact_compiler_actual_alpha_zero_ordinary_replay transitionRoom
      input
  · unfold ExactRelationAlphaOrdinaryReplayAt
    exact exact_compiler_actual_ordinary_event_replay transitionRoom input
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState (.alpha 1)
      ((exactOperationalTape input).messages.challengeUse (.alpha 1))
      (by rfl)
      (by simp [afterAcceptedQueryScan, relationTailEvents, challengeEvent])
      evaluator.afterQ16Run finalDecoded
  · unfold ExactRelationAlphaOrdinaryReplayAt
    exact exact_compiler_actual_ordinary_event_replay transitionRoom input
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState (.alpha 2)
      ((exactOperationalTape input).messages.challengeUse (.alpha 2))
      (by rfl)
      (by simp [afterAcceptedQueryScan, relationTailEvents, challengeEvent])
      evaluator.afterQ16Run finalDecoded
  · unfold ExactRelationAlphaOrdinaryReplayAt
    exact exact_compiler_actual_ordinary_event_replay transitionRoom input
      (afterAcceptedQueryScan (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState (.alpha 3)
      ((exactOperationalTape input).messages.challengeUse (.alpha 3))
      (by rfl)
      (by simp [afterAcceptedQueryScan, relationTailEvents, challengeEvent])
      evaluator.afterQ16Run finalDecoded

#print axioms ExactRelationAlphaOrdinaryReplayAt
#print axioms exact_compiler_all_relation_alpha_ordinary_replays

end
end AspisK1.V7Tag73ExactCompilerRelationAlphaOrdinaryReplay
