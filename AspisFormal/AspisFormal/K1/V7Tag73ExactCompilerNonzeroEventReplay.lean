import AspisFormal.K1.V7Tag73ExactCompilerActualGammaReplayClosure
import AspisFormal.K1.V7Tag73ExactCompilerOrdinaryEventReplay

/-!
# Role-neutral replay of any accepted nonzero challenge event

This is the nonzero-sampler counterpart of the generic ordinary-event replay.
It reuses the exact event coordinate extractor and the three-attempt deployed
nonzero decoder, while retaining adversary-first/cache-hit behavior.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerNonzeroEventReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerActualGammaReplayClosure
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerOrdinaryEventReplay
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

def ExactCompilerNonzeroReplayAt
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
    (id : ChallengeId) : Prop :=
  ∃ (initialDigest output : Digest256) (outputs : List Digest256)
    (advanced : Digest256) (advances : List Digest256)
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) (gammaOutputInput initialDigest))
    (decoded : DecodedSchedulerNativeGammaResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result)),
    GammaTableCoordinateChain (exactOperationalTable input) initialDigest
        (output :: outputs) (advanced :: advances) ∧
    exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
      .paused firstPause ∧
    runSchedulerNativeGammaFromFirstPause transitionFuel firstPause
        ((output, advanced) :: outputs.zip advances) = .ok decoded ∧
    decoded.response.run =
      runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) ∧
    decoded.value = exactOperationalChallenge input id

theorem exact_compiler_actual_nonzero_event_replay_at
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
      fixedInstance sample)
    (events : List MachineEvent) (state final : EvalState)
    (id : ChallengeId) (use : SamplerUse id)
    (nonzero : samplerMode id = .nonzeroQm31)
    (member : (.challenge id use : MachineEvent) ∈ events)
    (run : runMachineEventsWorkErased (exactOperationalTable input) events
      state = some final)
    (decodedAtFinal : StateSamplesDecodeAs
      (exactOperationalTape input).messages final) :
    ExactCompilerNonzeroReplayAt input id := by
  obtain ⟨before, _afterSample, _afterBlocks, allOutputs, allAdvances,
      _squeezeRun, _afterExact, outputsLength, advancesLength, coordinates,
      recordFinal⟩ :=
    challenge_coordinate_chain_in_work_erased_run
      (exactOperationalTable input) events state final id use member run
  have acceptedParameter := decodedAtFinal
    ({ id := id, blocks := allOutputs } : SampleRecord) recordFinal
  have nonzeroExact : decodeNonzeroExact allOutputs =
      some ((exactOperationalTape input).messages.challengeValue id) := by
    simpa [decodeChallengeParameter, nonzero] using acceptedParameter
  obtain ⟨prefixDecoded, prefixRun, _noRemaining, decodedValue⟩ :=
    decodeNonzeroExact_witness allOutputs
      ((exactOperationalTape input).messages.challengeValue id) nonzeroExact
  obtain ⟨exactValue, exactDecode⟩ :=
    decodeChallengeParameter_has_exact_tower_value
      exactSecureCircleParameterMap id allOutputs
        ((exactOperationalTape input).messages.challengeValue id)
          acceptedParameter
  have valueRun : decodeTagQM31ExactLE prefixDecoded.value = some exactValue := by
    simpa [decodedValue] using exactDecode
  have operationalValue : exactOperationalChallenge input id = exactValue := by
    simp [exactOperationalChallenge, exactChallengeValue, exactDecode]
  have outputsPositive : 0 < allOutputs.length := by
    rw [outputsLength]
    exact use.consumesBlock
  cases allOutputs with
  | nil => simp at outputsPositive
  | cons output outputs =>
      cases coordinates with
      | @next initialDigest output advanced outputs advances outputLookup
          advanceLookup tail =>
          obtain ⟨firstPause, paused⟩ :=
            exact_compiler_final_lookup_has_full_target_pause input
              (gammaOutputInput before.digest) output outputLookup
          obtain ⟨decoded, replayRun, reconstructed, replayValue⟩ :=
            run_scheduler_native_gamma_from_first_pause_actual_chain_succeeds
              input
                (exact_compiler_actual_gamma_coordinate_step transitionRoom input)
              (.next outputLookup advanceLookup tail) prefixDecoded exactValue
              prefixRun valueRun firstPause paused
          refine ⟨before.digest, output, outputs, advanced, advances,
            firstPause, decoded, .next outputLookup advanceLookup tail, paused,
            replayRun, reconstructed, ?_⟩
          exact replayValue.trans operationalValue.symm

#print axioms ExactCompilerNonzeroReplayAt
#print axioms exact_compiler_actual_nonzero_event_replay_at

end
end AspisK1.V7Tag73ExactCompilerNonzeroEventReplay
