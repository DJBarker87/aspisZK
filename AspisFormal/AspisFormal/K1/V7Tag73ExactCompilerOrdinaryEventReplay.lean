import AspisFormal.K1.V7Tag73ExactCompilerActualGammaReplayClosure
import AspisFormal.K1.V7Tag73ExactCompilerOrdinaryPrefixReplayLift
import AspisFormal.K1.V7Tag73OperationalSemanticReplay

/-!
# Role-neutral replay of any accepted ordinary challenge event

This file extracts an exact output/advance coordinate chain from an arbitrary
successful work-erased event list and connects it to the cache-aware ordinary
scheduler replay.  The construction is generic in the challenge identifier;
logical ownership is used only to locate and decode the emitted sample record,
never to classify the first creator of a SHA coordinate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerOrdinaryEventReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerActualGammaReplayClosure
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerOrdinaryPrefixReplayLift
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
open AspisK1.V7Tag73SchedulerNativeOrdinaryReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73SemanticRoundReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Reusable pointwise statement produced by the cache-aware ordinary replay
bridge. -/
def ExactCompilerOrdinaryReplayAt
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
    decoded.value = exactOperationalChallenge input id

/-- Locate one literal challenge occurrence in a successful work-erased event
list and retain its complete consumed output/advance chain. -/
theorem challenge_coordinate_chain_in_work_erased_run
    (table : FixedOracleTable) (events : List MachineEvent)
    (state final : EvalState) (id : ChallengeId) (use : SamplerUse id)
    (member : (.challenge id use : MachineEvent) ∈ events)
    (run : runMachineEventsWorkErased table events state = some final) :
    ∃ (before afterSample afterBlocks : EvalState)
      (outputs advances : List Digest256),
      squeezeMany table (.challenge id) use.blocksUsed before =
          some (outputs, afterBlocks) ∧
      afterSample = { afterBlocks with
        samples := afterBlocks.samples ++ [{ id := id, blocks := outputs }] } ∧
      outputs.length = use.blocksUsed ∧
      advances.length = outputs.length ∧
      GammaTableCoordinateChain table before.digest outputs advances ∧
      { id := id, blocks := outputs } ∈ final.samples := by
  induction events generalizing state with
  | nil => simp at member
  | cons event rest ih =>
      simp only [runMachineEventsWorkErased] at run
      obtain ⟨next, eventRun, restRun⟩ := Option.bind_eq_some_iff.mp run
      rcases List.mem_cons.mp member with head | tail
      · subst event
        obtain ⟨outputs, afterBlocks, squeezeRun, nextExact, outputsLength,
            emitted⟩ :=
          challenge_event_work_erased_exposes_record table state next id use
            eventRun
        obtain ⟨advances, advancesLength, coordinates, _calls⟩ :=
          squeeze_many_coordinates table (.challenge id) use.blocksUsed state
            afterBlocks outputs squeezeRun
        have included := machine_events_work_erased_samples_included table rest
          next final restRun
        exact ⟨state, next, afterBlocks, outputs, advances, squeezeRun,
          nextExact, outputsLength, advancesLength, coordinates,
          included _ emitted⟩
      · exact ih (state := next) tail restRun

/-- Any successful ordinary challenge occurrence in the exact accepted source
admits an executable cache-aware replay that reconstructs the complete literal
production run and returns the exact operational challenge value. -/
theorem exact_compiler_actual_ordinary_event_replay
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
    (ordinary : samplerMode id = .ordinaryQm31)
    (member : (.challenge id use : MachineEvent) ∈ events)
    (run : runMachineEventsWorkErased (exactOperationalTable input) events
      state = some final)
    (decodedAtFinal : StateSamplesDecodeAs
      (exactOperationalTape input).messages final) :
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
      decoded.value = exactOperationalChallenge input id := by
  obtain ⟨before, _afterSample, _afterBlocks, allOutputs, allAdvances,
      _squeezeRun, _afterExact, outputsLength, advancesLength, coordinates,
      recordFinal⟩ :=
    challenge_coordinate_chain_in_work_erased_run
      (exactOperationalTable input) events state final id use member run
  have acceptedParameter := decodedAtFinal
    ({ id := id, blocks := allOutputs } : SampleRecord) recordFinal
  have ordinaryExact : decodeOrdinaryExact allOutputs =
      some ((exactOperationalTape input).messages.challengeValue id) := by
    simpa [decodeChallengeParameter, ordinary] using acceptedParameter
  obtain ⟨prefixDecoded, prefixRun, _noRemaining, decodedValue⟩ :=
    decodeOrdinaryExact_witness allOutputs
      ((exactOperationalTape input).messages.challengeValue id) ordinaryExact
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
            run_scheduler_native_ordinary_from_first_pause_actual_chain_succeeds
              input
                (exact_compiler_actual_gamma_coordinate_step transitionRoom input)
              (.next outputLookup advanceLookup tail) prefixDecoded exactValue
              prefixRun valueRun firstPause paused
          refine ⟨before.digest, output, outputs, advanced, advances,
            firstPause, decoded, .next outputLookup advanceLookup tail, paused,
            replayRun, reconstructed, ?_⟩
          exact replayValue.trans operationalValue.symm

/-- Pack the event-local theorem into its reusable pointwise predicate. -/
theorem exact_compiler_actual_ordinary_event_replay_at
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
    (ordinary : samplerMode id = .ordinaryQm31)
    (member : (.challenge id use : MachineEvent) ∈ events)
    (run : runMachineEventsWorkErased (exactOperationalTable input) events
      state = some final)
    (decodedAtFinal : StateSamplesDecodeAs
      (exactOperationalTape input).messages final) :
    ExactCompilerOrdinaryReplayAt input id := by
  unfold ExactCompilerOrdinaryReplayAt
  exact exact_compiler_actual_ordinary_event_replay transitionRoom input events
    state final id use ordinary member run decodedAtFinal

#print axioms ExactCompilerOrdinaryReplayAt
#print axioms challenge_coordinate_chain_in_work_erased_run
#print axioms exact_compiler_actual_ordinary_event_replay
#print axioms exact_compiler_actual_ordinary_event_replay_at

end
end AspisK1.V7Tag73ExactCompilerOrdinaryEventReplay
