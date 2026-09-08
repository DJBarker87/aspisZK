import AspisFormal.K1.V7Tag73ExactAlphaZeroPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactCompilerActualGammaReplayClosure
import AspisFormal.K1.V7Tag73ExactCompilerOrdinaryPrefixReplayLift

/-!
# Cache-aware replay of the production alpha-zero ordinary sampler

The accepted-source alpha-zero cut already exposes the exact fixed-table
output/advance chain and deployed decoder result.  This leaf connects that
source evidence to the role-neutral scheduler-native ordinary replay.  In
particular, the first creation of a coordinate may belong to any machine
actor: a later verifier cache hit is handled without allocating a second
random-oracle answer.

This proves one concrete production ordinary sampler replay.  It does not
yet assert the cross-sample coordinate factorization used by the K1.5
probability bound.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerAlphaZeroOrdinaryReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
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
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeOrdinaryReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The literal accepted alpha-zero sampler can be replayed from its first
fresh creation, even when later coordinates are cache hits caused by an
earlier adversary query.  The returned value and terminal execution are the
exact production ones. -/
theorem exact_compiler_actual_alpha_zero_ordinary_replay
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
      decoded.value = exactOperationalChallenge input (.alpha 0) := by
  obtain ⟨_evaluator, _segments, _beforeAlphaProducer, beforeAlpha,
      _afterAlphaSample, _afterAlpha, _afterBlocks, _afterFinal256,
      allOutputs, allAdvances, exactValue, _producerPrefixRun, _boundaryRun,
      _boundaryLookup, _squeezeRun, _afterAlphaExact, _alphaBindRun,
      _alphaBindLookup, _final256Run, outputsLength, advancesLength,
      coordinates, _terminalExact, _callsExact, acceptedParameter,
      exactDecode, operationalValue, _final256Lookup, _finalNonceLookup,
      _q16BaseExact⟩ :=
    exact_compiler_constructs_alpha_zero_prefix_coordinates input
  have ordinaryExact : decodeOrdinaryExact allOutputs =
      some ((exactOperationalTape input).messages.challengeValue (.alpha 0)) := by
    simpa [decodeChallengeParameter, samplerMode] using acceptedParameter
  obtain ⟨prefixDecoded, prefixRun, _noRemaining, decodedValue⟩ :=
    decodeOrdinaryExact_witness allOutputs
      ((exactOperationalTape input).messages.challengeValue (.alpha 0))
      ordinaryExact
  have valueRun : decodeTagQM31ExactLE prefixDecoded.value = some exactValue := by
    simpa [decodedValue] using exactDecode
  have outputsPositive : 0 < allOutputs.length := by
    rw [outputsLength]
    exact ((exactOperationalTape input).messages.challengeUse
      (.alpha 0)).consumesBlock
  cases allOutputs with
  | nil => simp at outputsPositive
  | cons output outputs =>
      cases coordinates with
      | @next initialDigest output advanced outputs advances outputLookup
          advanceLookup tail =>
          obtain ⟨firstPause, paused⟩ :=
            exact_compiler_final_lookup_has_full_target_pause input
              (gammaOutputInput beforeAlpha.digest) output outputLookup
          obtain ⟨decoded, replayRun, reconstructed, replayValue⟩ :=
            run_scheduler_native_ordinary_from_first_pause_actual_chain_succeeds
              input
                (exact_compiler_actual_gamma_coordinate_step transitionRoom input)
              (.next outputLookup advanceLookup tail) prefixDecoded exactValue
              prefixRun valueRun firstPause paused
          refine ⟨beforeAlpha.digest, output, outputs, advanced, advances,
            firstPause, decoded, .next outputLookup advanceLookup tail, paused,
            replayRun, reconstructed, ?_⟩
          exact replayValue.trans operationalValue.symm

#print axioms exact_compiler_actual_alpha_zero_ordinary_replay

end
end AspisK1.V7Tag73ExactCompilerAlphaZeroOrdinaryReplay
