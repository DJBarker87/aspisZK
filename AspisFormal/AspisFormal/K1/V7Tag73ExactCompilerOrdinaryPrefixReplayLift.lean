import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixReplayLift
import AspisFormal.K1.V7Tag73SchedulerNativeOrdinaryReplay

/-!
# Lift exact compiler coordinate steps through an ordinary sampler

The cache-or-future coordinate step is independent of the logical challenge
role.  This leaf lifts that invariant through the ordinary QM31 decoder and
the production first-output pause.  It is the common scheduler bridge needed
by semantic, relation-alpha, and fixed-family K1.5 source closures.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCompilerOrdinaryPrefixReplayLift

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaPrefixReplayLift
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSchedulerPauseBinding
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeOrdinaryReplay
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaCoordinates
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A successful ordinary-prefix driver over an exact final-table coordinate
chain reconstructs the literal production root run. -/
theorem run_scheduler_native_ordinary_prefix_actual_chain_reconstructs
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
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∀ {digest : Digest256} {outputs advances : List Digest256},
      GammaTableCoordinateChain (exactOperationalTable input) digest outputs
        advances →
      ∀ (consumedBlocks : Nat) (priorOutputs : List Digest256)
        (state : SchedulerNativeGammaCursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result))
        (aligned : ExactCompilerRootGammaCursorAligned input state)
        (decoded : DecodedSchedulerNativeOrdinaryResponse
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result)),
        runSchedulerNativeOrdinaryPrefix transitionFuel (outputs.zip advances)
            consumedBlocks digest priorOutputs state = .ok decoded →
          decoded.response.run =
            runSchedulerNativeListRun transitionFuel
              (exactPlainRomCursor configuration sample.1)
              (freshAnswerTapeToList sample.2) := by
  intro digest outputs advances chain
  induction chain with
  | done digest =>
      intro consumedBlocks priorOutputs state aligned decoded run
      simp [runSchedulerNativeOrdinaryPrefix] at run
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      intro consumedBlocks priorOutputs state aligned decoded run
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (gammaOutputInput digest) output state aligned
          outputLookup
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (gammaAdvanceInput digest) advanced afterOutput
          outputAligned advanceLookup
      simp only [List.zip_cons_cons, runSchedulerNativeOrdinaryPrefix] at run
      rw [outputRun] at run
      simp only at run
      rw [advanceRun] at run
      simp only at run
      split at run
      next decodedRun =>
        split at run
        next value valueRun => cases run
        next valueRun =>
          cases run
          exact exact_compiler_root_gamma_alignment_reconstructs_run input
            afterAdvance advanceAligned
      next decodedRun =>
        exact ih (consumedBlocks + 1) (priorOutputs ++ [output]) afterAdvance
          advanceAligned decoded run

/-- The same reconstruction holds at the production entry point whose first
output request has already been found by the exact root scanner. -/
theorem run_scheduler_native_ordinary_from_first_pause_actual_chain_reconstructs
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
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    {initialDigest output advanced : Digest256}
    {outputs advances : List Digest256}
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      initialDigest (output :: outputs) (advanced :: advances))
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) (gammaOutputInput initialDigest))
    (paused : exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
      .paused firstPause)
    (decoded : DecodedSchedulerNativeOrdinaryResponse
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result))
    (run : runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
      ((output, advanced) :: outputs.zip advances) = .ok decoded) :
    decoded.response.run =
      runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1)
        (freshAnswerTapeToList sample.2) := by
  cases chain with
  | next outputLookup advanceLookup tail =>
      let initial := exactCompilerInitialGammaCursor input
      let directAfterOutput : SchedulerNativeGammaCursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result) :=
        { cursor := firstPause.resumeCursorWith output
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input output
          tracePrefix := initial.tracePrefix ++ firstPause.consumedTrace ++
            [machineFreshRecord firstPause output] }
      have scanned : scanSchedulerNativeToInput transitionFuel
          (gammaOutputInput initialDigest) initial.cursor
          initial.remainingAnswers = .paused firstPause := paused
      have missing : lookupEntry initial.oracle
          (gammaOutputInput initialDigest) = none := rfl
      have directOutputRun :
          consumeSchedulerNativeGammaCoordinate transitionFuel .output
              (gammaOutputInput initialDigest) output initial =
            .ok directAfterOutput := by
        simpa [directAfterOutput, initial, List.append_assoc] using
          consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
            transitionFuel .output (gammaOutputInput initialDigest) output
              initial missing firstPause scanned
      obtain ⟨afterOutput, outputRun, ⟨afterOutputAligned⟩⟩ :=
        coordinateStep .output (gammaOutputInput initialDigest) output initial
          (exactCompilerInitialGammaCursorAlignment input) outputLookup
      have afterOutputExact : afterOutput = directAfterOutput := by
        rw [directOutputRun] at outputRun
        exact Except.ok.inj outputRun.symm
      subst afterOutput
      obtain ⟨afterAdvance, advanceRun, ⟨afterAdvanceAligned⟩⟩ :=
        coordinateStep .advance (gammaAdvanceInput initialDigest) advanced
          directAfterOutput afterOutputAligned advanceLookup
      have advanceRunDirect :
          consumeSchedulerNativeGammaCoordinate transitionFuel .advance
              (gammaAdvanceInput initialDigest) advanced
              { cursor := firstPause.resumeCursorWith output
                remainingAnswers := firstPause.remainingAnswers
                oracle := freshQueryState firstPause.actor
                  firstPause.requestState firstPause.input output
                tracePrefix := firstPause.consumedTrace ++
                  [machineFreshRecord firstPause output] } =
            .ok afterAdvance := by
        simpa [directAfterOutput, initial, exactCompilerInitialGammaCursor,
          List.append_assoc] using advanceRun
      simp only [runSchedulerNativeOrdinaryFromFirstPause] at run
      rw [advanceRunDirect] at run
      simp only at run
      split at run
      next decodedRun =>
        split at run
        next valueRun => cases run
        next valueRun =>
          cases run
          exact exact_compiler_root_gamma_alignment_reconstructs_run input
            afterAdvance afterAdvanceAligned
      next decodedRun =>
        exact run_scheduler_native_ordinary_prefix_actual_chain_reconstructs
          input coordinateStep tail 1 [output] afterAdvance afterAdvanceAligned
            decoded run

/-- A successful ordinary decoder equation over the exact coordinate chain
constructs a successful executable replay; replay success is not assumed. -/
theorem run_scheduler_native_ordinary_prefix_actual_chain_succeeds
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
    (coordinateStep : ExactCompilerGammaCoordinateStep input) :
    ∀ {digest : Digest256} {outputs advances : List Digest256},
      GammaTableCoordinateChain (exactOperationalTable input) digest outputs
          advances →
      ∀ (consumedBlocks : Nat) (priorOutputs : List Digest256)
        (state : SchedulerNativeGammaCursor
          (globalFull256OracleCallCap parameters)
          (SchedulerNativePlainRomResult TapeIdentity Statement
            Tag73K12ParsedProof Payload Result))
        (aligned : ExactCompilerRootGammaCursorAligned input state)
        (finalDecoded : OrdinaryPrefixDecode) (value : QM31Exact),
        decodeOrdinaryPrefix priorOutputs = none →
        decodeOrdinaryPrefix (priorOutputs ++ outputs) = some finalDecoded →
        decodeTagQM31ExactLE finalDecoded.value = some value →
        ∃ decoded : DecodedSchedulerNativeOrdinaryResponse
            (SchedulerNativePlainRomResult TapeIdentity Statement
              Tag73K12ParsedProof Payload Result),
          runSchedulerNativeOrdinaryPrefix transitionFuel (outputs.zip advances)
              consumedBlocks digest priorOutputs state = .ok decoded ∧
          decoded.response.run =
            runSchedulerNativeListRun transitionFuel
              (exactPlainRomCursor configuration sample.1)
              (freshAnswerTapeToList sample.2) ∧
          decoded.value = value := by
  intro digest outputs advances chain
  induction chain with
  | done digest =>
      intro consumedBlocks priorOutputs state aligned finalDecoded value
        priorNone fullRun valueRun
      simp only [List.append_nil] at fullRun
      rw [priorNone] at fullRun
      contradiction
  | @next digest output advanced outputs advances outputLookup advanceLookup
      tail ih =>
      intro consumedBlocks priorOutputs state aligned finalDecoded value
        priorNone fullRun valueRun
      obtain ⟨afterOutput, outputRun, ⟨outputAligned⟩⟩ :=
        coordinateStep .output (gammaOutputInput digest) output state aligned
          outputLookup
      obtain ⟨afterAdvance, advanceRun, ⟨advanceAligned⟩⟩ :=
        coordinateStep .advance (gammaAdvanceInput digest) advanced afterOutput
          outputAligned advanceLookup
      let nextOutputs := priorOutputs ++ [output]
      cases currentRun : decodeOrdinaryPrefix nextOutputs with
      | none =>
          simp only [nextOutputs] at currentRun
          have fullRun' : decodeOrdinaryPrefix (nextOutputs ++ outputs) =
              some finalDecoded := by
            simpa [nextOutputs, List.append_assoc] using fullRun
          obtain ⟨decoded, tailRun, reconstructed, decodedValue⟩ :=
            ih (consumedBlocks + 1) nextOutputs afterAdvance advanceAligned
              finalDecoded value currentRun fullRun' valueRun
          refine ⟨decoded, ?_, reconstructed, decodedValue⟩
          simp only [List.zip_cons_cons, runSchedulerNativeOrdinaryPrefix]
          rw [outputRun]
          simp only
          rw [advanceRun]
          simp only
          rw [currentRun]
          exact tailRun
      | some currentDecoded =>
          simp only [nextOutputs] at currentRun
          have extended := decodeOrdinaryPrefix_append_of_some nextOutputs
            outputs currentDecoded currentRun
          have decodedExact :
              appendOrdinaryRemaining currentDecoded outputs = finalDecoded := by
            apply Option.some.inj
            exact extended.symm.trans (by
              simpa [nextOutputs, List.append_assoc] using fullRun)
          have currentValueExact :
              decodeTagQM31ExactLE currentDecoded.value = some value := by
            rw [show currentDecoded.value = finalDecoded.value by
              rw [← decodedExact]
              rfl]
            exact valueRun
          simp only [List.zip_cons_cons, runSchedulerNativeOrdinaryPrefix]
          rw [outputRun]
          simp only
          rw [advanceRun]
          simp only
          rw [currentRun]
          simp only
          split
          next invalidRun =>
            rw [currentValueExact] at invalidRun
            contradiction
          next validRun =>
            refine ⟨_, rfl, ?_, ?_⟩
            · exact exact_compiler_root_gamma_alignment_reconstructs_run input
                afterAdvance advanceAligned
            · exact Option.some.inj (validRun.symm.trans currentValueExact)

/-- Production first-pause form of the constructive ordinary replay theorem. -/
theorem run_scheduler_native_ordinary_from_first_pause_actual_chain_succeeds
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
    (coordinateStep : ExactCompilerGammaCoordinateStep input)
    {initialDigest output advanced : Digest256}
    {outputs advances : List Digest256}
    (chain : GammaTableCoordinateChain (exactOperationalTable input)
      initialDigest (output :: outputs) (advanced :: advances))
    (finalDecoded : OrdinaryPrefixDecode) (value : QM31Exact)
    (prefixRun : decodeOrdinaryPrefix (output :: outputs) = some finalDecoded)
    (valueRun : decodeTagQM31ExactLE finalDecoded.value = some value)
    (firstPause : SchedulerNativeFreshPause
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) (gammaOutputInput initialDigest))
    (paused : exactCompilerFullTargetScan input (gammaOutputInput initialDigest) =
      .paused firstPause) :
    ∃ decoded : DecodedSchedulerNativeOrdinaryResponse
        (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
          Payload Result),
      runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
          ((output, advanced) :: outputs.zip advances) = .ok decoded ∧
      decoded.response.run =
        runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) ∧
      decoded.value = value := by
  let initial := exactCompilerInitialGammaCursor input
  let directAfterOutput : SchedulerNativeGammaCursor
      (globalFull256OracleCallCap parameters)
      (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
        Payload Result) :=
    { cursor := firstPause.resumeCursorWith output
      remainingAnswers := firstPause.remainingAnswers
      oracle := freshQueryState firstPause.actor firstPause.requestState
        firstPause.input output
      tracePrefix := initial.tracePrefix ++ firstPause.consumedTrace ++
        [machineFreshRecord firstPause output] }
  have scanned : scanSchedulerNativeToInput transitionFuel
      (gammaOutputInput initialDigest) initial.cursor initial.remainingAnswers =
        .paused firstPause := paused
  have missing : lookupEntry initial.oracle (gammaOutputInput initialDigest) =
      none := rfl
  have directOutputRun :
      consumeSchedulerNativeGammaCoordinate transitionFuel .output
          (gammaOutputInput initialDigest) output initial =
        .ok directAfterOutput := by
    simpa [directAfterOutput, initial, List.append_assoc] using
      consume_scheduler_native_gamma_fresh_uses_exact_pause_actor
        transitionFuel .output (gammaOutputInput initialDigest) output initial
          missing firstPause scanned
  obtain ⟨decoded, prefixDriverRun, reconstructed, decodedValue⟩ :=
    run_scheduler_native_ordinary_prefix_actual_chain_succeeds input
      coordinateStep chain 0 [] initial
        (exactCompilerInitialGammaCursorAlignment input) finalDecoded value rfl
        (by simpa using prefixRun) valueRun
  refine ⟨decoded, ?_, reconstructed, decodedValue⟩
  have driversExact :
      runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
          ((output, advanced) :: outputs.zip advances) =
        runSchedulerNativeOrdinaryPrefix transitionFuel
          ((output, advanced) :: outputs.zip advances) 0 initialDigest []
            initial := by
    simp only [runSchedulerNativeOrdinaryFromFirstPause,
      runSchedulerNativeOrdinaryPrefix]
    rw [directOutputRun]
    rfl
  rw [driversExact]
  exact prefixDriverRun

#print axioms
  run_scheduler_native_ordinary_prefix_actual_chain_reconstructs
#print axioms
  run_scheduler_native_ordinary_from_first_pause_actual_chain_reconstructs
#print axioms run_scheduler_native_ordinary_prefix_actual_chain_succeeds
#print axioms
  run_scheduler_native_ordinary_from_first_pause_actual_chain_succeeds

end
end AspisK1.V7Tag73ExactCompilerOrdinaryPrefixReplayLift
