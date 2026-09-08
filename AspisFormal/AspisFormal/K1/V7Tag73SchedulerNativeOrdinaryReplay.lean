import AspisFormal.K1.V7Tag73SchedulerNativeGammaReplay
import AspisFormal.K1.V7Tag73K15OrdinaryDuplexCoordinates

/-!
# Scheduler-native replay of one ordinary Tag-73 duplex sampler

The gamma replay machinery contains a role-neutral cache-or-future coordinate
consumer, but its recursive driver is specialized to the three-attempt
nonzero decoder.  This leaf supplies the corresponding driver for an ordinary
QM31 challenge.  It consumes at most four output/advance pairs, accepts cache
hits without consuming the master tape, and scans to the exact fresh actor for
misses.  Thus it does not rely on a verifier-origin classifier and remains
valid when an adversary first exposed a later verifier coordinate.

This is an executable replay primitive only.  Source-specific leaves must
still prove that the selected duplex tape contains the literal production
coordinates and that the first output digest is the correct transcript state.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73SchedulerNativeOrdinaryReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73K15OrdinaryDuplexCoordinates
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerNativeTargetPause
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisV5ComponentCQM31TowerExact

noncomputable section

universe u

/-- Observable result of one ordinary sampler replay. -/
structure SchedulerNativeOrdinaryResponse (Result : Type u) where
  run : SchedulerNativeRun Result
  consumedBlocks : Nat
  returnedValue : Option QM31Exact
  decodedBytes : Option Qm31Bytes
  remainingAnswers : List Digest256

/-- Internal result retaining the exact deployed decoding equation. -/
structure DecodedSchedulerNativeOrdinaryResponse (Result : Type u) where
  response : SchedulerNativeOrdinaryResponse Result
  decoded : OrdinaryPrefixDecode
  value : QM31Exact
  valueExact : decodeTagQM31ExactLE decoded.value = some value
  responseBytesExact : response.decodedBytes = some decoded.value

/-- Four chronological output/advance pairs from the complete ordinary tape. -/
def ordinaryDuplexPairs (tape : TotalTag73DuplexOrdinaryTape) :
    List (Digest256 × Digest256) :=
  (List.ofFn tape.1).zip (List.ofFn tape.2)

/-- Continue an ordinary bounded sampler from an aligned scheduler cursor.
Each coordinate uses the existing cache-aware consumer. -/
def runSchedulerNativeOrdinaryPrefix
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) :
    (pairs : List (Digest256 × Digest256)) →
      (consumedBlocks : Nat) → (digest : Digest256) →
      (outputs : List Digest256) →
      SchedulerNativeGammaCursor globalOracleCalls Result →
      Except SchedulerNativeGammaReplayFailure
        (DecodedSchedulerNativeOrdinaryResponse Result)
  | [], _, _, _, _ => .error .samplerTapeExhausted
  | (output, advanced) :: rest, consumedBlocks, digest, outputs, state =>
      match consumeSchedulerNativeGammaCoordinate transitionFuel .output
          (gammaOutputInput digest) output state with
      | .error failure => .error failure
      | .ok afterOutput =>
        match consumeSchedulerNativeGammaCoordinate transitionFuel .advance
            (gammaAdvanceInput digest) advanced afterOutput with
        | .error failure => .error failure
        | .ok afterAdvance =>
          let nextOutputs := outputs ++ [output]
          match _decodedRun : decodeOrdinaryPrefix nextOutputs with
          | some decoded =>
              match valueRun : decodeTagQM31ExactLE decoded.value with
              | none => .error .decodedValueInvalid
              | some value =>
                  let tail := runSchedulerNativeListRun transitionFuel
                    afterAdvance.cursor afterAdvance.remainingAnswers
                  .ok
                    { response :=
                        { run :=
                            { terminal := tail.terminal
                              trace := afterAdvance.tracePrefix ++ tail.trace }
                          consumedBlocks := consumedBlocks + 1
                          returnedValue := some value
                          decodedBytes := some decoded.value
                          remainingAnswers := afterAdvance.remainingAnswers }
                      decoded := decoded
                      value := value
                      valueExact := valueRun
                      responseBytesExact := rfl }
          | none =>
              runSchedulerNativeOrdinaryPrefix transitionFuel rest
                (consumedBlocks + 1) advanced nextOutputs afterAdvance

/-- Start from the exact first fresh output pause.  The routed first output is
installed directly, so the source scan's realized answer is not inspected. -/
def runSchedulerNativeOrdinaryFromFirstPause
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest)) :
    (pairs : List (Digest256 × Digest256)) →
      Except SchedulerNativeGammaReplayFailure
        (DecodedSchedulerNativeOrdinaryResponse Result)
  | [] => .error .samplerTapeExhausted
  | (output, advanced) :: rest =>
      let afterOutput : SchedulerNativeGammaCursor globalOracleCalls Result :=
        { cursor := firstPause.resumeCursorWith output
          remainingAnswers := firstPause.remainingAnswers
          oracle := freshQueryState firstPause.actor firstPause.requestState
            firstPause.input output
          tracePrefix := firstPause.consumedTrace ++
            [machineFreshRecord firstPause output] }
      match consumeSchedulerNativeGammaCoordinate transitionFuel .advance
          (gammaAdvanceInput initialDigest) advanced afterOutput with
      | .error failure => .error failure
      | .ok afterAdvance =>
          let outputs := [output]
          match _decodedRun : decodeOrdinaryPrefix outputs with
          | some decoded =>
              match valueRun : decodeTagQM31ExactLE decoded.value with
              | none => .error .decodedValueInvalid
              | some value =>
                  let tail := runSchedulerNativeListRun transitionFuel
                    afterAdvance.cursor afterAdvance.remainingAnswers
                  .ok
                    { response :=
                        { run :=
                            { terminal := tail.terminal
                              trace := afterAdvance.tracePrefix ++ tail.trace }
                          consumedBlocks := 1
                          returnedValue := some value
                          decodedBytes := some decoded.value
                          remainingAnswers := afterAdvance.remainingAnswers }
                      decoded := decoded
                      value := value
                      valueExact := valueRun
                      responseBytesExact := rfl }
          | none =>
              runSchedulerNativeOrdinaryPrefix transitionFuel rest 1 advanced
                outputs afterAdvance

/-- Replay one successful ordinary-tape occurrence and require that the
deployed decoder returns the value supplied by the caller. -/
def replaySchedulerNativeOrdinaryOccurrence
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (tape : TotalTag73DuplexOrdinaryTape) (value : QM31Exact) :
    Except SchedulerNativeGammaReplayFailure
      (SchedulerNativeOrdinaryResponse Result) :=
  match runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
      (ordinaryDuplexPairs tape) with
  | .error failure => .error failure
  | .ok decoded =>
      if decoded.value = value then
        .ok { decoded.response with returnedValue := some value }
      else
        .error .gammaMismatch

@[simp] theorem replay_scheduler_native_ordinary_occurrence_independent_of_target_answer
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (replacement : Digest256)
    (tape : TotalTag73DuplexOrdinaryTape) (value : QM31Exact) :
    replaySchedulerNativeOrdinaryOccurrence transitionFuel
        { firstPause with targetAnswer := replacement } tape value =
      replaySchedulerNativeOrdinaryOccurrence transitionFuel firstPause tape
        value := by
  unfold replaySchedulerNativeOrdinaryOccurrence
  rfl

theorem replay_scheduler_native_ordinary_occurrence_returned_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (tape : TotalTag73DuplexOrdinaryTape) (value : QM31Exact)
    (response : SchedulerNativeOrdinaryResponse Result)
    (run : replaySchedulerNativeOrdinaryOccurrence transitionFuel firstPause
      tape value = .ok response) :
    response.returnedValue = some value := by
  unfold replaySchedulerNativeOrdinaryOccurrence at run
  dsimp only at run
  cases prefixRun : runSchedulerNativeOrdinaryFromFirstPause transitionFuel
      firstPause (ordinaryDuplexPairs tape) with
  | error failure => simp [prefixRun] at run
  | ok decoded =>
      by_cases equal : decoded.value = value
      · simp [prefixRun, equal] at run
        cases run
        rfl
      · simp [prefixRun, equal] at run

theorem replay_scheduler_native_ordinary_occurrence_decoded_exact
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (tape : TotalTag73DuplexOrdinaryTape) (value : QM31Exact)
    (response : SchedulerNativeOrdinaryResponse Result)
    (run : replaySchedulerNativeOrdinaryOccurrence transitionFuel firstPause
      tape value = .ok response) :
    ∃ encoded : Qm31Bytes,
      response.decodedBytes = some encoded ∧
      decodeTagQM31ExactLE encoded = some value := by
  unfold replaySchedulerNativeOrdinaryOccurrence at run
  dsimp only at run
  cases prefixRun : runSchedulerNativeOrdinaryFromFirstPause transitionFuel
      firstPause (ordinaryDuplexPairs tape) with
  | error failure => simp [prefixRun] at run
  | ok decoded =>
      by_cases equal : decoded.value = value
      · simp [prefixRun, equal] at run
        cases run
        refine ⟨decoded.decoded.value, ?_, ?_⟩
        · exact decoded.responseBytesExact
        · simpa [equal] using decoded.valueExact
      · simp [prefixRun, equal] at run

/-! ## Unread duplex suffixes are inert -/

/-- Once the ordinary decoder has returned, additional unused duplex pairs
cannot alter the scheduler result. -/
theorem run_scheduler_native_ordinary_prefix_append_of_ok
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) (pairs suffix : List (Digest256 × Digest256))
    (consumedBlocks : Nat) (digest : Digest256)
    (outputs : List Digest256)
    (state : SchedulerNativeGammaCursor globalOracleCalls Result)
    (decoded : DecodedSchedulerNativeOrdinaryResponse Result)
    (run : runSchedulerNativeOrdinaryPrefix transitionFuel pairs consumedBlocks
      digest outputs state = .ok decoded) :
    runSchedulerNativeOrdinaryPrefix transitionFuel (pairs ++ suffix)
      consumedBlocks digest outputs state = .ok decoded := by
  induction pairs generalizing consumedBlocks digest outputs state with
  | nil => simp [runSchedulerNativeOrdinaryPrefix] at run
  | cons pair rest ih =>
      obtain ⟨output, advanced⟩ := pair
      change runSchedulerNativeOrdinaryPrefix transitionFuel
        ((output, advanced) :: (rest ++ suffix)) consumedBlocks digest outputs
          state = .ok decoded
      simp only [runSchedulerNativeOrdinaryPrefix] at run ⊢
      cases outputRun : consumeSchedulerNativeGammaCoordinate transitionFuel
          .output (gammaOutputInput digest) output state with
      | error failure => simp [outputRun] at run
      | ok afterOutput =>
          simp only [outputRun] at run
          simp only at ⊢
          cases advanceRun : consumeSchedulerNativeGammaCoordinate
              transitionFuel .advance (gammaAdvanceInput digest) advanced
              afterOutput with
          | error failure => simp [advanceRun] at run
          | ok afterAdvance =>
              simp only [advanceRun] at run
              simp only at ⊢
              split at *
              next decodedRun =>
                split at *
                next valueRun => cases run
                next valueRun => exact run
              next decodedRun =>
                exact ih (consumedBlocks + 1) advanced
                  (outputs ++ [output]) afterAdvance run

/-- The first-pause entry point has the same suffix irrelevance. -/
theorem run_scheduler_native_ordinary_from_first_pause_append_of_ok
    {globalOracleCalls : Nat} {Result : Type u}
    (transitionFuel : Nat) {initialDigest : Digest256}
    (firstPause : SchedulerNativeFreshPause globalOracleCalls Result
      (gammaOutputInput initialDigest))
    (pairs suffix : List (Digest256 × Digest256))
    (decoded : DecodedSchedulerNativeOrdinaryResponse Result)
    (run : runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
      pairs = .ok decoded) :
    runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
      (pairs ++ suffix) = .ok decoded := by
  cases pairs with
  | nil => simp [runSchedulerNativeOrdinaryFromFirstPause] at run
  | cons pair rest =>
      obtain ⟨output, advanced⟩ := pair
      change runSchedulerNativeOrdinaryFromFirstPause transitionFuel firstPause
        ((output, advanced) :: (rest ++ suffix)) = .ok decoded
      simp only [runSchedulerNativeOrdinaryFromFirstPause] at run ⊢
      cases advanceRun : consumeSchedulerNativeGammaCoordinate transitionFuel
          .advance (gammaAdvanceInput initialDigest) advanced
          { cursor := firstPause.resumeCursorWith output
            remainingAnswers := firstPause.remainingAnswers
            oracle := freshQueryState firstPause.actor firstPause.requestState
              firstPause.input output
            tracePrefix := firstPause.consumedTrace ++
              [machineFreshRecord firstPause output] } with
      | error failure => simp [advanceRun] at run
      | ok afterAdvance =>
          simp only [advanceRun] at run
          simp only at ⊢
          split at *
          next decodedRun =>
            split at *
            next valueRun => cases run
            next valueRun => exact run
          next decodedRun =>
            exact run_scheduler_native_ordinary_prefix_append_of_ok
              transitionFuel rest suffix 1 advanced [output] afterAdvance
                decoded run

#print axioms ordinaryDuplexPairs
#print axioms runSchedulerNativeOrdinaryPrefix
#print axioms runSchedulerNativeOrdinaryFromFirstPause
#print axioms replaySchedulerNativeOrdinaryOccurrence
#print axioms
  replay_scheduler_native_ordinary_occurrence_independent_of_target_answer
#print axioms replay_scheduler_native_ordinary_occurrence_returned_exact
#print axioms replay_scheduler_native_ordinary_occurrence_decoded_exact
#print axioms run_scheduler_native_ordinary_prefix_append_of_ok
#print axioms run_scheduler_native_ordinary_from_first_pause_append_of_ok

end
end AspisK1.V7Tag73SchedulerNativeOrdinaryReplay
