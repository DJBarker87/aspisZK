import FSV8AlphaHistoryPhasePrefix
import FSV8CandidateOriginTrace
import FSV8V7FreshAlignment

/-!
# Actual aligned V7/FS steps for one V8 alpha squeeze pair

The finite `FSOracleExecution` log deliberately erases the V7 actor and
collapses cached/programmed provenance.  It therefore cannot be inverted to
manufacture the history required by the V7 alpha phase recognizer.

This leaf instead executes each query in the actual V7 state.  For a state
already aligned with the finite transcript interpreter, it constructs the
successor, its literal verifier record and its fresh-versus-cached origin.
Applying that result twice gives the source-shaped output/advance pair used by
one alpha candidate.  The advance query threads the output successor state but
retains the original pre-squeeze digest in its input.

This is deterministic source coupling.  It assigns no probability and does
not assume freshness.  Programmed restoration runs require the separate
programmed-alignment model; this fresh-only leaf is for the exact forward root.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AlignedAlphaSqueezeStep

open FSOracleExecution FSBoundedTranscript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule
open FSV8V7OracleMachineBridge
open FSV8V7StateAlignment
open FSV8V7CachedAlignment
open FSV8V7FreshAlignment
open FSV8CandidateOriginTrace
open FSV8AlphaHistoryPhasePrefix

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

theorem query_log_length (tape : Tape) (fs : State Bytes Block)
    (input : Bytes) :
    (FSOracleExecution.query tape fs input).2.log.length = fs.log.length + 1 := by
  cases hit : fs.cache input <;> simp [FSOracleExecution.query, hit]

/-- One actual verifier query, including its V7 history record and the
fresh/cache classification that the finite projection alone cannot recover. -/
structure AlignedVerifierStep {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (v7 : OracleState) (fs : State Bytes Block) (input : Bytes) : Type where
  nextV7 : OracleState
  origin : AnswerOrigin
  runEq :
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits .verifier
        v7 input =
      .ok ((FSOracleExecution.query tape fs input).1, nextV7)
  historyEq :
    nextV7.history = v7.history ++
      [{ input := input
         output := (FSOracleExecution.query tape fs input).1
         actor := .verifier
         origin := origin }]
  aligned : StateAligned tape finiteTape nextV7
    (FSOracleExecution.query tape fs input).2
  classified :
    (origin = .fresh /\ lookupEntry v7 input = none) \/
      (origin = .cached /\
        exists entry, lookupEntry v7 input = some entry)

/-- The actual source execution constructs, rather than assumes, the query
origin.  `NoProgrammed` in `StateAligned` is what turns a table hit into the
literal cached origin in this forward-root model. -/
def alignedVerifierStep_complete
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {fs : State Bytes Block}
    (aligned : StateAligned tape finiteTape v7 fs) (input : Bytes)
    (totalRoom : v7.totalCalls < limits.totalCalls)
    (freshRoom : v7.freshCalls < limits.freshCalls)
    (tapeRoom : fs.next < steps) :
    AlignedVerifierStep tape finiteTape limits v7 fs input := by
  cases lookup : lookupEntry v7 input with
  | none =>
      let nextV7 := freshSuccessor (.verifier) input (tape fs.next) v7
      have fsAnswer := fresh_fs_query_output aligned input tapeRoom lookup
      refine
        { nextV7 := nextV7
          origin := .fresh
          runEq := ?_
          historyEq := ?_
          aligned := fresh_successor_aligned aligned .verifier input tapeRoom lookup
          classified := Or.inl <| And.intro rfl lookup }
      · simpa [nextV7, fsAnswer] using
          fresh_query_success_equation aligned limits .verifier input tapeRoom
            totalRoom freshRoom lookup
      · simp [nextV7, freshSuccessor, fsAnswer]
  | some entry =>
      have cache := lookup_some_implies_cache_some aligned input entry lookup
      have sourceFresh : entry.source = .fresh := by
        have member : entry ∈ v7.table := by
          unfold lookupEntry at lookup
          exact List.mem_of_find?_eq_some lookup
        exact aligned.noProgrammed entry member
      let nextV7 := cachedSuccessor (.verifier) input entry v7
      refine
        { nextV7 := nextV7
          origin := .cached
          runEq := ?_
          historyEq := ?_
          aligned := cached_successor_aligned aligned .verifier input entry lookup
          classified := Or.inr <| And.intro rfl <| Exists.intro entry lookup }
      · simp [queryOracle, Nat.not_le.mpr totalRoom, lookup, nextV7,
          cachedSuccessor, FSOracleExecution.query, cache]
      · simp [nextV7, cachedSuccessor, FSOracleExecution.query, cache,
          sourceFresh, cachedOrigin]

def alphaMarkerInput (s : Transcript) (nonce : NonceBytes) : Bytes :=
  List.ofFn s.digest ++ [0, 20] ++ (0 :: List.ofFn nonce)

/-- The actual alpha-nonce absorption constructs the base phase prefix.  The
record is not merely located later in the terminal history. -/
structure AlignedAlphaMarker {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (v7 : OracleState) (s : Transcript) (nonce : NonceBytes) : Type where
  afterMarker : OracleState
  origin : AnswerOrigin
  runEq :
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits .verifier
        v7 (alphaMarkerInput s nonce) =
      .ok ((FSOracleExecution.query tape s.oracle
        (alphaMarkerInput s nonce)).1, afterMarker)
  historyEq :
    afterMarker.history = v7.history ++
      [markerRecord s.digest
        (FSOracleExecution.query tape s.oracle (alphaMarkerInput s nonce)).1
        nonce origin]
  aligned : StateAligned tape finiteTape afterMarker
    (FSBoundedTranscript.absorb tape s 20
      (0 :: List.ofFn nonce)).oracle
  prefixPath : RejectedCandidatePrefix afterMarker.history []
  classified :
    (origin = .fresh /\ lookupEntry v7 (alphaMarkerInput s nonce) = none) \/
      (origin = .cached /\
        exists entry, lookupEntry v7 (alphaMarkerInput s nonce) = some entry)

def alignedAlphaMarker_complete
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (nonce : NonceBytes)
    (aligned : StateAligned tape finiteTape v7 s.oracle)
    (totalRoom : v7.totalCalls < limits.totalCalls)
    (freshRoom : v7.freshCalls < limits.freshCalls)
    (tapeRoom : s.oracle.next < steps) :
    AlignedAlphaMarker tape finiteTape limits v7 s nonce := by
  let step := alignedVerifierStep_complete aligned (alphaMarkerInput s nonce)
    totalRoom freshRoom tapeRoom
  refine
    { afterMarker := step.nextV7
      origin := step.origin
      runEq := step.runEq
      historyEq := ?_
      aligned := ?_
      prefixPath := ?_
      classified := step.classified }
  · simpa [alphaMarkerInput, markerRecord,
      AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAbsorb,
      AspisK1.V7Tag73TranscriptSchedule.foldWorkNonceLabel] using step.historyEq
  · simpa [alphaMarkerInput, FSBoundedTranscript.absorb] using step.aligned
  · rw [show step.nextV7.history = v7.history ++
        [markerRecord s.digest
          (FSOracleExecution.query tape s.oracle
            (alphaMarkerInput s nonce)).1 nonce step.origin] by
      simpa [alphaMarkerInput, markerRecord,
        AspisK1.V7Tag73TranscriptSchedule.bytes,
        AspisK1.V7Tag73TranscriptSchedule.domAbsorb,
        AspisK1.V7Tag73TranscriptSchedule.foldWorkNonceLabel] using
          step.historyEq]
    exact RejectedCandidatePrefix.marker v7.history s.digest
      (FSOracleExecution.query tape s.oracle (alphaMarkerInput s nonce)).1
      nonce step.origin

/-- The two real V7 queries consumed by one transcript squeeze. -/
structure AlignedSqueezePair {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (v7 : OracleState) (s : Transcript) : Type where
  afterOutput : OracleState
  afterAdvance : OracleState
  outputOrigin : AnswerOrigin
  advanceOrigin : AnswerOrigin
  outputRun :
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits .verifier
        v7 (outputInput s) =
      .ok ((outputStep tape s).1, afterOutput)
  advanceRun :
    queryOracle (controllerFromFreshAnswerTape finiteTape) limits .verifier
        afterOutput (advanceInput s) =
      .ok ((advanceStep tape s).1, afterAdvance)
  outputHistory :
    afterOutput.history = v7.history ++
      [outputRecord s.digest (outputStep tape s).1 outputOrigin]
  advanceHistory :
    afterAdvance.history = afterOutput.history ++
      [advanceRecord s.digest (advanceStep tape s).1 advanceOrigin]
  afterOutputAligned : StateAligned tape finiteTape afterOutput
    (outputStep tape s).2
  aligned : StateAligned tape finiteTape afterAdvance
    (squeeze tape s).2.oracle
  outputClassified :
    (outputOrigin = .fresh /\ lookupEntry v7 (outputInput s) = none) \/
      (outputOrigin = .cached /\
        exists entry, lookupEntry v7 (outputInput s) = some entry)
  advanceClassified :
    (advanceOrigin = .fresh /\
        lookupEntry afterOutput (advanceInput s) = none) \/
      (advanceOrigin = .cached /\
        exists entry,
          lookupEntry afterOutput (advanceInput s) = some entry)

def alignedSqueezePair_complete
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    (aligned : StateAligned tape finiteTape v7 s.oracle)
    (totalRoom : v7.totalCalls + 2 ≤ limits.totalCalls)
    (freshRoom : v7.freshCalls + 2 ≤ limits.freshCalls)
    (tapeRoom : s.oracle.next + 2 ≤ steps) :
    AlignedSqueezePair tape finiteTape limits v7 s := by
  have totalNow : v7.totalCalls < limits.totalCalls := by omega
  have freshNow : v7.freshCalls < limits.freshCalls := by omega
  have tapeNow : s.oracle.next < steps := by omega
  let first := alignedVerifierStep_complete aligned (outputInput s)
    totalNow freshNow tapeNow
  have firstTotal : first.nextV7.totalCalls + 1 ≤ limits.totalCalls := by
    rw [first.aligned.totalCalls, query_log_length]
    rw [← aligned.totalCalls]
    omega
  have firstFresh : first.nextV7.freshCalls + 1 ≤ limits.freshCalls := by
    rw [first.aligned.freshCalls]
    have bound := query_next_bound tape s.oracle (outputInput s)
    rw [aligned.freshCalls] at freshRoom
    omega
  have firstTape :
      (FSOracleExecution.query tape s.oracle (outputInput s)).2.next + 1 ≤
        steps := by
    have bound := query_next_bound tape s.oracle (outputInput s)
    omega
  let second := alignedVerifierStep_complete first.aligned (advanceInput s)
    (by omega) firstFresh firstTape
  refine
    { afterOutput := first.nextV7
      afterAdvance := second.nextV7
      outputOrigin := first.origin
      advanceOrigin := second.origin
      outputRun := ?_
      advanceRun := ?_
      outputHistory := ?_
      advanceHistory := ?_
      afterOutputAligned := ?_
      aligned := ?_
      outputClassified := first.classified
      advanceClassified := second.classified }
  · simpa [first, outputStep] using first.runEq
  · simpa [first, second, advanceStep, outputStep] using second.runEq
  · simpa [first, outputInput, outputRecord, outputStep,
      AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domSqueeze] using first.historyEq
  · simpa [first, second, advanceInput, advanceRecord,
      FSV8CandidateOriginTrace.advanceStep,
      FSV8CandidateOriginTrace.outputStep,
      AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAdvance] using second.historyEq
  · simpa [first, FSV8CandidateOriginTrace.outputStep] using first.aligned
  · simpa [first, second, FSV8CandidateOriginTrace.advanceStep,
      FSV8CandidateOriginTrace.outputStep,
      FSV8CandidateOriginTrace.advanceInput,
      FSV8CandidateOriginTrace.outputInput, FSBoundedTranscript.squeeze]
      using second.aligned

/-- A rejected candidate extends the *actual* chronological V7 history to the
next candidate prefix.  No terminal-history membership premise is used. -/
theorem aligned_rejected_squeeze_extends_prefix
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {v7 : OracleState} {s : Transcript}
    {prior : List Block}
    (prefixPath : RejectedCandidatePrefix v7.history prior)
    (bounded : prior.length < 4)
    (aligned : StateAligned tape finiteTape v7 s.oracle)
    (totalRoom : v7.totalCalls + 2 ≤ limits.totalCalls)
    (freshRoom : v7.freshCalls + 2 ≤ limits.freshCalls)
    (tapeRoom : s.oracle.next + 2 ≤ steps)
    (rejected : decodeChallengeParameter exactSecureCircleParameterMap
      (.alpha 0) (prior ++ [(outputStep tape s).1]) = none) :
    exists pair : AlignedSqueezePair tape finiteTape limits v7 s,
      RejectedCandidatePrefix pair.afterAdvance.history
        (prior ++ [(outputStep tape s).1]) := by
  let pair := alignedSqueezePair_complete aligned totalRoom freshRoom tapeRoom
  refine Exists.intro pair ?_
  rw [pair.advanceHistory, pair.outputHistory]
  simpa [List.append_assoc] using
    RejectedCandidatePrefix.rejected prefixPath bounded s.digest
      (outputStep tape s).1 (advanceStep tape s).1 pair.outputOrigin
      pair.advanceOrigin rejected

#print axioms query_log_length
#print axioms alignedVerifierStep_complete
#print axioms alignedAlphaMarker_complete
#print axioms alignedSqueezePair_complete
#print axioms aligned_rejected_squeeze_extends_prefix

end
end AspisV8Completion.FSV8AlignedAlphaSqueezeStep
