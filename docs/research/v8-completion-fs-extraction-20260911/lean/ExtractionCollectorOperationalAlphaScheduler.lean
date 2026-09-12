import ExtractionCollectorOperationalSuccessfulReplay
import SuccessfulReplayActualAlphaSchedulerScan

/-!
# Source-shaped scheduler scan for one checked extraction cell

This leaf replaces the arbitrary cursor and answer-list inputs to the alpha
scan with source-shaped constructions. A checked cell first constructs its
exact legal replay and same-body `SuccessfulReplay`. The scheduler cursor is
built from that replay's literal V7 oracle state and the compiled V8
`wholeStagedScript`; its answer list is the finite-tape suffix starting at the
state's fresh-call count.

The theorem carries the successful finite-tape machine halt, but does not yet
prove that the separately evaluated scheduler run equals that machine run.
It remains a fresh-pause/absence classification and does not prove that
absence is impossible, construct a nested matrix schedule, or attach a
probability to either branch.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 1600

namespace AspisV8Completion.ExtractionCollectorOperationalAlphaScheduler

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73SchedulerNativeTargetPause
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorSource
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedMatrix
open ExtractionCollectorSuccessfulReplay
open ExtractionCollectorVerifiedSuccessfulReplay
open ExtractionCollectorOperationalSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8ProgrammedProjectionAlignment
open SuccessfulReplayAlphaBoundary
open SuccessfulReplayActualAlphaSchedulerScan
open FSV8AlphaChallengeInputBridge

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev Tape := FSBoundedTranscript.Tape

/-- The literal result-carrying scheduler entry for one V8 Script.  The state,
program, actor, fuel and limits are inputs to the executable cursor rather
than fields supplied later to a theorem about its run. -/
def verifierScriptCursor {A : Type} {calls n : Nat}
    (limits : OracleLimits) (limitBound : limits.totalCalls ≤ calls)
    (state : OracleState) (coherent : HistoryTotalCoherent state)
    (script : Script Bytes Block A n) :
    SchedulerNativeCursor calls A :=
  .machine limits limitBound .verifier state (compileScript script) n coherent
    (fun result _ _ => .returned result)

/-- The finite-tape suffix beginning at `state.freshCalls`.
`ProjectionFacts` proves that the state's fresh history is the corresponding
prefix of this tape. Equality between a scheduler run on this suffix and the
carried successful finite-tape machine run remains a separate theorem. -/
def remainingFreshAnswers {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps) (state : OracleState) :
    List Digest256 :=
  (freshAnswerTapeToList finiteTape).drop state.freshCalls

theorem checked_cell_constructs_source_alpha_scheduler_scan
    {TapeIdentity Observation Statement Proof : Type*}
    {n m steps : Nat}
    (origin : SameTapeExperimentOrigin
      TapeIdentity Observation Statement Proof Bytes)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : FSBoundedTranscript.RootCuts)
    (initialDigest : Block)
    (finiteTape : FreshAnswerTape Block steps) (tape : Tape)
    (limits : OracleLimits)
    (cell : Cell origin firstWork secondWork z cuts initialDigest finiteTape limits)
    (boundaryFacts : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        constructLegalReplay origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) = .ok replay →
        ProjectionFacts tape finiteTape replay.val.replayRun.oracle)
    (totalRoom : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        replay.val.replayRun.oracle.totalCalls + stagedBudget n m ≤
          limits.totalCalls)
    (freshRoom : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        replay.val.replayRun.oracle.freshCalls + stagedBudget n m ≤
          limits.freshCalls)
    (tapeRoom : ∀ replay :
        {run : CoupledReplay TapeIdentity Statement Proof Bytes //
          IsOperationalCoupling origin.capability
            (fixedFirstRunRecordFromOrigin origin cell.configuration) run},
        (projectOracleState replay.val.replayRun.oracle).next + stagedBudget n m ≤
          steps)
    (transitionFuel : Nat) :
    ∃ replay, constructLegalReplay origin.capability
        (fixedFirstRunRecordFromOrigin origin cell.configuration) = .ok replay ∧
      ∃ facts : ProjectionFacts tape finiteTape replay.val.replayRun.oracle,
      ∃ successful : SuccessfulReplay z cuts initialDigest firstWork secondWork,
        successful.body = cell.submitted ∧
        SelectedAccepted.mk successful.body successful.record
            successful.finalDigest = cell.accepted ∧
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits
            .verifier (stagedBudget n m) replay.val.replayRun.oracle
            (compileScript (wholeStagedScript firstWork secondWork z cuts
              successful.body initialDigest))).halt =
          .returned (.ok successful.record, successful.finalDigest) ∧
        successful.oracle = projectOracleState replay.val.replayRun.oracle ∧
        ∃ afterAlphaNonce,
          IsActualAlphaBoundary successful afterAlphaNonce ∧
          ((∃ pause : SchedulerNativeFreshPause limits.totalCalls
                (Except FSAuthenticatedInterleavedPrefixMiddle.Error
                    (Record successful.body z) × Block)
                (alphaCandidateInput afterAlphaNonce),
              scanSchedulerNativeToInput transitionFuel
                  (alphaCandidateInput afterAlphaNonce)
                  (verifierScriptCursor limits (le_refl limits.totalCalls)
                    replay.val.replayRun.oracle
                    (show HistoryTotalCoherent replay.val.replayRun.oracle from
                      facts.historyTotal)
                    (wholeStagedScript firstWork secondWork z cuts successful.body
                      initialDigest))
                  (remainingFreshAnswers finiteTape replay.val.replayRun.oracle) =
                .paused pause ∧
              pause.input = alphaCandidateInput afterAlphaNonce ∧
              pause.resumeRunWith transitionFuel pause.targetAnswer
                  pause.remainingAnswers =
                runSchedulerNativeListRun transitionFuel
                  (verifierScriptCursor limits (le_refl limits.totalCalls)
                    replay.val.replayRun.oracle
                    (show HistoryTotalCoherent replay.val.replayRun.oracle from
                      facts.historyTotal)
                    (wholeStagedScript firstWork secondWork z cuts successful.body
                      initialDigest))
                  (remainingFreshAnswers finiteTape replay.val.replayRun.oracle)) ∨
            ∃ run : SchedulerNativeRun
                (Except FSAuthenticatedInterleavedPrefixMiddle.Error
                    (Record successful.body z) × Block),
              scanSchedulerNativeToInput transitionFuel
                  (alphaCandidateInput afterAlphaNonce)
                  (verifierScriptCursor limits (le_refl limits.totalCalls)
                    replay.val.replayRun.oracle
                    (show HistoryTotalCoherent replay.val.replayRun.oracle from
                      facts.historyTotal)
                    (wholeStagedScript firstWork secondWork z cuts successful.body
                      initialDigest))
                  (remainingFreshAnswers finiteTape replay.val.replayRun.oracle) =
                .absent run ∧
              run = runSchedulerNativeListRun transitionFuel
                (verifierScriptCursor limits (le_refl limits.totalCalls)
                  replay.val.replayRun.oracle
                  (show HistoryTotalCoherent replay.val.replayRun.oracle from
                    facts.historyTotal)
                  (wholeStagedScript firstWork secondWork z cuts successful.body
                    initialDigest))
                (remainingFreshAnswers finiteTape replay.val.replayRun.oracle)) := by
  obtain ⟨replay, replayed, successful, bodyEq, acceptedEq, machineExact,
      oracleEq⟩ :=
    checked_cell_constructs_operational_successfulReplay origin firstWork
      secondWork z cuts initialDigest finiteTape tape limits cell boundaryFacts
      totalRoom freshRoom tapeRoom
  let facts := boundaryFacts replay replayed
  let coherent : HistoryTotalCoherent replay.val.replayRun.oracle :=
    facts.historyTotal
  let cursor := verifierScriptCursor limits (le_refl limits.totalCalls)
    replay.val.replayRun.oracle coherent
    (wholeStagedScript firstWork secondWork z cuts successful.body initialDigest)
  let answers := remainingFreshAnswers finiteTape replay.val.replayRun.oracle
  obtain ⟨afterAlphaNonce, actual, scan⟩ :=
    successful_replay_actual_alpha_scan successful transitionFuel cursor answers
  refine ⟨replay, replayed, facts, successful, bodyEq, acceptedEq, machineExact,
    oracleEq, afterAlphaNonce, actual, ?_⟩
  simpa [cursor, answers, coherent] using scan

#print axioms verifierScriptCursor
#print axioms remainingFreshAnswers
#print axioms checked_cell_constructs_source_alpha_scheduler_scan

end
end AspisV8Completion.ExtractionCollectorOperationalAlphaScheduler
