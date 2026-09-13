import FSV8AlignedAlphaCandidateProjectionSync
import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

/-!
# Synchronizing every fresh record consumed by an aligned alpha challenge

The earlier suffix bridge singled out the accepted pair's advance query.  This
leaf retains the entire chronological suffix appended by the rejected pairs
and the accepted final pair.  Projection alignment with the candidate machine
then gives an equality of the two ordered projected suffixes.  Consequently
every locally fresh record in the consumed alpha suffix has an exact
input/output/fresh match in the candidate-machine suffix, whose actor is
constructed by the actual `.verifier` run.

No freshness, target-event, probability, or whole-verifier inclusion premise
is introduced here.  Cached local records are retained in the ordered suffix
equality but are intentionally not promoted to the fresh enumeration.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8AlignedAlphaAllFreshSuffixSync

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaPairHistoryNesting FSV8CandidateOriginTrace
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

private theorem project_origin_eq_true_iff (origin : AnswerOrigin) :
    projectOrigin origin = true ↔ origin = .fresh := by
  cases origin <;> simp [projectOrigin]

private def projectedFreshQueryEnumeration :
    List (Event (List UInt8) Block) → List (List UInt8 × Block)
  | [] => []
  | event :: rest =>
      if event.fresh then
        (event.input, event.answer) :: projectedFreshQueryEnumeration rest
      else
        projectedFreshQueryEnumeration rest

private theorem fresh_query_enumeration_eq_projected
    (records : List QueryRecord) :
    freshQueryEnumeration records =
      projectedFreshQueryEnumeration (records.map projectRecord) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      rcases record with ⟨input, output, actor, origin⟩
      cases origin <;>
        simp [freshQueryEnumeration, projectedFreshQueryEnumeration,
          projectRecord, projectOrigin, ih]

/-- The complete alpha suffix and the candidate-machine suffix have the same
ordered input/output/freshness projection.  Thus this theorem preserves the
causal order of all consumed rejected and accepted pairs, rather than merely
locating the accepted pair's final query somewhere in the terminal history. -/
theorem successful_alpha_suffix_projection_eq_candidate_suffix
    {Result : Type*}
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState}
    {start : Transcript} {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (controller : AdaptiveController) (fuel : Nat)
    (program : OracleMachine Result)
    (candidateAligned : StateAligned tape finiteTape
      (runMachine controller limits .verifier fuel startV7 program).oracle
      final.oracle)
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ alphaSuffix candidateSuffix,
      final.oracle.log =
        (startV7.history ++ alphaSuffix).map projectRecord ∧
      (runMachine controller limits .verifier fuel startV7 program).oracle.history =
        startV7.history ++ candidateSuffix ∧
      alphaSuffix.map projectRecord = candidateSuffix.map projectRecord ∧
      (∀ record ∈ candidateSuffix, record.actor = .verifier) := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, _blocksExact,
      finalExact, _accepted, _finalPhase⟩
  subst final
  rcases
      AspisV8Completion.FSV8AlignedAlphaPairHistoryNesting.AlignedRejectedPath.entry_history_prefix
        path with ⟨priorSuffix, beforeHistory⟩
  let alphaSuffix : List QueryRecord :=
    priorSuffix ++
      [FSV8AlphaHistoryPhasePrefix.outputRecord finalStart.digest
        (outputStep tape finalStart).1 finalPair.outputOrigin,
       FSV8AlphaHistoryPhasePrefix.advanceRecord finalStart.digest
        (advanceStep tape finalStart).1 finalPair.advanceOrigin]
  have finalHistory : finalPair.afterAdvance.history =
      startV7.history ++ alphaSuffix := by
    rw [finalPair.advanceHistory, finalPair.outputHistory, ← beforeHistory]
    simp only [alphaSuffix, List.append_assoc, List.singleton_append]
  obtain ⟨candidateSuffix, candidateHistory, _candidateTable,
      candidateProperties, _candidateLength⟩ :=
    run_machine_fresh_extension_data controller limits .verifier fuel startV7
      program
  have projectedTerminal :
      finalPair.afterAdvance.history.map projectRecord =
        (runMachine controller limits .verifier fuel startV7 program).oracle.history.map
          projectRecord := by
    rw [← finalPair.aligned.history, ← candidateAligned.history]
  have projectedSuffix :
      alphaSuffix.map projectRecord = candidateSuffix.map projectRecord := by
    rw [finalHistory, candidateHistory] at projectedTerminal
    simp only [List.map_append] at projectedTerminal
    exact (List.append_right_inj
      (startV7.history.map projectRecord)).mp projectedTerminal
  refine ⟨alphaSuffix, candidateSuffix, ?_, candidateHistory,
    projectedSuffix, ?_⟩
  · calc
      (squeeze tape finalStart).2.oracle.log =
          finalPair.afterAdvance.history.map projectRecord :=
        finalPair.aligned.history
      _ = (startV7.history ++ alphaSuffix).map projectRecord := by
        rw [finalHistory]
  · intro record member
    exact (candidateProperties record member).1

/-- Every fresh record in the complete consumed alpha suffix has an exact
fresh verifier record in the candidate suffix.  Because the preceding theorem
equates the full projected lists, this membership statement applies uniformly
to output and advance records of every rejected pair and the accepted pair. -/
theorem successful_every_local_fresh_record_in_candidate_suffix
    {Result : Type*}
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState}
    {start : Transcript} {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (controller : AdaptiveController) (fuel : Nat)
    (program : OracleMachine Result)
    (candidateAligned : StateAligned tape finiteTape
      (runMachine controller limits .verifier fuel startV7 program).oracle
      final.oracle)
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ alphaSuffix candidateSuffix,
      final.oracle.log =
        (startV7.history ++ alphaSuffix).map projectRecord ∧
      (runMachine controller limits .verifier fuel startV7 program).oracle.history =
        startV7.history ++ candidateSuffix ∧
      (∀ localRecord ∈ alphaSuffix,
        localRecord.origin = .fresh →
          ∃ candidateRecord ∈ candidateSuffix,
            candidateRecord.input = localRecord.input ∧
            candidateRecord.output = localRecord.output ∧
            candidateRecord.origin = .fresh ∧
            candidateRecord.actor = .verifier) := by
  obtain ⟨alphaSuffix, candidateSuffix, finalHistory, candidateHistory,
      projectedSuffix, candidateActors⟩ :=
    successful_alpha_suffix_projection_eq_candidate_suffix controller fuel
      program candidateAligned success
  refine ⟨alphaSuffix, candidateSuffix, finalHistory, candidateHistory, ?_⟩
  intro localRecord localMember localFresh
  have projectedMember : projectRecord localRecord ∈
      candidateSuffix.map projectRecord := by
    rw [← projectedSuffix]
    exact List.mem_map.mpr ⟨localRecord, localMember, rfl⟩
  rcases List.mem_map.mp projectedMember with
    ⟨candidateRecord, candidateMember, projected⟩
  refine ⟨candidateRecord, candidateMember, ?_, ?_, ?_,
    candidateActors candidateRecord candidateMember⟩
  · exact congrArg (fun event => event.input) projected
  · exact congrArg (fun event => event.answer) projected
  · have freshBool : projectOrigin candidateRecord.origin = true := by
      have projectedFresh := congrArg (fun event => event.fresh) projected
      change projectOrigin candidateRecord.origin =
        projectOrigin localRecord.origin at projectedFresh
      rw [localFresh] at projectedFresh
      simpa [projectOrigin] using projectedFresh
    exact (project_origin_eq_true_iff candidateRecord.origin).mp freshBool

/-- The fresh input/output coordinates of every pair consumed by alpha occur
in exactly the same chronological order in the candidate-machine suffix.
Unlike pointwise membership, this rules out satisfying different local calls
with one reordered candidate record. -/
theorem successful_alpha_fresh_query_enumeration_eq_candidate_suffix
    {Result : Type*}
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState}
    {start : Transcript} {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (controller : AdaptiveController) (fuel : Nat)
    (program : OracleMachine Result)
    (candidateAligned : StateAligned tape finiteTape
      (runMachine controller limits .verifier fuel startV7 program).oracle
      final.oracle)
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ alphaSuffix candidateSuffix,
      final.oracle.log =
        (startV7.history ++ alphaSuffix).map projectRecord ∧
      (runMachine controller limits .verifier fuel startV7 program).oracle.history =
        startV7.history ++ candidateSuffix ∧
      freshQueryEnumeration alphaSuffix =
        freshQueryEnumeration candidateSuffix ∧
      (∀ record ∈ candidateSuffix, record.actor = .verifier) := by
  obtain ⟨alphaSuffix, candidateSuffix, finalHistory, candidateHistory,
      projectedSuffix, candidateActors⟩ :=
    successful_alpha_suffix_projection_eq_candidate_suffix controller fuel
      program candidateAligned success
  refine ⟨alphaSuffix, candidateSuffix, finalHistory, candidateHistory, ?_,
    candidateActors⟩
  rw [fresh_query_enumeration_eq_projected,
    fresh_query_enumeration_eq_projected, projectedSuffix]

#print axioms successful_alpha_suffix_projection_eq_candidate_suffix
#print axioms successful_every_local_fresh_record_in_candidate_suffix
#print axioms successful_alpha_fresh_query_enumeration_eq_candidate_suffix

end
end AspisV8Completion.FSV8AlignedAlphaAllFreshSuffixSync
