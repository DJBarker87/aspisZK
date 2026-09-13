import FSV8AlignedAlphaCandidateProjectionSync
import AspisFormal.K1.V7Tag73VerifierOracleStability
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

/-!
# Synchronizing a fresh aligned alpha pair with the candidate-machine suffix

This leaf cancels the common entry-history projection rather than asserting
equality of oracle states.  The literal aligned pair supplies the projected
fresh record.  `run_machine_fresh_extension_data` supplies the candidate
machine's appended records and, crucially, their verifier actor provenance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8AlignedAlphaCandidateSuffixSync

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaPairHistoryNesting FSV8CandidateOriginTrace
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VerifierOracleStability

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

private theorem project_origin_eq_true_iff (origin : AnswerOrigin) :
    projectOrigin origin = true ↔ origin = .fresh := by
  cases origin <;> simp [projectOrigin]

/-- If the finite alpha execution and the V7 candidate machine start from the
same aligned state, the accepted pair's fresh advance has an exact matching
record in the records appended by that candidate machine.  Its actor is
therefore the actual machine actor, not reconstructed from `StateAligned`. -/
theorem successful_final_pair_fresh_advance_in_candidate_suffix
    {Result : Type*}
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState}
    {start : Transcript} {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (controller : AdaptiveController) (fuel : Nat)
    (program : OracleMachine Result)
    (startAligned : StateAligned tape finiteTape startV7 start.oracle)
    (candidateAligned : StateAligned tape finiteTape
      (runMachine controller limits .verifier fuel startV7 program).oracle
      final.oracle)
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits startV7 start
        rejected beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits
        beforeFinal finalStart,
        finalPair.advanceOrigin = .fresh →
          ∃ appended record,
            (runMachine controller limits .verifier fuel startV7 program).oracle.history =
              startV7.history ++ appended ∧
            record ∈ appended ∧
            record.input = advanceInput finalStart ∧
            record.output = (advanceStep tape finalStart).1 ∧
            record.origin = .fresh ∧
            record.actor = .verifier := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, _blocksExact,
      finalExact, _accepted, _finalPhase⟩
  subst final
  refine ⟨rejected, finalStart, beforeFinal, path, finalPair, ?_⟩
  intro fresh
  let pairRecord : QueryRecord :=
    { input := advanceInput finalStart
      output := (advanceStep tape finalStart).1
      actor := .verifier
      origin := .fresh }
  have pairMember : pairRecord ∈ finalPair.afterAdvance.history := by
    rw [finalPair.advanceHistory]
    apply List.mem_append_right
    simp [pairRecord, FSV8AlphaHistoryPhasePrefix.advanceRecord, fresh,
      advanceInput, AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAdvance]
  rcases
      AspisV8Completion.FSV8AlignedAlphaPairHistoryNesting.AlignedRejectedPath.entry_history_prefix
        path with ⟨pairPrior, beforeHistory⟩
  have pairHistory : finalPair.afterAdvance.history =
      startV7.history ++
        (pairPrior ++
          [FSV8AlphaHistoryPhasePrefix.outputRecord finalStart.digest
            (outputStep tape finalStart).1 finalPair.outputOrigin,
           FSV8AlphaHistoryPhasePrefix.advanceRecord finalStart.digest
            (advanceStep tape finalStart).1 finalPair.advanceOrigin]) := by
    rw [finalPair.advanceHistory, finalPair.outputHistory, ← beforeHistory]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨appended, candidateHistory, _candidateTable, candidateProperties,
      _candidateLength⟩ :=
    run_machine_fresh_extension_data controller limits .verifier fuel startV7
      program
  have projectedTerminal :
      finalPair.afterAdvance.history.map projectRecord =
        (runMachine controller limits .verifier fuel startV7 program).oracle.history.map
          projectRecord := by
    rw [← finalPair.aligned.history, ← candidateAligned.history]
  have projectedSuffix :
      (pairPrior ++
          [FSV8AlphaHistoryPhasePrefix.outputRecord finalStart.digest
            (outputStep tape finalStart).1 finalPair.outputOrigin,
           FSV8AlphaHistoryPhasePrefix.advanceRecord finalStart.digest
            (advanceStep tape finalStart).1 finalPair.advanceOrigin]).map projectRecord =
        appended.map projectRecord := by
    rw [pairHistory, candidateHistory] at projectedTerminal
    simp only [List.map_append] at projectedTerminal
    have cancelled :
        pairPrior.map projectRecord ++
            [FSV8AlphaHistoryPhasePrefix.outputRecord finalStart.digest
              (outputStep tape finalStart).1 finalPair.outputOrigin,
             FSV8AlphaHistoryPhasePrefix.advanceRecord finalStart.digest
              (advanceStep tape finalStart).1 finalPair.advanceOrigin].map
                projectRecord =
          appended.map projectRecord :=
      (List.append_right_inj (startV7.history.map projectRecord)).mp
        projectedTerminal
    simpa only [List.map_append] using cancelled
  have pairRecordSuffix : pairRecord ∈
      pairPrior ++
        [FSV8AlphaHistoryPhasePrefix.outputRecord finalStart.digest
          (outputStep tape finalStart).1 finalPair.outputOrigin,
         FSV8AlphaHistoryPhasePrefix.advanceRecord finalStart.digest
          (advanceStep tape finalStart).1 finalPair.advanceOrigin] := by
    apply List.mem_append_right
    simp [pairRecord, FSV8AlphaHistoryPhasePrefix.advanceRecord, fresh,
      advanceInput, AspisK1.V7Tag73TranscriptSchedule.bytes,
      AspisK1.V7Tag73TranscriptSchedule.domAdvance]
  have projectedInCandidate : projectRecord pairRecord ∈
      appended.map projectRecord := by
    rw [← projectedSuffix]
    exact List.mem_map.mpr ⟨pairRecord, pairRecordSuffix, rfl⟩
  rcases List.mem_map.mp projectedInCandidate with
    ⟨record, recordMember, projected⟩
  have properties := candidateProperties record recordMember
  refine ⟨appended, record, candidateHistory, recordMember, ?_, ?_, ?_,
    properties.1⟩
  · exact congrArg (fun event => event.input) projected
  · exact congrArg (fun event => event.answer) projected
  · have freshBool : projectOrigin record.origin = true :=
      congrArg (fun event => event.fresh) projected
    exact (project_origin_eq_true_iff record.origin).mp freshBool

/-- An exact fresh record in the candidate-machine appended suffix remains in
the enclosing verifier's fresh-query enumeration.  The histories are literal
source prefixes; no oracle-state equality is used. -/
theorem candidate_suffix_fresh_record_mem_enclosing_enumeration
    (entry start candidateFinal wholeFinal : OracleState)
    (appended : List QueryRecord) (record : QueryRecord)
    (entryPrefix : entry.history <+: start.history)
    (candidateHistory : candidateFinal.history = start.history ++ appended)
    (candidatePrefix : candidateFinal.history <+: wholeFinal.history)
    (recordMember : record ∈ appended)
    (recordFresh : record.origin = .fresh) :
    (record.input, record.output) ∈
      freshQueryEnumeration (historySince entry wholeFinal) := by
  rcases entryPrefix with ⟨before, startHistory⟩
  rcases candidatePrefix with ⟨after, wholeHistory⟩
  rcases List.mem_iff_append.mp recordMember with ⟨prior, later, appendedExact⟩
  unfold historySince
  rw [candidateHistory] at wholeHistory
  rw [← wholeHistory, ← startHistory, appendedExact]
  simp [List.append_assoc, freshQueryEnumeration, recordFresh]

#print axioms successful_final_pair_fresh_advance_in_candidate_suffix
#print axioms candidate_suffix_fresh_record_mem_enclosing_enumeration

end
end AspisV8Completion.FSV8AlignedAlphaCandidateSuffixSync
