import FSV8AlignedAlphaPairHistoryNesting

/-!
# Synchronizing an aligned alpha terminal with the candidate machine

`StateAligned` intentionally erases the actor tag, so this leaf proves the
strongest unconditional synchronization available at that interface: every
fresh final-pair record has a fresh record with the same input and output in
the candidate-machine terminal history.  The separate source-run provenance
lemma must identify the matching suffix record's actor as `.verifier`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlignedAlphaCandidateProjectionSync

open FSBoundedTranscript
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8CandidateOriginTrace
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

private theorem project_origin_eq_true_iff (origin : AnswerOrigin) :
    projectOrigin origin = true ↔ origin = .fresh := by
  cases origin <;> simp [projectOrigin]

/-- The actual accepted final pair and the candidate machine share the same
finite transcript terminal.  Consequently the final pair's fresh advance is
present, with exact input/output and fresh origin, in the candidate terminal
history.  No equality of the two `OracleState`s is asserted. -/
theorem successful_final_pair_fresh_advance_in_aligned_candidate
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 candidateFinal : OracleState}
    {start : Transcript} {blocks : List Block} {final : Transcript}
    {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value)
    (candidateAligned : StateAligned tape finiteTape candidateFinal final.oracle) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits startV7 start
        rejected beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits
        beforeFinal finalStart,
        finalPair.advanceOrigin = .fresh →
          ∃ record ∈ candidateFinal.history,
            record.input = advanceInput finalStart ∧
            record.output = (advanceStep tape finalStart).1 ∧
            record.origin = .fresh := by
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
  have mappedMember : projectRecord pairRecord ∈
      candidateFinal.history.map projectRecord := by
    have inPairMap : projectRecord pairRecord ∈
        finalPair.afterAdvance.history.map projectRecord :=
      List.mem_map.mpr ⟨pairRecord, pairMember, rfl⟩
    have pairHistory := finalPair.aligned.history
    have candidateHistory := candidateAligned.history
    rw [← candidateHistory]
    rw [pairHistory]
    exact inPairMap
  rcases List.mem_map.mp mappedMember with ⟨record, recordMember, projected⟩
  refine ⟨record, recordMember, ?_, ?_, ?_⟩
  · exact congrArg FSOracleExecution.Event.input projected
  · exact congrArg FSOracleExecution.Event.answer projected
  · have freshBool : projectOrigin record.origin = true := by
      exact congrArg FSOracleExecution.Event.fresh projected
    exact (project_origin_eq_true_iff record.origin).mp freshBool

#print axioms successful_final_pair_fresh_advance_in_aligned_candidate

end
end AspisV8Completion.FSV8AlignedAlphaCandidateProjectionSync
