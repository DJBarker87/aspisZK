import FSV8AlignedAlphaPairDispositions

/-!
# Chronological nesting of the reached alpha pairs

This leaf records the history inclusions already carried by an actual
`AlignedRejectedPath` and its accepted final pair.  It is deliberately local:
the later source-factorisation theorem must still place the complete alpha run
inside the returned whole-verifier history.

No decomposition, freshness, target, or probability premise is added.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 1600

namespace AspisV8Completion.FSV8AlignedAlphaPairHistoryNesting

open FSBoundedTranscript
open FSV8AlignedAlphaSqueezeStep
open FSV8AlignedAlphaChallengeRun
open FSV8AlignedAlphaPairDispositions
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

/-- The entry history of a rejected alpha path is a literal prefix of its
terminal history.  This follows from the two append equations of every actual
pair, including cached calls. -/
theorem AlignedRejectedPath.entry_history_prefix
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
    (path : AlignedRejectedPath tape finiteTape limits startV7 start
      blocks v7 s) -> startV7.history <+: v7.history := by
  intro blocks v7 s path
  induction path with
  | base aligned prefixPath => exact List.prefix_refl _
  | @snoc prior v7 s priorPath pair bounded reject ih =>
      have toOutput : v7.history <+: pair.afterOutput.history := by
        rw [pair.outputHistory]
        exact List.prefix_append _ _
      have toAdvance : pair.afterOutput.history <+: pair.afterAdvance.history := by
        rw [pair.advanceHistory]
        exact List.prefix_append _ _
      exact ih.trans (toOutput.trans toAdvance)

/-- The end of the rejected path precedes the end of the accepted final pair
in the exact successful challenge. -/
theorem SuccessfulAlignedChallenge.rejected_end_prefix_final_pair
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits startV7 start
        rejected beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits
        beforeFinal finalStart,
        startV7.history <+: beforeFinal.history ∧
        beforeFinal.history <+: finalPair.afterAdvance.history := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, _blocksExact,
      _finalExact, _accepted, _finalPhase⟩
  have beforeToOutput : beforeFinal.history <+: finalPair.afterOutput.history := by
    rw [finalPair.outputHistory]
    exact List.prefix_append _ _
  have outputToAdvance : finalPair.afterOutput.history <+:
      finalPair.afterAdvance.history := by
    rw [finalPair.advanceHistory]
    exact List.prefix_append _ _
  exact ⟨rejected, finalStart, beforeFinal, path, finalPair,
    AspisV8Completion.FSV8AlignedAlphaPairHistoryNesting.AlignedRejectedPath.entry_history_prefix
      path,
    beforeToOutput.trans outputToAdvance⟩

/-- A fresh advance record of the accepted final pair is literally present in
that pair's terminal history.  This is the smallest placement fact later used
to enter the returned verifier fresh-query enumeration. -/
theorem final_pair_fresh_advance_record_mem
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ rejected finalStart beforeFinal,
      ∃ path : AlignedRejectedPath tape finiteTape limits startV7 start
        rejected beforeFinal finalStart,
      ∃ finalPair : AlignedSqueezePair tape finiteTape limits
        beforeFinal finalStart,
        finalPair.advanceOrigin = .fresh ->
          { input := FSV8CandidateOriginTrace.advanceInput finalStart
            output := (FSV8CandidateOriginTrace.advanceStep tape finalStart).1
            actor := .verifier
            origin := .fresh } ∈ finalPair.afterAdvance.history := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, finalPair, _blocksExact,
      _finalExact, _accepted, _finalPhase⟩
  refine ⟨rejected, finalStart, beforeFinal, path, finalPair, ?_⟩
  intro fresh
  rw [finalPair.advanceHistory]
  apply List.mem_append_right
  simp [FSV8AlphaHistoryPhasePrefix.advanceRecord, fresh,
    FSV8CandidateOriginTrace.advanceInput,
    AspisK1.V7Tag73TranscriptSchedule.bytes,
    AspisK1.V7Tag73TranscriptSchedule.domAdvance]

#print axioms AlignedRejectedPath.entry_history_prefix
#print axioms SuccessfulAlignedChallenge.rejected_end_prefix_final_pair
#print axioms final_pair_fresh_advance_record_mem

end
end AspisV8Completion.FSV8AlignedAlphaPairHistoryNesting
