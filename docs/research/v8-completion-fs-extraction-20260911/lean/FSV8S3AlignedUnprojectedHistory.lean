import FSV8S3VerifierHistorySection
import FSV8AlignedAlphaChallengeRun

/-! S3: retain the unprojected verifier suffix produced by an aligned path. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8S3AlignedUnprojectedHistory

open FSOracleExecution FSBoundedTranscript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open FSV8V7OracleMachineBridge FSV8V7StateAlignment
open FSV8AlignedAlphaSqueezeStep FSV8AlignedAlphaChallengeRun
open FSV8CandidateOriginTrace FSV8AlphaHistoryPhasePrefix
open FSV8S3VerifierHistorySection

noncomputable section

abbrev SourceBytes := List UInt8
abbrev SourceBlock := FSBoundedTranscript.Block
abbrev SourceTape := FSBoundedTranscript.Tape
abbrev SourceTranscript := FSBoundedTranscript.Transcript

theorem aligned_step_record_verifierFC
    {steps : Nat} {tape : SourceTape} {finiteTape : FreshAnswerTape SourceBlock steps}
    {limits : OracleLimits} {v7 : OracleState} {fs : State SourceBytes SourceBlock}
    {input : SourceBytes}
    (step : AlignedVerifierStep tape finiteTape limits v7 fs input) :
    VerifierFC
      { input := input, output := (FSOracleExecution.query tape fs input).1,
        actor := .verifier, origin := step.origin } := by
  rcases step.classified with ⟨fresh, _⟩ | ⟨cached, _⟩
  · exact ⟨rfl, Or.inl fresh⟩
  · exact ⟨rfl, Or.inr cached⟩

theorem aligned_pair_records_verifierFC
    {steps : Nat} {tape : SourceTape} {finiteTape : FreshAnswerTape SourceBlock steps}
    {limits : OracleLimits} {v7 : OracleState} {s : SourceTranscript}
    (pair : AlignedSqueezePair tape finiteTape limits v7 s) :
    ∀ r ∈ [outputRecord s.digest (outputStep tape s).1 pair.outputOrigin,
            advanceRecord s.digest (advanceStep tape s).1 pair.advanceOrigin],
      VerifierFC r := by
  have outputGood : VerifierFC
      (outputRecord s.digest (outputStep tape s).1 pair.outputOrigin) := by
    rcases pair.outputClassified with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨rfl, Or.inl h⟩
    · exact ⟨rfl, Or.inr h⟩
  have advanceGood : VerifierFC
      (advanceRecord s.digest (advanceStep tape s).1 pair.advanceOrigin) := by
    rcases pair.advanceClassified with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨rfl, Or.inl h⟩
    · exact ⟨rfl, Or.inr h⟩
  intro r hr
  simp at hr
  rcases hr with rfl | rfl
  · exact outputGood
  · exact advanceGood

theorem aligned_path_has_canonical_suffix
    {steps : Nat} {tape : SourceTape} {finiteTape : FreshAnswerTape SourceBlock steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : SourceTranscript}
    {blocks : List SourceBlock} {v7 : OracleState} {s : SourceTranscript}
    (path : AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s) :
    ∃ suffix : List QueryRecord,
      v7.history = startV7.history ++ suffix ∧
      (∀ r ∈ suffix, VerifierFC r) ∧ suffix.length = 2 * blocks.length := by
  induction path with
  | base aligned prefixPath =>
    exact ⟨[], by simp, by simp, by simp⟩
  | @snoc prior v7 s path pair bounded reject ih =>
    rcases ih with ⟨suffix, history, good, length⟩
    let records :=
      [outputRecord s.digest (outputStep tape s).1 pair.outputOrigin,
       advanceRecord s.digest (advanceStep tape s).1 pair.advanceOrigin]
    refine ⟨suffix ++ records, ?_, ?_, ?_⟩
    · rw [pair.advanceHistory, pair.outputHistory, history]
      simp [records, List.append_assoc]
    · intro r member
      rcases List.mem_append.mp member with old | new
      · exact good r old
      · exact aligned_pair_records_verifierFC pair r new
    · simp [records, length, Nat.mul_add]

theorem successful_candidate_has_unprojected_final_history
    {steps : Nat} {tape : SourceTape} {finiteTape : FreshAnswerTape SourceBlock steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : SourceTranscript}
    {blocks : List SourceBlock} {final : SourceTranscript} {value : Qm31Bytes}
    (success : SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value) :
    ∃ (finalV7 : OracleState) (suffix : List QueryRecord),
      StateAligned tape finiteTape finalV7 final.oracle ∧
      finalV7.history = startV7.history ++ suffix ∧
      (∀ r ∈ suffix, VerifierFC r) ∧ suffix.length = 2 * blocks.length := by
  rcases success with
    ⟨rejected, finalStart, beforeFinal, path, pair, blocksEq, finalEq,
      accepted, finalPhase⟩
  obtain ⟨priorSuffix, priorHistory, priorGood, priorLength⟩ :=
    aligned_path_has_canonical_suffix path
  let records :=
    [outputRecord finalStart.digest (outputStep tape finalStart).1 pair.outputOrigin,
     advanceRecord finalStart.digest (advanceStep tape finalStart).1 pair.advanceOrigin]
  refine ⟨pair.afterAdvance, priorSuffix ++ records, ?_, ?_, ?_, ?_⟩
  · simpa only [finalEq] using pair.aligned
  · rw [pair.advanceHistory, pair.outputHistory, priorHistory]
    simp [records, List.append_assoc]
  · intro r member
    rcases List.mem_append.mp member with old | new
    · exact priorGood r old
    · exact aligned_pair_records_verifierFC pair r new
  · simp [records, blocksEq, priorLength, Nat.mul_add]

#print axioms aligned_step_record_verifierFC
#print axioms aligned_path_has_canonical_suffix
#print axioms successful_candidate_has_unprojected_final_history

end
end AspisV8Completion.FSV8S3AlignedUnprojectedHistory
