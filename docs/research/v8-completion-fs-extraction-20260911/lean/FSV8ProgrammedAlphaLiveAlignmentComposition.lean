import FSV8SuccessfulProgrammedAlignmentFuel
import FSV8CandidateScriptLiveBridge
import FSV8AlignedAlphaChallengeRun

/-!
# Small composition from a returned candidate to the aligned live alpha trace

This deliberately abstracts the large source cut.  Its consumer must construct
the two alignments and the literal candidate return from one source execution.
The point of the leaf is to isolate the inexpensive causal composition from
elaboration of the nested pre-alpha source term.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace AspisV8Completion.FSV8ProgrammedAlphaLiveAlignmentComposition

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge
open FSV8CandidateScriptLiveBridge FSV8AlignedAlphaChallengeRun
open FSV8AlphaHistoryPhasePrefix

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K

private theorem programmed_alignment_to_fresh_only
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {v7 : OracleState} {state : State Bytes Block}
    (aligned : FSV8V7ProgrammedAlignment.StateAligned tape finiteTape v7 state)
    (noProgrammed : FSV8V7StateAlignment.NoProgrammed v7) :
    FSV8V7StateAlignment.StateAligned tape finiteTape v7 state := by
  exact
    { totalCalls := aligned.totalCalls
      freshCalls := aligned.freshCalls
      cache := aligned.cache
      history := aligned.history
      tapePrefix := aligned.tapePrefix
      noProgrammed := noProgrammed
      coherent := aligned.coherent
      tapeMatches := aligned.tapeMatches
      withinTape := aligned.withinTape
      tapeCompatibility := aligned.tapeCompatibility }

/-- Given the literal candidate return and source-constructed alignments, the
same candidate constructs the live chronological alpha execution and its
terminal remains aligned.  No freshness, target, or probability premise is
introduced here. -/
theorem returned_candidate_constructs_aligned_live
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits)
    (startV7 candidateV7 : OracleState) (start : Transcript)
    (alpha0 : K) (candidateDigest : Block)
    (functionalReturned :
      (run tape (FSNonzeroQM31.candidateScript start.digest) start.oracle).1 =
        some (.ok alpha0, candidateDigest))
    (initialAligned : FSV8V7ProgrammedAlignment.StateAligned tape finiteTape
      startV7 start.oracle)
    (candidateAligned : FSV8V7ProgrammedAlignment.StateAligned tape finiteTape
      candidateV7
      (run tape (FSNonzeroQM31.candidateScript start.digest) start.oracle).2)
    (startNoProgrammed : FSV8V7StateAlignment.NoProgrammed startV7)
    (prefixPath : RejectedCandidatePrefix startV7.history [])
    (totalRoom : startV7.totalCalls + 8 ≤ limits.totalCalls)
    (freshRoom : startV7.freshCalls + 8 ≤ limits.freshCalls)
    (tapeRoom : start.oracle.next + 8 ≤ steps) :
    ∃ limbs,
      SuccessfulAlignedChallenge tape finiteTape limits startV7 start
        (FSLiveChallengeTrace.challenge tape start).blocks
        (FSLiveChallengeTrace.challenge tape start).final
        (AspisK1.V7Tag73SamplerDecoder.encodeQm31Limbs limbs) ∧
      FSV8V7ProgrammedAlignment.StateAligned tape finiteTape candidateV7
        (FSLiveChallengeTrace.challenge tape start).final.oracle := by
  obtain ⟨limbs, liveSuccess, _assembled, finalExact⟩ :=
    successful_candidateScript_constructs_live tape start alpha0 candidateDigest
      functionalReturned
  have successful := successful_live_challenge_constructs_aligned_run
    (programmed_alignment_to_fresh_only initialAligned startNoProgrammed)
    prefixPath totalRoom freshRoom tapeRoom liveSuccess
  have terminalAligned : FSV8V7ProgrammedAlignment.StateAligned tape finiteTape
      candidateV7 (FSLiveChallengeTrace.challenge tape start).final.oracle := by
    rw [finalExact]
    exact candidateAligned
  exact ⟨limbs, successful, terminalAligned⟩

#print axioms returned_candidate_constructs_aligned_live

end AspisV8Completion.FSV8ProgrammedAlphaLiveAlignmentComposition
