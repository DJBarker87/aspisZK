import FSV8AlignedAlphaSqueezeStep
import FSV8AlphaChallengeDecoderBridge

/-!
# Complete chronological V8 alpha candidate in aligned V7/FS states

This leaf recursively follows the actual one-to-four `squeeze` path of a live
ordinary alpha candidate.  Every proper candidate is proved rejected by the
deployed decoder, every output/advance pair is executed in the actual V7
state, and the final accepted pair moves the literal history recognizer to
`inactive`.

The starting state must already be the constructed post-alpha-nonce marker
state.  Connecting that state to the exact whole verifier is a later root-cut
theorem.  This leaf is deterministic and assigns no probability.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8AlignedAlphaChallengeRun

open FSOracleExecution FSBoundedTranscript FSLiveChallengeTrace
open FSV8AlignedAlphaSqueezeStep FSV8AlphaChallengeDecoderBridge
open FSV8AlphaHistoryPhasePrefix FSV8CandidateOriginTrace
open FSV8V7StateAlignment
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape

theorem squeeze_log_length (tape : Tape) (s : Transcript) :
    (squeeze tape s).2.oracle.log.length = s.oracle.log.length + 2 := by
  simp [FSBoundedTranscript.squeeze, query_log_length]

theorem squeeze_next_le (tape : Tape) (s : Transcript) :
    (squeeze tape s).2.oracle.next ≤ s.oracle.next + 2 := by
  have first := query_next_bound tape s.oracle (outputInput s)
  have second := query_next_bound tape
    (FSOracleExecution.query tape s.oracle (outputInput s)).2 (advanceInput s)
  simpa [FSBoundedTranscript.squeeze, outputInput, advanceInput] using
    (show
      (FSOracleExecution.query tape
        (FSOracleExecution.query tape s.oracle (outputInput s)).2
        (advanceInput s)).2.next ≤ s.oracle.next + 2 by omega)

theorem SqueezePath.log_length {tape : Tape} :
    forall {start blocks current}, SqueezePath tape start blocks current ->
      current.oracle.log.length = start.oracle.log.length + 2 * blocks.length := by
  intro start blocks current path
  induction path with
  | nil => simp
  | @snoc current blocks path ih =>
      rw [squeeze_log_length, ih]
      simp only [List.length_append, List.length_singleton]
      omega

theorem SqueezePath.next_le {tape : Tape} :
    forall {start blocks current}, SqueezePath tape start blocks current ->
      current.oracle.next ≤ start.oracle.next + 2 * blocks.length := by
  intro start blocks current path
  induction path with
  | nil => simp
  | @snoc current blocks path ih =>
      have step := squeeze_next_le tape current
      simp only [List.length_append, List.length_singleton]
      omega

/- Every constructor is tied to the stated start.  Each `snoc` stores the
actual V7 pair object, including both histories and both cache/fresh
classifications. -/
inductive AlignedRejectedPath {steps : Nat} (tape : Tape)
    (finiteTape : FreshAnswerTape Block steps) (limits : OracleLimits)
    (startV7 : OracleState) (start : Transcript) :
    List Block -> OracleState -> Transcript -> Prop where
  | base
      (aligned : StateAligned tape finiteTape startV7 start.oracle)
      (prefixPath : RejectedCandidatePrefix startV7.history []) :
      AlignedRejectedPath tape finiteTape limits startV7 start [] startV7 start
  | snoc {prior : List Block} {v7 : OracleState} {s : Transcript}
      (path : AlignedRejectedPath tape finiteTape limits startV7 start prior v7 s)
      (pair : AlignedSqueezePair tape finiteTape limits v7 s)
      (bounded : prior.length < 4)
      (reject : decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (prior ++ [(outputStep tape s).1]) = none) :
      AlignedRejectedPath tape finiteTape limits startV7 start
        (prior ++ [(outputStep tape s).1]) pair.afterAdvance
        (squeeze tape s).2

theorem AlignedRejectedPath.aligned
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
      AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s ->
        StateAligned tape finiteTape v7 s.oracle := by
  intro blocks v7 s path
  induction path with
  | base aligned _ => exact aligned
  | snoc _ pair _ _ => exact pair.aligned

theorem AlignedRejectedPath.prefixPath
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
      AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s ->
        RejectedCandidatePrefix v7.history blocks := by
  intro blocks v7 s path
  induction path with
  | base _ prefixPath => exact prefixPath
  | @snoc prior v7 s path pair bounded reject ih =>
      rw [pair.advanceHistory, pair.outputHistory]
      simpa [List.append_assoc] using
        RejectedCandidatePrefix.rejected ih bounded s.digest
          (outputStep tape s).1 (advanceStep tape s).1 pair.outputOrigin
          pair.advanceOrigin reject

theorem AlignedRejectedPath.sourcePath
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript} :
    {blocks : List Block} -> {v7 : OracleState} -> {s : Transcript} ->
      AlignedRejectedPath tape finiteTape limits startV7 start blocks v7 s ->
        SqueezePath tape start blocks s := by
  intro blocks v7 s path
  induction path with
  | base _ _ => exact .nil start
  | snoc _ _ _ _ ih => exact .snoc ih

/-- Recursive construction from the actual live squeeze path.  The
`allRejected` premise is about the deployed decoder on every nonempty prefix
through `blocks`; for the proper prefix of a successful challenge it is
constructed below from prefix minimality. -/
theorem alignedRejectedPath_of_squeezePath
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {current : Transcript}
    (sourcePath : SqueezePath tape start blocks current)
    (startAligned : StateAligned tape finiteTape startV7 start.oracle)
    (startPrefix : RejectedCandidatePrefix startV7.history [])
    (allRejected : forall count, 0 < count -> count ≤ blocks.length ->
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        (blocks.take count) = none)
    (blockCap : blocks.length ≤ 4)
    (totalRoom : startV7.totalCalls + 2 * blocks.length ≤ limits.totalCalls)
    (freshRoom : startV7.freshCalls + 2 * blocks.length ≤ limits.freshCalls)
    (tapeRoom : start.oracle.next + 2 * blocks.length ≤ steps) :
    exists finalV7,
      AlignedRejectedPath tape finiteTape limits startV7 start
        blocks finalV7 current := by
  induction sourcePath with
  | nil => exact Exists.intro startV7 (.base startAligned startPrefix)
  | @snoc previous blocks priorPath ih =>
      have priorCap : blocks.length ≤ 4 := by
        simp only [List.length_append, List.length_singleton] at blockCap
        omega
      have priorRejected : forall count, 0 < count -> count ≤ blocks.length ->
          decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
            (blocks.take count) = none := by
        intro count positive within
        have complete := allRejected count positive (by
          simp only [List.length_append, List.length_singleton]
          omega)
        rw [List.take_append_of_le_length within] at complete
        exact complete
      have priorTotal :
          startV7.totalCalls + 2 * blocks.length ≤ limits.totalCalls := by
        simp only [List.length_append, List.length_singleton] at totalRoom
        omega
      have priorFresh :
          startV7.freshCalls + 2 * blocks.length ≤ limits.freshCalls := by
        simp only [List.length_append, List.length_singleton] at freshRoom
        omega
      have priorTape :
          start.oracle.next + 2 * blocks.length ≤ steps := by
        simp only [List.length_append, List.length_singleton] at tapeRoom
        omega
      obtain ⟨currentV7, currentPath⟩ := ih
        priorRejected priorCap priorTotal priorFresh priorTape
      have currentTotalEq :
          currentV7.totalCalls = startV7.totalCalls + 2 * blocks.length := by
        rw [currentPath.aligned.totalCalls,
          FSV8AlignedAlphaChallengeRun.SqueezePath.log_length priorPath,
          ← startAligned.totalCalls]
      have currentFreshLe :
          currentV7.freshCalls ≤ startV7.freshCalls + 2 * blocks.length := by
        rw [currentPath.aligned.freshCalls, startAligned.freshCalls]
        exact FSV8AlignedAlphaChallengeRun.SqueezePath.next_le priorPath
      have currentTapeLe :
          previous.oracle.next ≤ start.oracle.next + 2 * blocks.length :=
        FSV8AlignedAlphaChallengeRun.SqueezePath.next_le priorPath
      have pairTotal : currentV7.totalCalls + 2 ≤ limits.totalCalls := by
        simp only [List.length_append, List.length_singleton] at totalRoom
        omega
      have pairFresh : currentV7.freshCalls + 2 ≤ limits.freshCalls := by
        simp only [List.length_append, List.length_singleton] at freshRoom
        omega
      have pairTape : previous.oracle.next + 2 ≤ steps := by
        simp only [List.length_append, List.length_singleton] at tapeRoom
        omega
      let pair := alignedSqueezePair_complete currentPath.aligned
        pairTotal pairFresh pairTape
      have bounded : blocks.length < 4 := by
        simp only [List.length_append, List.length_singleton] at blockCap
        omega
      have rejected :
          decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
            (blocks ++ [(outputStep tape previous).1]) = none := by
        change decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
          (blocks ++ [(squeeze tape previous).1]) = none
        have full := allRejected (blocks ++ [(squeeze tape previous).1]).length
          (by simp) (Nat.le_refl _)
        rw [List.take_length] at full
        exact full
      exact Exists.intro pair.afterAdvance
        (.snoc currentPath pair bounded rejected)

def SuccessfulAlignedChallenge
    {steps : Nat} (tape : Tape) (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (startV7 : OracleState) (start : Transcript)
    (blocks : List Block) (final : Transcript) (value : Qm31Bytes) : Prop :=
  exists rejected finalStart beforeFinal,
    exists _rejectedPath : AlignedRejectedPath tape finiteTape limits startV7 start
      rejected beforeFinal finalStart,
    exists finalPair : AlignedSqueezePair tape finiteTape limits
      beforeFinal finalStart,
      blocks = rejected ++ [(outputStep tape finalStart).1] /\
      final = (squeeze tape finalStart).2 /\
      decodeChallengeParameter exactSecureCircleParameterMap
        (.alpha 0) (rejected ++ [(outputStep tape finalStart).1]) = some value /\
      relationAlphaHistoryPhase 0 finalPair.afterAdvance.history = .inactive

/-- Generic last-pair decomposition.  Stating this over variable indexed
`blocks` and `final` avoids selecting a path retrospectively from the
instrumented challenge object. -/
theorem successful_squeezePath_constructs_aligned_run
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {blocks : List Block} {final : Transcript} {value : Qm31Bytes}
    (sourcePath : SqueezePath tape start blocks final)
    (startAligned : StateAligned tape finiteTape startV7 start.oracle)
    (startPrefix : RejectedCandidatePrefix startV7.history [])
    (totalRoom : startV7.totalCalls + 8 ≤ limits.totalCalls)
    (freshRoom : startV7.freshCalls + 8 ≤ limits.freshCalls)
    (tapeRoom : start.oracle.next + 8 ≤ steps)
    (blocksPositive : 0 < blocks.length)
    (blocksCap : blocks.length ≤ 4)
    (acceptedAll : decodeChallengeParameter exactSecureCircleParameterMap
      (.alpha 0) blocks = some value)
    (minimal : forall count, count < blocks.length ->
      decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
        (blocks.take count) = none) :
    SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      blocks final value := by
  cases sourcePath with
  | nil => simp at blocksPositive
  | @snoc finalStart rejected priorPath =>
      have rejectedCap : rejected.length ≤ 4 := by
        simp only [List.length_append, List.length_singleton] at blocksCap
        omega
      have rejectedLt : rejected.length < 4 := by
        simpa using blocksCap
      have rejectedAll : forall count, 0 < count -> count ≤ rejected.length ->
          decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
            (rejected.take count) = none := by
        intro count positive within
        have strict : count <
            (rejected ++ [(outputStep tape finalStart).1]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have rejectedByMinimal := minimal count strict
        rw [List.take_append_of_le_length within] at rejectedByMinimal
        exact rejectedByMinimal
      have rejectedTotal :
          startV7.totalCalls + 2 * rejected.length ≤ limits.totalCalls := by
        omega
      have rejectedFresh :
          startV7.freshCalls + 2 * rejected.length ≤ limits.freshCalls := by
        omega
      have rejectedTape :
          start.oracle.next + 2 * rejected.length ≤ steps := by
        omega
      obtain ⟨beforeFinal, rejectedPath⟩ :=
        alignedRejectedPath_of_squeezePath priorPath startAligned startPrefix
          rejectedAll rejectedCap rejectedTotal rejectedFresh rejectedTape
      have totalEq :
          beforeFinal.totalCalls = startV7.totalCalls + 2 * rejected.length := by
        rw [rejectedPath.aligned.totalCalls,
          FSV8AlignedAlphaChallengeRun.SqueezePath.log_length priorPath,
          ← startAligned.totalCalls]
      have freshLe :
          beforeFinal.freshCalls ≤ startV7.freshCalls + 2 * rejected.length := by
        rw [rejectedPath.aligned.freshCalls, startAligned.freshCalls]
        exact FSV8AlignedAlphaChallengeRun.SqueezePath.next_le priorPath
      have nextLe :
          finalStart.oracle.next ≤ start.oracle.next + 2 * rejected.length :=
        FSV8AlignedAlphaChallengeRun.SqueezePath.next_le priorPath
      have finalPairTotal : beforeFinal.totalCalls + 2 ≤ limits.totalCalls := by
        rw [totalEq]
        omega
      have finalPairFresh : beforeFinal.freshCalls + 2 ≤ limits.freshCalls := by
        exact le_trans (Nat.add_le_add_right freshLe 2) (by omega)
      have finalPairTape : finalStart.oracle.next + 2 ≤ steps := by
        exact le_trans (Nat.add_le_add_right nextLe 2) (by omega)
      let finalPair := alignedSqueezePair_complete rejectedPath.aligned
        finalPairTotal finalPairFresh finalPairTape
      have accepted :
          decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
              (rejected ++ [(outputStep tape finalStart).1]) =
            some value := by
        change decodeChallengeParameter exactSecureCircleParameterMap (.alpha 0)
          (rejected ++ [(squeeze tape finalStart).1]) = some value
        exact acceptedAll
      have priorPhase := rejectedPath.prefixPath
      have outputPhase := phase_after_output beforeFinal.history rejected
        finalStart.digest (outputStep tape finalStart).1 finalPair.outputOrigin
        (rejectedCandidatePrefix_phase priorPhase)
      have finalPhase : relationAlphaHistoryPhase 0
          finalPair.afterAdvance.history = .inactive := by
        rw [finalPair.advanceHistory, finalPair.outputHistory]
        apply phase_after_accepted_advance _ rejected
          (outputStep tape finalStart).1 finalStart.digest
          (advanceStep tape finalStart).1 finalPair.advanceOrigin
          value
        · exact outputPhase
        · exact accepted
      exact ⟨rejected, finalStart, beforeFinal, rejectedPath, finalPair,
        rfl, rfl, accepted, finalPhase⟩

/-- A successful live candidate constructs its entire V7 chronological
execution: all proper rejected pairs plus the accepted final pair. -/
theorem successful_live_challenge_constructs_aligned_run
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {startV7 : OracleState} {start : Transcript}
    {limbs : List Nat}
    (startAligned : StateAligned tape finiteTape startV7 start.oracle)
    (startPrefix : RejectedCandidatePrefix startV7.history [])
    (totalRoom : startV7.totalCalls + 8 ≤ limits.totalCalls)
    (freshRoom : startV7.freshCalls + 8 ≤ limits.freshCalls)
    (tapeRoom : start.oracle.next + 8 ≤ steps)
    (liveSuccess : (FSLiveChallengeTrace.challenge tape start).result = some limbs) :
    SuccessfulAlignedChallenge tape finiteTape limits startV7 start
      (FSLiveChallengeTrace.challenge tape start).blocks
      (FSLiveChallengeTrace.challenge tape start).final
      (encodeQm31Limbs limbs) := by
  exact successful_squeezePath_constructs_aligned_run
    (challenge_squeezePath tape start) startAligned startPrefix totalRoom
      freshRoom tapeRoom (challenge_blocks_bounds tape start).1
      (challenge_blocks_bounds tape start).2
      (challenge_decode_alpha_zero tape start limbs liveSuccess)
      (challenge_decode_alpha_zero_prefix_minimal tape start limbs liveSuccess)

#print axioms squeeze_log_length
#print axioms squeeze_next_le
#print axioms SqueezePath.log_length
#print axioms SqueezePath.next_le
#print axioms AlignedRejectedPath.aligned
#print axioms AlignedRejectedPath.prefixPath
#print axioms AlignedRejectedPath.sourcePath
#print axioms alignedRejectedPath_of_squeezePath
#print axioms successful_squeezePath_constructs_aligned_run
#print axioms successful_live_challenge_constructs_aligned_run

end
end AspisV8Completion.FSV8AlignedAlphaChallengeRun
