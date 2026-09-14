import FSLiveChallengeTrace
import FSNonzeroQM31
import FSTranscriptScript
import Mathlib.Tactic

/-!
# S8 path-sensitive buffered sampler cost

This file proves the call bound on the actual source-shaped buffered sampler.
It counts every oracle lookup in the log, including cache hits.  Exhaustion is
not conditioned away: `FSLiveChallengeTrace.challenge` records the path taken
by both successful and exhausted executions.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.S8BufferedPotential

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveChallengeTrace

/-- Each raw query appends one log record, including a cached query. -/
theorem query_log_length (tape : Tape) (s : Oracle) (input : List UInt8) :
    (query tape s input).2.log.length = s.log.length + 1 := by
  obtain ⟨event, h, _, _⟩ := query_log tape s input
  simp only [h, List.length_append, List.length_singleton]

/-- A source squeeze always performs its output and advance calls. -/
theorem squeeze_log_length (tape : Tape) (s : Transcript) :
    (squeeze tape s).2.oracle.log.length = s.oracle.log.length + 2 := by
  simp only [squeeze, query_log_length]

theorem words_length (block : Block) : (words block).length = 8 := by
  simp only [words, List.length_map, List.length_range]

/-- Conservation law for one actual word consumption. -/
theorem nextWord_balance (tape : Tape) (s : Stream) :
    4 * (FSBoundedTranscript.nextWord tape s).2.transcript.oracle.log.length +
        s.remaining.length =
      4 * s.transcript.oracle.log.length +
        (FSBoundedTranscript.nextWord tape s).2.remaining.length + 1 := by
  cases h : s.remaining with
  | cons a rest =>
      simp only [FSBoundedTranscript.nextWord, h, List.length_cons]
      omega
  | nil =>
      simp only [FSBoundedTranscript.nextWord, h, List.length_nil,
        List.length_tail, words_length, squeeze_log_length]
      omega

/-- Arithmetic endpoint used after summing the conservation identity. -/
theorem four_limb_cost_from_conservation (calls wordsUsed remainder : Nat)
    (wordsBound : wordsUsed ≤ 32) (remainingBound : remainder ≤ 7)
    (balance : 4 * calls = wordsUsed + remainder)
    (paired : calls % 2 = 0) : calls ≤ 8 := by
  omega

/-- Every recorded squeeze contributes exactly two log entries. -/
theorem squeezePath_log_length (tape : Tape) (start : Transcript) :
    ∀ {blocks : List Block} {final : Transcript},
      SqueezePath tape start blocks final →
        final.oracle.log.length = start.oracle.log.length + 2 * blocks.length := by
  intro blocks final path
  induction path with
  | nil => simp
  | snoc path ih =>
      rw [squeeze_log_length, ih]
      simp only [List.length_append, List.length_singleton]
      omega

/-- The literal buffered QM31 draw adds at most eight shared-oracle calls.

This is unconditional over the tape, cache and decoder outcome.  In
particular, it covers an exhausted limb and counts cached output/advance calls
as calls. -/
theorem live_challenge_log_length_le_eight (tape : Tape) (s : Transcript) :
    (FSLiveChallengeTrace.challenge tape s).final.oracle.log.length ≤
      s.oracle.log.length + 8 := by
  have path := FSLiveChallengeTrace.challenge_squeezePath tape s
  have exactLength := squeezePath_log_length tape s path
  have blocks := (FSLiveChallengeTrace.challenge_blocks_bounds tape s).2
  omega

/-- The existing source sampler erases to the live trace, so its actual final
oracle has the same path-sensitive eight-call bound. -/
theorem source_challenge_log_length_le_eight (tape : Tape) (s : Transcript) :
    (FSBoundedTranscript.challenge tape s).2.oracle.log.length ≤
      s.oracle.log.length + 8 := by
  have erased := (FSLiveChallengeTrace.challenge_erase tape s).2
  rw [← erased]
  exact live_challenge_log_length_le_eight tape s

/-- The source `challengeScript` runs exactly the same sampler state, hence the
same bound applies to the executable script rather than merely its static
allowance of 66. -/
theorem source_challengeScript_log_length_le_eight (tape : Tape)
    (s : Transcript) :
    (run tape (challengeScript s.digest) s.oracle).2.log.length ≤
      s.oracle.log.length + 8 := by
  rw [run_challenge]
  exact source_challenge_log_length_le_eight tape s

/-- The selected candidate wrapper only decodes the four limbs.  It performs
no oracle operation beyond the source challenge it wraps. -/
theorem source_candidate_log_length_le_eight (tape : Tape) (s : Transcript) :
    (FSNonzeroQM31.candidate tape s).2.oracle.log.length ≤
      s.oracle.log.length + 8 := by
  have bound := source_challenge_log_length_le_eight tape s
  cases sampled : (FSBoundedTranscript.challenge tape s).1 with
  | none => simpa [FSNonzeroQM31.candidate, sampled] using bound
  | some limbs =>
      cases assembled : FSV7OODSampler.assemble limbs with
      | none => simpa [FSNonzeroQM31.candidate, sampled, assembled] using bound
      | some value =>
          simpa [FSNonzeroQM31.candidate, sampled, assembled] using bound

/-- The executable candidate script inherits the exact eight-call bound,
despite carrying the conservative static allowance 66. -/
theorem source_candidateScript_log_length_le_eight (tape : Tape)
    (s : Transcript) :
    (run tape (FSNonzeroQM31.candidateScript s.digest) s.oracle).2.log.length ≤
      s.oracle.log.length + 8 := by
  rw [FSNonzeroQM31.run_candidate]
  exact source_candidate_log_length_le_eight tape s

/-- At most `n` candidate draws occur in the source nonzero wrapper.  Decoder
failure and the first nonzero value stop early and retain their smaller cost. -/
theorem source_nonzero_log_length_le (tape : Tape) : ∀ n (s : Transcript),
    (FSNonzeroQM31.nonzero tape n s).2.oracle.log.length ≤
      s.oracle.log.length + 8 * n := by
  intro n
  induction n with
  | zero => intro s; simp [FSNonzeroQM31.nonzero]
  | succ n ih =>
      intro s
      simp only [FSNonzeroQM31.nonzero]
      have first := source_candidate_log_length_le_eight tape s
      split
      · simp only [Prod.snd]
        omega
      · split
        · have rest := ih (FSNonzeroQM31.candidate tape s).2
          omega
        · simp only [Prod.snd]
          omega

/-- Executable-script form of the bounded nonzero wrapper. -/
theorem source_nonzeroScript_log_length_le (tape : Tape) (n : Nat)
    (s : Transcript) :
    (run tape (FSNonzeroQM31.nonzeroScript n s.digest) s.oracle).2.log.length ≤
      s.oracle.log.length + 8 * n := by
  rw [FSNonzeroQM31.run_nonzero]
  exact source_nonzero_log_length_le tape n s

/-- Arithmetic composition for the selected core-prefix inventory.  The
separate source consumer must establish its 49 sampler invocations and 28
absorbs; this theorem does not pretend to produce that control-flow fact. -/
theorem selected_core_prefix_arithmetic (ordinaryInvocations absorbs : Nat)
    (ordinaryBound : ordinaryInvocations ≤ 49)
    (absorbBound : absorbs ≤ 28) :
    8 * ordinaryInvocations + absorbs ≤ 420 := by
  omega

#print axioms query_log_length
#print axioms squeeze_log_length
#print axioms nextWord_balance
#print axioms four_limb_cost_from_conservation
#print axioms squeezePath_log_length
#print axioms live_challenge_log_length_le_eight
#print axioms source_challenge_log_length_le_eight
#print axioms source_challengeScript_log_length_le_eight
#print axioms source_candidate_log_length_le_eight
#print axioms source_candidateScript_log_length_le_eight
#print axioms source_nonzero_log_length_le
#print axioms source_nonzeroScript_log_length_le
#print axioms selected_core_prefix_arithmetic

end AspisV8Completion.S8BufferedPotential
