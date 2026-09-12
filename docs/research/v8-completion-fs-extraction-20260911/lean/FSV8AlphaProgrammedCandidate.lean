import AlphaDigestEncodingProbe
import FSV8AlphaChallengeInputBridge
import FSV8V7OracleMachineBridge

/-!
# A programmed/cached alpha output drives the literal candidate sampler

This deterministic leaf closes the byte/field seam.  It does not assert that
the alpha input was an adversary prequery, that programming succeeded, or that
the projected state is the state reached by a legal replay.  Those facts are
owned by the target-disposition and restoration layers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.FSV8AlphaProgrammedCandidate

open FSOracleExecution FSBoundedTranscript FSNonzeroQM31
open AspisK1.V7FsAokExperiment
open FSV8AlphaChallengeInputBridge
open FSV8V7OracleMachineBridge
open AlphaDigestEncodingProbe

noncomputable section

theorem projected_lookup_first_squeeze
    (tape : FSBoundedTranscript.Tape) (state : OracleState)
    (transcript : Transcript)
    (entry : TableEntry) (value : FSNonzeroQM31.K)
    (oracleEq : transcript.oracle = projectOracleState state)
    (lookup : lookupEntry state (alphaCandidateInput transcript) = some entry)
    (outputEq : entry.output = canonicalOutput value) :
    (squeeze tape transcript).1 = canonicalOutput value := by
  have lookup' :
      lookupEntry state (List.ofFn transcript.digest ++ [1]) = some entry := by
    simpa [alphaCandidateInput] using lookup
  have cacheHit :
      (projectOracleState state).cache (List.ofFn transcript.digest ++ [1]) =
        some entry.output := by
    change Option.map TableEntry.output
      (lookupEntry state (List.ofFn transcript.digest ++ [1])) =
        some entry.output
    rw [lookup']
    rfl
  change (query tape transcript.oracle
    (List.ofFn transcript.digest ++ [1])).1 = canonicalOutput value
  rw [oracleEq]
  simp only [query, cacheHit]
  exact outputEq

theorem projected_lookup_drives_candidate
    (tape : FSBoundedTranscript.Tape) (state : OracleState)
    (transcript : Transcript)
    (entry : TableEntry) (value : FSNonzeroQM31.K)
    (oracleEq : transcript.oracle = projectOracleState state)
    (lookup : lookupEntry state (alphaCandidateInput transcript) = some entry)
    (outputEq : entry.output = canonicalOutput value) :
    (candidate tape transcript).1 = .ok value := by
  exact candidate_of_first_canonical_output tape transcript value
    (projected_lookup_first_squeeze tape state transcript entry value
      oracleEq lookup outputEq)

#print axioms projected_lookup_first_squeeze
#print axioms projected_lookup_drives_candidate

end
end AspisV8Completion.FSV8AlphaProgrammedCandidate
