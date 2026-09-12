import FSNonzeroQM31
import FSOODSamplerExposure

/-!
The first literal squeeze of a positive-fuel nonzero-QM31 sampler remains in
its final chronological history, including zero retries and failure paths.

This is deterministic source timing.  It neither asserts freshness nor
conditions on sampler success.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSNonzeroSqueezeExposure
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
open FSExposureOrder FSOODSamplerExposure FSNonzeroQM31

theorem candidate_oracle_eq_challenge (tape : Tape) (s : Transcript) :
    (candidate tape s).2.oracle = (challenge tape s).2.oracle := by
  unfold candidate
  cases sampled : (challenge tape s).1 with
  | none => simp only [sampled]
  | some limbs =>
      cases assembled : FSV7OODSampler.assemble limbs <;>
        simp only [sampled, assembled]

/-- Whatever the first candidate returns, its consumed history is a prefix of
the complete positive-fuel nonzero sampler history.  A decoded zero may cause
another attempt, but cannot erase the first one. -/
theorem candidate_prefix_nonzero (tape : Tape) (n : Nat) (s : Transcript) :
    Prefix (candidate tape s).2.oracle
      (run tape (nonzeroScript (n + 1) s.digest) s.oracle).2 := by
  simp only [nonzeroScript, run_bind, run_candidate]
  cases status : (candidate tape s).1 with
  | error error =>
      simp [status, Prefix, run]
  | ok value =>
      by_cases zero : value = 0
      · simp only [status, zero, ↓reduceIte]
        exact run_extends tape (nonzeroScript n (candidate tape s).2.digest)
          (candidate tape s).2.oracle
      · simp [status, zero, Prefix, run]

theorem nonzero_squeeze_mem (tape : Tape) (n : Nat) (s : Transcript) :
    squeezeInput s.digest ∈
      inputs (run tape (nonzeroScript (n + 1) s.digest) s.oracle).2.log := by
  apply mem_inputs_of_prefix (candidate_prefix_nonzero tape n s)
  rw [candidate_oracle_eq_challenge tape s]
  exact challenge_logs_start tape s

#print axioms candidate_oracle_eq_challenge
#print axioms candidate_prefix_nonzero
#print axioms nonzero_squeeze_mem

end AspisV8Completion.FSNonzeroSqueezeExposure
