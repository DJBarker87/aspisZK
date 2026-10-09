import FSV8AlphaHistoryPhasePrefix
import AspisFormal.K1.V7Tag73VerifierOracleStability

/-!
# One actual alpha-marker query constructs the phase-prefix base case

This is the small deterministic consumer of the source marker-query theorem.
It retains the call's actual cached/fresh origin and does not require an
aligned state, target event, or probability premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.FSV8MarkerQueryPrefixPath

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VerifierOracleStability
open FSV8AlphaHistoryPhasePrefix

/-- The successful literal marker query appends exactly the `markerRecord`
that initializes `RejectedCandidatePrefix`. -/
theorem marker_query_constructs_candidate_prefix_path
    (controller : AdaptiveController) (limits : OracleLimits)
    (state nextState : OracleState) (digest answer : ShaOutput)
    (nonce : NonceBytes)
    (success : queryOracle controller limits .verifier state
      (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce) =
        .ok (answer, nextState)) :
    RejectedCandidatePrefix nextState.history [] := by
  obtain ⟨record, historyEq, inputEq, outputEq, actorEq, _tableCase⟩ :=
    query_oracle_success_table_history_cases controller limits .verifier state
      nextState (bytes digest ++ [domAbsorb, foldWorkNonceLabel, 0] ++ bytes nonce)
      answer success
  have recordEq : record = markerRecord digest answer nonce record.origin := by
    rcases record with ⟨recordInput, recordOutput, recordActor, recordOrigin⟩
    simp only at inputEq outputEq actorEq ⊢
    subst recordInput
    subst recordOutput
    subst recordActor
    rfl
  rw [historyEq, recordEq]
  exact RejectedCandidatePrefix.marker state.history digest answer nonce
    record.origin

#print axioms marker_query_constructs_candidate_prefix_path

end AspisV8Completion.FSV8MarkerQueryPrefixPath
