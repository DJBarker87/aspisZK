import FSV8AcceptedExactRootAlphaMarkerOrigin
import FSV8FreshQueryRecord
import AspisFormal.K1.V7Tag73ExactCompilerGammaTraceOccurrence

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8MarkerFreshVerifierQueryBridge

open FSOracleExecution
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open FSV8FreshQueryRecord

noncomputable section

def markerFreshRecord (actor : QueryActor) (input : ShaInput)
    (output : Digest256) : QueryRecord :=
  { input := input
    output := output
    actor := actor
    origin := .fresh }

/- The marker-fresh branch alone determines the exact record appended by the
   literal successful marker query.  This is the strongest local fact before
   connecting the marker segment to the verifier projection trace. -/
theorem markerFresh_exact_record_since_marker
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (markerState markerNext : OracleState)
    (markerInput : ShaInput) (markerAnswer : Digest256)
    (missing : lookupEntry markerState markerInput = none)
    (success : queryOracle controller limits actor markerState markerInput =
      .ok (markerAnswer, markerNext)) :
    ∃ record,
      record ∈ historySince markerState markerNext ∧
      record.actor = actor ∧ record.origin = .fresh ∧
      record.input = markerInput ∧ record.output = markerAnswer := by
  have historyExact := successful_missing_query_appends_fresh_record
    controller limits actor markerState markerNext markerInput markerAnswer
    missing success
  let record : QueryRecord :=
    { input := markerInput
      output := markerAnswer
      actor := actor
      origin := .fresh }
  have exactSince : historySince markerState markerNext = [record] := by
    unfold historySince
    rw [historyExact]
    convert List.drop_append_length
      (l₁ := markerState.history) (l₂ := [record]) using 1
  refine ⟨record, ?_, rfl, rfl, rfl, rfl⟩
  rw [exactSince]
  simp

/-- A fresh marker transition lying chronologically between a segment's entry
and final states occurs in that segment's exact fresh-query enumeration.  The
two prefix hypotheses concern literal source histories; no transcript label or
independence assumption is used. -/
theorem markerFresh_mem_fresh_enumeration_of_history_prefixes
    (entryState markerState markerNext finalState : OracleState)
    (actor : QueryActor) (markerInput : ShaInput) (markerAnswer : Digest256)
    (entryPrefix : entryState.history <+: markerState.history)
    (historyExact : markerNext.history = markerState.history ++
      [markerFreshRecord actor markerInput markerAnswer])
    (finalPrefix : markerNext.history <+: finalState.history) :
    (markerInput, markerAnswer) ∈
      freshQueryEnumeration (historySince entryState finalState) := by
  rcases entryPrefix with ⟨between, markerHistory⟩
  rcases finalPrefix with ⟨after, finalHistory⟩
  rw [historyExact] at finalHistory
  unfold historySince
  rw [← finalHistory, ← markerHistory]
  simp [List.append_assoc, markerFreshRecord, freshQueryEnumeration]

#print axioms markerFresh_exact_record_since_marker
#print axioms markerFresh_mem_fresh_enumeration_of_history_prefixes

end
end AspisV8Completion.FSV8MarkerFreshVerifierQueryBridge
