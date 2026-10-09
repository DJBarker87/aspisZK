import FSV8ProgrammedAlphaFreshDisposition
import AspisFormal.K1.V7Tag73CumulativeReplayHistory
import AspisFormal.K1.V7Tag73CausalProgrammingFreshness

/-!
# A prior alpha-coordinate creator is a marker-time causal target

This leaf performs the answer-level step that table provenance alone cannot
justify.  If a record for markerAnswer concatenated with domain 1 is already
in the chronological history when the marker request returns markerAnswer,
that answer belongs to the operational request target set.  A record from an
earlier historySince segment is first transported through the actual history
prefixes.

The result is deterministic.  It neither asserts that the marker request was
fresh nor lifts the request-level hit to the exact-root target event.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSV8AlphaMarkerPriorCreatorTarget

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CumulativeReplayHistory
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73CausalProgrammingFreshness

/-- Membership in an exact chronological suffix remains visible through a
later history prefix. -/
theorem history_since_member_survives_prefix
    (initial middle later : OracleState) (record : QueryRecord)
    (initialPrefix : initial.history <+: middle.history)
    (laterPrefix : middle.history <+: later.history)
    (member : record ∈ historySince initial middle) :
    record ∈ later.history := by
  have middleExact :=
    history_eq_initial_append_history_since initial middle initialPrefix
  have middleMember : record ∈ middle.history := by
    rw [middleExact]
    exact List.mem_append_right initial.history member
  exact laterPrefix.subset middleMember

/-- An earlier exact alpha-output-coordinate creator makes the marker answer a
literal-prefix target at the marker request.  currentInput is retained because
the operational target set also accounts for the current request; this proof
uses only the genuinely prior record. -/
theorem prior_alpha_creator_hits_marker_request_target
    (seen : Finset Digest256) (markerState : OracleState)
    (currentInput : ShaInput) (markerAnswer : Digest256)
    (record : QueryRecord)
    (member : record ∈ markerState.history)
    (inputExact : record.input = bytes markerAnswer ++ [1]) :
    markerAnswer ∈
      operationalRequestTargets seen markerState.history currentInput := by
  apply (operational_request_target_hit_iff_mem seen markerState.history
    currentInput markerAnswer).mp
  exact .priorLiteralPrefix record member (by
    rw [inputExact]
    exact literal_squeeze_input_has_state_prefix markerAnswer 1)

/-- The source-shaped form used by V8 insertion provenance: a creator in an
earlier segment is carried to the marker cut and therefore exposes the same
literal-prefix target. -/
theorem earlier_segment_alpha_creator_hits_marker_request_target
    (seen : Finset Digest256)
    (initial segmentEnd markerState : OracleState)
    (currentInput : ShaInput) (markerAnswer : Digest256)
    (record : QueryRecord)
    (initialPrefix : initial.history <+: segmentEnd.history)
    (markerPrefix : segmentEnd.history <+: markerState.history)
    (member : record ∈ historySince initial segmentEnd)
    (inputExact : record.input = bytes markerAnswer ++ [1]) :
    markerAnswer ∈
      operationalRequestTargets seen markerState.history currentInput := by
  exact prior_alpha_creator_hits_marker_request_target seen markerState
    currentInput markerAnswer record
    (history_since_member_survives_prefix initial segmentEnd markerState record
      initialPrefix markerPrefix member)
    inputExact

#print axioms history_since_member_survives_prefix
#print axioms prior_alpha_creator_hits_marker_request_target
#print axioms earlier_segment_alpha_creator_hits_marker_request_target

end AspisV8Completion.FSV8AlphaMarkerPriorCreatorTarget
