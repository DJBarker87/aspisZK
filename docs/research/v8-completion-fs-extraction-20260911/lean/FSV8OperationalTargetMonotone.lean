import FSV8FreshRequestTargetEvent

/-!
# Operational request targets persist under chronological history extension

The fresh-marker composition needs to transport a target witnessed at the
literal local marker state to the same request state reconstructed from the
global scheduler.  This leaf proves the purely extensional half of that step.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8OperationalTargetMonotone

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

theorem operational_request_targets_mono_history
    (seen : Finset Digest256) (earlier later : List QueryRecord)
    (input : ShaInput) (answer : Digest256)
    (historyPrefix : earlier <+: later)
    (target : answer ∈ operationalRequestTargets seen earlier input) :
    answer ∈ operationalRequestTargets seen later input := by
  rcases (operational_request_target_hit_iff_mem seen earlier input answer).mpr
      target with answerSeen | ⟨record, member, literal⟩ | current
  · exact (operational_request_target_hit_iff_mem seen later input answer).mp
      (.priorFullOutput answerSeen)
  · exact (operational_request_target_hit_iff_mem seen later input answer).mp
      (.priorLiteralPrefix record (historyPrefix.subset member) literal)
  · exact (operational_request_target_hit_iff_mem seen later input answer).mp
      (.currentLiteralPrefix current)

#print axioms operational_request_targets_mono_history

end AspisV8Completion.FSV8OperationalTargetMonotone
