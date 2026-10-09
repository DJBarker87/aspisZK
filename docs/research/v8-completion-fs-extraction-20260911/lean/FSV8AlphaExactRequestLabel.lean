import AspisFormal.K1.V7Tag73K15RelationAlphaPreAnswerRouters
import AspisFormal.K1.V7Tag73SchedulerNativeResult
import AspisFormal.K1.V7Tag73SchedulerCausalStateAlignment

/-!
# Scheduler alpha label at an exact verifier fresh request

This is the deterministic request-level half of the fresh-output bridge.  It
does not identify a source request with a position of the whole root trace,
and it says nothing about target locality.  It merely shows that once the
actual source construction has reached a literal verifier fresh request, the
causal router asks for precisely the label computed from that request's full
cached-inclusive history.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 1400

namespace AspisV8Completion.FSV8AlphaExactRequestLabel

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73K15RelationAlphaPreAnswerRouters
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SchedulerCausalStateAlignment
open AspisK1.V7Tag73SchedulerNativeResult

noncomputable section

/-- At the exact cursor exposing a verifier fresh request, the alpha router's
pre-answer label is definitionally the source-history label.  Cached records
are retained in `state.history`; only the current request is fresh. -/
theorem scheduler_relation_alpha_label_of_exact_verifier_fresh_request
    {globalOracleCalls : Nat} {Result : Type}
    (round : Fin 4) (transitionFuel : Nat)
    (cursor : UnifiedExposureCursor globalOracleCalls)
    (state : OracleState) (input : ShaInput)
    (request : SchedulerNativeRequest globalOracleCalls Result)
    (reached : seekUnifiedExposure transitionFuel cursor = request.erase)
    (exact : IsExactSchedulerNativeMachineFreshRequest .verifier state input
      request) :
    schedulerRelationAlphaLabel round transitionFuel cursor =
      relationAlphaPreferredSlotFromHistory round state.history input := by
  cases exact
  simp [schedulerRelationAlphaLabel, reached, SchedulerNativeRequest.erase]

#print axioms scheduler_relation_alpha_label_of_exact_verifier_fresh_request

end
end AspisV8Completion.FSV8AlphaExactRequestLabel
