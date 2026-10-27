import R1Z.PV_OptB_SourceSecondFailure
import R1Z.PV_OptB_SourceStopStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceConditionalDifference
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- Exact source distinction with all missing native body facts explicit.
It must not be called a checked admitted-witness counterexample. -/
theorem semantic_vs_second_entropy {S : Type} (entropy : Entropy S) (pub : Pub)
    (left right : Compiled) (hash : Hash) (store leftStore rightStore : Store)
    (state next final : S) (secret : Secret)
    (first : entropy.call_mut state 0#usize = .ok (.Ok secret,next))
    (second : entropy.call_mut next 1#usize = .ok (.Err .Entropy,final))
    (leftBody : prover.prove_masked_attempt pub left .S2 hash secret store =
      .ok (.Err .Semantic,leftStore))
    (rightBody : prover.prove_masked_attempt pub right .S2 hash secret store =
      .ok (.Err .Rejected,rightStore)) :
    prover.retry_attempt entropy pub left .S2 hash store state 0#usize ≠
      prover.retry_attempt entropy pub right .S2 hash store state 0#usize := by
  have leftResult := PV_OptB_SourceStopStep.stopped entropy pub left hash store leftStore state next secret
    0#usize (by simp only [prover.ATTEMPT_CAP]; decide) .Semantic (by intro h; cases h) first leftBody
  have rightResult := PV_OptB_SourceSecondFailure.second_callback_error entropy pub right hash
    store rightStore state next final secret .Entropy first rightBody second
  rw [leftResult,rightResult]
  intro same
  cases same

#print axioms semantic_vs_second_entropy
end R1Z.PV_OptB_SourceConditionalDifference
