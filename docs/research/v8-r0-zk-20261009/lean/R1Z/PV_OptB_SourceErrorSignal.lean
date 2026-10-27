import R1Z.PV_OptB_SourceSecondFailure
import R1Z.PV_OptB_SourceSuccessStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceErrorSignal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

def entropyError : Result (core.result.Result prover.RetriedProof verifier.Error × Store) → Bool
  | .ok (.Err .Entropy,_) => true
  | _ => false

/-- A coarse projection is enough to distinguish, if the actual body facts
are supplied. It is not substituted for the complete endpoint observer. -/
theorem success_vs_second_entropy {S : Type} (entropy : Entropy S) (pub : Pub)
    (left right : Compiled) (hash : Hash) (store leftStore rightStore : Store)
    (state next final : S) (secret : Secret) (proof : alloc.vec.Vec U8) (audit : prover.MaskedFixtureAudit)
    (first : entropy.call_mut state 0#usize = .ok (.Ok secret,next))
    (second : entropy.call_mut next 1#usize = .ok (.Err .Entropy,final))
    (leftBody : prover.prove_masked_attempt pub left .S2 hash secret store =
      .ok (.Ok (proof,audit),leftStore))
    (rightBody : prover.prove_masked_attempt pub right .S2 hash secret store =
      .ok (.Err .Rejected,rightStore)) :
    entropyError (prover.retry_attempt entropy pub left .S2 hash store state 0#usize) ≠
      entropyError (prover.retry_attempt entropy pub right .S2 hash store state 0#usize) := by
  rw [PV_OptB_SourceSuccessStep.succeeded entropy pub left hash store leftStore state next secret
    0#usize (by simp only [prover.ATTEMPT_CAP]; decide) proof audit first leftBody,
    PV_OptB_SourceSecondFailure.second_callback_error entropy pub right hash store rightStore
      state next final secret .Entropy first rightBody second]
  intro impossible
  cases impossible

#print axioms success_vs_second_entropy
end R1Z.PV_OptB_SourceErrorSignal
