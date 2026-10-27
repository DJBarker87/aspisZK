import R1Z.PV_OptB_SourceEntropyStep
set_option autoImplicit false
namespace R1Z.PV_OptB_SourceSecondFailure
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]

/-- A reached second callback error after an actual rejected source body.
This is conditional source control; it does not assert that an admitted
witness supplies the body premise. -/
theorem second_callback_error {S : Type} (entropy : Entropy S) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store afterStore : Store) (state next final : S) (secret : Secret)
    (e : verifier.Error)
    (first : entropy.call_mut state 0#usize = .ok (.Ok secret,next))
    (body : prover.prove_masked_attempt pub compiled .S2 hash secret store =
      .ok (.Err .Rejected,afterStore))
    (second : entropy.call_mut next 1#usize = .ok (.Err e,final)) :
    prover.retry_attempt entropy pub compiled .S2 hash store state 0#usize =
      .ok (.Err e,afterStore) := by
  rw [PV_OptB_SourceRetryStep.rejected entropy pub compiled hash store afterStore state next secret
    0#usize (by simp only [prover.ATTEMPT_CAP]; decide) first body]
  rw [show Usize.wrapping_add 0#usize 1#usize = 1#usize from by
    apply UScalar.eq_of_val_eq
    rw [ProverCommitRetrySource34.add_one _ (by decide)]
    rfl]
  exact PV_OptB_SourceEntropyStep.callback_error entropy pub compiled hash afterStore next final e
    1#usize (by simp only [prover.ATTEMPT_CAP]; decide) second

#print axioms second_callback_error
end R1Z.PV_OptB_SourceSecondFailure
