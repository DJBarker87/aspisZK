import R1Z.PV_RE_FiniteRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryOutcomes
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]
variable {C : Type} (entropy : Entropy C) (pub : Public)
  (compiled : Compiled) (v : transport.Variant) (hash : Hash)
  (store : Store) (state : C) (k : Usize)

/-- All source branches at and beyond the cap terminate before entropy. -/
theorem exhausted (cap : k >= prover.ATTEMPT_CAP) :
    prover.retry_attempt entropy pub compiled v hash store state k =
      .ok (.Err .AttemptsExhausted,store) := by
  rw [unfold_retry]
  unfold step
  rw [if_pos cap]

theorem entropy_failure (active : ¬ k >= prover.ATTEMPT_CAP) (e : Error)
    (h : entropy.call_mut state k = .fail e) :
    prover.retry_attempt entropy pub compiled v hash store state k = .fail e := by
  rw [unfold_retry]
  unfold step
  rw [if_neg active, h]
  rfl

theorem entropy_diverges (active : ¬ k >= prover.ATTEMPT_CAP)
    (h : entropy.call_mut state k = .div) :
    prover.retry_attempt entropy pub compiled v hash store state k = .div := by
  rw [unfold_retry]
  unfold step
  rw [if_neg active, h]
  rfl

theorem entropy_error (active : ¬ k >= prover.ATTEMPT_CAP)
    (e : verifier.Error) (after : C)
    (h : entropy.call_mut state k = .ok (.Err e,after)) :
    prover.retry_attempt entropy pub compiled v hash store state k =
      .ok (.Err e,store) := by
  rw [unfold_retry]
  unfold step
  rw [if_neg active, h]
  rfl

/-- Rejection is the sole branch that enters the recursive continuation. -/
theorem rejected (active : ¬ k >= prover.ATTEMPT_CAP)
    (secret : Secrets) (after : C) (nextStore : Store)
    (h : entropy.call_mut state k = .ok (.Ok secret,after))
    (body : prover.prove_masked_attempt pub compiled v hash secret store =
      .ok (.Err .Rejected,nextStore)) :
    prover.retry_attempt entropy pub compiled v hash store state k =
      prover.retry_attempt entropy pub compiled v hash nextStore after
        (Usize.wrapping_add k 1#usize) := by
  rw [unfold_retry]
  unfold step
  rw [if_neg active, h]
  change (prover.prove_masked_attempt pub compiled v hash secret store >>= _) = _
  rw [body]
  rfl

#print axioms exhausted
#print axioms entropy_failure
#print axioms entropy_diverges
#print axioms entropy_error
#print axioms rejected
end R1Z.PV_RE_RetryOutcomes
