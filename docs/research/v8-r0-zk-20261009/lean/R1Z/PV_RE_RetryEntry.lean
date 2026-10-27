import R1Z.PV_RE_AttemptEntry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryEntry
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_AttemptEntry
variable [ExternalTypes] [ExternalFuns]
abbrev Entropy (C : Type) := core.ops.function.FnMut C Usize
  (core.result.Result Secrets verifier.Error)
abbrev RetryReply := Result ((core.result.Result prover.RetriedProof verifier.Error) × Store)

/-- Exact branch before the entropy callback. The rejected branch is literal;
no entropy, hash or attempt-body reduction is used. -/
theorem first {C : Type} (entropy : Entropy C) (pub : Public) (compiled : Compiled)
    (v : transport.Variant) (hash : Hash) (store : Store) (state : C) (k : Usize) :
    ∃ next : (core.result.Result Secrets verifier.Error × C) → RetryReply,
      prover.retry_attempt entropy pub compiled v hash store state k =
        if k >= prover.ATTEMPT_CAP then .ok (.Err .AttemptsExhausted,store)
        else (entropy.call_mut state k >>= next) := by
  rw [prover.retry_attempt]
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_RetryEntry
