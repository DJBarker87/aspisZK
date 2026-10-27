import R1Z.PV_RE_RetryEntry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryZero
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_AttemptEntry PV_RE_RetryEntry
variable [ExternalTypes] [ExternalFuns]

theorem below : ¬ ((0#usize) >= prover.ATTEMPT_CAP) := by
  change ¬ (8 ≤ (0 : Nat))
  omega

/-- The actual initial retry position takes the entropy branch for every
public/compiled payload. This does not assume that entropy succeeds. -/
theorem first {C : Type} (entropy : Entropy C) (pub : Public) (compiled : Compiled)
    (v : transport.Variant) (hash : Hash) (store : Store) (state : C) :
    ∃ next : (core.result.Result Secrets verifier.Error × C) → RetryReply,
      prover.retry_attempt entropy pub compiled v hash store state 0#usize =
        (entropy.call_mut state 0#usize >>= next) := by
  obtain ⟨next,h⟩ := PV_RE_RetryEntry.first entropy pub compiled v hash store state 0#usize
  exact ⟨next,by simpa only [below,if_false] using h⟩

#print axioms below
#print axioms first
end R1Z.PV_RE_RetryZero
