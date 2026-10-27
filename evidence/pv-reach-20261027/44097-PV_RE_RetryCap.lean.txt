import R1Z.PV_RE_RetryEntry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryCap
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_AttemptEntry PV_RE_RetryEntry
variable [ExternalTypes] [ExternalFuns]

theorem at_cap : (8#usize) >= prover.ATTEMPT_CAP := by
  change (8 : Nat) ≤ 8
  exact Nat.le_refl _

/-- Concrete non-vacuity of the exhausted-cap branch, without reducing an
entire retry run. It calls neither entropy nor the attempt continuation. -/
theorem exhausted {C : Type} (entropy : Entropy C) (pub : Public) (compiled : Compiled)
    (v : transport.Variant) (hash : Hash) (store : Store) (state : C) :
    prover.retry_attempt entropy pub compiled v hash store state 8#usize =
      .ok (.Err .AttemptsExhausted,store) := by
  obtain ⟨next,h⟩ := PV_RE_RetryEntry.first entropy pub compiled v hash store state 8#usize
  simpa only [at_cap,if_true] using h

#print axioms at_cap
#print axioms exhausted
end R1Z.PV_RE_RetryCap
