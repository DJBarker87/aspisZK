import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee003
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible` (callee `aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (statement_digest : Array Std.U8 32#usize) (mask_nonce : Array Std.U8 32#usize) :
  ∃ next, aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible (self := self) (statement_digest := statement_digest) (mask_nonce := mask_nonce) =
    (aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path
      { self with last_error := none } mask_nonce >>= next) := by
  unfold aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee003
