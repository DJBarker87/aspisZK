import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix003
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context` (op111).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  ∃ next, @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context _ _ self context =
    (aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT >>= next) := by
  unfold aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix003
