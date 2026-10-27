import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee007
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d` (callee `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (expected_factor_fingerprint : Std.U64) (active_masks : Array Std.U16 64#usize) :
  ∃ next, aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d (self := self) (hash := hash) (context := context) (expected_factor_fingerprint := expected_factor_fingerprint) (active_masks := active_masks) =
    (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context
      self context >>= next) := by
  unfold aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_zero_factor_d
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee007
