import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix002
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d` (op134).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  ∃ next, @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d _ _ self hash context =
    (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1 >>= next) := by
  unfold aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix002
