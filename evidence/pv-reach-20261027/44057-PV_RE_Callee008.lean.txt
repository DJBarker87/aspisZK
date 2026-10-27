import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee008
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1` (callee `aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (h1 : Slice aspis_core.field.QM31) (padding : Slice aspis_core.field.QM31) :
  ∃ next, aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1 (h1 := h1) (padding := padding) =
    (aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows >>= next) := by
  unfold aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_h1_padding_mask_v1
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee008
