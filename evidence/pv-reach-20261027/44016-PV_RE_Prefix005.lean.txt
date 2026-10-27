import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix005
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1` (op132).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (trace : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (material : aspis_prover.state_only_hiding.StateOnlyMaskMaterial) :
  ∃ next, @aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1 _ _ trace material =
    (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 >>= next) := by
  unfold aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix005
