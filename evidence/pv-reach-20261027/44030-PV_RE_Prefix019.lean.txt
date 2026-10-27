import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix019
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.lean_copy_row_values` (op228).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (trace : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1) (lambda : aspis_core.field.QM31) :
  ∃ next, @host_semantic.lean_copy_row_values _ _ trace lambda =
    (aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1 >>= next) := by
  unfold host_semantic.lean_copy_row_values
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix019
