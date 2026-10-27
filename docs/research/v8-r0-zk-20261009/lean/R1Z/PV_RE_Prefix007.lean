import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix007
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows` (op133).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
   :
  ∃ next, @aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows _ _  =
    (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1 >>= next) := by
  unfold aspis_prover.state_only_hiding.pool_v1_pair_forest_copy_active_rows
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix007
