import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee020
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.no_pole` (callee `host_semantic.lean_copy_row_values`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (lambda : aspis_core.field.QM31) (chi : aspis_core.field.QM31) :
  ∃ next, host_semantic.no_pole (compiled := compiled) (lambda := lambda) (chi := chi) =
    (host_semantic.lean_copy_row_values compiled.trace lambda >>= next) := by
  unfold host_semantic.no_pole
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee020
