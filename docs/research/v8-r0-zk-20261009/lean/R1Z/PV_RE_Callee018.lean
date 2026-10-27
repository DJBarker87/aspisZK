import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee018
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.check_secure_column` (callee `host_semantic.check_secure_column_loop`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (column : Array aspis_core.field.QM31 1024#usize) :
  ∃ next, host_semantic.check_secure_column (column := column) =
    (host_semantic.check_secure_column_loop column 0#usize >>= next) := by
  unfold host_semantic.check_secure_column
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee018
