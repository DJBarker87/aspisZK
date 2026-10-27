import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee021
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.point_claims` (callee `r1_wire.statement_points`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) :
  ∃ next, host_semantic.point_claims (columns := columns) (point := point) =
    (r1_wire.statement_points point >>= next) := by
  unfold host_semantic.point_claims
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee021
