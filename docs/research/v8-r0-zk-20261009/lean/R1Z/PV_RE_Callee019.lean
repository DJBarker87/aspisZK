import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee019
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.initial_mask_value` (callee `host_semantic.boolean_point`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (row : Std.Usize) :
  ∃ next, host_semantic.initial_mask_value (columns := columns) (row := row) =
    (host_semantic.boolean_point row >>= next) := by
  unfold host_semantic.initial_mask_value
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee019
