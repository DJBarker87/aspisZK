import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix013
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.boolean_point` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (row : Std.Usize) :
  ∃ next, @host_semantic.boolean_point _ _ row =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_semantic.boolean_point
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix013
