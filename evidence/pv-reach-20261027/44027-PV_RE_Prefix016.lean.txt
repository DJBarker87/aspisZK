import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix016
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.extra` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (coefficients : Array aspis_core.field.QM31 1024#usize) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
  ∃ next, @host_semantic.extra _ _ coefficients a b =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_semantic.extra
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix016
