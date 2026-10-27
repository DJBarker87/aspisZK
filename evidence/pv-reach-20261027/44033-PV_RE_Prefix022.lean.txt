import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix022
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.interpolate` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (values : Array aspis_core.field.QM31 28#usize) :
  ∃ next, @host_sumcheck.interpolate _ _ values =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_sumcheck.interpolate
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix022
