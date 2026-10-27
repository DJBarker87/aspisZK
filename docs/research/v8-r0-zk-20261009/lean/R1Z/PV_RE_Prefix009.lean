import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix009
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.base_coefficients` (op55).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (coefficients : Array aspis_core.field.wide_exact.WideExact 1024#usize) :
  ∃ next, @host_commitment.base_coefficients _ _ coefficients =
    (aspis_core.field.M31.ZERO >>= next) := by
  unfold host_commitment.base_coefficients
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix009
