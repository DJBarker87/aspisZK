import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix023
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.interpolation_basis` (op55).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (i : Std.Usize) :
  ∃ next, @host_sumcheck.interpolation_basis _ _ i =
    (aspis_core.field.M31.ZERO >>= next) := by
  unfold host_sumcheck.interpolation_basis
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix023
