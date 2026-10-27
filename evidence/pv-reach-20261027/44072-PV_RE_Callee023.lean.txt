import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee023
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.interpolation_basis_cell` (callee `host_sumcheck.interpolation_shift`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize) :
  ∃ next, host_sumcheck.interpolation_basis_cell (basis := basis) (k := k) (j := j) =
    (host_sumcheck.interpolation_shift basis k >>= next) := by
  unfold host_sumcheck.interpolation_basis_cell
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee023
