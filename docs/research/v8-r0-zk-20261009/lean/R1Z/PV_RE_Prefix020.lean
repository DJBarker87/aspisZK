import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix020
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.lift` (op61).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (x : aspis_core.field.M31) :
  ∃ next, @host_semantic.lift _ _ x =
    (aspis_core.field.CM31.from_m31 x >>= next) := by
  unfold host_semantic.lift
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix020
