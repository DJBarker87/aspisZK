import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix031
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.inactive_sum_m31` (op55).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (values : Slice aspis_core.field.M31) (masks : Array Std.U16 64#usize) :
  ∃ next, @prover.inactive_sum_m31 _ _ values masks =
    (aspis_core.field.M31.ZERO >>= next) := by
  unfold prover.inactive_sum_m31
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix031
