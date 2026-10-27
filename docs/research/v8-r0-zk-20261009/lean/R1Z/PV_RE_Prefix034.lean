import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix034
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.opening_row` (op42).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gp : Array aspis_core.field.wide_exact.WideExact 29#usize) (row : Std.Usize) :
  ∃ next, @prover.opening_row _ _ coefficients gp row =
    (aspis_core.field.wide_exact.WideExact.ZERO >>= next) := by
  unfold prover.opening_row
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix034
