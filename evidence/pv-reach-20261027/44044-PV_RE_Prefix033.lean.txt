import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix033
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.opening_inactive` (op42).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) :
  ∃ next, @prover.opening_inactive _ _ q w =
    (aspis_core.field.wide_exact.WideExact.ZERO >>= next) := by
  unfold prover.opening_inactive
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix033
