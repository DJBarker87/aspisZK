import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix032
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.opening_batch` (op254).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) :
  ∃ next, @prover.opening_batch _ _ coefficients gamma =
    (weights.powers 29#usize gamma >>= next) := by
  unfold prover.opening_batch
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix032
