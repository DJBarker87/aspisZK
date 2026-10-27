import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix029
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.fixed_k_column` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (values : Slice aspis_core.field.QM31) :
  ∃ next, @prover.fixed_k_column _ _ values =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold prover.fixed_k_column
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix029
