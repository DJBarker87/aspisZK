import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix030
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.inactive_sum_k` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) :
  ∃ next, @prover.inactive_sum_k _ _ values masks =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold prover.inactive_sum_k
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix030
