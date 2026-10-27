import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix014
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.claim_mask_value` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize) :
  ∃ next, @host_semantic.claim_mask_value _ _ claims point =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_semantic.claim_mask_value
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix014
