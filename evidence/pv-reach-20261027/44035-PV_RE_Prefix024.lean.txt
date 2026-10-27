import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix024
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_sumcheck.merge_evaluations` (op64).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize) :
  ∃ next, @host_sumcheck.merge_evaluations _ _ evaluations assignments =
    (aspis_core.field.QM31.ZERO >>= next) := by
  unfold host_sumcheck.merge_evaluations
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix024
