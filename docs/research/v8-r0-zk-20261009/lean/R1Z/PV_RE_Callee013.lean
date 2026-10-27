import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee013
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_commitment.validate_commitment_lanes` (callee `host_commitment.validate_commitment_lanes_loop`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) :
  ∃ next, host_commitment.validate_commitment_lanes (messages := messages) (lanes := lanes) =
    (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize >>= next) := by
  unfold host_commitment.validate_commitment_lanes
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee013
